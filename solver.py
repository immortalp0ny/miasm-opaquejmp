from struct import pack

import idaapi
import ida_bytes
import ida_kernwin as kw

from collections import namedtuple
from miasm.core.locationdb import LocationDB
from miasm.analysis.depgraph import DependencyGraph

from miasm.core.bin_stream_ida import bin_stream_ida
from miasm.core.bin_stream import bin_stream
from miasm.ir.ir import IRBlock, IRCFG
from miasm.core.asmblock import AsmCFG, AsmBlock
from miasm.arch.x86.arch import conditional_branch
from miasm.analysis.machine import Machine
from miasm.expression.expression import Expr, LocKey, ExprId

LOG_LEVEL = 2


def log(msg, code='+'):
    levels = {'@': -1,  # Important messages
              '~': -2,  # Critical errors
              '+': 0,  # Normal messages
              '!': 1,  # Warnings errors
              '?': 2,  # Info messages
              }

    msg_level = levels.get(code, None)

    if msg_level is None:
        raise Exception(f"Unknown msg code {msg_level}")

    if msg_level > LOG_LEVEL:
        return

    print(f"[{code}] {msg}")


def get_target_arch():
    info = idaapi.get_inf_structure()

    if info.is_64bit():
        bits = 64
    elif info.is_32bit():
        bits = 32
    else:
        bits = 16

    return bits


def get_target_path():
    return idaapi.get_input_file_path()


def get_stream():
    return bin_stream_ida()


def get_vars(cond: Expr, vars=[]):
    if cond.is_id():
        vars.append(cond)

    return cond


def is_static_expr(cond):
    cvars = []

    cond.visit(lambda cond: get_vars(cond, cvars))

    if not cvars:
       return True

    return False


def simple_unwrap_expr(expr: Expr, loc_db: LocationDB):
    ra = -1
    if expr.is_int():
        ra = int(expr)
    elif expr.is_loc():
        ra = loc_db.get_location_offset(expr.loc_key)
        if ra is None:
            ra = -1

    return ra


IRLoop = namedtuple("IRLoop", "head tail body")


class IDALifter:
    def __init__(self, arch: int, stream: bin_stream):
        self._arch = arch
        self._machine: Machine = Machine(f"x86_{self._arch}")
        self._bs: bin_stream = stream
        self._mdis = self._machine.dis_engine(self._bs)

    def _new_flow(self, start_ea):
        """
        Transform code from IDA to asm and ir cfg
        :param start_ea: Address of a function
        :return: None
        """
        self._ir_arch = self._machine.ira(self._mdis.loc_db)
        self._asm_cfg: AsmCFG = self._mdis.dis_multiblock(start_ea)
        self._ir_cfg: IRCFG = self._ir_arch.new_ircfg_from_asmcfg(self._asm_cfg)

        self._root_ir: IRBlock = self._ir_cfg.get_block(start_ea)

        self._root = self._root_ir.loc_key

        self._loops = []

        for back_edge, body in self._ir_cfg.compute_natural_loops(self._root):
            tail, head = back_edge

            l = IRLoop(head=tail, tail=head, body=body)

            self._loops.append(l)

    @property
    def ip(self):
        """
        Get instruction pointer symbol
        :return:
        """
        if self._arch == 32:
            return ExprId("EIP", 32)
        elif self._arch == 64:
            return ExprId("RIP", 64)
        elif self._arch == 16:
            return ExprId("IP", 16)

        raise Exception(f"Unknown bitness {self._arch}")

    def _is_loop_head(self, loc: LocKey):
        for l in self._loops:
            if l.head == loc:
                return True, l

        return False, None

    def _is_loop_tail(self, loc: LocKey):
        for l in self._loops:
            if l.tail == loc:
                return True, l

        return False, None

    def _get_loop(self, loc: LocKey):
        status, loop = self._is_loop_head(loc)
        if status:
            return loop

        status, loop = self._is_loop_body(loc)
        if status:
            return loop

        status, loop = self._is_loop_tail(loc)
        if status:
            return loop

        return None

    def _is_loop_body(self, loc: LocKey):
        for l in self._loops:
            if loc in l.body:
                return True, l

        return False, None

    def update(self, ea):
        self._new_flow(ea)


class IDAFlowRecovery(IDALifter):
    def __init__(self, ea: int, stream: bin_stream, arch: int, ids_check=True, mem_check=True):
        self._ea = ea

        super().__init__(arch, stream)

        self.update(ea)

        self._ids_check = ids_check
        self._mem_check = mem_check

        self._flow_patches_map = {}
        self._branch_conditions = []

        self._mark_branch_conditions()

    @property
    def flow_fixes(self):
        return self._flow_patches_map

    def _mark_branch_conditions(self):
        """
        For any cjmp in CFG tries to find all solutions for []IP symbol
        :return:
        """
        ir_loc: LocKey
        ir_block: IRBlock

        for ir_loc, ir_block in self._ir_cfg.blocks.items():
            # check for detect current location that is head or tail of natural loop

            is_head, _ = self._is_loop_head(ir_loc)
            is_tail, _ = self._is_loop_tail(ir_loc)

            if not ir_block.dst.is_cond() or is_head or is_tail:
                continue

            dg = DependencyGraph(self._ir_cfg)

            dst_solutions = set()

            for sol in dg.get(ir_loc, [self.ip], ir_block.assignblks[-1].instr.offset, set()):
                try:
                    solutions = sol.emul(self._ir_arch)
                except NotImplementedError as ex:
                    log(f"Unsupported expression in location - {ir_loc}", code='!')

                    dst_solutions = set()
                    break

                ip_expr = solutions.get(self.ip)

                # print(f"{ir_loc} - {hex(self._ir_cfg.loc_db.get_location_offset(ir_loc))} - {ip_expr}")

                if not ip_expr.is_int() and not ip_expr.is_loc() and not is_static_expr(ip_expr):
                    dst_solutions = set()
                    break

                if not ip_expr.is_int() and not ip_expr.is_loc():
                    log(f"Static ip expressions unsupported now [{ip_expr}]")

                    # invlidate dst_solutions
                    dst_solutions = set()

                    break

                dst_solutions.update([ip_expr])

            if len(dst_solutions) != 1:
                continue

            static_dst = dst_solutions.pop()
            static_addr = simple_unwrap_expr(static_dst, self._ir_cfg.loc_db)

            if static_addr == -1:
                log(f"Oops ... {static_dst}. Fail resolve dst by a simple approach", code='!')
                continue

            self._flow_patches_map[self._ir_cfg.loc_db.get_location_offset(ir_loc)] = static_addr

    def apply(self):
        """
        Apply patches to found opaque branch
        :return: None
        """
        for src, dst in self._flow_patches_map.items():
            asm_block: AsmBlock = self._mdis.dis_block(src)

            if asm_block.lines[-1].name not in conditional_branch:
                log(f"Unsupported asm pattern at {hex(src)}", code='!')
                continue

            patch_addr = asm_block.lines[-1].offset

            opcode1 = ida_bytes.get_byte(patch_addr)

            # Fast and Furious
            if opcode1 == 0x0F:
                ida_bytes.patch_bytes(patch_addr, b"\xe9" + pack("<I", (dst - (patch_addr + 5) & (2**32 - 1))))
            elif ((opcode1 & 0xe0) == 0xe0) or ((opcode1 & 0x70) == 0x70):
                ida_bytes.patch_byte(patch_addr, 0xeb)
            else:
                log(f"Unknown first part of opcode at {hex(patch_addr)}", code='!')
                continue

            log(f"Apply patch JCC -> JMP at {hex(patch_addr)}")


ifr = IDAFlowRecovery(kw.get_screen_ea(), get_stream(), get_target_arch())
ifr.apply()
