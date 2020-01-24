# OpaqueJmps solver for IDA
Simple script that is trying to find opaque jumps in specified function and resolve their. 
By "resolve" i mean reaching of the path created by condition jumps from section of code before that. 
If exist only one static (int) solution (for True or False branch) that mean that jump is opaque jump.
    
    **** code ***
    JZ something   <- EIP=(Condition ? A : B); True == (Condition == True and Condition == False) 
    **** code ****                                             

### Workflow
 * Translates code from IDA to MiasmIR
 * Finds all cjmp in IRCFG
 * Creates DependencyGraph for EIP/RIP and asks a solution for that symbol
 * Checks if only one ExprInt solution found then it is an opaque jump
 
### Some limitations
* Sometimes that solver make a false prediction (Not found some solutions)
* For very big graph it takes much more time.
* And ofcourse it's not work in all possible cases =)