from z3 import Implies, And, Or, Not, If, Store, Const, Int, Function, BoolSort, Ints, IntSort, K, Array
import z3
z3.set_param(proof=True)
from hw.base.verification_utils import CHCs


def mk_int_array(data):
    a = K(IntSort(), 0)
    for i, d in enumerate(data):
        a = Store(a, i, d)
    return a


def create_checs(pre_condition, input_vars, program, post_condition):
    """
    Example:
    { stack = [a, b] }
    PUSH 13
    POP 2; ALU MUL
    POP 2; ALU ADD
    POP 1
    { ret = a + b * 13 }

    gives
    CHCs([
    #Implies(And(stack[0] == a, stack[1] == b, sp == 2), U[0](sigma)),
    Implies(And(stack == mk_int_array([a,b]), sp == 2), U[0](sigma)),
    Implies(U[0](sigma), U[1](a, b, Store(stack, sp, 13), sp + 1)),
    Implies(U[1](sigma), U[2](a, b, Store(stack, sp - 2, stack[sp - 1] * stack[sp - 2]), sp - 1)),
    Implies(U[2](sigma), U[3](a, b, Store(stack, sp - 2, stack[sp - 1] + stack[sp - 2]), sp - 1)),
    Implies(U[3](sigma), U[4](a, b, stack, sp - 1)),
    Implies(U[4](sigma), stack[sp] == a + b * 13),
    ])
    """

    # TODO Where should we define those variables? should we get them from outside the function? or here?
    stack = Array("stack", IntSort(), IntSort())
    sp, r0, r1 = Ints('sp r0 r1')

    sigma = input_vars + [stack, sp, r0, r1]
    # Create the CHCs
    chcs = []

    U = {i: Function(f"U{i}", *(v.sort() for v in sigma), BoolSort())
         for i in range(len(program)+1)}
    # Initial state
    chcs.append(Implies(pre_condition, U[0](sigma)))


    for i in range(len(program)):  # Do for i in range
        instruction = program[i]
        if instruction[0] == 'PUSH':
            value = instruction[1]
            chcs.append(Implies(U[i](sigma), U[i+1]([*input_vars, Store(stack, sp, value), sp + 1, r0, r1])))
        elif instruction[0] == 'POP':
            amount_of_registers = instruction[1]
            if amount_of_registers == 1:
                # For POP 1: r0 gets the top of stack (stack[sp-1]), stack pointer decreases by 1
                chcs.append(Implies(U[i](sigma), U[i + 1](*input_vars, stack, sp - 1, stack[sp], r1)))
            elif amount_of_registers == 2:
                # For POP 2: r0 gets top of stack (stack[sp-1]), r1 gets second element (stack[sp-2]),
                # stack pointer decreases by 2
                chcs.append(Implies(U[i](sigma), U[i + 1](*input_vars, stack, sp - 2, stack[sp], stack[sp - 1])))
        elif instruction[0] == 'ALU':
            op = instruction[1]
            # Compute result based on operation using r0 and r1
            if op == 'ADD':
                result = r0 + r1
            elif op == 'MUL':
                result = r0 * r1
            elif op == 'SUB':
                result = r0 - r1
            else:
                raise ValueError(f"Unknown ALU operation: {op}")
            # Push result onto stack at sp, increment sp
            chcs.append(Implies(U[i](sigma), U[i + 1](*input_vars, Store(stack, sp, result), sp + 1, r0, r1)))
        elif instruction[0] == "DUP":
            offset = instruction[1]
            chcs.append(Implies(U[i](sigma), U[i + 1](*input_vars, Store(stack, sp, stack[sp - offset]), sp + 1, r0, r1)))
        elif instruction[0] == "JMP":
            addr = program.index(instruction[1] + ":")
            chcs.append(Implies(U[i](sigma), U[addr](*input_vars, stack, sp, r0, r1)))
        elif instruction[0] == "JZ":
            addr = program.index(instruction[1] + ":")
            chcs.append(Implies(And(U[i](sigma), r0 == 0), U[addr](*input_vars, stack, sp, r0, r1)))
            chcs.append(Implies(And(U[i](sigma), r0 != 0), U[i + 1](*input_vars, stack, sp, r0, r1)))
        elif instruction[0] == "JNZ":
            addr = program.index(instruction[1] + ":")
            chcs.append(Implies(And(U[i](sigma), r0 == 0), U[addr](*input_vars, stack, sp, r0, r1)))
            chcs.append(Implies(And(U[i](sigma), r0 != 0), U[i + 1](*input_vars, stack, sp, r0, r1)))

    # Final state
    chcs.append(Implies(U[len(program)](sigma), post_condition))
    return CHCs(chcs)


def main():
    stack = Array("stack", IntSort(), IntSort())
    sp, r0, r1 = Ints('sp r0 r1')
    chcs = create_checs(pre_condition=And(stack[0] == 1, stack[1] == 5, sp == 2),
                 input_vars=[],
                 program=
                 [("PUSH", 13),
                  ("POP", 2),
                  ("ALU", "MUL"),
                  ("POP", 2),
                  ("ALU", "ADD"),
                  ("POP", 1)],
                 post_condition=stack[sp] == 6 * 13)
    print(chcs.solve())


if __name__ == '__main__':
    main()
