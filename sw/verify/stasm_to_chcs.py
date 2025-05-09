from graphviz import Source
from z3 import Implies, And, Or, Not, If, Store, Const, Int, Function, BoolSort, Ints, IntSort, K, Array
import z3
z3.set_param(proof=True)
from hw.base.verification_utils import CHCs


def mk_int_array(data):
    a = K(IntSort(), 0)
    for i, d in enumerate(data):
        a = Store(a, i, d)
    return a

def extract_instructions_and_labels(program):
    instructions = []
    label_to_index = {}
    instr_index = 0
    for item in program:
        if isinstance(item, str) and item.endswith(":"):
            label = item[:-1]  # Remove ":"
            label_to_index[label] = instr_index
        elif isinstance(item, tuple):
            instructions.append(item)
            instr_index += 1
        else:
            raise ValueError(f"Invalid program item: {item}")
    return instructions, label_to_index


def create_checs(pre_condition, input_vars, program, post_condition):
    """
    Create a set of CHCs for a given program.
    """

    memory = Array("memory", IntSort(), IntSort())
    stack = Array("stack", IntSort(), IntSort())
    sp, r0, r1 = Ints('sp r0 r1')

    sigma = input_vars + [memory, stack, sp, r0, r1]
    # Create the CHCs
    chcs = []

    U = {i: Function(f"U{i}", *(v.sort() for v in sigma), BoolSort())
         for i in range(len(program)+1)}
    # Initial state
    chcs.append(Implies(pre_condition, U[0](*sigma)))


    for i in range(len(program)):  # Do for i in range
        instruction = program[i]
        if instruction[0] == 'PUSH':
            value = instruction[1]
            chcs.append(Implies(U[i](*sigma), U[i+1](*input_vars, memory, Store(stack, sp, value), sp + 1, r0, r1)))
        elif instruction[0] == 'POP':
            amount_of_registers = instruction[1]
            if amount_of_registers == 1:
                # For POP 1: r0 gets the top of stack (stack[sp-1]), stack pointer decreases by 1
                chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, memory, stack, sp - 1, stack[sp - 1], r1)))
            elif amount_of_registers == 2:
                # For POP 2: r0 gets top of stack (stack[sp-1]), r1 gets second element (stack[sp-2]),
                # stack pointer decreases by 2
                chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, memory, stack, sp - 2, stack[sp - 1], stack[sp - 2])))
        elif instruction[0] == 'ALU':
            op = instruction[1]
            # Compute result based on operation using r0 and r1
            if op == 'ADD':
                result = r0 + r1
            elif op == 'MUL':
                result = r0 * r1
            elif op == 'SUB':
                result = r0 - r1
            elif op == "LT":
                result = If(r0 < r1, 1, 0)
            else:
                raise ValueError(f"Unknown ALU operation: {op}")
            # Push result onto stack at sp, increment sp
            chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, memory, Store(stack, sp, result), sp + 1, r0, r1)))
        elif instruction[0] == "DUP":
            offset = instruction[1]
            chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, memory, Store(stack, sp, stack[sp - offset]), sp + 1, r0, r1)))
        elif instruction[0] == "JMP":
            addr = program.index(instruction[1] + ":")
            chcs.append(Implies(U[i](*sigma), U[addr](*input_vars, memory, stack, sp, r0, r1)))
        elif instruction[0] == "JZ":
            addr = program.index(instruction[1] + ":")
            chcs.append(Implies(And(U[i](*sigma), r0 == 0), U[addr](*input_vars, memory, stack, sp, r0, r1)))
            chcs.append(Implies(And(U[i](*sigma), r0 != 0), U[i + 1](*input_vars, memory, stack, sp, r0, r1)))
        elif instruction[0] == "JNZ":
            addr = program.index(instruction[1] + ":")
            chcs.append(Implies(And(U[i](*sigma), r0 == 0), U[addr](*input_vars, memory, stack, sp, r0, r1)))
            chcs.append(Implies(And(U[i](*sigma), r0 != 0), U[i + 1](*input_vars, memory, stack, sp, r0, r1)))
        elif instruction[0] == "STOR":
            # Store r0 at memory[r1]
            chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, Store(memory, r1, r0), stack, sp, r0, r1)))
        elif instruction[0] == "LOAD":
            # Load memory[r1] and push to stack
            chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, Store(stack, sp, memory[r1]), stack, sp + 1, r0, r1)))

    # Final state
    chcs.append(Implies(U[len(program)](*sigma), post_condition))
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
                 post_condition=stack[sp] == 1 + 5 * 13)

    print(chcs.solve())


if __name__ == '__main__':
    main()
