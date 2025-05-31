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


def create_chcs(pre_condition, input_vars, program, post_condition):
    memory = Array("memory", IntSort(), IntSort())
    stack = Array("stack", IntSort(), IntSort())
    sp, r0, r1 = Ints('sp r0 r1')

    sigma = input_vars + [memory, stack, sp, r0, r1]
    # Extract instructions and labels
    instructions, label_to_index = extract_instructions_and_labels(program)
    chcs = []

    # States based on instructions only
    U = {i: Function(f"U{i}", *(v.sort() for v in sigma), BoolSort())
         for i in range(len(instructions) + 1)}
    # Initial state
    chcs.append(Implies(pre_condition, U[0](*sigma)))

    for i, instruction in enumerate(instructions):
        if instruction[0] == 'PUSH':
            value = instruction[1]
            chcs.append(Implies(U[i](*sigma), U[i+1](*input_vars, memory, Store(stack, sp + 1, value), sp + 1, r0, r1)))
        elif instruction[0] == 'POP':
            amount_of_registers = instruction[1]
            if amount_of_registers == 1:
                chcs.append(Implies(And(U[i](*sigma), sp >= 0),
                                   U[i + 1](*input_vars, memory, stack, sp - 1, stack[sp], r1)))
            elif amount_of_registers == 2:
                chcs.append(Implies(And(U[i](*sigma), sp >= 1),
                                    U[i + 1](*input_vars, memory, stack, sp - 2, stack[sp - 1], stack[sp])))
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
            chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, memory, Store(stack, sp + 1, result), sp + 1, r0, r1)))
        elif instruction[0] == "DUP":
            offset = instruction[1]
            chcs.append(Implies(And(U[i](*sigma), sp >= offset),
                               U[i + 1](*input_vars, memory, Store(stack, sp + 1, stack[sp - offset]), sp + 1, r0, r1)))
        elif instruction[0] == "JMP":
            label = instruction[1]
            if label not in label_to_index:
                raise ValueError(f"Label {label} not found")
            addr = label_to_index[label]
            chcs.append(Implies(U[i](*sigma), U[addr](*input_vars, memory, stack, sp, r0, r1)))
        elif instruction[0] == "JZ":
            label = instruction[1]
            if label not in label_to_index:
                raise ValueError(f"Label {label} not found")
            addr = label_to_index[label]
            chcs.append(Implies(And(U[i](*sigma), r0 == 0), U[addr](*input_vars, memory, stack, sp, r0, r1)))
            chcs.append(Implies(And(U[i](*sigma), r0 != 0), U[i + 1](*input_vars, memory, stack, sp, r0, r1)))
        elif instruction[0] == "JNZ":
            label = instruction[1]
            if label not in label_to_index:
                raise ValueError(f"Label {label} not found")
            addr = label_to_index[label]
            chcs.append(Implies(And(U[i](*sigma), r0 != 0), U[addr](*input_vars, memory, stack, sp, r0, r1)))
            chcs.append(Implies(And(U[i](*sigma), r0 == 0), U[i + 1](*input_vars, memory, stack, sp, r0, r1)))
        elif instruction[0] == "STOR":
            # Store r0 at memory[r1]
            chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, Store(memory, r1, r0), stack, sp, r0, r1)))
        elif instruction[0] == "LOAD":
            chcs.append(Implies(U[i](*sigma), U[i + 1](*input_vars, memory, Store(stack, sp + 1, memory[r0]), sp + 1, r0, r1)))

    # Final state after all instructions
    chcs.append(Implies(U[len(instructions)](*sigma), post_condition))
    return CHCs(chcs)


def main():
    def READ_FROM_ARRAY():
        """
        Pops the top as index and then base addr and push the value at that index from the array at addr
        :return:
        """
        return [
            ("POP", 2),  # r0 = index, r1 = base addr
            ("ALU", "ADD"),  # push base addr + index
            ("POP", 1),  # r0 = base addr + index
            ("LOAD", 0),  # push value at base addr + index
        ]

    program_find_max = [
        ("PUSH", 0),
        ("DUP", 2),
        *READ_FROM_ARRAY(),
        # Stack is now: [arr_addr, length, a[0]]
        # Now let's define max = a[0]
        ("DUP", 0),
        # Stack is now: [arr_addr, length, a[0], mx=a[0]]
        # Now after we saved a[0] on stack we can use this mem for i
        # lets set i = 1 to memory address &a[0]
        ("PUSH", 1),
        ("DUP", 4),
        ("POP", 2),
        ("STOR", 0),
        "CHECK_COND:",
        # First put i in r0 and n in r1
        ("DUP", 3),
        ("POP", 1),
        ("LOAD", 0),
        ("DUP", 3),
        ("POP", 2),
        # Check i < n
        ("ALU", "LT"),
        ("POP", 1),
        ("JNZ", "LOOP_BODY"),
        ("JMP", "END"),
        "LOOP_BODY:",
        # read i from mem and put on stack
        ("DUP", 3),
        ("POP", 1),
        ("LOAD", 0),
        # put base addr on stack
        ("DUP", 4),
        # Put a[i] on stack
        *READ_FROM_ARRAY(),
        # Put mx on stack
        ("DUP", 1),
        # now stack is [base_addr, n, a[0], mx, a[i], mx]
        ("POP", 2),
        ("ALU", "LT"),
        # now stack is [base_addr, n, a[0], mx, (result a[i] < mx)]
        ("POP", 1),
        ("JNZ", "INC_I"),
        ("JMP", "UPDATE"),
        "INC_I:",
        # Put i on stack
        ("PUSH", 0),
        ("DUP", 4),
        *READ_FROM_ARRAY(),
        ("PUSH", 1),
        ("POP", 2),
        ("ALU", "ADD"),
        ("DUP", 4),
        ("POP", 2),
        ("STOR", 0),
        ("JMP", "CHECK_COND"),
        "UPDATE:",
        ("POP", 1),  # remove old mx from stack
        # Push base addr
        ("DUP", 2),
        ("POP", 1),
        ("LOAD", 0),
        # Now i is on top of stack
        ("DUP", 3),
        *READ_FROM_ARRAY(),  # so now a[i] is where mx was on stack so mx = a[i]
        ("JMP", "INC_I"),
        "END:",
        # Restore a[0]:
        # Put a[0] on stack (we saved it before):
        ("DUP", 1),
        # Put base_addr on stack:
        ("DUP", 4),
        ("POP", 2),
        ("STOR", 0),
        ("POP", 2),
        ("POP", 1),
        ("POP", 1)
    ]
    stack = Array("stack", IntSort(), IntSort())
    memory = Array("memory", IntSort(), IntSort())
    sp, r0, r1 = Ints('sp r0 r1')

    pre_condition = And(
        stack[0] == 0, stack[1] == 1, sp == 2,
        memory[0] == 2
    )
    chcs = create_chcs(pre_condition=pre_condition,
                       input_vars=[],
                       program=program_find_max,
                       post_condition=And(sp == 0,
                                          memory[0] == 2,
                                          r1 == 9999))
    d = {'xform.inline_eager': False, 'xform.inline_linear': False}
    print(chcs.solve(d))


if __name__ == '__main__':
    main()
