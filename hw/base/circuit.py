import z3

def net_to_smt(working_block):
    """
    This function generates SMT constraints for a given working block.
    It returns a list of SMT constraints.

    Args:
        working_block: A list of net objects.

    Returns:
        A list of SMT constraints.
    """
    constraints = []
    
    # Create a mapping from wire names to Z3 bit vectors
    wire_map = {}
    
    # First pass: create Z3 variables for all wires
    for net in working_block:
        for arg in net.args:
            if arg.name not in wire_map:
                wire_map[arg.name] = z3.BitVec(arg.name, arg.bitwidth)
        for dest in net.dests:
            if dest.name not in wire_map:
                wire_map[dest.name] = z3.BitVec(dest.name, dest.bitwidth)
    
    # Second pass: generate constraints for each net
    for net in working_block:
        if net.op == 'w':  # Wire connection
            src = wire_map[net.args[0].name]
            dst = wire_map[net.dests[0].name]
            constraints.append(src == dst)
            
        elif net.op == '&':  # AND operation
            result = wire_map[net.dests[0].name]
            args = [wire_map[arg.name] for arg in net.args]
            constraints.append(result == z3.And(*args))
            
        elif net.op == '|':  # OR operation
            result = wire_map[net.dests[0].name]
            args = [wire_map[arg.name] for arg in net.args]
            constraints.append(result == z3.Or(*args))
            
        elif net.op == '^':  # XOR operation
            result = wire_map[net.dests[0].name]
            args = [wire_map[arg.name] for arg in net.args]
            constraints.append(result == z3.Xor(*args))
            
        elif net.op == '~':  # NOT operation
            result = wire_map[net.dests[0].name]
            arg = wire_map[net.args[0].name]
            constraints.append(result == z3.Not(arg))
            
        elif net.op == 'c':  # Concatenation
            result = wire_map[net.dests[0].name]
            args = [wire_map[arg.name] for arg in net.args]
            constraints.append(result == z3.Concat(*args))
            
        elif net.op == 's':  # Selection
            result = wire_map[net.dests[0].name]
            arg = wire_map[net.args[0].name]
            start = net.op_param[0]
            end = net.op_param[1]
            constraints.append(result == z3.Extract(end, start, arg))
            
        elif net.op == 'r':  # Register
            result = wire_map[net.dests[0].name]
            arg = wire_map[net.args[0].name]
            constraints.append(result == arg)  # For combinational verification, treat registers as wires
            
        elif net.op == 'x':  # Constant
            result = wire_map[net.dests[0].name]
            value = net.op_param
            constraints.append(result == value)
    
    return constraints