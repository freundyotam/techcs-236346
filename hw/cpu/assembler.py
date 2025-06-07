from collections import namedtuple
import array
from hw.cpu import instruction_set as isa


class Assembly(namedtuple('Assembly', ['words', 'start_addr', 'label_addrs'])):
    def to_bin(self):
        assert _array_sanity()  # ensure that 'I' marks 32-bit words
        return array.array('I', self.words).tobytes()
    def save_bin(self, filename='a.bin'):
        with open(filename, 'wb') as f:
            f.write(self.to_bin())

class Label:
    def __init__(self, l): self.name = l


def asm_bin(l, start_addr=0x0):
    return asm_ex(l, start_addr).to_bin()

def asm(l, start_addr=0x0):
    labels = {}
    
    def first_pass(l):
        for instr in l:
            if isinstance(instr, list):
                for i in first_pass(instr): yield i
            elif isinstance(instr, str):
                yield Label(instr)
            else:
                yield instr
                
    def second_pass(l):
        addr = start_addr
        for instr in l:
            if isinstance(instr, Label):
                labels[instr.name] = addr
            else:
                yield instr
                addr += 1

    def warg(op, arg):
        if isinstance(op, str): op = isa.CODES[op]
        if isinstance(arg, Label): arg = labels[arg.name]
        elif isinstance(arg, str):
            arg = isa.CODES[arg] if op == isa.ALU else labels[arg]
        elif isinstance(arg, tuple):
            arg = (arg[1] << 4) | arg[0]
        return (arg << 4) | op
                
    def third_pass(l):
        for instr in l:
            if isinstance(instr, tuple):
                yield warg(*instr)
            else:
                yield instr
                
    l = list(second_pass(first_pass(l)))
    return Assembly(list(third_pass(l)), start_addr, labels)


def disasm(l):
    from instruction_set import MNEMONICS as M
    if isinstance(l, bytes):
        assert _array_sanity()
        l = array.array('I', l)
    return [(M.get(instr & 0xf, '??'), instr >> 4) for instr in l]

def with_addr(l, start_addr=0):
    for i, el in enumerate(l):
        yield (start_addr + i, el)

def disasm_with_addr(l, start_addr=0):
    return with_addr(disasm(l), start_addr)

def disasm_pretty(l, start_addr=0):
    for addr, (op, arg) in disasm_with_addr(l, start_addr):
        print("%04x %s %x" % (addr, op, arg))


def _array_sanity():
    return array.array('I', [0xdead]).tobytes() == b'\xad\xde\x00\x00'

def chunk16(u32a):
    return [(u32 >> bi) & 0xffff for u32 in u32a for bi in [0, 16]]    

if __name__ == '__main__':
    prog = ['horiz',
 ('DUP', 2),
 ('DUP', 2),
 ('POP', 2),
 ('ALU', 'LT'),
 ('POP', 1),
 ('JZ', 'horiz:0'),
 ('PUSH', 1),
 ('JMP', 'horiz:1'),
 'horiz:0',
 ('DUP', 1),
 ('DUP', 3),
 ('POP', 2),
 ('ALU', 'LT'),
 ('POP', 1),
 ('JZ', 'horiz:2'),
 ('PUSH', 65535),
 ('JMP', 'horiz:3'),
 'horiz:2',
 ('PUSH', 0),
 'horiz:3',
 'horiz:1',
 ('DUP', 0),
 ('POP', 1),
 ('JZ', 'horiz:4'),
 ('PUSH', 'horiz:5'),
 ('DUP', 4),
 ('DUP', 3),
 ('JMP', 'block'),
 'horiz:5',
 ('POP', 1),
 ('PUSH', 'horiz:6'),
 ('JMP', 'wait'),
 'horiz:6',
 ('POP', 1),
 ('DUP', 3),
 ('DUP', 1),
 ('POP', 2),
 ('ALU', 'ADD'),
 ('DUP', 3),
 ('DUP', 3),
 ('YANK', (3, 4)),
 ('JMP', 'horiz'),
 ('JMP', 'horiz:7'),
 'horiz:4',
 ('PUSH', 0),
 'horiz:7',
 ('YANK', (1, 1)),
 ('YANK', (1, 3)),
 ('POP', 2),
 ('RET', 1),
 'vert',
 ('DUP', 1),
 ('DUP', 1),
 ('POP', 2),
 ('ALU', 'LT'),
 ('POP', 1),
 ('JZ', 'vert:0'),
 ('PUSH', 1),
 ('JMP', 'vert:1'),
 'vert:0',
 ('DUP', 0),
 ('DUP', 2),
 ('POP', 2),
 ('ALU', 'LT'),
 ('POP', 1),
 ('JZ', 'vert:2'),
 ('PUSH', 65535),
 ('JMP', 'vert:3'),
 'vert:2',
 ('PUSH', 0),
 'vert:3',
 'vert:1',
 ('DUP', 0),
 ('POP', 1),
 ('JZ', 'vert:4'),
 ('PUSH', 'vert:5'),
 ('DUP', 4),
 ('DUP', 4),
 ('JMP', 'block'),
 'vert:5',
 ('POP', 1),
 ('PUSH', 'vert:6'),
 ('JMP', 'wait'),
 'vert:6',
 ('POP', 1),
 ('DUP', 3),
 ('DUP', 3),
 ('DUP', 2),
 ('POP', 2),
 ('ALU', 'ADD'),
 ('DUP', 3),
 ('YANK', (3, 4)),
 ('JMP', 'vert'),
 ('JMP', 'vert:7'),
 'vert:4',
 ('PUSH', 0),
 'vert:7',
 ('YANK', (1, 1)),
 ('YANK', (1, 3)),
 ('POP', 2),
 ('RET', 1),
 'square',
 ('PUSH', 'square:0'),
 ('DUP', 1),
 ('DUP', 2),
 ('DUP', 5),
 ('POP', 2),
 ('ALU', 'ADD'),
 ('DUP', 4),
 ('JMP', 'horiz'),
 'square:0',
 ('POP', 1),
 ('PUSH', 'square:1'),
 ('DUP', 1),
 ('DUP', 4),
 ('POP', 2),
 ('ALU', 'ADD'),
 ('DUP', 3),
 ('DUP', 4),
 ('DUP', 6),
 ('POP', 2),
 ('ALU', 'ADD'),
 ('JMP', 'vert'),
 'square:1',
 ('POP', 1),
 ('PUSH', 'square:2'),
 ('DUP', 1),
 ('DUP', 4),
 ('POP', 2),
 ('ALU', 'ADD'),
 ('DUP', 2),
 ('DUP', 4),
 ('DUP', 6),
 ('POP', 2),
 ('ALU', 'ADD'),
 ('JMP', 'horiz'),
 'square:2',
 ('POP', 1),
 ('PUSH', 'square:3'),
 ('DUP', 1),
 ('DUP', 3),
 ('DUP', 5),
 ('POP', 2),
 ('ALU', 'ADD'),
 ('DUP', 4),
 ('JMP', 'vert'),
 'square:3',
 ('POP', 1),
 ('PUSH', 0),
 ('YANK', (1, 3)),
 ('POP', 2),
 ('RET', 1),
 'main',
 ('PUSH', 'main:0'),
 ('PUSH', 5),
 ('PUSH', 5),
 ('PUSH', 10),
 ('JMP', 'square'),
 'main:0',
 ('POP', 1),
 ('POP', 2),
 ('RET', 1)]
    print(asm(prog))