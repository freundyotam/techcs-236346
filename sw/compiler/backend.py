from collections import namedtuple
from ir import Const, Var, Seq, If, FuncDef


class CompilerBackend:
    def __init__(self):
        self.stack_state = []
        self.code = []
        self.sig = CompilerBackend.FuncSignature('', 0, False)
        self.labels = set()
        
    def emit(self, code):
        if not isinstance(code, list): code = [code]
        for instr in code:
            self.code.append(instr)
        
    def push(self, e):
        self.stack_state.append(e)
        
    def pop(self, c=1):
        if c > 0:
            del self.stack_state[-c:]
        
    def fresh_label(self):
        for i in range(0, 1 << 30):
            l = f"{self.sig.name}:{i}"
            if l not in self.labels:
                self.labels.add(l)
                return l
        assert False, 'too many labels!'
    
    def _shorthand(self, e):
        if isinstance(e, int): return Const(e)
        elif isinstance(e, list): return Seq(e)
        else:
            return e

    def func(self, signature, body=None):
        if body is None and isinstance(signature, FuncDef):
            signature, body = self._sig_of(signature), signature.body
        if body is None: raise TypeError('body is missing')
        self.sig = signature
        self.emit([self.sig.name])
        self.expr(body)
        assert self.sig.ret  # @todo void
        r, nargs = int(self.sig.ret), self.sig.nargs
        if nargs:
            self.emit([('YANK', (r, nargs))])
        self.emit([('POP', r + 1), ('RET', r)])
        self.pop(r)
        assert not self.stack_state  # stack must be empty or that's a compiler bug
    
    def funcs(self, func_defs):
        for fd in func_defs: self.func(fd)
    
    def _sig_of(self, fd):
        return CompilerBackend.FuncSignature(fd.name, fd.nargs, fd.ret)
                
    def expr(self, e):
        e = self._shorthand(e)
        if isinstance(e, Const):
            self.emit(('PUSH', e.value))
        elif isinstance(e, Var):
            self.emit(('DUP', e.offset + len(self.stack_state)))
        elif isinstance(e, If):
            self.expr(e.cond)
            l1 = self.fresh_label()
            self.emit([('POP', 1), ('JZ', l1)])
            self.pop()
            self.expr(e.then)
            self.pop()   # pop both "then" and "else" exprs, later `e` is pushed instead
            l2 = self.fresh_label()
            self.emit([('JMP', l2), l1])
            self.expr(e.else_)
            self.pop()
            self.emit(l2)
        elif isinstance(e, Seq):
            assert(e.stmts)  # @todo handle empty and unit-returning statements

            start_level = len(self.stack_state)
            for stmt in e.stmts: self.expr(stmt)
            npushed = len(self.stack_state) - start_level
            assert npushed >= 0
            if npushed > 1: self.emit(('YANK', (1, npushed - 1)))
            self.pop(npushed)   # later `e` is pushed
        else:
            op = e[0]
            if op == '@' or op == '@.':
                call_func = e[1]; args = e[2:]
                if op == '@':
                    ret_loc = self.fresh_label()
                    self.emit(('PUSH', ret_loc)); self.push('ret_loc')
            else:
                args = e[1:]
            for sub in args: self.expr(sub)
            if   op == '+':  self.emit([('POP', 2), ('ALU', 'ADD')])
            elif op == '*':  self.emit([('POP', 2), ('ALU', 'MUL')])
            elif op == '-':  self.emit([('POP', 2), ('ALU', 'SUB')])
            elif op == '0-': self.emit([('POP', 1), ('ALU', 'NEG')])
            elif op == '<':  self.emit([('POP', 2), ('ALU', 'LT')])
            elif op == '|':  self.emit([('POP', 2), ('ALU', 'OR')])
            elif op == '&':  self.emit([('POP', 2), ('ALU', 'AND')])
            elif op == '~':  self.emit([('POP', 1), ('ALU', 'NOT')])
            elif op == '<<': self.emit([('POP', 2), ('ALU', 'SHL')])
            elif op == '>>': self.emit([('POP', 2), ('ALU', 'SHR')])
            elif op == '@':
                self.emit([('JMP', call_func), ret_loc])
                self.pop()  # so that we pop len(args)+1 in total
            elif op == '@.':
                tn, sn = len(args), len(self.stack_state) + self.sig.nargs
                if sn > tn:
                    assert tn > 0
                    self.emit(('YANK', (tn, sn - tn)))
                self.emit(('JMP', call_func))
                # stack semantics is a bit weird in this case
                self.pop(len(self.stack_state)); self.push(e); return
            elif op == 'ignore':
                self.emit(('POP', 1)); self.pop()
                return  # do not push `e`
            else:
                raise KeyError(op)
                
            self.pop(len(args))
            
        self.push(e)

    FuncSignature = namedtuple('FuncSignature', ['name', 'nargs', 'ret'])
    

def asm_pretty(asm):
    '''
    Assembly text pretty-printer.
    '''
    for insn in asm:
        if isinstance(insn, str):
            print(f"{insn}:")
        else:
            e = [(",".join(map(str, s)) if isinstance(s, tuple) else str(s))
                 for s in insn]
            print(f"  {' '.join(e)}")
    
def cli_main():
    import sys
    from parser import IRParser
    
    parser = IRParser()
    funcs = parser(sys.stdin.read())
    
    c = CompilerBackend()
    c.funcs(funcs)
    asm_pretty(c.code)
    
    
if __name__ == '__main__':
    cli_main()