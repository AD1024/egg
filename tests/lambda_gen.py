import ast
import inspect

class Currying(ast.NodeTransformer):
    
    def __init__(self, bindings, inline=True):
        self.inline = inline
        self.bindings = bindings

    def visit_Assign(self, node: ast.Assign):
        target = self.visit(node.targets[0])
        rhs = self.visit(node.value)
        self.bindings[str(target)] = rhs
        return ast.Assign(targets=node.targets, value=rhs, lineno=node.lineno)
        
    def visit_Name(self, node: ast.Name):
        if self.inline and node.id in self.bindings and self.bindings[node.id].__class__.__name__ == 'function':
            return uncurry_ast(self.bindings[node.id], self.bindings)
        return node
    
    def visit_Lambda(self, node: ast.Lambda):
        args = node.args
        if len(args.args) == 1:
            node.body = self.visit(node.body)
            return node
        else:
            def curried(args):
                if len(args) == 1:
                    return ast.Lambda(args=args, body=self.visit(node.body))
                else:
                    return ast.Lambda(args=[args[0]],
                                      body=curried(args[1:]))
            return curried(args.args)
    
    def visit_Call(self, node: ast.Call):
        args = node.args
        if len(args) == 1:
            node.func = self.visit(node.func)
            node.args = [self.visit(arg) for arg in args]
            return node
        else:
            def curried_call(args):
                if len(args) == 1:
                    ret = ast.Call()
                    ret.func = self.visit(node.func)
                    ret.args = args
                    ret.keywords = []
                    return ret
                else:
                    return ast.Call(func=curried_call(args[:-1]), args=[args[-1]], keywords=[])
            return curried_call(args)

    def visit_FunctionDef(self, node: ast.FunctionDef):
        assert len(node.args.args) == 0, "no args is allowed for outmost definition"
        return ast.Module(body=list(map(self.visit, node.body)), type_ignores={})

class ToEggExpr(ast.NodeVisitor):

    cont = lambda x, visitor: visitor.visit(x)

    def visit_Call(self, node: ast.Call) -> str:
        assert len(node.args) == 1, "Need currying first!"
        func = self.visit(node.func)
        arg = self.visit(node.args[0])
        return f'(app {func} {arg})'

    def visit_arg(self, node: ast.arg) -> str:
        return f'(var {node.arg})'

    def visit_Lambda(self, node: ast.Lambda) -> str:
        args = node.args if isinstance(node.args, list) else node.args.args
        assert len(args) == 1, "Need currying first!"
        body = self.visit(node.body)
        return f'(lam {args[0].arg} {body})'

    def visit_Name(self, node: ast.Name) -> str:
        return f'(var {node.id})'
    
    def visit_IfExp(self, node: ast.IfExp) -> str:
        cond = self.visit(node.test)
        ifb = self.visit(node.body)
        elb = self.visit(node.orelse)
        return f'(if {cond} {ifb} {elb})'
    
    def visit_Constant(self, node: ast.Constant) -> str:
        return str(node.n)
    
    def visit_BinOp(self, node: ast.BinOp) -> str:
        op = {
            ast.Add: '+',
            ast.Sub: '-',
            ast.Mult: '*',
            ast.Div: '/',
            ast.FloorDiv: '/',
        }.get(type(node.op))
        if not op:
            raise SyntaxError(f'{node.op} is not supported')
        return f'({op} {self.visit(node.left)} {self.visit(node.right)})'
    
    def visit_Compare(self, node: ast.Compare) -> str:
        assert len(node.ops) == 1, "do not chain compares!"
        op = {
            ast.Eq: '=',
            # other ops are not specified in egg yet
        }.get(type(node.ops))
        if not op:
            raise SyntaxError(f'{node.op} is not supported')
        return f'({op} {self.visit(node.left)} {self.visit(node.comparators[0])})'

    def _module_builder(self, body: list[ast.expr], cont) -> str:
        if len(body) == 1:
            stmt = body[0]
            if isinstance(stmt, ast.Return):
                stmt: ast.Return = stmt
                expr = stmt.value
            elif isinstance(stmt, ast.Expr):
                stmt: ast.Expr = stmt
                expr = stmt.value
            else:
                raise SyntaxError(f'Expecting a return or an expr at the end, got: {stmt} of type {type(stmt)}')
            return cont(expr)
        stmt = body[0]
        assert isinstance(stmt, ast.Assign)
        assert len(stmt.targets) == 1, "Pls assign to 1 variable each time!"
        return self._module_builder(body[1:], lambda x: f'(let {stmt.targets[0].id} {self.visit(stmt.value)} {cont(x)})')

    def visit_Module(self, node: ast.Module) -> str:
        assert len(node.body) >= 1, "empty body found!"
        return self._module_builder(node.body, self.visit)


def uncurry_ast(assign, bindings, inline=True):
    src = inspect.getsource(assign).strip()
    rt = ast.parse(src)
    if inline:
        rt = Currying(bindings, inline=True).visit(rt.body[0].value)
    else:
        rt = Currying(bindings, inline=True).visit(rt)
    return rt

def uncurry(assign, bindings, inline=True):
    rt = uncurry_ast(assign, bindings, inline)
    try:
        return eval(ast.unparse(rt))
    except Exception as _:
        return rt

def test_currying():
    lam = lambda x, y, z: x + y + z
    app = lambda x, y, z: lam(x, y, z)
    # ==> lambda x: lambda y: lambda z: x + y + z
    uncurried_app = uncurry(app, locals())
    assert app(1, 2, 3) == uncurried_app(1)(2)(3) == 6

def assign_module():
    f = lambda x: x + 1
    g = lambda x, y: x + y
    return f(g(1, 2))

if __name__ == '__main__':
    test_currying()
    mod = uncurry(assign_module, locals(), inline=False)
    print(ToEggExpr().visit(mod.body[0]))