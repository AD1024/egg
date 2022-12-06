import ast
import inspect

class Currying(ast.NodeTransformer):
    
    def __init__(self, bindings):
        self.bindings = bindings
        
    def visit_Name(self, node: ast.Name):
        if node.id in self.bindings and self.bindings[node.id].__class__.__name__ == 'function':
            print(node.id)
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
                    return ast.Lambda(args=args[0],
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

def uncurry_ast(assign, bindings):
    src = inspect.getsource(assign).strip()
    rt = ast.parse(src)
    rt = Currying(bindings).visit(rt.body[0].value)
    return rt

def uncurry(assign, bindings):
    rt = uncurry_ast(assign, bindings)
    print(ast.unparse(rt))
    return eval(ast.unparse(rt))

def test_currying():
    lam = lambda x, y, z: x + y + z
    app = lambda x, y, z: lam(x, y, z)
    # ==> lambda x: lambda y: lambda z: x + y + z
    uncurried_app = uncurry(app, locals())
    assert app(1, 2, 3) == uncurried_app(1)(2)(3) == 6
    
def lambda_calculus():
    succ = lambda x: lambda s: lambda z: s(x(z))
    zero = lambda s: lambda z: z
    plus = lambda x: lambda y: lambda s: lambda z: x(s)(y(s)(z))
    times = lambda x: lambda y: lambda s: lambda z: x(y(s))(z)
    true = lambda t: lambda f: t
    false = lambda t: lambda f: f
    
    ite = lambda c: lambda t: lambda f: c(t)(f)
    is_zero = lambda x: x(lambda _: false)(true)
    pair = lambda x: lambda y: lambda f: f(x)(y)
    fst = lambda p: p(lambda x: lambda _: x)
    snd = lambda p: p(lambda _: lambda y: y)
    
    zero_pair = pair(zero)(zero)
    succ_pair = lambda p: pair(succ(fst(p)))(fst(p))
    pred = lambda x: snd(x(succ_pair)(zero_pair))
    
    rec_zp = lambda n: pair(n)(zero)
    rec_succ = lambda f: lambda p: pair(f(snd(p))(fst(p)))(succ(snd(p)))
    natrec = lambda f: lambda n: fst(n(rec_succ(f))(rec_zp(n)))
    
    # nat_rec_inlined = uncurry(natrec, locals())
    nil = lambda f: lambda x: x
    cons = lambda x: lambda xs: lambda f: lambda z: f(x)(xs(f)(z))
    
    seq0 = lambda x: pair(pred(x))(nil)
    seqS = lambda p: pair(pred(fst(p)))(cons(fst(p))(snd(p)))
    
    seq = lambda x: snd (x(seqS)(seq0(x)))
    
    is_nil = lambda xs: xs(lambda _: lambda _: false)(true)
    insert_init = pair(true)(nil)
    andb = lambda x: lambda y: x(y)(false)
    le = lambda x: lambda y: is_zero(pred(y(x)))
    eq = lambda x: lambda y: andb(le(x)(y))(le(y)(x))
    length = lambda xs: xs(lambda hd: lambda tl: succ(tl))(zero)
    
    insert = lambda x: lambda xs: is_nil(xs)\
                                    (cons(x)(xs))\
                                    (snd(xs
                                         (lambda hd: lambda tl: (le(x)(hd))
                                            ((fst(tl))
                                                (pair(false)(cons(hd)(cons(x)(snd(tl)))))
                                                (pair(false)(cons(x)(snd(tl)))))
                                            (eq(length(snd(tl)))(pred(length(xs)))
                                                (pair(false)(cons(x)(cons(hd)(snd(tl)))))
                                                (pair(fst(tl))(cons(hd)(snd(tl))))))(insert_init)))
    insert_prime = uncurry(insert, locals())
    
    
if __name__ == '__main__':
    # test_currying()
    lambda_calculus()