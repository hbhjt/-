namespace MiniCompiler

inductive Expr where
  | const : Int -> Expr
  | add   : Expr -> Expr -> Expr
  | sub   : Expr -> Expr -> Expr
  | mul   : Expr -> Expr -> Expr
deriving Repr

def eval : Expr → Int
  | Expr.const n =>
      n
  | Expr.add e1 e2 =>
      eval e1 + eval e2
  | Expr.sub e1 e2 =>
      eval e1 - eval e2
  | Expr.mul e1 e2 =>
      eval e1 * eval e2

def example1 : Expr :=
  Expr.add
    (Expr.const 1)
    (Expr.const 2)

def example2 : Expr :=
  Expr.add
    (Expr.const 1)
    (Expr.mul
      (Expr.const 2)
      (Expr.const 3))

-- (10 - 3) * (2 + 4)
def example3 : Expr :=
  Expr.mul
    (Expr.sub
      (Expr.const 10)
      (Expr.const 3))
    (Expr.add
      (Expr.const 2)
      (Expr.const 4))

#check Expr
#check eval

#eval eval example1
#eval eval example2
#eval eval example3

end MiniCompiler
