inductive Expr where
  | const : Int → Expr
  | add : Expr -> Expr -> Expr
  | sub : Expr -> Expr -> Expr
  | mul : Expr -> Expr -> Expr

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

#check example1
#check example2
