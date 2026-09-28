import MiniCompiler.Env

namespace MiniCompiler

/-
========================================
算术表达式
========================================
-/

inductive AExpr where
  | const : Int -> AExpr
  | var   : String -> AExpr
  | add   : AExpr -> AExpr -> AExpr
  | sub   : AExpr -> AExpr -> AExpr
  | mul   : AExpr -> AExpr -> AExpr
deriving Repr

/--
算术表达式解释器
-/
def evalA : AExpr -> Env -> Int
  | AExpr.const n, _ =>
      n

  | AExpr.var name, env =>
      env name

  | AExpr.add e1 e2, env =>
      evalA e1 env + evalA e2 env

  | AExpr.sub e1 e2, env =>
      evalA e1 env - evalA e2 env

  | AExpr.mul e1 e2, env =>
      evalA e1 env * evalA e2 env


/-
========================================
布尔表达式
========================================
-/

inductive BExpr where
  | eq   : AExpr -> AExpr -> BExpr
  | less : AExpr -> AExpr -> BExpr
  | and  : BExpr -> BExpr -> BExpr
  | not  : BExpr -> BExpr
deriving Repr

/--
布尔表达式解释器
-/
def evalB : BExpr -> Env -> Bool
  | BExpr.eq e1 e2, env =>
      evalA e1 env == evalA e2 env

  | BExpr.less e1 e2, env =>
      evalA e1 env < evalA e2 env

  | BExpr.and b1 b2, env =>
      evalB b1 env && evalB b2 env

  | BExpr.not b, env =>
      !evalB b env


/-
========================================
测试表达式
========================================
-/

-- 1 + 2 * 3
def example1 : AExpr :=
  AExpr.add
    (AExpr.const 1)
    (AExpr.mul
      (AExpr.const 2)
      (AExpr.const 3))

-- x * 2 + y
def example2 : AExpr :=
  AExpr.add
    (AExpr.mul
      (AExpr.var "x")
      (AExpr.const 2))
    (AExpr.var "y")

-- x < y
def exampleBool1 : BExpr :=
  BExpr.less
    (AExpr.var "x")
    (AExpr.var "y")

-- (x < y) AND NOT (x = 0)
def exampleBool2 : BExpr :=
  BExpr.and
    (BExpr.less
      (AExpr.var "x")
      (AExpr.var "y"))
    (BExpr.not
      (BExpr.eq
        (AExpr.var "x")
        (AExpr.const 0)))

end MiniCompiler
