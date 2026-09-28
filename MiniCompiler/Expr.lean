import MiniCompiler.Env

namespace MiniCompiler

/-
========================================
算术表达式 AST
========================================
-/

inductive AExpr where
  | const : Int → AExpr
  | var   : String → AExpr
  | add   : AExpr → AExpr → AExpr
  | sub   : AExpr → AExpr → AExpr
  | mul   : AExpr → AExpr → AExpr
deriving Repr, DecidableEq


/-
========================================
布尔表达式 AST
========================================
-/

inductive BExpr where
  | eq   : AExpr → AExpr → BExpr
  | less : AExpr → AExpr → BExpr
  | and  : BExpr → BExpr → BExpr
  | not  : BExpr → BExpr
deriving Repr


/-
========================================
算术表达式解释器
========================================
-/

def evalA : AExpr → Env → Int
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
布尔表达式解释器
========================================
-/

def evalB : BExpr → Env → Bool
  | BExpr.eq e1 e2, env =>
      decide (evalA e1 env = evalA e2 env)

  | BExpr.less e1 e2, env =>
      decide (evalA e1 env < evalA e2 env)

  | BExpr.and b1 b2, env =>
      evalB b1 env && evalB b2 env

  | BExpr.not b, env =>
      !evalB b env


/-
========================================
测试环境
========================================
-/

def exampleEnv : Env :=
  update
    (update emptyEnv "x" 10)
    "y" 3


/-
========================================
算术表达式测试
========================================
-/

-- 1 + 2 * 3
def exampleA1 : AExpr :=
  AExpr.add
    (AExpr.const 1)
    (AExpr.mul
      (AExpr.const 2)
      (AExpr.const 3))


-- x * 2 + y
def exampleA2 : AExpr :=
  AExpr.add
    (AExpr.mul
      (AExpr.var "x")
      (AExpr.const 2))
    (AExpr.var "y")


-- (10 - 3) * (2 + 4)
def exampleA3 : AExpr :=
  AExpr.mul
    (AExpr.sub
      (AExpr.const 10)
      (AExpr.const 3))
    (AExpr.add
      (AExpr.const 2)
      (AExpr.const 4))


#eval evalA exampleA1 exampleEnv
-- 7

#eval evalA exampleA2 exampleEnv
-- 23

#eval evalA exampleA3 exampleEnv
-- 42


/-
========================================
布尔表达式测试
========================================
-/

-- x < y
def exampleB1 : BExpr :=
  BExpr.less
    (AExpr.var "x")
    (AExpr.var "y")


-- (x < y) AND NOT (x = 0)
def exampleB2 : BExpr :=
  BExpr.and
    (BExpr.less
      (AExpr.var "x")
      (AExpr.var "y"))
    (BExpr.not
      (BExpr.eq
        (AExpr.var "x")
        (AExpr.const 0)))


#eval evalB exampleB1 exampleEnv
-- false

#eval evalB exampleB2 exampleEnv
-- false

end MiniCompiler
