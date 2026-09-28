import MiniCompiler.Env

namespace MiniCompiler

/-
========================================
Arithmetic Expressions
========================================
-/

inductive AExpr where
  | const : Int → AExpr
  | var   : String → AExpr
  | add   : AExpr → AExpr → AExpr
  | sub   : AExpr → AExpr → AExpr
  | mul   : AExpr → AExpr → AExpr
deriving Repr, DecidableEq


/--
算术表达式求值。
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
Boolean Expressions
========================================
-/

inductive BExpr where
  | eq   : AExpr → AExpr → BExpr
  | less : AExpr → AExpr → BExpr
  | and  : BExpr → BExpr → BExpr
  | not  : BExpr → BExpr
deriving Repr, DecidableEq


/--
布尔表达式求值。
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
一些测试表达式
========================================
-/

-- 1 + 2 * 3
def arithmeticExample : AExpr :=
  AExpr.add
    (AExpr.const 1)
    (AExpr.mul
      (AExpr.const 2)
      (AExpr.const 3))


-- x * 2 + y
def variableExample : AExpr :=
  AExpr.add
    (AExpr.mul
      (AExpr.var "x")
      (AExpr.const 2))
    (AExpr.var "y")


-- x < 10
def booleanExample : BExpr :=
  BExpr.less
    (AExpr.var "x")
    (AExpr.const 10)

end MiniCompiler
