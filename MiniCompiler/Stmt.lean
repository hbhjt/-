import MiniCompiler.Expr

namespace MiniCompiler

/-
========================================
Statement AST
========================================
-/

inductive Stmt where

  /-- 什么都不做 -/
  | skip : Stmt

  /-- x := expr -/
  | assign :
      String →
      AExpr →
      Stmt

  /-- s1 ; s2 -/
  | seq :
      Stmt →
      Stmt →
      Stmt

  /-- if cond then s1 else s2 -/
  | ifThenElse :
      BExpr →
      Stmt →
      Stmt →
      Stmt

  /-- while cond do body -/
  | whileDo :
      BExpr →
      Stmt →
      Stmt

deriving Repr


/-
========================================
测试程序

x := 0;

while x < 3 do
    x := x + 1
========================================
-/

def counterProgram : Stmt :=
  Stmt.seq

    (Stmt.assign
      "x"
      (AExpr.const 0))

    (Stmt.whileDo

      (BExpr.less
        (AExpr.var "x")
        (AExpr.const 3))

      (Stmt.assign
        "x"
        (AExpr.add
          (AExpr.var "x")
          (AExpr.const 1))))


/-
========================================
另一个测试程序

x := 5;

if x < 10 then
    y := 1
else
    y := 2
========================================
-/

def ifProgram : Stmt :=
  Stmt.seq

    (Stmt.assign
      "x"
      (AExpr.const 5))

    (Stmt.ifThenElse

      (BExpr.less
        (AExpr.var "x")
        (AExpr.const 10))

      (Stmt.assign
        "y"
        (AExpr.const 1))

      (Stmt.assign
        "y"
        (AExpr.const 2)))


/-
无限循环：

while 1 = 1 do
    skip
-/

def infiniteLoop : Stmt :=
  Stmt.whileDo

    (BExpr.eq
      (AExpr.const 1)
      (AExpr.const 1))

    Stmt.skip

end MiniCompiler
