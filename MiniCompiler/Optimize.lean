import MiniCompiler.Expr

namespace MiniCompiler

/-
========================================
Add Optimization
========================================

Constant folding:
  1 + 2 -> 3

Algebraic simplification:
  e + 0 -> e
========================================
-/

def optAdd (a b : AExpr) : AExpr :=
  match a, b with

  | AExpr.const x, AExpr.const y =>
      AExpr.const (x + y)

  | a, AExpr.const y =>
      if y = 0 then
        a
      else
        AExpr.add a (AExpr.const y)

  | a, b =>
      AExpr.add a b


/-
========================================
Sub Optimization
========================================

Constant folding:
  5 - 2 -> 3

Algebraic simplification:
  e - 0 -> e
========================================
-/

def optSub (a b : AExpr) : AExpr :=
  match a, b with

  | AExpr.const x, AExpr.const y =>
      AExpr.const (x - y)

  | a, AExpr.const y =>
      if y = 0 then
        a
      else
        AExpr.sub a (AExpr.const y)

  | a, b =>
      AExpr.sub a b


/-
========================================
Mul Optimization
========================================

Constant folding:
  2 * 3 -> 6

Algebraic simplification:
  e * 1 -> e
========================================
-/

def optMul (a b : AExpr) : AExpr :=
  match a, b with

  | AExpr.const x, AExpr.const y =>
      AExpr.const (x * y)

  | a, AExpr.const y =>
      if y = 1 then
        a
      else
        AExpr.mul a (AExpr.const y)

  | a, b =>
      AExpr.mul a b


/-
========================================
Recursive Optimizer
========================================
-/

def optimize : AExpr → AExpr

  | AExpr.const n =>
      AExpr.const n

  | AExpr.var name =>
      AExpr.var name

  | AExpr.add e1 e2 =>
      optAdd
        (optimize e1)
        (optimize e2)

  | AExpr.sub e1 e2 =>
      optSub
        (optimize e1)
        (optimize e2)

  | AExpr.mul e1 e2 =>
      optMul
        (optimize e1)
        (optimize e2)


/-
========================================
Correctness of optAdd
========================================
-/

theorem evalA_optAdd
    (a b : AExpr)
    (env : Env) :
    evalA (optAdd a b) env =
      evalA a env + evalA b env := by

  cases b with

  | const y =>

      cases a with

      | const x =>
          rfl

      | var name =>

          by_cases h : y = 0

          · simp [optAdd, evalA, h]

          · simp [optAdd, evalA, h]

      | add a1 a2 =>

          by_cases h : y = 0

          · simp [optAdd, evalA, h]

          · simp [optAdd, evalA, h]

      | sub a1 a2 =>

          by_cases h : y = 0

          · simp [optAdd, evalA, h]

          · simp [optAdd, evalA, h]

      | mul a1 a2 =>

          by_cases h : y = 0

          · simp [optAdd, evalA, h]

          · simp [optAdd, evalA, h]


  | var name =>

      cases a <;>
        rfl


  | add b1 b2 =>

      cases a <;>
        rfl


  | sub b1 b2 =>

      cases a <;>
        rfl


  | mul b1 b2 =>

      cases a <;>
        rfl


/-
========================================
Correctness of optSub
========================================
-/

theorem evalA_optSub
    (a b : AExpr)
    (env : Env) :
    evalA (optSub a b) env =
      evalA a env - evalA b env := by

  cases b with

  | const y =>

      cases a with

      | const x =>
          rfl

      | var name =>

          by_cases h : y = 0

          · simp [optSub, evalA, h]

          · simp [optSub, evalA, h]

      | add a1 a2 =>

          by_cases h : y = 0

          · simp [optSub, evalA, h]

          · simp [optSub, evalA, h]

      | sub a1 a2 =>

          by_cases h : y = 0

          · simp [optSub, evalA, h]

          · simp [optSub, evalA, h]

      | mul a1 a2 =>

          by_cases h : y = 0

          · simp [optSub, evalA, h]

          · simp [optSub, evalA, h]


  | var name =>

      cases a <;>
        rfl


  | add b1 b2 =>

      cases a <;>
        rfl


  | sub b1 b2 =>

      cases a <;>
        rfl


  | mul b1 b2 =>

      cases a <;>
        rfl


/-
========================================
Correctness of optMul
========================================
-/

theorem evalA_optMul
    (a b : AExpr)
    (env : Env) :
    evalA (optMul a b) env =
      evalA a env * evalA b env := by

  cases b with

  | const y =>

      cases a with

      | const x =>
          rfl

      | var name =>

          by_cases h : y = 1

          · simp [optMul, evalA, h]

          · simp [optMul, evalA, h]

      | add a1 a2 =>

          by_cases h : y = 1

          · simp [optMul, evalA, h]

          · simp [optMul, evalA, h]

      | sub a1 a2 =>

          by_cases h : y = 1

          · simp [optMul, evalA, h]

          · simp [optMul, evalA, h]

      | mul a1 a2 =>

          by_cases h : y = 1

          · simp [optMul, evalA, h]

          · simp [optMul, evalA, h]


  | var name =>

      cases a <;>
        rfl


  | add b1 b2 =>

      cases a <;>
        rfl


  | sub b1 b2 =>

      cases a <;>
        rfl


  | mul b1 b2 =>

      cases a <;>
        rfl


/-
========================================
Milestone 1

Semantic preservation of optimization
========================================

For every expression e
and every environment env:

evalA (optimize e) env
=
evalA e env
========================================
-/

theorem optimize_correct
    (e : AExpr)
    (env : Env) :
    evalA (optimize e) env =
      evalA e env := by

  induction e with

  | const n =>

      rfl


  | var name =>

      rfl


  | add e1 e2 ih1 ih2 =>

      calc

        evalA
            (optimize
              (AExpr.add e1 e2))
            env

            =
            evalA (optimize e1) env
            +
            evalA (optimize e2) env := by

              exact
                evalA_optAdd
                  (optimize e1)
                  (optimize e2)
                  env


        _ =
            evalA e1 env
            +
            evalA e2 env := by

              rw [ih1, ih2]


        _ =
            evalA
              (AExpr.add e1 e2)
              env := by

              rfl


  | sub e1 e2 ih1 ih2 =>

      calc

        evalA
            (optimize
              (AExpr.sub e1 e2))
            env

            =
            evalA (optimize e1) env
            -
            evalA (optimize e2) env := by

              exact
                evalA_optSub
                  (optimize e1)
                  (optimize e2)
                  env


        _ =
            evalA e1 env
            -
            evalA e2 env := by

              rw [ih1, ih2]


        _ =
            evalA
              (AExpr.sub e1 e2)
              env := by

              rfl


  | mul e1 e2 ih1 ih2 =>

      calc

        evalA
            (optimize
              (AExpr.mul e1 e2))
            env

            =
            evalA (optimize e1) env
            *
            evalA (optimize e2) env := by

              exact
                evalA_optMul
                  (optimize e1)
                  (optimize e2)
                  env


        _ =
            evalA e1 env
            *
            evalA e2 env := by

              rw [ih1, ih2]


        _ =
            evalA
              (AExpr.mul e1 e2)
              env := by

              rfl


/-
========================================
Tests
========================================

Original:

(1 + 2) * (x + 0)

Optimized:

3 * x
========================================
-/

def optimizeExample : AExpr :=
  AExpr.mul

    (AExpr.add
      (AExpr.const 1)
      (AExpr.const 2))

    (AExpr.add
      (AExpr.var "x")
      (AExpr.const 0))


#eval optimizeExample

#eval optimize optimizeExample


/-
Another test:

(10 - 0) * 1

becomes:

10
-/

def optimizeExample2 : AExpr :=
  AExpr.mul

    (AExpr.sub
      (AExpr.const 10)
      (AExpr.const 0))

    (AExpr.const 1)


#eval optimizeExample2

#eval optimize optimizeExample2


end MiniCompiler
