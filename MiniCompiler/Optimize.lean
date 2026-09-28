import MiniCompiler.Expr

namespace MiniCompiler

/-
==================================================
局部优化器：加法
==================================================

优化规则：

0 + e   ==> e
e + 0   ==> e

Const x + Const y
    ==> Const (x + y)
-/

def optAdd (a b : AExpr) : AExpr :=
  if a = AExpr.const 0 then
    b
  else if b = AExpr.const 0 then
    a
  else
    match a, b with
    | AExpr.const x, AExpr.const y =>
        AExpr.const (x + y)
    | _, _ =>
        AExpr.add a b


/-
==================================================
局部优化器：减法
==================================================

优化规则：

e - 0   ==> e

Const x - Const y
    ==> Const (x - y)
-/

def optSub (a b : AExpr) : AExpr :=
  if b = AExpr.const 0 then
    a
  else
    match a, b with
    | AExpr.const x, AExpr.const y =>
        AExpr.const (x - y)
    | _, _ =>
        AExpr.sub a b


/-
==================================================
局部优化器：乘法
==================================================

优化规则：

1 * e   ==> e
e * 1   ==> e

Const x * Const y
    ==> Const (x * y)
-/

def optMul (a b : AExpr) : AExpr :=
  if a = AExpr.const 1 then
    b
  else if b = AExpr.const 1 then
    a
  else
    match a, b with
    | AExpr.const x, AExpr.const y =>
        AExpr.const (x * y)
    | _, _ =>
        AExpr.mul a b


/-
==================================================
完整递归优化器
==================================================
-/

def optimize : AExpr → AExpr
  | AExpr.const n =>
      AExpr.const n

  | AExpr.var x =>
      AExpr.var x

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
==================================================
测试
==================================================
-/

-- (1 + 2) * (x + 0)
-- 优化为：3 * x
def optimizeExample1 : AExpr :=
  AExpr.mul
    (AExpr.add
      (AExpr.const 1)
      (AExpr.const 2))
    (AExpr.add
      (AExpr.var "x")
      (AExpr.const 0))


-- (10 - 0) * 1
-- 优化为：10
def optimizeExample2 : AExpr :=
  AExpr.mul
    (AExpr.sub
      (AExpr.const 10)
      (AExpr.const 0))
    (AExpr.const 1)


-- (2 * 3) + (4 - 1)
-- 优化为：9
def optimizeExample3 : AExpr :=
  AExpr.add
    (AExpr.mul
      (AExpr.const 2)
      (AExpr.const 3))
    (AExpr.sub
      (AExpr.const 4)
      (AExpr.const 1))


#eval optimizeExample1
#eval optimize optimizeExample1

#eval optimizeExample2
#eval optimize optimizeExample2

#eval optimizeExample3
#eval optimize optimizeExample3


/-
==================================================
局部加法优化正确性
==================================================
-/

theorem evalA_optAdd
    (a b : AExpr)
    (env : Env) :
    evalA (optAdd a b) env =
      evalA a env + evalA b env := by

  unfold optAdd

  by_cases ha : a = AExpr.const 0

  · subst a
    simp [evalA]

  · by_cases hb : b = AExpr.const 0

    · subst b
      simp [evalA, ha]

    · simp [ha, hb]

      cases a <;>
      cases b <;>
      simp [evalA]


/-
==================================================
局部减法优化正确性
==================================================
-/

theorem evalA_optSub
    (a b : AExpr)
    (env : Env) :
    evalA (optSub a b) env =
      evalA a env - evalA b env := by

  unfold optSub

  by_cases hb : b = AExpr.const 0

  · subst b
    simp [evalA]

  · simp [hb]

    cases a <;>
    cases b <;>
    simp [evalA]


/-
==================================================
局部乘法优化正确性
==================================================
-/

theorem evalA_optMul
    (a b : AExpr)
    (env : Env) :
    evalA (optMul a b) env =
      evalA a env * evalA b env := by

  unfold optMul

  by_cases ha : a = AExpr.const 1

  · subst a
    simp [evalA]

  · by_cases hb : b = AExpr.const 1

    · subst b
      simp [evalA, ha]

    · simp [ha, hb]

      cases a <;>
      cases b <;>
      simp [evalA]


/-
==================================================
最终定理：优化器正确性
==================================================

对于任意环境 env 和表达式 e：

evalA (optimize e) env = evalA e env
-/

theorem optimize_correct
    (env : Env)
    (e : AExpr) :
    evalA (optimize e) env =
      evalA e env := by

  induction e with

  | const n =>
      rfl

  | var x =>
      rfl

  | add e1 e2 ih1 ih2 =>
      calc
        evalA
            (optimize (AExpr.add e1 e2))
            env
            =
            evalA (optimize e1) env
              +
            evalA (optimize e2) env := by

              simpa [optimize] using
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
            (optimize (AExpr.sub e1 e2))
            env
            =
            evalA (optimize e1) env
              -
            evalA (optimize e2) env := by

              simpa [optimize] using
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
            (optimize (AExpr.mul e1 e2))
            env
            =
            evalA (optimize e1) env
              *
            evalA (optimize e2) env := by

              simpa [optimize] using
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
==================================================
运行测试
==================================================
-/

def proofTestEnv : Env :=
  update emptyEnv "x" 100


#eval evalA optimizeExample1 proofTestEnv
#eval evalA (optimize optimizeExample1) proofTestEnv

#eval evalA optimizeExample2 proofTestEnv
#eval evalA (optimize optimizeExample2) proofTestEnv

#eval evalA optimizeExample3 proofTestEnv
#eval evalA (optimize optimizeExample3) proofTestEnv


end MiniCompiler
