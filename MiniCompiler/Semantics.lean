import MiniCompiler.Stmt

namespace MiniCompiler

/-
========================================
Big-Step Operational Semantics
========================================

BigStep stmt initialEnv finalEnv

表示：

程序 stmt 从 initialEnv 开始执行，
最终可以终止于 finalEnv。
========================================
-/

inductive BigStep :
    Stmt →
    Env →
    Env →
    Prop where


  /-
  ==============================
  Skip
  ==============================

       --------------
       skip, s ⇓ s
  -/

  | skip
      (env : Env) :

      BigStep
        Stmt.skip
        env
        env


  /-
  ==============================
  Assignment
  ==============================

  x := e

  最终环境：

  s[x -> eval(e,s)]
  -/

  | assign
      (env : Env)
      (name : String)
      (expr : AExpr) :

      BigStep

        (Stmt.assign
          name
          expr)

        env

        (update
          env
          name
          (evalA expr env))


  /-
  ==============================
  Sequence
  ==============================

  (S1,s1) ⇓ s2

  (S2,s2) ⇓ s3

  ----------------

  (S1;S2,s1) ⇓ s3
  -/

  | seq

      {s1 s2 : Stmt}

      {env1 env2 env3 : Env}

      (h1 :
        BigStep
          s1
          env1
          env2)

      (h2 :
        BigStep
          s2
          env2
          env3) :

      BigStep

        (Stmt.seq
          s1
          s2)

        env1
        env3


  /-
  ==============================
  If True
  ==============================
  -/

  | ifTrue

      {condition : BExpr}

      {thenBranch elseBranch : Stmt}

      {env finalEnv : Env}

      (hcondition :
        evalB condition env = true)

      (hthen :
        BigStep
          thenBranch
          env
          finalEnv) :

      BigStep

        (Stmt.ifThenElse
          condition
          thenBranch
          elseBranch)

        env
        finalEnv


  /-
  ==============================
  If False
  ==============================
  -/

  | ifFalse

      {condition : BExpr}

      {thenBranch elseBranch : Stmt}

      {env finalEnv : Env}

      (hcondition :
        evalB condition env = false)

      (helse :
        BigStep
          elseBranch
          env
          finalEnv) :

      BigStep

        (Stmt.ifThenElse
          condition
          thenBranch
          elseBranch)

        env
        finalEnv


  /-
  ==============================
  While False
  ==============================

  condition = false

  --------------------

  while condition do body
  不执行 body。
  -/

  | whileFalse

      {condition : BExpr}

      {body : Stmt}

      {env : Env}

      (hcondition :
        evalB condition env = false) :

      BigStep

        (Stmt.whileDo
          condition
          body)

        env
        env


  /-
  ==============================
  While True
  ==============================

  condition(s) = true

  body,s ⇓ s1

  while condition body,s1 ⇓ s2

  --------------------------------

  while condition body,s ⇓ s2
  -/

  | whileTrue

      {condition : BExpr}

      {body : Stmt}

      {env env1 env2 : Env}

      (hcondition :
        evalB condition env = true)

      (hbody :
        BigStep
          body
          env
          env1)

      (hwhile :
        BigStep
          (Stmt.whileDo
            condition
            body)
          env1
          env2) :

      BigStep

        (Stmt.whileDo
          condition
          body)

        env
        env2


/-
========================================
简单 BigStep 示例
========================================
-/

example :
    BigStep
      (Stmt.assign
        "x"
        (AExpr.const 5))
      emptyEnv
      (update
        emptyEnv
        "x"
        5) := by

  simpa [evalA] using
    (BigStep.assign
      emptyEnv
      "x"
      (AExpr.const 5))

end MiniCompiler
