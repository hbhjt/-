import MiniCompiler.Stmt

namespace MiniCompiler

/-
========================================
执行 Monad
========================================

StateT Env
    管理变量状态

Except String
    管理运行异常
========================================
-/

abbrev ExecM :=
  StateT Env (Except String)


/--
读取当前环境。
-/
def getEnv : ExecM Env :=
  fun env =>
    .ok (env, env)


/--
替换当前环境。
-/
def putEnv
    (newEnv : Env) :
    ExecM Unit :=
  fun _ =>
    .ok ((), newEnv)


/--
产生执行异常。
-/
def throwExec
    {α : Type}
    (message : String) :
    ExecM α :=
  fun _ =>
    .error message


/-
========================================
带 Fuel 的 Statement Interpreter
========================================

Fuel 的目的：

确保 exec 本身是一个一定终止的 Lean 函数。
-/

def exec :
    Nat →
    Stmt →
    ExecM Unit

  /-
  Fuel 已经耗尽。
  -/
  | 0, _ =>
      throwExec
        "execution fuel exhausted"


  /-
  skip
  -/
  | fuel + 1, Stmt.skip =>
      pure ()


  /-
  x := expression
  -/
  | fuel + 1,
      Stmt.assign name expr => do

      let env ← getEnv

      let value :=
        evalA expr env

      let newEnv :=
        update env name value

      putEnv newEnv


  /-
  s1 ; s2
  -/
  | fuel + 1,
      Stmt.seq s1 s2 => do

      exec fuel s1

      exec fuel s2


  /-
  if condition then
      s1
  else
      s2
  -/
  | fuel + 1,
      Stmt.ifThenElse
        condition
        thenBranch
        elseBranch => do

      let env ← getEnv

      if evalB condition env then

        exec fuel thenBranch

      else

        exec fuel elseBranch


  /-
  while condition do
      body
  -/
  | fuel + 1,
      Stmt.whileDo condition body => do

      let env ← getEnv

      if evalB condition env then

        exec fuel body

        exec fuel
          (Stmt.whileDo
            condition
            body)

      else

        pure ()


/-
========================================
方便外部调用的函数
========================================

输入：

fuel
stmt
initialEnv

输出：

Except String Env
========================================
-/

def runStmt
    (fuel : Nat)
    (stmt : Stmt)
    (env : Env) :
    Except String Env :=

  match exec fuel stmt env with

  | .ok (_, finalEnv) =>
      .ok finalEnv

  | .error message =>
      .error message

end MiniCompiler
