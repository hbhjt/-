namespace MiniCompiler

/--
变量环境。

Env 是一个函数：
输入变量名 String，
输出变量当前的整数值 Int。
-/
abbrev Env := String → Int


/--
空环境。

所有变量默认值都是 0。
-/
def emptyEnv : Env :=
  fun _ => 0


/--
更新环境。

update env "x" 10

返回一个新的环境：
x 的值变成 10，
其他变量保持原来的值。
-/
def update (env : Env) (name : String) (value : Int) : Env :=
  fun x =>
    if x = name then
      value
    else
      env x


/-
========================================
简单测试
========================================
-/

def testEnv : Env :=
  update
    (update emptyEnv "x" 10)
    "y" 20

#eval testEnv "x"   -- 10
#eval testEnv "y"   -- 20
#eval testEnv "z"   -- 0

end MiniCompiler
