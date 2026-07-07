# Schemer — 项目上下文

一个把 Scheme 子集编译到 x86-64 汇编的增量式编译器（IU 的 P523 / Dybvig 编译器课程改编）。整个大作业分 15 个 lab（a1–a15），每加一节就在流水线**前端**加几个 pass，处理更高级的语法；后端逐步补全。

## 目标（每个 lab 在做什么）
- **a1** `generate-x86-64`：把类汇编 `(begin (set! ...) ...)` 输出成 x86-64。
- **a2** `expose-frame-var` / `flatten-program`：引入栈帧变量 fvN、顶层 letrec + 尾调用，拍平成 `(code ...)`。
- **a3** `finalize-locations` / `expose-basic-blocks`：引入 `if` 控制流与 `locate` 别名，拆基本块 + 条件跳转。
- **a4** `uncover-register-conflict` / `assign-registers` / `discard-call-live`：活跃分析建冲突图 + 图着色分配寄存器（不溢出）。
- **a5** `uncover-frame-conflict` / `introduce-allocation-forms` / `select-instructions` / `assign-frame` / `finalize-frame-locations`：溢出到栈帧，用 `(iterate ...)` 循环反复分配直到全部安家。
- a6–a15（尚未做）：调用约定、堆分配、`let`、`specify-representation`(值表示)、`lift-letrec`/`normalize-context`、闭包转换、闭包优化、赋值/复杂常量/`purify-letrec`、最后 `parse-scheme`。docs/challenge.pdf 有两个加分优化。

## 工作流程
1. lab 在**上游** `JohnClass2023/Schemer` 的 aN 分支（本仓库 origin=`diefish1024/Schemer` 只有 master）。已加 remote：`upstream`。
2. 做下一节：`git merge --no-edit upstream/aN`（会带进 `aN/` 目录：assign PDF、`aN-wrapper.scm`、`testsN.scm`）。冲突永远选 incoming。**一次只 merge 一个**。
3. 在 `src/` 下实现/修改该节的 pass（见下方模块划分）。
4. 测试：`python3 ./build/build.py aN` 生成 `test.scm`，再 `scheme test.scm` 里跑 `(test-all)` / `(analyze-all)` / `(test-one 'prog)` / `(tracer #t)`。
5. 通过后 commit。

## 环境注意
- 本机没有系统级 Chez，也无 sudo。已把 `chezscheme` 的 .deb 解压到 `~/chez-root`，包了个 `~/bin/scheme`（设了 `SCHEMEHEAPDIRS`）。直接用 `~/bin/scheme test.scm`。
- gcc 已有；build.scm 用 `gcc -m64 runtime.c t.s` 编译运行生成的汇编。
- `test.scm`、`output/` 已被 `.gitignore` 忽略。

## 源码模块划分（src/）
`build.py` 只 `(load "src/schemer.scm")`，所以 schemer.scm 是**加载器**，一次性 load 各模块（notice.md 只禁止「每个 pass 重复 load」，不禁止拆文件）。每个 pass 仍是顶层 `define`，driver 靠 `(eval pass-name)` 调用。
- `src/schemer.scm` — 加载器，按顺序 load 下面各模块。
- `src/utils.scm` — 编译器自用的共享工具：`relop?`、`int?`、`build-conflict-graph`（通用活跃分析建冲突图）、`subst-tail`（结构化替换 + 自移动→nop）。
- `src/verify.scm` — 前端验证（`verify-scheme`，目前恒等）。
- `src/alloc.scm` — 寄存器/栈帧分配簇（a4/a5 的 9 个 pass）。
- `src/codegen.scm` — 后端：`expose-frame-var`、`expose-basic-blocks`、`flatten-program`、`generate-x86-64`。
（`lib/helpers.scm`、`lib/match.scm` 是课程给的工具，别改。）

## 关键约定 / 我的要求
- **每个 assignment 实现完单独 commit**，message 用简短一句如 `feat: implement a3 ...`；**不要**带 Claude 署名、不要长篇正文，保持和历史 commit 风格一致。
- **`note/` 文件夹**：每个 lab 写一篇详细实现思路（`note/aN.md`）。**不提交**（已在 `.git/info/exclude` 里排除，不动 `.gitignore`）。
- `verify-scheme` / `verify-uil` 允许写成恒等函数（notice.md：语法检查统一放到 a15 的 `parse-scheme`）。
- 各 pass 是**逐版本重定义**的（如 `generate-x86-64` a1 认 `(begin)`、a2 起认 `(code)`）；用旧 pipeline 跑最新代码不成立，每节验收固化在各自 commit。
- 遇到 match 子句：结构相同/元数不同的模式靠顺序区分，通配 `,x` 兜底放最后。

## 当前进度
a1–a5 **已完成并各自 commit**，测试：a1 17/17、a2 29/29、a3 50/50、a4 55/56（最后 1 个需 a5 溢出，文档已说明）、a5 81/81。下一步从 `git merge --no-edit upstream/a6` 开始。
