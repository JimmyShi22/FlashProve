# FlashProve 验证器 no_std 移植摸底清单（S0）

- 仓库：`/Users/shakku/trustless-ai/FlashProve`（origin = `trustless-ai/FlashProve`）
- 分支：`feat/nostd-verifier`（从 `main` 新建，基线 commit `9e2bdd8f`）
- 范围：只读摸底。未修改 `verifier/`、`blocks/`、`prover/` 的任何文件。
- 目标（本轮硬验收）：`examples/accepted-proof/` 输出 `YES`，`result-v1` 逐字段与 C++ 原版一致；篡改 proof 字节、错误 commitment ID 必须返回 `NO`。

---

## 0. 结论摘要

1. **验证内核是纯计算，no_std 可行**。真正阻断 no_std 的只有：`fork/pipe/waitpid`、`printf/fflush/ferror`、`exit()/abort()`、`prctl/fcntl`、文件读取、`std::thread/mutex/atomic`、`std::chrono`、`try/catch`。这些全部集中在驱动/外壳层，可以剥离。
2. **默认调用不需要并发**。不传 `-j` 时 `nthreads=1`；`parFor()` 走串行 `for` 分支，`std::thread` 分支不执行。三 stage 的 `fork()` 只是进程隔离外壳；改成同进程顺序执行 + 状态重置即可保持语义。
3. **实测规模比 PM 备忘大**：`verifier/src` 共 36 个文件、**13,166 行**（PM 备忘约 9,300 行偏低）；静态 include 闭包另含 `blocks/` 79 个头文件 **23,447 行**、`prover/*/plan_rounds.h` 4 个头文件 **394 行**，静态合计 **37,007 行**。运行期只走 verifier 侧路径，prover 侧实现（Engine、写证明、测试）不需要移植，但 `blocks/iop` 仍是主要工作量（11,825 行）。
4. **本机可以跑 C++ 原版**：`verifier/build.sh` 依赖 GNU `stat -c`/`mv -fT`/g++ 13，不能在 macOS 直接跑；但用 Apple clang 15 直接编译 `cp_verify.cpp` 成功。官方示例输出 `YES`，`result-v1` 与 README 完全一致，`build=93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595`。两个负面控制也已在原版上实测。
5. **两个对齐要点**：
   - `build=` 是 `build.sh` 对源码列表算的 SHA-256，本仓库当前值为 `93afdaf5…9595`（已用 `build.sh` 同款管道复核）。Rust 侧应把它作为编译期常量（或 build script 复算），否则 `result-v1` 不可能逐字段一致。
   - `q_V`（verifier 自身 hash 调用数）**不进入 `result-v1` 任何字段**，只出现在 `accounting:` 行。`least-round` 等字段来自 `blk::account()` 的 plan 计算。PM 备忘中“q_V 用于对齐 result-v1”这一点需要修正。本示例实测 `q_V = 136,088`。S3 P0 仍要求 `accounting:` 的数字与文本骨架逐字节一致（见 §7、A2）。

---

## 1. 实测基线与环境

### 1.1 源码规模（静态 include 闭包）

| 部分 | 文件数 | 行数 | 说明 |
|---|---:|---:|---|
| `verifier/src` | 36 | 13,166 | `cp_verify.cpp` 3,433 行；其余头/`.inc` 9,733 行 |
| `blocks/*.h`（闭包内） | 79 | 23,447 | 不含 `tests/`；由 `g++ -MM` 得出 |
| `prover/*/plan_rounds.h` + `prover/hiding/token_plan.h` | 4 | 394 | prover/verifier 共享的轮次表 |
| **静态合计** | **119** | **37,007** | 运行期 reachable 子集小于此值 |

闭包生成命令（只读）：

```sh
cd verifier/src
g++ -std=c++17 -MM -I. -I../../blocks -I../../prover \
  -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  cp_verify.cpp
```

`blocks/` 闭包按目录：`iop` 31 文件/11,825 行、`frame` 18/3,514、`numbers` 7/3,125、`chain` 5/1,945、`hash` 4/1,026、`tree` 3/610、`field` 3/475、`code` 3/399、`engine` 3/340、`base.h` 131、`fence.h` 57。

> 注意：静态闭包 ≠ 必须移植。`blocks/iop` 里 prover 侧代码（`*_prove`、`Engine`、`ProverRounds` 写入路径）、`blocks/engine/engine.h`、`blocks/chain/closed.h`（其注释明确说 `cp_verify` 不调用）、`blocks/toy/`、所有 `tests/` 均不在验证器运行路径上。S1/S2 应按 verifier 调用图裁剪。

### 1.2 Rust 工具链

```text
$ cargo --version
cargo 1.97.1 (c980f4866 2026-06-30)
$ rustc --version
rustc 1.97.1 (8bab26f4f 2026-07-14)
$ rustup show
Default host: aarch64-apple-darwin
installed toolchains: stable-aarch64-apple-darwin (active), 1.97.0-aarch64-apple-darwin
installed targets: aarch64-apple-darwin, riscv32imac-unknown-none-elf
```

判断：

- `core` + `alloc` 可用，满足 `#![no_std]` + `extern crate alloc` 的 S1 要求。
- **未安装** `riscv32im-unknown-none-elf`（RISC0/SP1 常用裸目标）；只有 `riscv32imac-unknown-none-elf`。本轮硬验收在 host 上完成，不受阻；到真正上 zkVM 时由 RISC0/SP1 自带工具链解决。未擅自安装大型组件。
- 无外部 crate 依赖是可行的；唯一可能需要引入的小 crate 是 `libm`（纯 Rust 浮点函数），见 §8 R1。是否需要引入需 TL 决策。
- zkVM 目标通常没有 A 扩展（`riscv32im`），因此核心 crate 不应依赖 `core::sync::atomic` 的 64 位原子；本移植按单线程设计，直接删掉计数器原子性。

### 1.3 C++ 原版基线（重要）

`verifier/build.sh` 在 macOS 上不能直接运行（GNU `stat -c`、`mv -fT`、要求 g++ 13）。但 `cp_verify.cpp` 本身可用 Apple clang 15 直接编译：

```sh
mkdir -p /tmp/fp_cpp_build
clang++ -O2 -std=c++17 -pthread \
  -Iverifier/src -Iblocks -Iprover \
  -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o /tmp/fp_cpp_build/cp_verify verifier/src/cp_verify.cpp
# EXIT=0
```

官方示例（`-q`）：

```sh
/tmp/fp_cpp_build/cp_verify examples/accepted-proof/config examples/accepted-proof/ivk \
  examples/accepted-proof/example.req examples/accepted-proof/example.y \
  examples/accepted-proof/example.proof \
  -id 79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183 -q
# EXIT=0
```

末尾 golden 输出：

```text
commitment: 49 closeness rounds of the one-time files rest on another source than the bound within a third of the distance; the table has a record: the binding of the weights rests on the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given
proof of work: up to 32 bits counted in 38 rounds; with it the least round has 128.00 bits, without it 96.23 bits
result-v1 status=0 claim=exact-match id=79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183 bits=128 work=32 work-rounds=38 least-round=128.00 least-round-without-work=96.23 commitment-assumed-rounds=49 record=1 r=60 e=64 T=64 tokens=61..63 y=yes policy=exact-match C=256 theta=256 cap=0 s=16 sh=8 sT=4 F=24 above-clip=0 leaf=0 stages=key,leaf,request dw=8 build=93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595
YES
```

负面控制（同一二进制实测）：

```text
# 篡改 example.proof 中间字节 (offset 2072650, ^= 0x01)
EXIT=1
---- the call ----
refused by the stage request: an opening does not lead to its root
NO: proof-refused

# 错误 commitment ID（末位 …2183 → …2184）
EXIT=1
id: these are not the files of the commitment that you named; nothing in them was checked
id: take the commitment ID from your own record of where it was published, never from these files
NO: model-statement
```

其他观测：`accounting: hash calls: … q_V …: 136088`；`-q` 输出共 105 行。示例文件大小：proof 4,145,300 B、key.bin 1,096,408 B、leaf/0.bin 536,952 B、req 264 B、y 4 B。

> 局限：这是 macOS + Apple clang + Apple libm 的构建，不是发布用的 Linux g++/glibc 构建。其输出与仓库 README 中记录的 `result-v1` 完全一致，说明该示例对 libm 差异不敏感；但严格意义上仍建议后续在 Linux g++ 上复核一次。本机 Docker 客户端存在，但 daemon 不可用（`docker info` exit 1），未启动/安装任何组件。

### 1.4 `build=` 字段的复核

`verifier/build.sh` 的算法：在 `verifier/src` 下对 `*`、`../../prover/*/plan_rounds.h`、`../../prover/hiding/token_plan.h` 以及 `blocks/` 下所有非 `tests/` 的 `*.h` 求 `sha256sum`，再把整份清单的文本做 SHA-256。用同款管道实测：

```text
build_word=93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595
```

与 C++ 运行输出一致。`docs/nostd-inventory.md` 与未来的 `rust-nostd-verifier/` 不在该清单内，因此不会改变这个值。

---

## 2. 架构与执行语义

```text
main()
 └─ cpMain()                 解析命令行、读 key/request/y/proof、校验长度与头部
     ├─ cpStagesRun([key, leaf, request])
     │    ├─ fork+pipe 三个子进程（每个 runStage 一次）
     │    ├─ 父进程收三份 stdout，解析 "result:" / "accounting:" / "work:" 文本
     │    └─ cpStagesRun 汇总 → cpCovered() → 末尾四行（commitment/work/result-v1/verdict）
     └─ cpWritten()/main()   fflush/ferror 检查，exit status
```

- 三个 stage：`key` 检查 `ivk/key.bin`；`leaf` 检查 `ivk/leaf/<k>.bin`（信任 key 的表，单看 form）；`request` 检查 proof（信任 leaf 的表）。三者都过才 `YES`。
- `runStage()` 是每个 stage 的主体：解析 parameter file → 建 layout/plans → `blk::configure()` → 执行 `check_key` / `check_entry_if_tested` / `check_proof_if_tested`。
- `fork()` 的作用只有两个：**全局状态隔离** 和 **`refuse()` 直接 `exit(1)` 的进程隔离**。默认串行时没有共享线程状态；Rust 用「每 stage 一个状态对象 + `Result<_, Refusal>`」即可等价替代，无需 `fork`。
- `parFor(n, fn)`：`innerThreads <= 1 || n < 2` 时直接串行循环；`-j` 不传时 `nthreads=1`，key/leaf 的线程数为 `max(1, 1/8)=1`。并发分支在硬验收路径上不可达。
- 需要按 stage 重置的可变文件级状态（实测）：
  `TAU`、`LIDB`、`NMINH`、`stageWorkNote`、`acctNote`、`residualStreamLimbs`、`gateTableInputFractionBits`、`SMAX`、`RCL`、`GCL`、`statedTarget`、`currentSegment`、`refuseThrows`、`innerThreads`、`runVersionWord`、`stageShapesMade` 等。
  Rust 侧应把它们收进 `Settings`/`StageState`，或在每次 `run_stage()` 开始时显式重置；不要依赖进程重启。

---

## 3. `verifier/src` 模块清单

图例：

- **OS/IO**：`无` = 不触达 OS；`printf` = 标准输出/诊断；`exit` = `refuse()/abort()/exit()`；`IO` = 文件/`stat`/`fopen`；`thr` = thread/mutex/atomic；`time` = chrono。
- **纯计算**：`是` = 只依赖 core/alloc；`是*` = 核心纯计算，但同文件含需剥离的外壳；`否` = host 侧。
- **规模**：S < 200 行，M 200–600，L > 600。

### 3.1 驱动、公共与哈希

| 文件 | 行 | 规模 | 职责 | OS/IO | 纯计算 | blocks 依赖 | 备注 |
|---|---:|---|---|---|---|---|---|
| `cp_verify.cpp` | 3433 | L | `main`、命令行、三 stage、文件读取、fork/pipe、输出末尾四行；也含 `runStage()` 验证主体 | fork/pipe/wait/prctl/fcntl/stat/fopen/printf/exit/thr/time | 否 / 是* | `frame/check*`、`configure`、`parameters`、`heads`、`prints`、`req_frame`、`wf_units` | 拆成 host 外壳 + 纯 `run_stage` 两半；`runStage` 是移植核心 |
| `vf_common.h` | 978 | L | `refuse`、`parFor`、文件读取、版本/阈值/status、`Served` 策略、`lastLine`、`Ex` 域运算、`TH`、`Tr` | printf/exit/IO/thr/time | 是* | `field/field`、`hash/tweak`、`frame/version`、`numbers/accounting`（经 `vf_accounting_record`） | 按职责再拆：`field`/`transcript`/`output`/`host_io` |
| `vf_input_files.h` | 53 | S | 读 configuration、校验 key/proof 头 | IO（`lstat`/`needBytes`，`cpConfRead()`） | 是* | `frame/heads` | `cpConfRead()`（:36-47）属 host；`cpWord`/`cpKeyHead`/`cpProofHead`（:19-53）是纯函数，进 core |
| `cp_configured.h` | 46 | S | 供 `cp_commit`/`cp_prove` 复用 `blk::Configured` 的链接入口 | 无 | 否（host 接口） | `frame/configure` | **不移植**（仅 host 侧保留或删除） |
| `vf_rejection_names.txt` | 304 | M | 拒绝名分类清单（数据，不入编译） | 无 | n/a | 无 | 转为 Rust 常量/测试表；每一条加 C++ 源出处注释，并逐条注明 `verifier/tests` 覆盖情况（`commitment_id_test.py` / `what_a_yes_covers_test.py` / `known_answers/`）；它参与 `build=` |
| `vf_digest_words.h` | 13 | S | `DIGEST_WORDS=8` 常量 | 无 | 是 | 无 | 常量 |
| `vf_widths_and_bounds.h` | 40 | S | `u32/u64`、哈希宽度、权重宽度/界 | 无 | 是 | 无 | 常量 |
| `vf_accounting_record.h` | 153 | S | stage 的 accounting 以文本行传给父进程，再解析回来 | snprintf/sstream | 是* | `numbers/accounting` | Rust 同进程可改为结构化传递；若保留文本输出需 `core::fmt` |
| `vf_earlier_hash_f.h` | 168 | S | BLAKE2b 压缩函数 F（RFC 7693），带调用计数 | atomic/thread_local | 是* | 无 | 计数去掉即可；F 本体纯计算 |
| `vf_earlier_hash.h` | 77 | S | 验证器自有哈希 `H(num; words)`、`words64/words32` | 无 | 是 | 无 | 纯计算 |

### 3.2 seam：transcript / chain / 段 / 权重 / 数字行

| 文件 | 行 | 规模 | 职责 | OS/IO | 纯计算 | blocks 依赖 | 备注 |
|---|---:|---|---|---|---|---|---|
| `vf_request_chain.h` | 129 | S | 逐 segment 走 request 链（`mb::ChainCheck`），汇总线性等式 | 无 | 是 | `iop/req`、`iop/req_rows` | 用虚接口 `LinkHook`；Rust 用 trait/枚举 |
| `vf_segments.inc` | 340 | M | 从 plan/layout 构造 `blk::configure()` 的 shapes（`buildLinksH`）并跑 links | printf/snprintf/new | 是* | `frame/configure`、`frame/prints` 等 | 进度输出可删；shape 构造必须保留 |
| `vf_transcript_channel.h` | 140 | S | 把 `RoundName` 映射到 `blk::VerifierRounds` 通道，读/抽 challenge | printf（fault 时） | 是* | `chain/rounds`、`numbers/round_names` | 诊断 printf 改 host 回调 |
| `vf_transcript_calls.h` | 49 | S | 子证明使用的 `trRead/trAnswer/trBatch/...` | 无 | 是 | `vf_transcript_channel` | 纯逻辑 |
| `vf_subproof_segment.h` | 390 | M | 子证明的数组表、虚拟行、claim 汇总、`rootInH`/`doorH` | try/catch/thread_local | 是* | `vf_request_chain`、`iop/*` | `Refusal` 异常→`Result`；`currentSegment` 改为显式参数 |
| `vf_weights_layout.h` | 338 | M | 权重矩阵 W 的 layout 与子证明的权重 claim | 无 | 是 | `vf_subproof_engine`、`vf_weights_merge` | 纯计算 |
| `vf_weights_merge.h` | 59 | S | 批量合并权重 claim，输出 `rm/beta/fv'` | 无 | 是 | `vf_subproof_engine` | 纯计算 |
| `vf_weights_pending_claim.h` | 55 | S | 生成留给 LIN 的 pending claim | 无 | 是 | `iop/member`、`vf_subproof_segment` | 纯计算 |
| `vf_norm_digit_rows.h` | 135 | S | 五 limb 残差流的 digit row、范围与线性方程 | 无 | 是 | `vf_subproof_engine` | 有一个可变全局 `residualStreamLimbs` |

### 3.3 子证明（核心计算）

| 文件 | 行 | 规模 | 职责 | OS/IO | 纯计算 | blocks 依赖 | 备注 |
|---|---:|---|---|---|---|---|---|
| `vf_layers_plan.inc` | 182 | S | layer 子证明的 plan | 无 | 是 | `numbers/plan`（经上层） | 纯 plan 构造 |
| `vf_layers_check.inc` | 1204 | L | 一组 layer 的完整检查（含 MC/MoE、norm、gating、weights） | snprintf/map/function | 是* | 多个 `iop/*` | 进度输出可删；核心最大单文件之一 |
| `vf_output_head_plan.inc` | 145 | S | output head 子证明的 plan | 无 | 是 | `numbers/plan` | 纯 plan |
| `vf_output_head_check.inc` | 646 | L | output head 的检查（digit row、logits、softmax/argmax） | snprintf/map | 是* | 多个 `iop/*` | 进度输出可删 |
| `vf_attention_shape.h` | 387 | M | attention 子证明的 shape、lookup call、no-overflow 条件 | 无（libm） | 是 | `vf_common` | 使用 `exp/ldexp/nearbyint`，需浮点对齐 |
| `vf_attention_check.h` | 972 | L | scores、causal softmax、weighted sum 检查（SC3/SCD） | map/function | 是 | `vf_attention_shape`、`vf_subproof_engine`、`vf_smallness_test`、`attn/plan_rounds` | 核心大文件 |
| `vf_subproof_engine.h` | 435 | M | 子证明共享引擎：hidden value + mask、Affine claim、数组/虚拟行、weighted sum | map/array/memory | 是 | `vf_smallness_packing`、`vf_sumcheck_*`、`vf_lookup_helpers` | 所有子证明的地基 |
| `vf_lookup_argument.h` | 397 | M | 隐藏值上的 lookup argument（product trees） | memory | 是 | `numbers/blocks` | 与 `blocks/iop/lkp.h` 是两套实现：这里用于子证明 |
| `vf_lookup_helpers.h` | 113 | S | 子证明 lookup 的 glue（`uEnt`、`HStack` 等） | 无 | 是 | `vf_lookup_argument`、`prover/plan_rounds` | 纯计算 |
| `vf_smallness_matrices.h` | 30 | S | `TMat`/`Tail` 数据结构 | 无 | 是 | `vf_common` | 纯数据 |
| `vf_smallness_packing.h` | 157 | S | cell packing（3 lane、radix 2^20）、placement、tie | 无 | 是 | `vf_common` | 纯计算 |
| `vf_smallness_test.h` | 223 | M | approximate range check（tail） | 无 | 是 | `vf_smallness_matrices`、`vf_subproof_engine`、`vf_subproof_segment` | 纯计算 |
| `vf_smallness_test_members.inc` | 1049 | L | smallness test 的成员/矩阵/functional/plan | 无 | 是 | 上层 `blk::Plan` | 大但机械 |
| `vf_sumcheck_psc.h` | 134 | S | 带隐藏多项式的 sumcheck（PSC） | 无 | 是 | `iop/hp` | 纯计算 |
| `vf_sumcheck_receive.h` | 60 | S | sumcheck 轮次接收（`roundIn`） | 无 | 是 | `vf_subproof_engine` | 纯计算 |
| `vf_sumcheck_token.h` | 57 | S | token sumcheck（TSC） | 无 | 是 | `head/plan_rounds` | 纯计算 |
| `vf_sumcheck_attention.h` | 75 | S | SC3 / SCD | 无 | 是 | `vf_subproof_engine` | 纯计算 |

---

## 4. `blocks/` 依赖组件清单

### 4.1 顶层组件

| 组件 | 文件/行数 | 职责 | 对 no_std 的影响 | 处置 |
|---|---|---|---|---|
| `blocks/base.h` | 1 / 131 | 整数类型、`BLK_HD`、`BLK_REQUIRE` 守卫 | `abort()`、`fprintf(stderr)`、`thread_local` | 去外壳：守卫→`Result`/panic 策略 |
| `blocks/fence.h` | 1 / 57 | 测试开关防误编译 | 编译期宏 | host/build 侧保留，不进 core |
| `blocks/hash/` | 4 / 1,026 | BLAKE2b 压缩、BLAKE2b 模式、域分离 tweak | `tweak.h` 是域分离 tweak（`Tweak`），不是计数；hash 调用计数分两处：`blk::hash_calls_made`（`BLK_COUNT_HASH_CALLS` 时，`tweak.h`）+ `f2b` 计数（`vf_earlier_hash_f.h`） | 域分离直接移植；两处计数改单线程普通 u64；hash 直接移植 |
| `blocks/field/` | 3 / 475 | Goldilocks F、三次扩域 E、MLE | 纯计算 | 直接移植 |
| `blocks/chain/` | 5 / 1,945 | Fiat-Shamir hash chain、`VerifierRounds` 通道、session | `rounds.h` 有 `fprintf(stderr)` 诊断；`closed.h` cp_verify 不调用 | 诊断改回调；`closed.h` 不移植 |
| `blocks/code/` | 3 / 399 | Reed–Solomon 码、coset、short position | `code.h` 用 `std::mutex` 做 transform-table 缓存 | 单线程改为预计算/上下文缓存 |
| `blocks/tree/` | 3 / 610 | Merkle 树、opening、position list | 纯计算（`opening.h` 引用 prover 侧 `Coins` 类型） | 只移植 verifier 侧 + 必要类型 |
| `blocks/numbers/` | 7 / 3,125 | `Big`/`Real` 精确算术、码界、plan、planners、accounting | `accounting.h`/`plan.h` 有 printf/fprintf；`blocks.h` 有 atomic 编号；`real.h` 用 libm 仅做打印 bits | 计算部分直接移植；打印/浮点转 host 或确定性实现 |
| `blocks/frame/` | 18 / 3,514 | 参数解析、派生、configure、文件 plan、头部、check_key/entry/proof、frame shapes | `prints.h` printf；`fields.h`/`req_frame.h` 仅少量 printf；其余纯 | 核心全移植；prints 转 host |
| `blocks/iop/` | 31 / 11,825 | 证明系统各 block（SEND/FOLD/CS/IOPP/BASE、LKP/RNG/WF、LIN/LINK、REQ、tensor/relation/psc…） | verifier 侧纯计算；prover 侧含 Engine/写证明/大内存 | 只移植 verifier 调用图；prover 侧不移植 |
| `blocks/engine/` | 3 / 340 | `Engine` 抽象、CPU sumcheck、`Coins` 表 | prover 侧；`tree/opening.h` 仅需 `table.h` 的类型 | 不移植（必要类型内联到 tree seam） |
| `prover/*/plan_rounds.h` | 4 / 394 | 子证明轮次表（prover/verifier 共享） | 纯常量/布局 | 直接移植为 Rust 常量 |

### 4.2 `blocks/iop/` 内部（31 文件）

| 子类 | 文件（行数） | 说明 |
|---|---|---|
| 状态/代数 | `relation.h` 713、`tensor.h` 773、`hp.h` 277、`psc.h` 265、`summand.h` 116、`message.h` 135、`mask.h` 147、`row_value.h` 60、`line.h` 43、`psc_rows.h` 85、`split.h` 117、`bat.h` 154、`batt.h` 171、`batt_shown.h` 188 | 线性 claim、结构化系数、sumcheck 代数、字节编码；纯计算，优先移植 |
| 折叠/邻近测试 | `fold.h` 494、`fold_algebra.h` 135、`fold_rounds.h` 177、`cs.h` 732、`laid.h` 197、`single_rows.h` 173、`iopp.h` 302、`base_case.h` 249 | verifier 侧是核心路径；prover 侧折叠实现可跳过 |
| lookup/范围 | `lkp.h` 1140、`rng.h` 633、`wf.h` 667 | `lkp` 主要用于 key 文件 WF；子证明另有 `vf_lookup_argument.h` |
| 承诺表 | `foldeq.h` 853、`lin.h` 888、`link.h` 482、`member.h` 186 | 承诺表、LIN、LINK、pending claim；核心 |
| 请求框架 | `req.h` 793、`req_rows.h` 171、`send.h` 566、`context.h` 564 | 请求 proof 的外框、oracle 消息、上下文；核心 |

---

## 5. no_std 可行性结论表

| 类别 | 内容 | 处置 |
|---|---|---|
| **可直接移植**（core + alloc） | `blocks/{field,hash,tree,numbers(计算部分),iop(verifier 侧),frame(解析/check)}`；`vf_digest_words`、`vf_widths_and_bounds`、`vf_earlier_hash*`、`vf_input_files`、`vf_subproof_engine`、`vf_smallness_*`、`vf_lookup_*`、`vf_sumcheck_*`、`vf_weights_*`、`vf_norm_digit_rows`、`vf_attention_shape/check`、`vf_layers_*`、`vf_output_head_*`、`vf_request_chain` | 直接写 `#![no_std]` 模块；容器换 `alloc::{Vec,String,BTreeMap,BTreeSet}` |
| **需去外壳后移植** | `vf_common`（文件/printf/exit/threads/chrono）、`vf_accounting_record`（snprintf/sstream）、`vf_earlier_hash_f`（atomic/thread_local）、`vf_subproof_segment`（try/catch、thread_local）、`vf_transcript_channel`（printf）、`vf_segments`/`vf_layers_check`/`vf_output_head_check`（snprintf 进度）、`blocks/base.h`（abort/fprintf/thread_local）、`blocks/hash/tweak.h`（atomic）、`blocks/code/code.h`（mutex 缓存）、`blocks/numbers/blocks.h`（atomic 编号）、`blocks/numbers/accounting.h`+`plan.h`（printf/fprintf）、`blocks/frame/prints.h`/`fields.h`/`req_frame.h`（printf）、`blocks/chain/rounds.h`（fprintf 诊断） | 统一策略：`refuse()→Result<_,Refusal>`；打印→`fmt::Write` 或 host 回调；线程/原子→单线程普通变量；`try/catch→Result`；缓存→上下文对象 |
| **仅 host 侧保留** | `cp_verify.cpp` 的 `main/cpMain/cpUsage/cpPlanMain/cpStagesRun/cpWritten`；文件读取/`stat`/`fopen`；`fork/pipe/waitpid`；`prctl/fcntl/fflush/ferror`；`chrono::now`；`cp_configured.h`；`blocks/fence.h` | 放在 `fp-host`（std crate）或 host binary；不进入 zkVM guest |
| **不需要移植** | prover 侧 `*_prove`/`Engine`/`ProverRounds`/`blocks/engine/engine.h`/`engine_cpu`/`sumcheck_cpu`；`blocks/chain/closed.h`（cp_verify 不调用）；`blocks/toy/`；`blocks/**/tests/`；`verifier/tests/`；`prover/`（除 4 个 `plan_rounds.h`） | 只保留类型/常量被 verifier 引用的部分 |

### 5.1 no_std 替换对照

| C++ | Rust no_std 方案 |
|---|---|
| `std::string` / `std::vector` | `alloc::string::String` / `alloc::vec::Vec` |
| `std::map` / `std::set` | `alloc::collections::BTreeMap` / `BTreeSet`（需要确定性顺序，正好合适） |
| `std::function` | 泛型闭包或 `alloc::boxed::Box<dyn Fn>` |
| `std::shared_ptr` | `alloc::rc::Rc`（单线程；避免 `Arc` 对 atomics 的依赖） |
| `std::thread` / `mutex` / `atomic` | 删除；单线程普通变量/`RefCell` |
| `printf` / `snprintf` | `core::fmt::Write` 到 `String`；host 统一输出 |
| `exit()` / `abort()` / `refuse()` | `Result<T, Refusal>`；`Refusal { name, internal }` |
| `try/catch` | `Result` |
| `std::chrono` | 仅 host 计时；核心不感知时间 |
| `exp/sin/cos/pow/log2/ldexp/nearbyint` | `libm` crate 或自实现（需逐位/逐整数对齐，见 §8 R1） |

---

## 6. 建议的移植顺序与分片

依赖主链（强依赖，箭头表示“需要先有”）：

```text
types/constants ──> field(F,E) ──┐
                    hash(BLAKE2b/H) ──> chain/rounds ──> iop ──> frame/check ──> vf 子证明 ──> runStage/result-v1
                    Big/Real ──> plan/accounting ──┘        │
                                                              └─> tree/code/message
```

### Wave 0（S1：骨架，串行）

- `rust-nostd-verifier/` workspace：`fp-core`（`#![no_std]` + `alloc`）+ `fp-host`（std）+ `tests/parity`。
- 错误模型 `Refusal`、类型/常量、`build=` 常量（`93afdaf5…9595`）。
- host 侧文件读取/CLI 参数解析骨架；golden fixtures（§1.3 的 C++ 输出、负面控制）。
- 对拍脚本：跑 core 单测 + 可选的 C++ 原版（本机 `/tmp` 二进制）对比 `result-v1`。

### Wave 1（基础，三路并行 + 一路 host）

| 车道 | 内容 | 对拍门 |
|---|---|---|
| A. 域 | `blocks/field/gl64.h` → `field.h` → `Ex`/`eqTab`/`eqOne` | 域算术向量；C++/Python 参考 |
| B. 哈希 | `blake2b_f.h` → `vf_earlier_hash_f/h` → `hash/hash.h`+`domains.h` → `TH` | `verifier/tests/hash_vectors.txt`（57 条）、`blocks/hash/tests/mode_vectors.txt`、`known_answers/blake2b_f.py` |
| C. 精确算术/plan | `numbers/real.h` → `setting.h` → `codes.h` → `plan.h` → `blocks.h` → `accounting.h` | C++ `-plan` 输出；`least-round=128.00/96.23`、`work-rounds=38` |
| D. host/输出 | 文件读取、长度/头部校验、`-id/-policy/-q/-j`、`result-v1` 格式化、`build=` | 命令行/负面控制状态码与最后一行 |

### Wave 2（协议底座，A+B+C 汇合后）

- `iop/message`（Reader/Writer）→ `chain/rounds`/`public`/`chain` → `tree/*` + `code/*`。
- `iop` 代数核心：`relation`、`tensor`、`hp`、`psc`、`summand`、`mask`、`line`、`bat`/`batt`。
- `iop` 折叠/邻近：`fold*`、`cs`、`laid`、`single_rows`、`iopp`、`base_case`、`split`。
- `iop` 承诺/查找：`foldeq`、`lin`、`link`、`member`、`lkp`、`rng`、`wf`。
- `frame`：`parameters`、`derive`、`configure`、`files`、`heads`、`hiding_conditions`、`key_fixed`、`lin_frame`/`link_frame`/`wf_frame`、`req_frame`、`wf_units`。
- `frame/check_key`、`check_entry`、`check`。
- 可并行：`(chain+tree+message)`、`(iop 代数/折叠)`、`(numbers/plan 收尾 + frame 解析)`。`iop` 是关键路径。

### Wave 3（验证器子证明，Wave 2 后）

- 共享地基（串行）：`vf_common` 核心、`vf_transcript_*`、`vf_subproof_engine`、`vf_smallness_*`、`vf_lookup_*`、`vf_sumcheck_*`。
- 三路子证明并行：
  - attention：`vf_attention_shape` → `vf_attention_check`
  - layers：`vf_layers_plan` → `vf_layers_check`
  - output head：`vf_output_head_plan` → `vf_output_head_check`
- 汇合：`vf_weights_layout/merge/pending`、`vf_norm_digit_rows`、`vf_segments`、`vf_request_chain`。

### Wave 4（驱动与验收，串行）

- 同进程 `run_stage`：顺序执行 key/leaf/request，状态重置，`Refusal→NO`。
- `cpCovered`/`result-v1`/末尾四行；`h_par`、commitment ID。
- 验收门：
  - G1：哈希/域向量全过。
  - G2：plan/accounting 的 bits 字段与 C++ 一致。
  - G3：示例的 ID、`h_par`、`result-v1` 与 §1.3 逐字节一致（`build=` 固定）。
  - G4：`YES` + exit 0。
  - G5：篡改 proof → `NO: proof-refused`；错误 ID → `NO: model-statement`（exit 1）。
  - G6（后续）：RISC0/SP1 guest 构建与执行；本机 `q_V=136,088` 可作 cycle 估算起点。

---

## 7. `result-v1` 字段来源（对齐规范）

| 字段 | C++ 来源 | Rust 侧要求 |
|---|---|---|
| `status` | `goodStatus`（0）或 14 | 固定 0（YES 路径） |
| `claim` | `cpCovered()`：`next-token` / `exact-match` / `policy` | 由 request 的 r/e/T 与 policy 判定 |
| `id` | 三 stage 各自算出的 commitment ID；无 `-id` 时为 `not-shown-without-id` | 同 C++；`-id` 必须逐字符比较 |
| `bits` | `-bits`，默认 128 | 同 |
| `work` | `call.needs_work ? mostWork : 0`，`mostWork` 为 `Accounting::work` 最大值 | plan/accounting 计算 |
| `work-rounds` | `call.by_work` | plan/accounting 计算 |
| `least-round` | `cut2(call.groups[0].all())` | Real/Bound → double → 两位小数（向弱侧截断） |
| `least-round-without-work` | `cut2(call.lists.bits)` | 同上 |
| `commitment-assumed-rounds` | key/leaf 两 stage 的 `closeness[1]` 之和 | plan/accounting 计算 |
| `record` | 固定 1（parameter file `record 1`） | 校验后固定 1 |
| `r`/`e`/`T`/`tokens`/`y` | `cpCovered()` 从 request 与 stage `result:` 字段构造 | 结构化计算，避免文本解析 |
| `policy`/`C`/`theta`/`cap`/`s`/`sh`/`sT`/`F`/`above-clip`/`leaf` | request stage 的 `result:` 字段 + `aboveClip()` | 保留同一公式与整数语义 |
| `stages` | 常量 `key,leaf,request` | 常量 |
| `dw` | `DW=8` | 常量 |
| `build` | `VF_SOURCE_DIGEST` | 常量 `93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595` |

注意（S3 验收口径，TL review 修正）：

- `q_V` 只进入 `accounting:` 行，**不进入 `result-v1`**。但 **S3 P0 要求**：
  1. 末尾四行（`commitment:` / `proof of work:` / `result-v1` / `YES`）逐字节一致，exit 0；
  2. `accounting:` 行的数字（`q_V=136088`、`least-round` 等）必须由 Rust 复算且逐字节一致（`q_V` 是 zkVM cycle 估算依据，G6 引用它）；
  3. `accounting:` 文本骨架逐字节一致。
- `least-round` 的两位小数来自 `Real::log2()`（内部用 `std::log2`）与 `cut2()`（`floor(100x)/100`）。Rust 需要保证误差 < 0.005；示例的 `128.00`、`96.23` 可作为门。
- `above-clip()` 是整数公式，不涉及浮点。

---

## 8. 风险与待 TL 决策

| # | 风险 | 说明 | 建议 |
|---|---|---|---|
| R1 | **公开表 libm 对齐**（高） | `cp_verify.cpp` 用 `exp/sin/cos/pow/round` 生成 SILU/Sigmoid/RoPE/Exp 表，并用 `H` 哈希后与 `policy.txt` 的 `tsilu*/tsig*/trope*/texp*` 比较。Rust 的 `libm` 若与 C++ 实现差 1 ULP，可能改变整数取整结果 → `table-digest-*` 拒绝 | S2 第一门禁：Rust 生成的四个表逐项与 C++ 对齐，并重算 digest 与 policy 行比较；必要时 in-tree 实现或按参数预生成。**需 TL 决定是否允许引入 `libm` crate**（非密码学依赖） |
| R2 | 两位小数/浮点打印（中） | `least-round` 依赖 `log2`/`floor`；`vf_attention_shape` 用 `exp/ldexp/nearbyint` | 用示例 `128.00/96.23` 做门；必要时实现确定性 `log2`/`exp` |
| R3 | **移植规模**（高） | 静态 37k 行，`blocks/iop` 11.8k；虽可裁剪 prover 侧，仍是多周量级 | 按 §6 分片并行；每片以对拍向量收口 |
| R4 | `build=` 字段（低） | 已实测固定值；若未来改动 `verifier/src`/`blocks/*.h` 会变 | Rust 侧常量 + 一个 host 脚本复核；不改 C++ 源 |
| R5 | stage 全局状态重置（中） | C++ 靠 fork 隔离；Rust 同进程需重置约 16 个全局量 | S1 就设计 `Settings`/`StageState`，禁止可变全局 |
| R6 | 错误顺序/拒绝名（中） | 负面控制的最后一行与 exit code 依赖 `cpMain` 的检查顺序 | 按 `cpMain` 原顺序实现：命令行 → 长度 → 头部 → ID → 各 stage |
| R7 | zkVM 资源（中） | 示例 `q_V=136,088`，输入 4.1MB + 1.6MB；内存/cycle 未测 | S4 后测 RISC0/SP1 cycle；本轮不设硬指标 |
| R8 | 工具链（低） | 缺 `riscv32im-unknown-none-elf`；RISC0/SP1 自带 | 不擅自安装；zKVM 阶段由 TL 决定 |
| R9 | Linux g++ 原版复核（中） | 本机基线是 Apple clang + Apple libm，不是发布构建 | 输出已与 README 一致；建议有 Linux 环境时跑一次 `build.sh` 复核（Docker daemon 当前不可用） |

---

## 9. 证据命令汇总

```sh
# 源码规模
find verifier/src -type f -exec wc -l {} +
cd verifier/src && g++ -std=c++17 -MM -I. -I../../blocks -I../../prover \
  -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' cp_verify.cpp

# build= 复核（与 build.sh 同款；注意必须在 verifier/src 下执行，路径才会一致）
export LC_ALL=C
(cd verifier/src && \
  sha256sum * ../../prover/*/plan_rounds.h ../../prover/hiding/token_plan.h && \
  cd ../../blocks && find . -type f -name '*.h' ! -path '*/tests/*' | sort | xargs sha256sum) \
  | sha256sum | cut -c1-64
# -> 93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595

# Rust 工具链
cargo --version && rustc --version && rustup target list --installed

# C++ 基线（macOS）
clang++ -O2 -std=c++17 -pthread -Iverifier/src -Iblocks -Iprover \
  -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o /tmp/fp_cpp_build/cp_verify verifier/src/cp_verify.cpp
/tmp/fp_cpp_build/cp_verify examples/accepted-proof/config examples/accepted-proof/ivk \
  examples/accepted-proof/example.req examples/accepted-proof/example.y \
  examples/accepted-proof/example.proof \
  -id 79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183 -q   # EXIT=0, YES
```

---

## 10. S0 结论

- **可行**：验证内核不依赖 OS；外壳可完整剥离；默认串行路径不触发线程。
- **可验收**：本机已能运行 C++ 原版并得到 golden `YES`/`result-v1` 与两个负面控制，S3/S4 有明确对照物。
- **主要工作量**在 `blocks/iop` + `blocks/frame/check*` + 三个子证明检查（`vf_layers_check`、`vf_output_head_check`、`vf_attention_check`），而非 `vf_common`。
- **S0 结束，等待 TL review 后再进入 S1。**
