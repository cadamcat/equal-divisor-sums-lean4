[English](README.md) | [简体中文](README_zh.md)

# Lean 4 中约数和相等的互素数对

令 h(x) 表示满足 1 ≤ a < b < x、gcd(a, b) = 1 且 σ(a) = σ(b) 的数对个数。本仓库用 Lean 4 证明：对每个 ε > 0，当 x 充分大时，h(x) > x^(2−ε)。这是[Erdős 问题 #824](https://www.erdosproblems.com/824)。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

证明各部分之间的每个接口都表述为一个命题（`…_statement`），并由最终组装中的一个已证定理证明。唯一的 `sorry` 位于 `Challenge.lean`，是 Comparator 的陈述占位符。

## 主要结果

```lean
theorem Erdos824.erdos_824 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop, (x : ℝ) ^ (2 - ε) < (h x : ℝ)
```

`h` 是 Formal Conjectures 的定义（`FormalConjectures/ErdosProblems/824.lean`），该定理是其 `erdos_824` 右端的结论；该猜想的答案为 `True`。[Challenge.lean](Challenge.lean) 只用 Mathlib 的定义表述该结论，而 [comparator.json](comparator.json) 配置 [Comparator](https://github.com/leanprover/comparator) 对两者进行比较。

## 路线

1. **条件界**（[Erdos824/LiZhuang](Erdos824/LiZhuang)）。Li 和 Zhuang 的定理 1.3，沿用 Pollack 和 Pomerance 的方法：如果对每个 `0 < δ < 1/4`，至少有 `y^(1−o(1))` 个 `p ≤ 5y` 的素数，其 `p + 1` 的每个素因子都不超过 `y^δ`，那么该界成立。这部分是移植的他们的 Lean 代码。
2. **光滑后继素数的供给**（[Erdos824/Succ](Erdos824/Succ)）。Li 和 Zhuang 的定理 1.4：给出 `p − 1` 光滑的素数 `p` 的加权膨胀图论证，也能给出 `p = 2u − 1` 且 `p + 1 = 2u` 光滑的素数。与符号无关的部分来自作者对 [totient-fibers-lean4](https://github.com/cadamcat/totient-fibers-lean4/tree/dfce35707a67fce7362cb2bd95af8b80a0b0373e) 的形式化，并以 [Erdos821](Erdos821) 纳入本仓库；依赖符号的模块则在 `Erdos824.Succ` 下改编。
3. **组装**（[Erdos824/Final.lean](Erdos824/Final.lean)）将两部分合并。

## 构建与验证

环境要求：Git 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 在 `PATH` 中。在仓库根目录运行：

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI 的 `lake update` hook 可能在解析完依赖后退出并报错，错误以 `iut: Lake resolved an unexpected checkout at …` 开头；接着运行补丁脚本。它会将 OpenAI 的 Lean 4.34.1 兼容性补丁应用到已获取的软件包上，也可在之后再次运行 `lake update` 时重新运行该脚本。`lake exe cache get` 会获取编译后的 Mathlib；其他依赖则从源代码编译。

`scripts/verify.sh` 会构建库和挑战，比较展开后的挑战陈述、库中陈述及 `h` 的定义，拒绝禁用结构，并检查定理的公理。未完成的证明会显示为 `sorryAx`，脚本以状态码 2 退出。v1.0.0 的这些检查记录（包括 Comparator 和内核重放）见 [docs/verification.md](docs/verification.md)。

## 固定依赖

- Lean `v4.34.1`，由 [lean-toolchain](lean-toolchain) 选定。
- OpenAI 的库 [`openai/math`](https://github.com/openai/math)，固定在 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`（`lean/`）；该库固定了 Mathlib 及其其他依赖，所有版本见 [lake-manifest.json](lake-manifest.json)。

关于纳入的代码及其许可证，见 [THIRD_PARTY.md](THIRD_PARTY.md)；关于本仓库的许可证（Apache-2.0），见 [LICENSE](LICENSE)。

导出的库包含来自 `Erdos821` 的 826 个模块和来自 `Erdos824` 的 160 个模块。
