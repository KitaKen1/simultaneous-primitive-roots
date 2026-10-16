# FC提出用：4仮定なし版と強いvariant

[SimultaneousPrimitiveRoots.lean](SimultaneousPrimitiveRoots.lean) がFCへの提出用ファイルです。
**OpenAIの4仮定を置かない2定理だけ**を並べています。問題固有の `def` はありません。
importは `public import FormalConjecturesUtil` の1行で、証明ライブラリや他の `FClikelean` ファイルには依存しません。

| 順番 | 定理 | 内容 |
|---|---|---|
| variant 1 | `simultaneous_primitive_roots_unconditional` | 空でない素数の有限集合について、4つの解析的仮定を置かず、`x < p < 2x` に `c x/(log x)²` 個以上の同時原始根素数がある |
| variant 2 | `positive_lower_density` | 平方条件を満たす2以上の整数の有限集合について、`x < p ≤ 2x` に `c x/log x` 個以上ある |

**強いvariant 2 ⇒ variant 1** をLeanで証明しています。
variant 1は、OpenAIの条件付き定理の結論から4仮定を外すことを意図した本repoの系です。
OpenAI原文に別の無条件定理として書かれている、という意味ではありません。
その結論と原文の対応が確認できれば、OpenAIの条件付き結論も従います。4仮定そのものを証明する必要はありません。

## OpenAIの4仮定付きは別ファイル

[OpenAIConditional.lean](OpenAIConditional.lean) は**repo内の参考資料で、今回のFC提出対象外**です。
4仮定付きの `simultaneous_primitive_roots` と、必要な5定義をここにまとめています。
原文の4入力と正確に同値かどうかは引き続き確認する項目であり、確認済みとは主張しません。

出典は OpenAI, *Simultaneous primitive roots: a conditional lower bound for prime bases*
（2026年10月4日）、[固定版PDFの定理1.1](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/simultaneous-primitive-roots-conditional-lower-bound-prime-bases.pdf#page=1) です。

| 原文の入力 | 参考ファイルの定義 | 内容の概要 |
|---|---|---|
| Input 3.1 | `HeckeZeroFreeHypothesis` | 指定したHecke L関数の非消滅 |
| Input 4.1(i)(ii) | `MarkedTypeIIHypothesis` | marked Type II評価とrough係数の打ち消し |
| Input 5.1 | `BlockSieveHypothesis` | block sieveの誤差評価 |
| Input 5.2 | `RoughDensityHypothesis` | rough densityの積分恒等式と誤差評価 |
| 共通の密度関数 | `roughDensity` | rough densityを表す積分の和 |

5定義の中に `sorry` はありません。ただし、定義に穴がないことと、原文の表現に正確に対応していることは別の確認です。

## 平方条件の必要性も別ファイル

[SquareConditionNecessary.lean](SquareConditionNecessary.lean) は独立した補足です。
「平方条件が破れると、全ての底を同時に原始根とする奇素数はない」と述べます。
この補足も、今回の2定理の提出ファイルからはimportしません。

| ファイル | 役割 | 問題文の `sorry` |
|---|---|---:|
| `SimultaneousPrimitiveRoots.lean` | FC提出用の2定理 | 2 |
| `OpenAIConditional.lean` | 4仮定付きの参考資料。原文対応を確認中 | 1 |
| `SquareConditionNecessary.lean` | 平方条件の必要性の補足 | 1 |

各 `sorry` は独立した問題文の証明欄です。完全な証明は別の証明ライブラリにあります。

## 自然言語とLeanの対応

2定理は、どちらも `theorem … :` の後を
`∀ A : Finset ℕ, A.Nonempty →` から始め、底の条件、個数の評価の順にそろえています。

| 内容 | variant 1 | variant 2 |
|---|---|---|
| 空でない有限集合 | `∀ A : Finset ℕ, A.Nonempty →` | 同じ |
| 底の条件 | `∀ a ∈ A, a.Prime` | `∀ a ∈ A, 2 ≤ a` |
| 平方条件 | 素数の集合なので自動的に成立 | `∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a)` |
| 解析的な追加仮定 | なし | なし |
| 下界 | `c * (x / (Real.log x) ^ 2)` | `c * (x / Real.log x)` |
| 区間 | `x < (p : ℝ) ∧ (p : ℝ) < 2 * x` | `x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x` |

`Finset` は重複のない有限集合です。原始根は
`p.Prime`、`¬ p ∣ a`、`orderOf (a : ZMod p) = p - 1` で表します。
正の定数と開始点を先に固定し、その後の全ての十分大きい実数 `x` に対して下界を主張します。
`Nat.card` が数える素数集合は `p < 2x` または `p ≤ 2x` により有限です。

## 証明とComparator

[Solution.lean](../lean/Solution.lean) が2つのvariantと平方条件の補足を証明します。
variant 1では、素数集合の平方条件を示してvariant 2を適用し、下界を弱めます。
区間の差は `n = ⌊x⌋₊` を使って調整します。`n ≥ 2` では上端の `2n` は合成数です。
定数と開始点も調整することで、`x < p < 2x` の結論を得ます。

[OpenAIMain.lean](../lean/SimultaneousPrimitiveRootsFinal/OpenAIMain.lean) は、
別に置いた4仮定付き参考定理にvariant 1を適用します。4仮定そのものの証明ではありません。

[Challenge.lean](../lean/Challenge.lean) と [Comparator設定](../lean/comparator.json) は、
従来どおり4仮定付き参考定理、2つのvariant、平方条件の補足の**4対象を維持**します。
参考定理の5定義もChallengeと証明側に残します。
Comparatorが照合するのはこれらのLean表現の一致であり、原文の自然言語との同値性ではありません。
この検証範囲は、今回のFC提出範囲より広いものです。

## FCの形式と出典

[参照repo](https://github.com/KitaKen1/entropic-rogers-shephard/blob/main/FClikelean/EntropicRogersShephard.lean) と同様に、
`module`、`public import FormalConjecturesUtil`、`@[expose] public section` を使います。
提出する2定理には `@[category research solved, AMS 11]` と `formal_proof using lean4 at "…"` を付けます。
FCに受理済みという意味ではありません。

参考文献は `[OAI26]` と `[Ki26]` です。
`[OAI26]` はOpenAIの条件付き論文、`[Ki26]` は本repoのLean形式化を指します。
無条件証明について参照する資料は、本repoのLean形式化です。
両variantと補足の証明URLは、固定commit
`c4775966844ff78f0488492ee2aef7bd1437c51d` の
[Solution.lean](https://github.com/KitaKen1/simultaneous-primitive-roots/blob/c4775966844ff78f0488492ee2aef7bd1437c51d/lean/Solution.lean) を指します。
このURLは、そのcommitがpublic repoに反映された後に利用できます。

独立した問題文ファイルは、固定版FC utilitiesを使ってLean 4.33.1で確認します。

```bash
cd ../tools/fc-style
lake build
python3 ../../scripts/check_fclike_standalone.py
```

既存の証明・公理・Comparator確認の範囲は
[four-target-review.json](../ci/four-target-review.json) に記録しています。
