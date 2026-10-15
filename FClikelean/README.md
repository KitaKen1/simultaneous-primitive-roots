# main・無条件版・強いvariantのLean問題文

[SimultaneousPrimitiveRoots.lean](SimultaneousPrimitiveRoots.lean) が中心のLeanファイルです。4仮定と必要な定義をこのファイル内に置き、main・無条件版・強いvariantの3定理を次の順で並べています。
**importは参照repoと同じ `public import FormalConjecturesUtil` の1行**です。`TauCeti`、本repoの証明ライブラリ、別の `FClikelean` ファイルへの依存はありません。

| 役割 | 定理 | 内容 |
|---|---|---|
| main | `simultaneous_primitive_roots` | OpenAI の定理1.1。4入力を仮定し、異なる正の素数を底として、`c x/(log x)²` の下界を得る |
| variant 1 | `simultaneous_primitive_roots_unconditional` | mainと同じ素数基底・開区間・下界から、4入力だけを外した系 |
| variant 2 | `positive_lower_density` | 平方条件を満たす2以上の整数を底として、解析入力を外部仮定に置かず、`c x/log x` の下界を得る |

平方条件の必要性を示す補助結果 `square_condition_necessary` は、
[SquareConditionNecessary.lean](SquareConditionNecessary.lean) に分けています。
これは「平方条件が破れると、同時原始根となる奇素数はない」という主張です。
中心の3定理の比較には必要ありません。中心のファイルはこの補助ファイルをimportしません。
補助ファイルも同じFC標準importで単独で読めます。

mainとvariant 1は `x < p < 2x`、variant 2は `x < p ≤ 2x` を数えます。
variant 2 ⇒ variant 1 ⇒ mainの結論、の順で導けます。variant 1は本repoで証明した系であり、OpenAI原文中の別の無条件定理を指すものではありません。
定数と開始点を先に固定し、その後の全ての実数 `x` に対して主張します。
`Finset` は重複のない有限集合です。`Nat.card` の対象は `p < 2x` または `p ≤ 2x` で上から抑えられるため有限です。
原始根は `p.Prime`、`¬ p ∣ q`、`orderOf (q : ZMod p) = p - 1` で表します。

## main の4入力

出典は OpenAI, *Simultaneous primitive roots: a conditional lower bound for prime bases*
（2026年10月4日）、[固定版 PDF](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/simultaneous-primitive-roots-conditional-lower-bound-prime-bases.pdf) の定理1.1です。

4つとも、中身を展開できる `def … : Prop` として書いています。
任意の命題を引数にした仮の名前や、内容のない公理ではありません。
4入力の定義に `sorry` はありません。定理の docstring は短い数学的説明と出典にとどめています。

| 原稿 | main の引数 | 定義ファイル | 含めた内容 |
|---|---|---|---|
| Input 3.1、p.3 | `HeckeZeroFreeHypothesis` | [同じLeanファイル](SimultaneousPrimitiveRoots.lean) | μ₁₂を含む円分数体、全ての有限位数指標の L 関数、`Re s > 1 − 10⁻⁶` の非消滅 |
| Input 4.1(i)(ii)、pp.7–8 | `MarkedTypeIIHypothesis` | [同じLeanファイル](SimultaneousPrimitiveRoots.lean) | 係数条件から marked Type II 評価を得る節と、rough 係数の打ち消しを与える節の両方 |
| Input 5.1、pp.12–13 | `BlockSieveHypothesis` | [同じLeanファイル](SimultaneousPrimitiveRoots.lean) | block sieve の等式に相当する誤差評価、H の一様性、H=2 の上界 |
| Input 5.2、p.13 | `RoughDensityHypothesis` | [同じLeanファイル](SimultaneousPrimitiveRoots.lean) | rough density の積分恒等式と指数的誤差を持つ上界 |

### Input 3.1 の表現

有限位数 Hecke 指標を、イデアル上の乗法的な関数としてファイル内で定義しています。
`(Ideal (𝓞 F))⁰` は整数環 `𝓞 F` の非零整イデアルです。独自の型の略称は置いていません。
`HeckeZeroFreeHypothesis` 内に、指標の次の3条件を直接書いています。

- 値の集合が有限である。
- `χ I = 0` であることと、`I` が法 `𝔪` と互いに素でないことが同値である。
- `a ≡ 1 mod 𝔪` で全ての実埋め込みで正になる `a` が生成する主イデアルに、値1を取る。

法 `𝔪` は零イデアルを除きます。単位イデアルは許します。
これは ray class character を、法と互いに素でないイデアルで0に拡張した形です。
実埋め込みの正値条件は、法の無限部分に全ての実素点を含める表現です。
今回の対象は μ₁₂ を含む円分数体なので、実埋め込みはありません。
この古典的なイデアルによる表現と、原稿の idèle class character の対応は、
[Milne, *Class Field Theory*, Chapter VI, §1(c)(d)](https://www.jmilne.org/math/CourseNotes/CFT.pdf)
に説明されています。同値性自体を今回新たに Lean で証明したわけではなく、原文対応レビューの確認点です。

`HeckeZeroFreeHypothesis` 内で、同じ絶対ノルムを持つイデアル上で指標の値を足し、Mathlib の `LSeries` に渡します。
絶対ノルムごとの非零イデアルは有限です。
主指標は、法と互いに素なイデアル上で全て1になることを、局所的な `let principal` で表します。
この級数に `Re s > 1` で一致する有理型接続の**存在**と、指定領域での非消滅を要求します。
主指標だけは `s = 1` を除外します。非主指標には `s = 1` でも正則性と非消滅を要求します。
法により省かれる有限個の Euler 因子は `Re s > 0` では零点を作りません。
円分体は `12 ∣ m` と `IsCyclotomicExtension {m} ℚ F` で表しています。

### Input 4.1 の量化と定数

式(4.2)–(4.5)の `W`、素数群、`Vᵢ`、`ωᵢ`、mark を定義しています。
mark の2の指数は整数で書き、`K − Σωᵢ` の負の値を自然数の引き算で0に切り捨てません。
`MarkedTypeIIHypothesis` 内の `let rough` は「正の整数で、全ての素因数が y より大きい」です。1も含みます。

(i) は、許される係数を族 `𝒜 x Hm Hn` でまとめた形です。族には、区間や係数を定める全ての固定パラメータを含められます。
任意の区間に支持を持つ係数は、dyad に支持を持つ係数の一例です。
`MarkedTypeIIHypothesis` の前半に係数の仮定を直接書いています。各 `A₀, B, A > 0` について定数と開始点を先に選び、その後は dyad・族の係数・指標・周波数に一様な評価を要求します。
指標の法は `k ≤ (log x)^A₀`、周波数は `|t| ≤ 2 Hm Hn (log x)^B` です。
比較定数 `κ` は `x/κ ≤ Hm Hn ≤ κ x` に対応します。
`K₀` は固定データと共通の打ち消し評価を持つ族を選んだ後、個々の群指数 `aᵢ` を選ぶ前に置きます。
結論の定数と開始点は `aᵢ` に依存してよく、`F`・dyad・係数には一様です。
`F(ph) = F(h)` は `p ∣ h` の場合も要求します。

(ii) の係数は式(4.11)そのもので、**rough − rough** の差です。
`0 < γ < wminus < wplus < 1`、式(4.10)、任意の区間 `I`、`|v| ≤ (log x)^C`、全ての指標と周波数の範囲を含めています。
この節には mark が現れないため、`K` や群指数への不要な依存を付けていません。
`I : Set ℕ` の `Set.OrdConnected I` は、整数の区間であることを表します。

### Input 5.1 の余り

有限の対象を自然数で番号付けし、重みと各素数の悪条件を指定します。
`g` は素数での値を与え、平方因子を持たない積での値を `∏ p ∈ E, g p` と定義します。
余り `R` は「実際の重み − Y g」の差です。原稿の分解式を満たす任意の `R` は、この差と等しくなります。

ふるい後の重み・積・余りの和は、`BlockSieveHypothesis` 内の `let S`・`let V`・`let R` で書いています。
余りの和は指定素数集合の `powerset` で数えます。素数の有限集合の部分集合と、その平方因子を持たない積は一対一です。
空の部分集合の積は1なので、**ℓ=1 の余りも入ります**。余分な係数や重複度は付けません。
指定素数以外の `g(p)` は使わず、原稿の0への拡張に対応します。
同じ正の定数 `M` で2種類の誤差を抑える形は、原稿の別々の暗黙定数の大きい方を取った形です。
`M` と `H₀` は `η₀, C₀` の後、その他のデータや `H` の前に選びます。

### Input 5.2 の密度

`roughDensity` に式(4.7)の各積分と、その和を直接書いています。
`Fin (j − 1) → ℝ` は積分変数が `j − 1` 個あることを表します。
最初の項は `1/w`。`j ≥ 2` では、全ての変数が `γ` 以上、和が `w − γ` 以下の領域で積分します。
`RoughDensityHypothesis` は `bd, cd, Cd > 0` を先に選び、全ての `0 < b < min bd (1/2)` について式(5.3)を要求します。
Euler の定数には Mathlib の `Real.eulerMascheroniConstant` を使います。

## variant の対応

| 原文の対象 | Lean |
|---|---|
| 空でない有限集合 A ⊂ ℤ≥2 | `∀ A : Finset ℕ, A.Nonempty → (∀ a ∈ A, 2 ≤ a) →` |
| 奇数個の要素の積は平方でない | `∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a)` |
| SQ が破れると同時原始根となる奇素数はない | `square_condition_necessary` の `∀ p : ℕ, 2 < p → ¬ (...)` |

必要方向は非空性や底の下界を仮定しない、少し強い形です。
十分方向に GRH、Hypothesis H、OpenAI の4入力を要求する引数はありません。

## 検証の範囲

中心のファイルの3個、補助ファイルの1個の `sorry` は、独立した**問題文**の証明欄です。
4入力の定義やその補助定義には穴を置いていません。
中心のファイルだけで3つの問題文が完結します。外に置く `def` は4つの仮定と共通の密度 `roughDensity` の5個です。
Type II仮定の中でだけ使う式は、その仮定内の `let` に収めています。これは数学的内容を消す操作ではありません。
Lean 4.33.1で、中心と補助の各ファイルを独立にコンパイルできます。
これは4入力自体の証明や、原稿の全表現との同値性の証明を意味しません。

2つのvariantと補助結果の完全な証明は [Solution.lean](../lean/Solution.lean) にあります。
[Challenge.lean](../lean/Challenge.lean) には①main・②variant 1・③variant 2・補助結果の4つを置き、mainの4仮定と共通の密度関数も全て定義しています。importはMathlibだけで、証明ファイルには依存しません。
この4宣言と5定義がFC側と一致することをソース検査し、Comparatorも4定理とその依存する定義を直接照合します。
①の完全な証明は [OpenAIMain.lean](../lean/SimultaneousPrimitiveRootsFinal/OpenAIMain.lean) で②を適用します。4入力そのものの証明ではありません。

```bash
cd ../tools/fc-style
lake build
python3 ../../scripts/check_fclike_standalone.py
```

以前の分離の記録は [fclike-auxiliary-separation-review.json](../ci/fclike-auxiliary-separation-review.json)、
前回のスタイル整理と4仮定の同値性の記録は [fclike-comparable-statements-review.json](../ci/fclike-comparable-statements-review.json) にあります。


## 参考にした FC の形

[Artin の条件付き定理](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean)
の `HooleyHypothesis` のように、仮定を数学的な内容で命名しています。
[FC の定理文ガイド](https://github.com/google-deepmind/formal-conjectures/blob/main/STATEMENTS.md)
に従い、この問題固有の定義は同じファイル内に置いています。
FC 自体の標準 import は `FormalConjecturesUtil` で、その中から Mathlib が読み込まれます。
本repoも `module`、`public import FormalConjecturesUtil`、`@[expose] public section` を使い、全3定理と補助結果に `@[category research solved, AMS 11]` を付けています。
①は既知の条件付き定理、②・③は証明済みの結果なので、`research open` にはしません。
標準属性は、`tools/fc-style/` の固定版FC（Lean 4.33.1）で実際にコンパイルして確認します。
全定理に `formal_proof using lean4 at "…"` を付けています。①は `lean/SimultaneousPrimitiveRootsFinal/OpenAIMain.lean`、②・③・補助結果は `lean/Solution.lean` のGitHub URLを指します。現在は公開予定の `main` ブランチのURLです。まだpushしていません。公開後に、その版のcommitへ固定できます。

参考文献は `[OAI26]` と `[Ki26]` にそろえています。`[Ki26]` は Kenta Kitamura, *Positive Lower Density of Simultaneous Primitive Roots*（2026）に付随する本repoのLean形式化を指します。無条件版の証明を参照する先はLean repoです。


中心の3定理は、全て `theorem … :` の後を
`∀ A : Finset ℕ, A.Nonempty →` から始め、底の条件・追加条件・個数評価の順にそろえています。
main の4仮定は `∧` でまとめています。
証明用の [Solution.lean](../lean/Solution.lean) は従来の引数形式を保ちますが、2つのvariantと補助結果の命題の型は、対応する問題文と定義上同一です。


## variant 1の証明

`simultaneous_primitive_roots_unconditional` は `positive_lower_density` の系です。
異なる素数の積が平方にならないことを示し、③の下界を弱めます。
区間は整数 `n = ⌊x⌋₊` に対する③を使って合わせます。
`n < p ≤ 2n` の素数は `x < p < 2x` に入り、`n ≥ 2` なら上端 `2n` は合成数です。
開始点を大きくし、定数を半分にして、元のmainと同じ下界を得ます。
4つの解析入力自体の証明ではありません。

今回のビルド・公理・Comparator・独立した定理文の確認は
[four-target-review.json](../ci/four-target-review.json) に記録します。
