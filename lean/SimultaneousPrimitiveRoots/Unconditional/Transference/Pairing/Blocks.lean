module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Moment
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Corollary 3.11: the partition into blocks of length `H + 1`

Source: `verification/stage7-sources/S-02.tex`, lines 1291–1330 (`[S-02:1291–1330]`).

"Partition `I` into consecutive intervals `I_j` of length `⌈H⌉`, except possibly the last. Put
`f_j = 1_{I_j} f` and restrict `g` to the `H`-neighborhood of `I_j` to obtain `g_j`. These
neighborhoods have bounded overlap, and `⟨f, 𝒜 g⟩ = ∑_j ⟨f_j, 𝒜 g_j⟩`, `∑_j ‖g_j‖² ≪ ‖g‖²`."

Here `H = stepBound` bounds every displacement, the blocks are the sets of positions with a given
value of `blk n = ⌊n / (H + 1)⌋` (`blockOf`), and `blockNbhd j` is the `H`-neighborhood of the
block `j`.

* `markVec I f_n = ∑_{n ∈ I} f_n u_n` is the first endpoint; `gp_markVec` and `gsq_markVec`
  identify `pairMarkFree` and `markFreeNormSq` with its inner products and its norm.
* `sum_blockNbhd_le` — bounded overlap: every position lies in at most three neighborhoods, so
  `∑_j ‖g_j‖² ≤ 3 ‖g‖²`.
* `norm_pairMarkFree_sq_le` — `|⟨f, 𝒜 g⟩|² ≤ (∑_j ‖𝒜* f_j‖²) · 3 ‖g‖²`: adjointness
  `⟨f_j, 𝒜 g⟩ = ⟨𝒜* f_j, g⟩`, the support of `𝒜* f_j` in the neighborhood of the block, and
  Cauchy–Schwarz in every block and in the sum over the blocks. (The paper restricts `g` first and
  uses the adjoint afterwards; the two orders give the same bound.)
* `blockMoment r = ∑_j ⟨f_j, (𝒜 𝒜*)^r f_j⟩` is log-convex in `r` (`blockMoment_sq_le`); it is
  `‖f‖²` for `r = 0` and `∑_j ‖𝒜* f_j‖²` for `r = 1`. This replaces the paper's Hölder inequality
  with exponents `2`, `2R/(R-1)`, `2R` over the blocks: a sum of log-convex sequences is
  log-convex.
* `blockMoment_le` — "the finite matrix `(⟨u_n, B₀^R u_m⟩)_{n,m ∈ I_j}` is positive semidefinite;
  its largest eigenvalue is at most its trace, so mark independence implies
  `⟨f_j, B₀^R f_j⟩ ≤ (∑_{n ∈ I_j} |f_n|²) d_j`": here by `B₀^R = W* W` and Cauchy–Schwarz for the
  combination `W f_j = ∑ f_n W u_n`; and `∑_{n ∈ I_j} |f_n|² ≤ (H + 1) sup |f_n|²`.
* `pairMarkFree_pow_le` — the resulting inequality
  `|⟨f, 𝒜 g⟩|^{2R} ≤ (3‖g‖²)^R ‖f‖^{2(R-1)} (H + 1) sup|f_n|² ∑_{n ∈ I} ⟨u_n, (𝒜 𝒜*)^R u_n⟩`,
  for every finite set `I` of positions and every `R ≥ 1`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Blocks of positions and bounded overlap -/

/-- The index of the block of length `H + 1` containing the position `n`. -/
def blk (H : ℕ) (n : ℤ) : ℤ := n / ((H : ℤ) + 1)

theorem blk_mul_le (H : ℕ) (n : ℤ) : blk H n * ((H : ℤ) + 1) ≤ n :=
  Int.ediv_mul_le n (by omega)

theorem lt_blk_add_one_mul (H : ℕ) (n : ℤ) : n < (blk H n + 1) * ((H : ℤ) + 1) :=
  Int.lt_ediv_add_one_mul_self n (by omega)

/-- The positions at distance at most `H` from the block `j`. -/
def blockNbhd (H : ℕ) (j : ℤ) : Finset ℤ :=
  Finset.Icc (j * ((H : ℤ) + 1) - H) (j * ((H : ℤ) + 1) + H + H)

/-- A position of the neighborhood of the block `j` lies in the block `j - 1`, `j` or `j + 1`. -/
theorem mem_Icc_of_mem_blockNbhd {H : ℕ} {j n : ℤ} (h : n ∈ blockNbhd H j) :
    j ∈ Finset.Icc (blk H n - 1) (blk H n + 1) := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp h
  have hΛ : (0 : ℤ) < (H : ℤ) + 1 := by omega
  have h1 : blk H n < j + 2 := (Int.ediv_lt_iff_lt_mul hΛ).mpr (by linarith)
  have h2 : j - 1 ≤ blk H n := (Int.le_ediv_iff_mul_le hΛ).mpr (by linarith)
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- **Bounded overlap** [S-02:1293–1297]: the neighborhoods of the blocks cover every position at
most three times. -/
theorem sum_blockNbhd_le {φ : ℤ → ℝ} (hφ : ∀ n, 0 ≤ φ n) {G : ℝ}
    (hG : ∀ U : Finset ℤ, ∑ n ∈ U, φ n ≤ G) (H : ℕ) (𝒥 : Finset ℤ) :
    ∑ j ∈ 𝒥, ∑ n ∈ blockNbhd H j, φ n ≤ 3 * G := by
  have h1 : ∀ j ∈ 𝒥, ∑ n ∈ blockNbhd H j, φ n =
      ∑ n ∈ 𝒥.biUnion (blockNbhd H), if n ∈ blockNbhd H j then φ n else 0 := by
    intro j hj
    rw [Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem (blockNbhd H) hj)]
  have h2 : ∀ n ∈ 𝒥.biUnion (blockNbhd H),
      ∑ j ∈ 𝒥, (if n ∈ blockNbhd H j then φ n else 0) ≤ 3 * φ n := by
    intro n _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsub : (𝒥.filter fun j => n ∈ blockNbhd H j) ⊆
        Finset.Icc (blk H n - 1) (blk H n + 1) :=
      fun j hj => mem_Icc_of_mem_blockNbhd (Finset.mem_filter.mp hj).2
    have h3 : (Finset.Icc (blk H n - 1) (blk H n + 1)).card = 3 := by
      rw [Int.card_Icc]
      omega
    have hcard : ((𝒥.filter fun j => n ∈ blockNbhd H j).card : ℝ) ≤ 3 := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq h3
    exact mul_le_mul_of_nonneg_right hcard (hφ n)
  calc ∑ j ∈ 𝒥, ∑ n ∈ blockNbhd H j, φ n
      = ∑ j ∈ 𝒥, ∑ n ∈ 𝒥.biUnion (blockNbhd H), (if n ∈ blockNbhd H j then φ n else 0) :=
        Finset.sum_congr rfl h1
    _ = ∑ n ∈ 𝒥.biUnion (blockNbhd H), ∑ j ∈ 𝒥, (if n ∈ blockNbhd H j then φ n else 0) :=
        Finset.sum_comm
    _ ≤ ∑ n ∈ 𝒥.biUnion (blockNbhd H), 3 * φ n := Finset.sum_le_sum h2
    _ = 3 * ∑ n ∈ 𝒥.biUnion (blockNbhd H), φ n := (Finset.mul_sum _ _ _).symm
    _ ≤ 3 * G := mul_le_mul_of_nonneg_left (hG _) (by norm_num)

/-- The part of the finite set `I` in the block `j`. -/
def blockOf (H : ℕ) (I : Finset ℤ) (j : ℤ) : Finset ℤ := I.filter fun n => blk H n = j

theorem mem_blockOf_bounds {H : ℕ} {I : Finset ℤ} {j n : ℤ} (hn : n ∈ blockOf H I j) :
    j * ((H : ℤ) + 1) ≤ n ∧ n ≤ j * ((H : ℤ) + 1) + H := by
  have hblk : blk H n = j := (Finset.mem_filter.mp hn).2
  have h1 := blk_mul_le H n
  have h2 := lt_blk_add_one_mul H n
  rw [hblk] at h1 h2
  exact ⟨h1, by linarith⟩

/-- A block contains at most `H + 1` positions. -/
theorem card_blockOf_le (H : ℕ) (I : Finset ℤ) (j : ℤ) : (blockOf H I j).card ≤ H + 1 := by
  have hsub : blockOf H I j ⊆ Finset.Icc (j * ((H : ℤ) + 1)) (j * ((H : ℤ) + 1) + H) :=
    fun n hn => Finset.mem_Icc.mpr (mem_blockOf_bounds hn)
  have hcard : (Finset.Icc (j * ((H : ℤ) + 1)) (j * ((H : ℤ) + 1) + H)).card = H + 1 := by
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans_eq hcard

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-! ### The first endpoint `f = ∑ f_n u_n` -/

section MarkVec

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)

/-- **The first endpoint of Corollary 3.11** [S-02:1268–1270]: `f = ∑_{n ∈ I} f_n u_n`, "supported
on positions `I` and independent of the chosen marks, with value `f_n` at position `n`". -/
def markVec (I : Finset 𝔭.Pos) (fn : 𝔭.Pos → ℂ) : PState 𝔭 𝒢 J ℓ → ℂ :=
  ∑ n ∈ I, fn n • physUnit 𝔭 𝒢 J ℓ n

variable {𝔭 𝒢 J ℓ}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem markVec_apply_of_mem {I : Finset 𝔭.Pos} (fn : 𝔭.Pos → ℂ) {m : 𝔭.Pos} (hm : m ∈ I)
    (x : Lists 𝒢 J ℓ) :
    markVec 𝔭 𝒢 J ℓ I fn (m, x) = fn m * physUnit 𝔭 𝒢 J ℓ m (m, x) := by
  have h : ∀ n ∈ I, n ≠ m → (fn n • physUnit 𝔭 𝒢 J ℓ n) (m, x) = 0 := fun n _ hne => by
    rw [Pi.smul_apply, physUnit_apply_of_ne (Ne.symm hne), smul_zero]
  unfold markVec
  rw [Finset.sum_apply]
  exact (Finset.sum_eq_single_of_mem m hm h).trans rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem markVec_apply_of_notMem {I : Finset 𝔭.Pos} (fn : 𝔭.Pos → ℂ) {m : 𝔭.Pos} (hm : m ∉ I)
    (x : Lists 𝒢 J ℓ) : markVec 𝔭 𝒢 J ℓ I fn (m, x) = 0 := by
  unfold markVec
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hne : m ≠ n := fun h => hm (by rw [h]; exact hn)
  rw [Pi.smul_apply, physUnit_apply_of_ne hne, smul_zero]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem posSupp_markVec (I : Finset 𝔭.Pos) (fn : 𝔭.Pos → ℂ) :
    PosSupp 𝔭 𝒢 J ℓ (markVec 𝔭 𝒢 J ℓ I fn) ↑I :=
  fun _ x hm => markVec_apply_of_notMem fn hm x

theorem fib_markVec_of_mem {I : Finset 𝔭.Pos} (fn : 𝔭.Pos → ℂ) {m : 𝔭.Pos} (hm : m ∈ I)
    (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    fib 𝔭 𝒢 J ℓ m (markVec 𝔭 𝒢 J ℓ I fn) G = conj (fn m) * pairUnit 𝔭 𝒢 J ℓ m G := by
  have h : ∀ x : Lists 𝒢 J ℓ,
      markVec 𝔭 𝒢 J ℓ I fn (m, x) = (fn m • physUnit 𝔭 𝒢 J ℓ m) (m, x) :=
    fun x => markVec_apply_of_mem fn hm x
  rw [fib_congr_left h, fib_smul_left, fib_physUnit_self]

theorem fibSq_markVec_of_mem {I : Finset 𝔭.Pos} (fn : 𝔭.Pos → ℂ) {m : 𝔭.Pos} (hm : m ∈ I) :
    fibSq 𝔭 𝒢 J ℓ m (markVec 𝔭 𝒢 J ℓ I fn) = ‖fn m‖ ^ 2 * unitNormSq 𝔭 𝒢 J ℓ m := by
  have h : ∀ x : Lists 𝒢 J ℓ,
      markVec 𝔭 𝒢 J ℓ I fn (m, x) = (fn m • physUnit 𝔭 𝒢 J ℓ m) (m, x) :=
    fun x => markVec_apply_of_mem fn hm x
  rw [fibSq_congr h, fibSq_smul, fibSq_physUnit_self]

/-- **`pairMarkFree I f_n G` is the inner product `⟨f, G⟩`** with `f = ∑_{n ∈ I} f_n u_n`. -/
theorem gp_markVec (I : Finset 𝔭.Pos) (fn : 𝔭.Pos → ℂ) (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ (markVec 𝔭 𝒢 J ℓ I fn) G = pairMarkFree 𝔭 𝒢 J ℓ I fn G := by
  rw [gp_eq_sum_left I (posSupp_markVec I fn)]
  unfold pairMarkFree
  exact Finset.sum_congr rfl fun n hn => fib_markVec_of_mem fn hn G

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- A linear map applied to `f = ∑_{n ∈ I} f_n u_n`. -/
theorem map_markVec (T : (PState 𝔭 𝒢 J ℓ → ℂ) →ₗ[ℂ] (PState 𝔭 𝒢 J ℓ → ℂ)) (I : Finset 𝔭.Pos)
    (fn : 𝔭.Pos → ℂ) :
    T (markVec 𝔭 𝒢 J ℓ I fn) = ∑ n ∈ I, fn n • T (physUnit 𝔭 𝒢 J ℓ n) := by
  unfold markVec
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => map_smul _ _ _

/-- **`markFreeNormSq I f_n` is `‖f‖²`** for `f = ∑_{n ∈ I} f_n u_n`. -/
theorem gsq_markVec (I : Finset 𝔭.Pos) (fn : 𝔭.Pos → ℂ) :
    gsq 𝔭 𝒢 J ℓ (markVec 𝔭 𝒢 J ℓ I fn) = markFreeNormSq 𝔭 𝒢 J ℓ I fn := by
  rw [gsq_eq_sum I (posSupp_markVec I fn)]
  unfold markFreeNormSq
  exact Finset.sum_congr rfl fun n hn => fibSq_markVec_of_mem fn hn

end MarkVec

/-! ### The decomposition of the pairing over the blocks -/

section Blocks

variable {𝒢 : GroupFamily S B} {q : ℝ} {J ℓ : ℕ} {N : Type} [Fintype N]

/-- `⟨f, G⟩ = ∑_j ⟨f_j, G⟩` [S-02:1294–1296]. -/
theorem pairMarkFree_eq_sum_blocks (H : ℕ) (I : Finset ℤ) (fn : ℤ → ℂ)
    (G : PState intPos 𝒢 J ℓ → ℂ) :
    pairMarkFree intPos 𝒢 J ℓ I fn G =
      ∑ j ∈ I.image (blk H), gp intPos 𝒢 J ℓ (markVec intPos 𝒢 J ℓ (blockOf H I j) fn) G := by
  have h : ∀ j ∈ I.image (blk H),
      gp intPos 𝒢 J ℓ (markVec intPos 𝒢 J ℓ (blockOf H I j) fn) G =
        ∑ n ∈ I with blk H n = j, conj (fn n) * pairUnit intPos 𝒢 J ℓ n G :=
    fun j _ => gp_markVec (𝔭 := intPos) (blockOf H I j) fn G
  rw [Finset.sum_congr rfl h]
  unfold pairMarkFree
  exact (Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem _ hn) _).symm

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- `f_j` is supported on the block `j`. -/
theorem suppIcc_markVec_block (H : ℕ) (I : Finset ℤ) (fn : ℤ → ℂ) (j : ℤ) :
    SuppIcc (markVec intPos 𝒢 J ℓ (blockOf H I j) fn) (j * ((H : ℤ) + 1))
      (j * ((H : ℤ) + 1) + H) := by
  unfold SuppIcc
  exact posSupp_mono (posSupp_markVec (𝔭 := intPos) (blockOf H I j) fn) fun n hn =>
    mem_blockOf_bounds (Finset.mem_coe.mp hn)

/-- **One block** [S-02:1299–1305]: `|⟨f_j, 𝒜 g⟩|² ≤ ‖𝒜* f_j‖² · ‖g_j‖²`, where `g_j` is the
restriction of `g` to the `H`-neighborhood of the block. -/
theorem norm_gp_block_sq_le (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ)
    (fn : ℤ → ℂ) (g : PState intPos 𝒢 J ℓ → ℂ) (j : ℤ) :
    ‖gp intPos 𝒢 J ℓ (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn)
        (physOp intPos 𝒢 q 𝔉 k ζ g)‖ ^ 2 ≤
      gsq intPos 𝒢 J ℓ (physAdj intPos 𝒢 q 𝔉 k ζ
          (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn)) *
        ∑ n ∈ blockNbhd (stepBound 𝒢 J k) j, fibSq intPos 𝒢 J ℓ n g := by
  have hf := suppIcc_markVec_block (𝒢 := 𝒢) (J := J) (ℓ := ℓ) (stepBound 𝒢 J k) I fn j
  rw [gp_physOp_int 𝔉 k ζ hf g]
  exact norm_gp_sq_le_window (suppIcc_physAdj 𝔉 k ζ hf) g

/-- **`|⟨f, 𝒜 g⟩|² ≤ (∑_j ‖𝒜* f_j‖²) · 3 ‖g‖²`** [S-02:1291–1305]. -/
theorem norm_pairMarkFree_sq_le (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ)
    (fn : ℤ → ℂ) {g : PState intPos 𝒢 J ℓ → ℂ} (hg : MemPhysL2 intPos 𝒢 J ℓ g) :
    ‖pairMarkFree intPos 𝒢 J ℓ I fn (physOp intPos 𝒢 q 𝔉 k ζ g)‖ ^ 2 ≤
      (∑ j ∈ I.image (blk (stepBound 𝒢 J k)),
          gsq intPos 𝒢 J ℓ (physAdj intPos 𝒢 q 𝔉 k ζ
            (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn))) *
        (3 * physNormSq intPos 𝒢 J ℓ g) := by
  have hm : ∀ j : ℤ, 0 ≤ gsq intPos 𝒢 J ℓ (physAdj intPos 𝒢 q 𝔉 k ζ
      (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn)) := fun j =>
    gsq_nonneg_int (suppIcc_physAdj 𝔉 k ζ (suppIcc_markVec_block (stepBound 𝒢 J k) I fn j))
  have hγ : ∀ j : ℤ, 0 ≤ ∑ n ∈ blockNbhd (stepBound 𝒢 J k) j, fibSq intPos 𝒢 J ℓ n g :=
    fun j => Finset.sum_nonneg fun n _ => fibSq_nonneg (𝔭 := intPos) n g
  have h1 := norm_sum_sq_le_of_forall (I.image (blk (stepBound 𝒢 J k)))
    (fun j => gp intPos 𝒢 J ℓ (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn)
      (physOp intPos 𝒢 q 𝔉 k ζ g)) _ _ hm hγ
    (fun j _ => norm_gp_block_sq_le 𝔉 k ζ I fn g j)
  rw [pairMarkFree_eq_sum_blocks (stepBound 𝒢 J k)]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun j _ => hm j))
  exact sum_blockNbhd_le (φ := fun n => fibSq intPos 𝒢 J ℓ n g)
    (fun n => fibSq_nonneg (𝔭 := intPos) n g)
    (fun U => sum_fibSq_le_physNormSq (𝔭 := intPos) hg U) _ _

/-! ### The moments of the blocks -/

variable (𝒢 q)

/-- `∑_j ⟨f_j, (𝒜 𝒜*)^r f_j⟩ = ∑_j ‖altOp r f_j‖²`, the sum over the blocks of the `r`-th moments
of the pieces of the first endpoint. -/
def blockMoment (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ) (fn : ℤ → ℂ)
    (r : ℕ) : ℝ :=
  ∑ j ∈ I.image (blk (stepBound 𝒢 J k)),
    gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ r
      (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn))

variable {𝒢 q}

theorem blockMoment_nonneg (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ)
    (fn : ℤ → ℂ) (r : ℕ) : 0 ≤ blockMoment 𝒢 q 𝔉 k ζ I fn r := by
  unfold blockMoment
  exact Finset.sum_nonneg fun j _ => gsq_nonneg_int
    (suppIcc_altOp 𝒢 q 𝔉 k ζ r (suppIcc_markVec_block (stepBound 𝒢 J k) I fn j))

/-- **The block moments are log-convex** (Cauchy–Schwarz in every block and over the blocks). -/
theorem blockMoment_sq_le (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ)
    (fn : ℤ → ℂ) (r : ℕ) :
    blockMoment 𝒢 q 𝔉 k ζ I fn (r + 1) ^ 2 ≤
      blockMoment 𝒢 q 𝔉 k ζ I fn r * blockMoment 𝒢 q 𝔉 k ζ I fn (r + 1 + 1) := by
  unfold blockMoment
  exact sum_sq_le_of_forall _ _ _ _
    (fun j _ => gsq_nonneg_int
      (suppIcc_altOp 𝒢 q 𝔉 k ζ (r + 1) (suppIcc_markVec_block (stepBound 𝒢 J k) I fn j)))
    (fun j => gsq_nonneg_int
      (suppIcc_altOp 𝒢 q 𝔉 k ζ r (suppIcc_markVec_block (stepBound 𝒢 J k) I fn j)))
    (fun j => gsq_nonneg_int
      (suppIcc_altOp 𝒢 q 𝔉 k ζ (r + 1 + 1) (suppIcc_markVec_block (stepBound 𝒢 J k) I fn j)))
    (fun j _ => gsq_altOp_sq_le 𝒢 q 𝔉 k ζ r (suppIcc_markVec_block (stepBound 𝒢 J k) I fn j))

/-- The block moment of order `0` is `‖f‖²`. -/
theorem blockMoment_zero (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ)
    (fn : ℤ → ℂ) : blockMoment 𝒢 q 𝔉 k ζ I fn 0 = markFreeNormSq intPos 𝒢 J ℓ I fn := by
  have h : ∀ j ∈ I.image (blk (stepBound 𝒢 J k)),
      gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ 0
          (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn)) =
        ∑ n ∈ I with blk (stepBound 𝒢 J k) n = j, ‖fn n‖ ^ 2 * unitNormSq intPos 𝒢 J ℓ n :=
    fun j _ => gsq_markVec (𝔭 := intPos) (blockOf (stepBound 𝒢 J k) I j) fn
  unfold blockMoment
  rw [Finset.sum_congr rfl h]
  unfold markFreeNormSq
  exact Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem _ hn) _

/-- The block moment of order `1` is `∑_j ‖𝒜* f_j‖²`. -/
theorem blockMoment_one (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ)
    (fn : ℤ → ℂ) :
    blockMoment 𝒢 q 𝔉 k ζ I fn 1 =
      ∑ j ∈ I.image (blk (stepBound 𝒢 J k)),
        gsq intPos 𝒢 J ℓ (physAdj intPos 𝒢 q 𝔉 k ζ
          (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn)) := by
  unfold blockMoment
  exact Finset.sum_congr rfl fun j _ => by rw [altOp_one_apply]

/-- **The block moment of order `R` is controlled by the moments of the `u_n`**
[S-02:1306–1316]: `⟨f_j, B₀^R f_j⟩ ≤ (∑_{n ∈ I_j} |f_n|²) ∑_{n ∈ I_j} ⟨u_n, B₀^R u_n⟩`, and a block
has at most `H + 1` positions. -/
theorem blockMoment_le (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ) (fn : ℤ → ℂ)
    {s : ℝ} (hs : ∀ n ∈ I, ‖fn n‖ ≤ s) (R : ℕ) :
    blockMoment 𝒢 q 𝔉 k ζ I fn R ≤
      ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 * ∑ n ∈ I, physMoment intPos 𝒢 q 𝔉 k ζ R n := by
  have hblock : ∀ j ∈ I.image (blk (stepBound 𝒢 J k)),
      gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ R
          (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn)) ≤
        ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 *
          ∑ n ∈ I with blk (stepBound 𝒢 J k) n = j, physMoment intPos 𝒢 q 𝔉 k ζ R n := by
    intro j _
    have hlin : altOp 𝒢 q 𝔉 k ζ R (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn) =
        ∑ n ∈ blockOf (stepBound 𝒢 J k) I j,
          fn n • altOp 𝒢 q 𝔉 k ζ R (physUnit intPos 𝒢 J ℓ n) :=
      map_markVec (𝔭 := intPos) (altOp 𝒢 q 𝔉 k ζ R) (blockOf (stepBound 𝒢 J k) I j) fn
    have hsupp : ∀ n ∈ blockOf (stepBound 𝒢 J k) I j,
        SuppIcc (altOp 𝒢 q 𝔉 k ζ R (physUnit intPos 𝒢 J ℓ n))
          (j * ((stepBound 𝒢 J k : ℤ) + 1) - R * stepBound 𝒢 J k)
          (j * ((stepBound 𝒢 J k : ℤ) + 1) + stepBound 𝒢 J k + R * stepBound 𝒢 J k) := by
      intro n hn
      obtain ⟨h1, h2⟩ := mem_blockOf_bounds hn
      exact suppIcc_altOp 𝒢 q 𝔉 k ζ R (suppIcc_mono (suppIcc_physUnit n) h1 h2)
    have hgram := gsq_sum_smul_le (blockOf (stepBound 𝒢 J k) I j) fn hsupp
    have hcoef : ∑ n ∈ blockOf (stepBound 𝒢 J k) I j, ‖fn n‖ ^ 2 ≤
        ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 := by
      calc ∑ n ∈ blockOf (stepBound 𝒢 J k) I j, ‖fn n‖ ^ 2
          ≤ ∑ _n ∈ blockOf (stepBound 𝒢 J k) I j, s ^ 2 :=
            Finset.sum_le_sum fun n hn =>
              pow_le_pow_left₀ (norm_nonneg _) (hs n (Finset.mem_filter.mp hn).1) 2
        _ = ((blockOf (stepBound 𝒢 J k) I j).card : ℝ) * s ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 :=
            mul_le_mul_of_nonneg_right
              (by exact_mod_cast card_blockOf_le (stepBound 𝒢 J k) I j) (sq_nonneg s)
    have hmom : ∑ n ∈ blockOf (stepBound 𝒢 J k) I j,
          gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ R (physUnit intPos 𝒢 J ℓ n)) =
        ∑ n ∈ I with blk (stepBound 𝒢 J k) n = j, physMoment intPos 𝒢 q 𝔉 k ζ R n :=
      Finset.sum_congr rfl fun n _ => (physMoment_eq_gsq 𝒢 q 𝔉 k ζ R n).symm
    rw [hlin]
    calc gsq intPos 𝒢 J ℓ (∑ n ∈ blockOf (stepBound 𝒢 J k) I j,
          fn n • altOp 𝒢 q 𝔉 k ζ R (physUnit intPos 𝒢 J ℓ n))
        ≤ (∑ n ∈ blockOf (stepBound 𝒢 J k) I j, ‖fn n‖ ^ 2) *
            ∑ n ∈ blockOf (stepBound 𝒢 J k) I j,
              gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ R (physUnit intPos 𝒢 J ℓ n)) := hgram
      _ = (∑ n ∈ blockOf (stepBound 𝒢 J k) I j, ‖fn n‖ ^ 2) *
            ∑ n ∈ I with blk (stepBound 𝒢 J k) n = j, physMoment intPos 𝒢 q 𝔉 k ζ R n := by
          rw [hmom]
      _ ≤ ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 *
            ∑ n ∈ I with blk (stepBound 𝒢 J k) n = j, physMoment intPos 𝒢 q 𝔉 k ζ R n :=
          mul_le_mul_of_nonneg_right hcoef
            (Finset.sum_nonneg fun n _ => physMoment_nonneg 𝒢 q 𝔉 k ζ R n)
  unfold blockMoment
  calc ∑ j ∈ I.image (blk (stepBound 𝒢 J k)),
        gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ R
          (markVec intPos 𝒢 J ℓ (blockOf (stepBound 𝒢 J k) I j) fn))
      ≤ ∑ j ∈ I.image (blk (stepBound 𝒢 J k)), ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 *
          ∑ n ∈ I with blk (stepBound 𝒢 J k) n = j, physMoment intPos 𝒢 q 𝔉 k ζ R n :=
        Finset.sum_le_sum hblock
    _ = ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 * ∑ j ∈ I.image (blk (stepBound 𝒢 J k)),
          ∑ n ∈ I with blk (stepBound 𝒢 J k) n = j, physMoment intPos 𝒢 q 𝔉 k ζ R n :=
        (Finset.mul_sum _ _ _).symm
    _ = ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 * ∑ n ∈ I, physMoment intPos 𝒢 q 𝔉 k ζ R n :=
        congrArg (fun t => ((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 * t)
          (Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem _ hn) _)

/-- **The operator part of Corollary 3.11** [S-02:1291–1335]: for every finite set `I` of integer
positions, every first endpoint `f = ∑_{n ∈ I} f_n u_n` with `|f_n| ≤ s` on `I`, every
`g ∈ ℋ_ph` and every `R ≥ 1` (written `R + 1`),

`|⟨f, 𝒜 g⟩|^{2R} ≤ (3‖g‖²)^R · ‖f‖^{2(R-1)} · (H + 1) s² ∑_{n ∈ I} ⟨u_n, (𝒜 𝒜*)^R u_n⟩`,

where `H = stepBound` bounds every displacement `|kD|`. -/
theorem pairMarkFree_pow_le (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset ℤ)
    (fn : ℤ → ℂ) {g : PState intPos 𝒢 J ℓ → ℂ} (hg : MemPhysL2 intPos 𝒢 J ℓ g) {s : ℝ}
    (hs : ∀ n ∈ I, ‖fn n‖ ≤ s) (R : ℕ) :
    (‖pairMarkFree intPos 𝒢 J ℓ I fn (physOp intPos 𝒢 q 𝔉 k ζ g)‖ ^ 2) ^ (R + 1) ≤
      (3 * physNormSq intPos 𝒢 J ℓ g) ^ (R + 1) *
        (markFreeNormSq intPos 𝒢 J ℓ I fn ^ R *
          (((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 *
            ∑ n ∈ I, physMoment intPos 𝒢 q 𝔉 k ζ (R + 1) n)) := by
  have h3G : 0 ≤ 3 * physNormSq intPos 𝒢 J ℓ g :=
    mul_nonneg (by norm_num) (physNormSq_nonneg g)
  have h1 := norm_pairMarkFree_sq_le (q := q) 𝔉 k ζ I fn hg
  rw [← blockMoment_one (q := q) 𝔉 k ζ I fn] at h1
  have hlc := logConvex_pow (a := blockMoment 𝒢 q 𝔉 k ζ I fn)
    (blockMoment_nonneg 𝔉 k ζ I fn) (blockMoment_sq_le 𝔉 k ζ I fn) R
  have hF : 0 ≤ blockMoment 𝒢 q 𝔉 k ζ I fn 0 := blockMoment_nonneg 𝔉 k ζ I fn 0
  have hR := blockMoment_le (q := q) 𝔉 k ζ I fn hs (R + 1)
  rw [blockMoment_zero (q := q) 𝔉 k ζ I fn] at hlc hF
  calc (‖pairMarkFree intPos 𝒢 J ℓ I fn (physOp intPos 𝒢 q 𝔉 k ζ g)‖ ^ 2) ^ (R + 1)
      ≤ (blockMoment 𝒢 q 𝔉 k ζ I fn 1 * (3 * physNormSq intPos 𝒢 J ℓ g)) ^ (R + 1) :=
        pow_le_pow_left₀ (sq_nonneg _) h1 _
    _ = (3 * physNormSq intPos 𝒢 J ℓ g) ^ (R + 1) * blockMoment 𝒢 q 𝔉 k ζ I fn 1 ^ (R + 1) := by
        rw [mul_pow]
        ring
    _ ≤ (3 * physNormSq intPos 𝒢 J ℓ g) ^ (R + 1) *
          (markFreeNormSq intPos 𝒢 J ℓ I fn ^ R * blockMoment 𝒢 q 𝔉 k ζ I fn (R + 1)) :=
        mul_le_mul_of_nonneg_left hlc (pow_nonneg h3G _)
    _ ≤ (3 * physNormSq intPos 𝒢 J ℓ g) ^ (R + 1) *
          (markFreeNormSq intPos 𝒢 J ℓ I fn ^ R *
            (((stepBound 𝒢 J k : ℝ) + 1) * s ^ 2 *
              ∑ n ∈ I, physMoment intPos 𝒢 q 𝔉 k ζ (R + 1) n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR (pow_nonneg hF _))
          (pow_nonneg h3G _)

end Blocks

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing
