/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Jordan.Direct
import MatDecompFormal.Instances.RationalCanonical.BlockStrategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open scoped Polynomial

/-!
# Jordan Form: Framework Entry

This file assembles the Jordan descent strategy through the project square
descent framework.  The theorem is conditional on `JordanStepOracle`;
constructing that oracle from rational canonical form or primary decomposition
is the remaining algebraic work.
-/

/-- Universe-level base case for the Jordan target. -/
theorem jordan_base_univ
    {K : Type u} [Field K] (x : SquareUniverse K) :
    ((∀ (x_sub : PosSquareUniverse K), (x_sub : SquareUniverse K) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Jordan_P x := by
  intro hx _hsplit
  have hzero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  exact base_jordan_empty x.A

/--
Block-slice witness for a positive square-universe object.

This is the sliceability payload: it depends on the actual matrix being sliced,
and therefore supports matrix-dependent block/complement types.
-/
structure JordanBlockSliceWitness
    {K : Type u} [Field K] (x_sub : PosSquareUniverse K) where
  β : Type u
  [fintype_β : Fintype β]
  [decEq_β : DecidableEq β]
  [linOrder_β : LinearOrder β]
  γ : Type u
  [fintype_γ : Fintype γ]
  [decEq_γ : DecidableEq γ]
  [linOrder_γ : LinearOrder γ]
  ready : JordanBlockStepReady K x_sub.1.ι β γ x_sub.1.A

attribute [instance] JordanBlockSliceWitness.fintype_β
attribute [instance] JordanBlockSliceWitness.decEq_β
attribute [instance] JordanBlockSliceWitness.linOrder_β
attribute [instance] JordanBlockSliceWitness.fintype_γ
attribute [instance] JordanBlockSliceWitness.decEq_γ
attribute [instance] JordanBlockSliceWitness.linOrder_γ

/-- The square-universe recursive slice selected by a block-slice witness. -/
noncomputable def JordanBlockSliceWitness.slice
    {K : Type u} [Field K] {x_sub : PosSquareUniverse K}
    (w : JordanBlockSliceWitness x_sub) :
    SquareUniverse K :=
  { ι := w.γ
    A := jordanBlockSlice w.ready.e x_sub.1.A }

/--
One dependent block-descent step for a positive square-universe object.

The transformed matrix has the same ambient index as `x_sub`; its recursive
slice may have a matrix-dependent complement type.
-/
structure JordanBlockDriverStepData
    {K : Type u} [Field K] (x_sub : PosSquareUniverse K) where
  B : Matrix x_sub.1.ι x_sub.1.ι K
  P : Matrix x_sub.1.ι x_sub.1.ι K
  invertible_P : InvertibleMatrix P
  B_eq : B = P⁻¹ * x_sub.1.A * P
  witness :
    JordanBlockSliceWitness
      (⟨SquareUniverse.ofMatrix B, by simpa using x_sub.2⟩ : PosSquareUniverse K)

/-- The transformed positive universe object produced by a block-driver step. -/
noncomputable def JordanBlockDriverStepData.target
    {K : Type u} [Field K] {x_sub : PosSquareUniverse K}
    (data : JordanBlockDriverStepData x_sub) :
    PosSquareUniverse K :=
  ⟨SquareUniverse.ofMatrix data.B, by simpa using x_sub.2⟩

/-- Block-driver oracle: every positive object has a concrete block step. -/
structure JordanBlockDriverOracle
    (K : Type u) [Field K] : Type (u + 1) where
  step : ∀ (x_sub : PosSquareUniverse K), JordanBlockDriverStepData x_sub

/-- Convert an explicit two-sided inverse into the public matrix invertibility predicate. -/
lemma invertibleMatrix_of_hasMatrixInverse
    {K : Type u} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Pinv : Matrix ι ι K}
    (hInv : HasMatrixInverse P Pinv) :
    InvertibleMatrix P := by
  exact ⟨⟨P, Pinv, hInv.2, hInv.1⟩, rfl⟩

/--
Structured companion-block bridge for the RCF-to-Jordan route.

This is the real algebraic obligation for a cyclic RCF head block: a companion
matrix for a split polynomial has Jordan form.  It is intentionally more
specific than an arbitrary Jordan step oracle.
-/
structure JordanCompanionBlockBridge
    (K : Type u) [Field K] : Type (u + 1) where
  companion_hasJordan_of_splits :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
      {C : Matrix ι ι K} {p : K[X]},
      SingleCompanionBlockForm C p →
        p.Splits (RingHom.id K) →
          HasJordanMatrix C

/--
Degree-one companion blocks are already Jordan blocks up to the one-dimensional
matrix API.  This is the leaf case for the split companion-block bridge.
-/
theorem singleCompanionBlockForm_hasJordan_of_natDegree_eq_one
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (hC : SingleCompanionBlockForm C p)
    (hdeg : p.natDegree = 1) :
    HasJordanMatrix C := by
  exact hasJordanMatrix_of_card_eq_one
    (A := C)
    (by
      rw [singleCompanionBlockForm_card_eq_natDegree hC]
      exact hdeg)

/--
Concrete split-factorization payload for a polynomial over `K`.

This records the algebraic information needed by the higher-degree companion
block bridge: a split monic polynomial is written as a finite product of powers
of distinct linear factors.
-/
structure JordanSplitPolynomialFactorization
    (K : Type u) [Field K] (p : K[X]) : Type (u + 1) where
  rootIdx : Type u
  [fintype_rootIdx : Fintype rootIdx]
  [decEq_rootIdx : DecidableEq rootIdx]
  eigenvalue : rootIdx → K
  eigenvalue_injective : Function.Injective eigenvalue
  exponent : rootIdx → Nat
  exponent_pos : ∀ r, 0 < exponent r
  factorization :
    p = ∏ r : rootIdx,
      (Polynomial.X - Polynomial.C (eigenvalue r)) ^ exponent r

attribute [instance] JordanSplitPolynomialFactorization.fintype_rootIdx
attribute [instance] JordanSplitPolynomialFactorization.decEq_rootIdx

/--
Bridge from the convenient split-polynomial hypothesis to explicit linear-power
factorization data.

This is proof infrastructure for `JordanCompanionBlockBridge`, not a public
assumption of the final Jordan theorem.
-/
structure JordanSplitPolynomialFactorizationBridge
    (K : Type u) [Field K] : Type (u + 1) where
  factorization_of_splits :
    ∀ {p : K[X]},
      p.Monic →
        0 < p.natDegree →
          p.Splits (RingHom.id K) →
            JordanSplitPolynomialFactorization K p

/--
Concrete split-polynomial factorization bridge over a field.

The root index is the finset of roots of `p`; the exponent is the root
multiplicity.  This is the user-facing split hypothesis converted into the
distinct linear-power payload needed by the companion-block bridge.
-/
noncomputable def jordanSplitPolynomialFactorizationBridge
    (K : Type u) [Field K] :
    JordanSplitPolynomialFactorizationBridge K where
  factorization_of_splits := by
    intro p hp _hpos hsplit
    classical
    refine {
      rootIdx := {a : K // a ∈ p.roots.toFinset}
      eigenvalue := fun a => a.1
      eigenvalue_injective := ?_
      exponent := fun a => p.rootMultiplicity a.1
      exponent_pos := ?_
      factorization := ?_
    }
    · intro a b h
      exact Subtype.ext h
    · intro a
      have hmemRoots : a.1 ∈ p.roots := by
        exact Multiset.mem_toFinset.mp a.2
      have hcount : 0 < p.roots.count a.1 := by
        exact Multiset.count_pos.2 hmemRoots
      simpa [Polynomial.count_roots] using hcount
    · have hroots :
          p = Polynomial.C p.leadingCoeff *
            (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod := by
        exact Polynomial.eq_prod_roots_of_splits_id hsplit
      have hmonicCoeff : Polynomial.C p.leadingCoeff = (1 : K[X]) := by
        rw [hp.leadingCoeff]
        simp
      have hrootsMonic :
          p = (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod := by
        simpa [hmonicCoeff] using hroots
      have hfinset :
          (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod =
            p.roots.toFinset.prod fun a =>
              (Polynomial.X - Polynomial.C a) ^ p.rootMultiplicity a := by
        exact Polynomial.prod_multiset_root_eq_finset_root (p := p)
      calc
        p = (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod := hrootsMonic
        _ = p.roots.toFinset.prod fun a =>
              (Polynomial.X - Polynomial.C a) ^ p.rootMultiplicity a := hfinset
        _ = ∏ r : {a : K // a ∈ p.roots.toFinset},
              (Polynomial.X - Polynomial.C r.1) ^ p.rootMultiplicity r.1 := by
          exact Finset.prod_subtype
            (s := p.roots.toFinset)
            (p := fun a => a ∈ p.roots.toFinset)
            (by intro a; rfl)
            (fun a => (Polynomial.X - Polynomial.C a) ^ p.rootMultiplicity a)

/--
Bridge from explicit split-factorization data for a companion polynomial to a
Jordan form of the companion block.

The remaining higher-degree mathematics lives here: powers of linear factors
give Jordan-chain blocks, and coprime primary factors combine by block
decomposition.
-/
structure JordanFactorizedCompanionBlockBridge
    (K : Type u) [Field K] : Type (u + 1) where
  companion_hasJordan_of_factorization :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
      {C : Matrix ι ι K} {p : K[X]},
      SingleCompanionBlockForm C p →
        JordanSplitPolynomialFactorization K p →
          HasJordanMatrix C

/--
Jordan-chain obligation for a companion block whose polynomial is a single
linear factor power.

This is the local nilpotent/Jordan-chain theorem still needed inside the
higher-degree companion-block proof.  It is kept separate from the public
Jordan theorem and from the recursive driver.
-/
structure JordanLinearPowerCompanionBlockBridge
    (K : Type u) [Field K] : Type (u + 1) where
  companion_hasJordan_of_linear_power :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
      {C : Matrix ι ι K} (lam : K) (n : Nat),
      0 < n →
        SingleCompanionBlockForm C
          ((Polynomial.X - Polynomial.C lam) ^ n) →
          HasJordanMatrix C

/--
The chain-basis change matrix for the companion block of `(X - C lam)^n`.

Column `j` records the coefficients in the power basis of
`(X - C lam)^(n - 1 - j)`.  The explicit low-dimensional matrices below are
instances of this binomial formula.
-/
def linearPowerCompanionChange
    {K : Type u} [Field K] (lam : K) (n : Nat) :
    Matrix (Fin n) (Fin n) K :=
  fun i j =>
    if (i : Nat) ≤ n - 1 - (j : Nat) then
      (Nat.choose (n - 1 - (j : Nat)) (i : Nat) : K) *
        (-lam) ^ (n - 1 - (j : Nat) - (i : Nat))
    else
      0

/--
The inverse chain-basis change matrix for `(X - C lam)^n`.

This is the inverse binomial transform to `linearPowerCompanionChange`; row `r`
extracts the coefficient of `(X - C lam)^(n - 1 - r)` from a power-basis vector.
-/
def linearPowerCompanionChangeInv
    {K : Type u} [Field K] (lam : K) (n : Nat) :
    Matrix (Fin n) (Fin n) K :=
  fun r c =>
    if n - 1 - (r : Nat) ≤ (c : Nat) then
      (Nat.choose (c : Nat) (n - 1 - (r : Nat)) : K) *
        lam ^ ((c : Nat) - (n - 1 - (r : Nat)))
    else
      0

/--
The entries of `linearPowerCompanionChange` are coefficients of the chain
polynomials `(X - C lam)^(n - 1 - j)` in the power basis.
-/
theorem linearPowerCompanionChange_eq_coeff_X_sub_C_pow
    {K : Type u} [Field K] (lam : K) {n : Nat} (i j : Fin n) :
    linearPowerCompanionChange lam n i j =
      (((Polynomial.X - Polynomial.C lam) ^
        (n - 1 - (j : Nat)) : K[X]).coeff (i : Nat)) := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
  by_cases h : (i : Nat) ≤ n - 1 - (j : Nat)
  · simp [linearPowerCompanionChange, h]
    ring
  · have hlt : n - 1 - (j : Nat) < (i : Nat) := Nat.lt_of_not_ge h
    simp [linearPowerCompanionChange, h, Nat.choose_eq_zero_of_lt hlt]

/--
The entries of `linearPowerCompanionChangeInv` are coefficients of
`X^c = ((X - C lam) + C lam)^c` in the shifted chain basis.
-/
theorem linearPowerCompanionChangeInv_eq_coeff_X_add_C_pow
    {K : Type u} [Field K] (lam : K) {n : Nat} (r c : Fin n) :
    linearPowerCompanionChangeInv lam n r c =
      (((Polynomial.X + Polynomial.C lam) ^ (c : Nat) : K[X]).coeff
        (n - 1 - (r : Nat))) := by
  rw [Polynomial.coeff_X_add_C_pow]
  by_cases h : n - 1 - (r : Nat) ≤ (c : Nat)
  · simp [linearPowerCompanionChangeInv, h]
    ring
  · have hlt : (c : Nat) < n - 1 - (r : Nat) := Nat.lt_of_not_ge h
    simp [linearPowerCompanionChangeInv, h, Nat.choose_eq_zero_of_lt hlt]

/--
Translating the chain polynomial `(X - C lam)^k` by `X + C lam` recovers the
ordinary monomial `X^k`.
-/
theorem linearPowerCompanion_chain_comp_X_add_C
    {K : Type u} [Field K] (lam : K) (k : Nat) :
    (((Polynomial.X - Polynomial.C lam) ^ k : K[X]).comp
      (Polynomial.X + Polynomial.C lam)) = Polynomial.X ^ k := by
  rw [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  simp

/--
Coefficient form of `linearPowerCompanion_chain_comp_X_add_C`.
-/
theorem linearPowerCompanion_chain_comp_X_add_C_coeff
    {K : Type u} [Field K] (lam : K) (k m : Nat) :
    ((((Polynomial.X - Polynomial.C lam) ^ k : K[X]).comp
      (Polynomial.X + Polynomial.C lam)).coeff m) =
      if m = k then 1 else 0 := by
  rw [linearPowerCompanion_chain_comp_X_add_C]
  exact Polynomial.coeff_X_pow k m

/-- Entries above the chain-basis support of `linearPowerCompanionChange` vanish. -/
theorem linearPowerCompanionChange_eq_zero_of_lt
    {K : Type u} [Field K] (lam : K) {n : Nat} (i j : Fin n)
    (h : n - 1 - (j : Nat) < (i : Nat)) :
    linearPowerCompanionChange lam n i j = 0 := by
  simp [linearPowerCompanionChange, Nat.not_le_of_gt h]

/-- Entries below the support of the inverse binomial change matrix vanish. -/
theorem linearPowerCompanionChangeInv_eq_zero_of_lt
    {K : Type u} [Field K] (lam : K) {n : Nat} (r c : Fin n)
    (h : (c : Nat) < n - 1 - (r : Nat)) :
    linearPowerCompanionChangeInv lam n r c = 0 := by
  simp [linearPowerCompanionChangeInv, Nat.not_le_of_gt h]

/--
The anti-diagonal entries of the chain-basis change matrix are `1`.

The row `n - 1 - j` is represented by an arbitrary `Fin n` value `i`; this
form avoids constructing a dependent `Fin` term from subtraction.
-/
theorem linearPowerCompanionChange_antidiagonal
    {K : Type u} [Field K] (lam : K) {n : Nat} (i j : Fin n)
    (hij : (i : Nat) = n - 1 - (j : Nat)) :
    linearPowerCompanionChange lam n i j = 1 := by
  simp [linearPowerCompanionChange, hij]

/--
The anti-diagonal entries of the inverse binomial change matrix are `1`.
-/
theorem linearPowerCompanionChangeInv_antidiagonal
    {K : Type u} [Field K] (lam : K) {n : Nat} (r c : Fin n)
    (hrc : (c : Nat) = n - 1 - (r : Nat)) :
    linearPowerCompanionChangeInv lam n r c = 1 := by
  simp [linearPowerCompanionChangeInv, hrc]

/--
The exponent-one linear-power companion case is the already-proved
one-dimensional companion leaf.
-/
theorem companion_hasJordan_of_linear_power_one
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} (lam : K)
    (hC : SingleCompanionBlockForm C
      ((Polynomial.X - Polynomial.C lam) ^ (1 : Nat))) :
    HasJordanMatrix C := by
  exact singleCompanionBlockForm_hasJordan_of_natDegree_eq_one
    hC
    (by simp)

/--
A single-root split-factorization reduces the companion-block obligation to
the linear-power companion bridge.
-/
theorem companion_hasJordan_of_single_root_factorization
    {K : Type u} [Field K]
    (bridge : JordanLinearPowerCompanionBlockBridge K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (hC : SingleCompanionBlockForm C p)
    (factorization : JordanSplitPolynomialFactorization K p)
    [Unique factorization.rootIdx] :
    HasJordanMatrix C := by
  classical
  let r₀ : factorization.rootIdx := default
  let q : K[X] :=
    (Polynomial.X - Polynomial.C (factorization.eigenvalue r₀)) ^
      factorization.exponent r₀
  have hpq : p = q := by
    have hprod :
        (∏ r : factorization.rootIdx,
            (Polynomial.X - Polynomial.C (factorization.eigenvalue r)) ^
              factorization.exponent r) = q := by
      simp [q, r₀]
    exact factorization.factorization.trans hprod
  have hCq :
      SingleCompanionBlockForm C q := by
    simpa [hpq] using hC
  exact bridge.companion_hasJordan_of_linear_power
    (factorization.eigenvalue r₀)
    (factorization.exponent r₀)
    (factorization.exponent_pos r₀)
    hCq

/--
A single-root factorization with a known exponent rewrites the companion block
to the corresponding linear-power companion block.
-/
theorem singleCompanionBlockForm_of_single_root_factorization_exponent_eq
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (hC : SingleCompanionBlockForm C p)
    (factorization : JordanSplitPolynomialFactorization K p)
    [Unique factorization.rootIdx]
    {n : Nat}
    (hexp : factorization.exponent default = n) :
    SingleCompanionBlockForm C
      ((Polynomial.X - Polynomial.C (factorization.eigenvalue default)) ^ n) := by
  classical
  let r₀ : factorization.rootIdx := default
  let q : K[X] :=
    (Polynomial.X - Polynomial.C (factorization.eigenvalue r₀)) ^
      factorization.exponent r₀
  have hpq : p = q := by
    have hprod :
        (∏ r : factorization.rootIdx,
            (Polynomial.X - Polynomial.C (factorization.eigenvalue r)) ^
              factorization.exponent r) = q := by
      simp [q, r₀]
    exact factorization.factorization.trans hprod
  have hq :
      q =
        (Polynomial.X - Polynomial.C (factorization.eigenvalue default)) ^ n := by
    simp [q, r₀, hexp]
  simpa [hpq, hq] using hC

/--
A single-root factorization with exponent one is completely discharged by the
degree-one companion leaf.
-/
theorem companion_hasJordan_of_single_root_exponent_one_factorization
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (hC : SingleCompanionBlockForm C p)
    (factorization : JordanSplitPolynomialFactorization K p)
    [Unique factorization.rootIdx]
    (hexp : factorization.exponent default = 1) :
    HasJordanMatrix C := by
  classical
  let r₀ : factorization.rootIdx := default
  let q : K[X] :=
    (Polynomial.X - Polynomial.C (factorization.eigenvalue r₀)) ^
      factorization.exponent r₀
  have hpq : p = q := by
    have hprod :
        (∏ r : factorization.rootIdx,
            (Polynomial.X - Polynomial.C (factorization.eigenvalue r)) ^
              factorization.exponent r) = q := by
      simp [q, r₀]
    exact factorization.factorization.trans hprod
  have hq :
      q = (Polynomial.X - Polynomial.C (factorization.eigenvalue r₀)) ^ (1 : Nat) := by
    simp [q, r₀, hexp]
  have hCq :
      SingleCompanionBlockForm C
        ((Polynomial.X - Polynomial.C (factorization.eigenvalue r₀)) ^ (1 : Nat)) := by
    simpa [hpq, hq] using hC
  exact companion_hasJordan_of_linear_power_one
    (factorization.eigenvalue r₀)
    hCq

/--
Split companion-block bridge decomposed into a polynomial-factorization bridge
and a factorized-companion-to-Jordan bridge.
-/
structure JordanSplitCompanionBlockBridge
    (K : Type u) [Field K] : Type (u + 1) where
  factorizationBridge : JordanSplitPolynomialFactorizationBridge K
  factorizedCompanionBridge : JordanFactorizedCompanionBlockBridge K

/-- The decomposed split companion-block bridge supplies `JordanCompanionBlockBridge`. -/
noncomputable def JordanSplitCompanionBlockBridge.toCompanionBlockBridge
    {K : Type u} [Field K]
    (bridge : JordanSplitCompanionBlockBridge K) :
    JordanCompanionBlockBridge K where
  companion_hasJordan_of_splits := by
    intro ι _ _ _ C p hC hsplit
    exact bridge.factorizedCompanionBridge.companion_hasJordan_of_factorization
      hC
      (bridge.factorizationBridge.factorization_of_splits
        hC.1 hC.2.1 hsplit)

/--
Split-aware RCF bridge for the Jordan block driver.

The selected cyclic annihilator is an internal invariant-factor object.  This
bridge records the usable API needed by the recursive driver: whenever the
current recursive matrix has split characteristic polynomial, the selected
annihilator also splits, so the companion head block can be converted to a
Jordan block.
-/
structure JordanRCFSplitBlockBridge
    (K : Type u) [Field K] : Type (u + 1) where
  rcfOracle : RationalCanonicalBlockStepOracle.{u, u} K
  cyclic_annihilator_splits :
    ∀ (x_sub : PosSquareUniverse K)
      (_hsplit : x_sub.1.A.charpoly.Splits (RingHom.id K)),
      let step := rationalCanonicalBlockStep rcfOracle x_sub
      step.cyclic_annihilator.Splits (RingHom.id K)
  companionBridge : JordanCompanionBlockBridge K

/--
Sharper RCF bridge target: prove the selected cyclic annihilator divides the
current characteristic polynomial.

Together with `A.charpoly.Splits`, this mechanically yields the split condition
required by `JordanRCFSplitBlockBridge`.  This keeps the remaining RCF algebra
focused on the invariant-factor divisibility theorem.
-/
structure JordanRCFAnnihilatorDivisibilityBridge
    (K : Type u) [Field K] : Type (u + 1) where
  rcfOracle : RationalCanonicalBlockStepOracle.{u, u} K
  cyclic_annihilator_dvd_charpoly :
    ∀ (x_sub : PosSquareUniverse K),
      let step := rationalCanonicalBlockStep rcfOracle x_sub
      step.cyclic_annihilator ∣ x_sub.1.A.charpoly
  companionBridge : JordanCompanionBlockBridge K

/-- Divisibility of the selected cyclic annihilator supplies the split-aware RCF bridge. -/
noncomputable def JordanRCFAnnihilatorDivisibilityBridge.toSplitBlockBridge
    {K : Type u} [Field K]
    (bridge : JordanRCFAnnihilatorDivisibilityBridge K) :
    JordanRCFSplitBlockBridge K where
  rcfOracle := bridge.rcfOracle
  cyclic_annihilator_splits := by
    intro x_sub hsplit
    let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
    exact Polynomial.splits_of_splits_of_dvd (RingHom.id K)
      (Matrix.charpoly_monic x_sub.1.A).ne_zero
      hsplit
      (bridge.cyclic_annihilator_dvd_charpoly x_sub)
  companionBridge := bridge.companionBridge

/--
In an RCF cyclic block step, the selected head block characteristic polynomial
divides the characteristic polynomial of the current matrix.

This follows only from the block equation and similarity invariance.  The
remaining RCF/Jordan algebra is to identify the companion head characteristic
polynomial with the selected cyclic annihilator.
-/
theorem rationalCanonicalBlockStep_head_charpoly_dvd_charpoly
    {K : Type u} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, u} K)
    (x_sub : PosSquareUniverse K) :
    let step := rationalCanonicalBlockStep oracle x_sub
    step.head.charpoly ∣ x_sub.1.A.charpoly := by
  classical
  let step := rationalCanonicalBlockStep oracle x_sub
  let B : Matrix x_sub.1.ι x_sub.1.ι K := step.Pinv * x_sub.1.A * step.P
  have hInvUnit : InvertibleMatrix step.P :=
    invertibleMatrix_of_hasMatrixInverse step.inverse_P
  have hPinv : step.P⁻¹ = step.Pinv := by
    haveI : Invertible step.P := hInvUnit.invertible
    exact Matrix.inv_eq_left_inv step.inverse_P.1
  have hcharB : B.charpoly = x_sub.1.A.charpoly := by
    simpa [B, hPinv] using
      (jordan_similarity_charpoly
        (P := step.P)
        (A := x_sub.1.A)
        hInvUnit)
  have hcharReindex :
      (Matrix.reindex step.splitIndex step.splitIndex B).charpoly = B.charpoly := by
    exact Matrix.charpoly_reindex step.splitIndex B
  have hcharBlock :
      (rationalCanonicalBlockDiagLex step.head step.tail).charpoly =
        step.head.charpoly * step.tail.charpoly := by
    calc
      (rationalCanonicalBlockDiagLex step.head step.tail).charpoly =
          (Matrix.fromBlocks step.head 0 0 step.tail :
            Matrix (step.blockIdx ⊕ step.tailIdx) (step.blockIdx ⊕ step.tailIdx) K).charpoly := by
        simpa [rationalCanonicalBlockDiagLex] using
          Matrix.charpoly_reindex
            (sumToLexEquiv step.blockIdx step.tailIdx)
            (Matrix.fromBlocks step.head 0 0 step.tail :
              Matrix (step.blockIdx ⊕ step.tailIdx) (step.blockIdx ⊕ step.tailIdx) K)
      _ = step.head.charpoly * step.tail.charpoly := by
        simp
  have hprod : step.head.charpoly * step.tail.charpoly = x_sub.1.A.charpoly := by
    rw [← hcharBlock, ← step.block_eq, hcharReindex, hcharB]
  exact ⟨step.tail.charpoly, hprod.symm⟩

/--
Companion-head characteristic polynomial bridge for the RCF step.

After `rationalCanonicalBlockStep_head_charpoly_dvd_charpoly`, proving this
bridge is enough to obtain the selected-annihilator divisibility bridge.
-/
structure JordanRCFCompanionCharpolyBridge
    (K : Type u) [Field K] : Type (u + 1) where
  rcfOracle : RationalCanonicalBlockStepOracle.{u, u} K
  companion_head_charpoly :
    ∀ (x_sub : PosSquareUniverse K),
      let step := rationalCanonicalBlockStep rcfOracle x_sub
      step.head.charpoly = step.cyclic_annihilator
  companionBridge : JordanCompanionBlockBridge K

/--
The companion-head characteristic-polynomial bridge follows from the concrete
RCF block payload: the selected head is a verified single companion block for
the selected cyclic annihilator.
-/
noncomputable def JordanRCFCompanionCharpolyBridge.ofCompanionBridge
    {K : Type u} [Field K]
    (rcfOracle : RationalCanonicalBlockStepOracle.{u, u} K)
    (companionBridge : JordanCompanionBlockBridge K) :
    JordanRCFCompanionCharpolyBridge K where
  rcfOracle := rcfOracle
  companion_head_charpoly := by
    intro x_sub
    let step := rationalCanonicalBlockStep rcfOracle x_sub
    exact singleCompanionBlockForm_charpoly step.head_companion
  companionBridge := companionBridge

/-- The companion-head charpoly bridge supplies selected-annihilator divisibility. -/
noncomputable def JordanRCFCompanionCharpolyBridge.toAnnihilatorDivisibilityBridge
    {K : Type u} [Field K]
    (bridge : JordanRCFCompanionCharpolyBridge K) :
    JordanRCFAnnihilatorDivisibilityBridge K where
  rcfOracle := bridge.rcfOracle
  cyclic_annihilator_dvd_charpoly := by
    intro x_sub
    let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
    have hhead_dvd :
        step.head.charpoly ∣ x_sub.1.A.charpoly :=
      rationalCanonicalBlockStep_head_charpoly_dvd_charpoly bridge.rcfOracle x_sub
    simpa [(bridge.companion_head_charpoly x_sub).symm] using hhead_dvd
  companionBridge := bridge.companionBridge

/--
The split-dependent block-slice witness selected by an RCF cyclic block.

This is deliberately not a split-independent `JordanBlockDriverStepData`: the
head Jordan witness is obtained from the current recursive split hypothesis.
-/
noncomputable def JordanRCFSplitBlockBridge.blockSliceWitness
    {K : Type u} [Field K]
    (bridge : JordanRCFSplitBlockBridge K)
    (x_sub : PosSquareUniverse K)
    (hsplit : x_sub.1.A.charpoly.Splits (RingHom.id K)) :
    JordanBlockSliceWitness
      (⟨SquareUniverse.ofMatrix
        (rationalCanonicalBlockStepMatrix bridge.rcfOracle x_sub),
        by simpa [rationalCanonicalBlockStepMatrix] using x_sub.2⟩ :
        PosSquareUniverse K) := by
  classical
  let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
  let B : Matrix x_sub.1.ι x_sub.1.ι K := step.Pinv * x_sub.1.A * step.P
  have hHeadJordan : HasJordanMatrix step.head :=
    bridge.companionBridge.companion_hasJordan_of_splits
      step.head_companion
      (bridge.cyclic_annihilator_splits x_sub hsplit)
  have hReady :
      JordanBlockStepReady K x_sub.1.ι step.blockIdx step.tailIdx B := by
    refine {
      e := step.splitIndex
      head := step.head
      head_hasJordan := hHeadJordan
      head_nonempty := ?_
      block_eq := ?_
    }
    · exact Fintype.card_pos_iff.mp (by
        rw [step.block_card_eq]
        exact step.cyclic_blockSize_pos)
    · have hblock :
          Matrix.reindex step.splitIndex step.splitIndex B =
            jordanBlockDiagLex step.head step.tail := by
        simpa [B, rationalCanonicalBlockDiagLex, jordanBlockDiagLex] using
          step.block_eq
      have htail : jordanBlockSlice step.splitIndex B = step.tail := by
        unfold jordanBlockSlice
        rw [hblock]
        ext i j
        simp [jordanBlockDiagLex, Matrix.toBlocks₂₂, Matrix.reindex_apply]
      rw [htail]
      exact hblock
  exact {
    β := step.blockIdx
    γ := step.tailIdx
    ready := hReady
  }

/--
Split-dependent proof hooks for the RCF-backed Jordan block driver.

The slicing data remains structural, while the witness is constructed inside
the lift hook from the current matrix's split hypothesis.
-/
noncomputable def jordan_rcf_split_block_proofData
    (K : Type u) [Field K]
    (bridge : JordanRCFSplitBlockBridge K) :
    SquareProofData Jordan_P
      (rationalCanonicalBlockSliceData bridge.rcfOracle) where
  transport_sub := by
    intro x_sub y_sub hrel hPy hsplitX
    subst y_sub
    have hsplitB :
        (rationalCanonicalBlockStepMatrix bridge.rcfOracle x_sub).charpoly.Splits
          (RingHom.id K) := by
      let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
      have hchar :
          (rationalCanonicalBlockStepMatrix bridge.rcfOracle x_sub).charpoly =
            x_sub.1.A.charpoly := by
        have hInvUnit : InvertibleMatrix step.P :=
          invertibleMatrix_of_hasMatrixInverse step.inverse_P
        have hPinv : step.P⁻¹ = step.Pinv := by
          haveI : Invertible step.P := hInvUnit.invertible
          exact Matrix.inv_eq_left_inv step.inverse_P.1
        simpa [rationalCanonicalBlockStepMatrix, hPinv] using
          (jordan_similarity_charpoly
            (P := step.P)
            (A := x_sub.1.A)
            hInvUnit)
      simpa [hchar] using hsplitX
    have hJordanB :
        HasJordanMatrix (rationalCanonicalBlockStepMatrix bridge.rcfOracle x_sub) :=
      hPy hsplitB
    let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
    have hInvUnit : InvertibleMatrix step.P :=
      invertibleMatrix_of_hasMatrixInverse step.inverse_P
    have hPinv : step.P⁻¹ = step.Pinv := by
      haveI : Invertible step.P := hInvUnit.invertible
      exact Matrix.inv_eq_left_inv step.inverse_P.1
    exact jordan_transport_similarity
      hInvUnit
      (by simp [rationalCanonicalBlockStepMatrix, step, hPinv])
      hJordanB
  lift_from_slice_sub := by
    intro y_sub _ hSlice hsplitY
    let step := rationalCanonicalBlockStep bridge.rcfOracle y_sub
    let B : Matrix y_sub.1.ι y_sub.1.ι K := step.Pinv * y_sub.1.A * step.P
    have hHeadJordan : HasJordanMatrix step.head :=
      bridge.companionBridge.companion_hasJordan_of_splits
        step.head_companion
        (bridge.cyclic_annihilator_splits y_sub hsplitY)
    let hReady :
        JordanBlockStepReady K y_sub.1.ι step.blockIdx step.tailIdx B := {
      e := step.splitIndex
      head := step.head
      head_hasJordan := hHeadJordan
      head_nonempty := Fintype.card_pos_iff.mp (by
        rw [step.block_card_eq]
        exact step.cyclic_blockSize_pos)
      block_eq := by
        have hblock :
            Matrix.reindex step.splitIndex step.splitIndex B =
              jordanBlockDiagLex step.head step.tail := by
          simpa [B, rationalCanonicalBlockDiagLex, jordanBlockDiagLex] using
            step.block_eq
        have htail : jordanBlockSlice step.splitIndex B = step.tail := by
          unfold jordanBlockSlice
          rw [hblock]
          ext i j
          simp [jordanBlockDiagLex, Matrix.toBlocks₂₂, Matrix.reindex_apply]
        rw [htail]
        exact hblock
    }
    have hTail' :
        (jordanBlockSlice hReady.e B).charpoly.Splits (RingHom.id K) →
          HasJordanMatrix (jordanBlockSlice hReady.e B) := by
      intro hsplitTail
      change
        HasJordanMatrix (jordanBlockSlice step.splitIndex B)
      change
        (jordanBlockSlice step.splitIndex B).charpoly.Splits (RingHom.id K)
        at hsplitTail
      have htail : jordanBlockSlice hReady.e B = step.tail := by
        change jordanBlockSlice step.splitIndex B = step.tail
        unfold jordanBlockSlice
        have hblock :
            Matrix.reindex step.splitIndex step.splitIndex B =
              jordanBlockDiagLex step.head step.tail := by
          simpa [B, rationalCanonicalBlockDiagLex, jordanBlockDiagLex] using
            step.block_eq
        rw [hblock]
        ext i j
        simp [jordanBlockDiagLex, Matrix.toBlocks₂₂, Matrix.reindex_apply]
      have hsplitTail' : step.tail.charpoly.Splits (RingHom.id K) := by
        rwa [htail] at hsplitTail
      have hTailJordan : HasJordanMatrix step.tail := by
        exact hSlice hsplitTail'
      rwa [htail]
    have hInvUnit : InvertibleMatrix step.P :=
      invertibleMatrix_of_hasMatrixInverse step.inverse_P
    have hPinv : step.P⁻¹ = step.Pinv := by
      haveI : Invertible step.P := hInvUnit.invertible
      exact Matrix.inv_eq_left_inv step.inverse_P.1
    have hsplitB : B.charpoly.Splits (RingHom.id K) := by
      have hchar : B.charpoly = y_sub.1.A.charpoly := by
        simpa [B, hPinv] using
          (jordan_similarity_charpoly
            (P := step.P)
            (A := y_sub.1.A)
            hInvUnit)
      simpa [hchar] using hsplitY
    have hJordanB : HasJordanMatrix B :=
      jordanLiftReady_of_blockStepReady hReady hTail' hsplitB
    exact jordan_transport_similarity
      hInvUnit
      (by simp [B, hPinv])
      hJordanB

/-- RCF-backed split block Jordan induction instance. -/
noncomputable def jordan_rcf_split_block_framework_inst
    (K : Type u) [Field K]
    (bridge : JordanRCFSplitBlockBridge K) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstance
    Jordan_P
    jordan_base_univ
    (rationalCanonicalBlockSliceData bridge.rcfOracle)
    (rationalCanonicalBlockReach bridge.rcfOracle)
    (jordan_rcf_split_block_proofData K bridge)

/--
Framework-routed Jordan theorem from a split-aware RCF block bridge.

This is still conditional on the two algebraic bridge obligations recorded in
`JordanRCFSplitBlockBridge`, but the recursion itself is fully routed through
the dependent block subtype-descent template.
-/
theorem exists_jordan_matrix_framework_rcf_split_bridge
    {K : Type u} [Field K]
    (bridge : JordanRCFSplitBlockBridge K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  have hP :
      (jordan_rcf_split_block_framework_inst K bridge).P
        (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := jordan_rcf_split_block_framework_inst K bridge) A
  exact hP hsplit

/--
Framework-routed Jordan theorem from an RCF annihilator-divisibility bridge.

This is the preferred conditional RCF API: the remaining RCF-side obligation is
the invariant-factor divisibility theorem
`step.cyclic_annihilator ∣ A.charpoly`; splitness is then derived automatically
from the public `A.charpoly.Splits` hypothesis.
-/
theorem exists_jordan_matrix_framework_rcf_divisibility_bridge
    {K : Type u} [Field K]
    (bridge : JordanRCFAnnihilatorDivisibilityBridge K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A :=
  exists_jordan_matrix_framework_rcf_split_bridge
    bridge.toSplitBlockBridge A hsplit

/--
Framework-routed Jordan theorem from an RCF companion-head charpoly bridge.

The companion-head charpoly equality is now a concrete consequence of
`SingleCompanionBlockForm`; the remaining algebraic input is the companion block
Jordan bridge itself.
-/
theorem exists_jordan_matrix_framework_rcf_companion_charpoly_bridge
    {K : Type u} [Field K]
    (bridge : JordanRCFCompanionCharpolyBridge K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A :=
  exists_jordan_matrix_framework_rcf_divisibility_bridge
    bridge.toAnnihilatorDivisibilityBridge A hsplit

/--
Framework-routed Jordan theorem from a concrete RCF oracle and the companion
block Jordan bridge.  This discharges the companion-head characteristic
polynomial part of the RCF route internally.
-/
theorem exists_jordan_matrix_framework_rcf_companion_bridge
    {K : Type u} [Field K]
    (rcfOracle : RationalCanonicalBlockStepOracle.{u, u} K)
    (companionBridge : JordanCompanionBlockBridge K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A :=
  exists_jordan_matrix_framework_rcf_companion_charpoly_bridge
    (JordanRCFCompanionCharpolyBridge.ofCompanionBridge
      rcfOracle companionBridge)
    A hsplit

/-- Slice data for the dependent Jordan block driver. -/
noncomputable def jordan_block_sliceData
    (K : Type u) [Field K] :
    SquareSliceData K where
  r_sub := fun y_sub x_sub =>
    ∃ data : JordanBlockDriverStepData x_sub, y_sub = data.target
  IsSliceable_sub := fun y_sub =>
    Nonempty (JordanBlockSliceWitness y_sub)
  slice_sub := fun _y_sub hy =>
    let w := Classical.choice hy
    w.slice

/-- Reachability for the dependent Jordan block driver. -/
noncomputable def jordan_block_reach
    (K : Type u) [Field K]
    (oracle : JordanBlockDriverOracle K) :
    ∀ (x_sub : PosSquareUniverse K),
      squareSubtypeμ (x_sub : SquareUniverse K) > squareSubtypeμBase →
        SquareReachType (jordan_block_sliceData K) x_sub := by
  intro x_sub _hgt
  let data := oracle.step x_sub
  let y_sub : PosSquareUniverse K := data.target
  have hySlice : (jordan_block_sliceData K).IsSliceable_sub y_sub := by
    exact ⟨data.witness⟩
  refine ⟨y_sub, hySlice, ?_, ?_⟩
  · refine ⟨data, ?_⟩
    rfl
  · change Fintype.card (Classical.choice hySlice).γ < Fintype.card x_sub.1.ι
    have hready :
        Fintype.card (Classical.choice hySlice).γ <
          Fintype.card y_sub.1.ι :=
      jordan_block_slice_card_lt (Classical.choice hySlice).ready
    simpa [y_sub, JordanBlockDriverStepData.target] using hready

/-- Proof hooks for the dependent Jordan block driver. -/
noncomputable def jordan_block_proofData
    (K : Type u) [Field K] :
    SquareProofData Jordan_P (jordan_block_sliceData K) where
  transport_sub := by
    intro x_sub y_sub hrel hPy hsplitX
    rcases hrel with ⟨data, hy⟩
    have hsplitB :
        data.B.charpoly.Splits (RingHom.id K) := by
      have hchar : data.B.charpoly = x_sub.1.A.charpoly := by
        rw [data.B_eq]
        exact jordan_similarity_charpoly data.invertible_P
      simpa [hchar] using hsplitX
    have hJordanB : HasJordanMatrix data.B := by
      have hPy' : Jordan_P (SquareUniverse.ofMatrix data.B) := by
        simpa [hy, JordanBlockDriverStepData.target] using hPy
      exact hPy' hsplitB
    exact jordan_transport_similarity data.invertible_P data.B_eq hJordanB
  lift_from_slice_sub := by
    intro y_sub hy hSlice hsplitY
    let w := Classical.choice hy
    have hTail :
        w.slice.A.charpoly.Splits (RingHom.id K) →
          HasJordanMatrix w.slice.A := hSlice
    exact jordanLiftReady_of_blockStepReady w.ready hTail hsplitY

/-- Dependent block-driver Jordan induction instance. -/
noncomputable def jordan_block_framework_inst
    (K : Type u) [Field K]
    (oracle : JordanBlockDriverOracle K) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstance
    Jordan_P
    jordan_base_univ
    (jordan_block_sliceData K)
    (jordan_block_reach K oracle)
    (jordan_block_proofData K)

noncomputable def jordan_strategy_data
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareStrategyData K Jordan_P :=
  mkSquareStrategyData
    (jordan_strategy_core K oracle)
    (jordan_strategy_proof K oracle)

noncomputable def jordan_framework_inst
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstanceFromStrategy
    Jordan_P
    jordan_base_univ
    (jordan_strategy_data K oracle)

/--
Framework-routed Jordan theorem, conditional on the one-step Jordan oracle.
-/
theorem exists_jordan_matrix_framework
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  have hP :
      (jordan_framework_inst K oracle).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := jordan_framework_inst K oracle) A
  exact hP hsplit

/--
Framework-routed Jordan theorem, conditional on the concrete one-step oracle.
The public unsuffixed split theorem is provided in `SplitSpecialization`.
-/
theorem exists_jordan_matrix_framework_oracle
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  exact exists_jordan_matrix_framework oracle A hsplit

/--
Framework-routed Jordan theorem, conditional on structured head-tail block
data.  This is the preferred conditional API while the one-step algebra is
being discharged: it exposes concrete block readiness and converts it to the
framework oracle internally.
-/
theorem exists_jordan_matrix_framework_structured_oracle
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStructuredStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  exact exists_jordan_matrix_framework
    (fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      (oracle (κ := κ)).toStepOracle)
    A hsplit

/--
Framework-routed Jordan theorem through the dependent block driver.  This is
the block-step analogue of `exists_jordan_matrix_framework_oracle`; it still
keeps the oracle explicit, but its oracle payload is concrete block-removal
data and the proof is assembled by `mkSquareSubtypeInductionInstance`.
-/
theorem exists_jordan_matrix_framework_block_oracle
    {K : Type u} [Field K]
    (oracle : JordanBlockDriverOracle K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  have hP :
      (jordan_block_framework_inst K oracle).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := jordan_block_framework_inst K oracle) A
  exact hP hsplit

end MatDecompFormal.Instances
