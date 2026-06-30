/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.RationalCanonical.Existence
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

universe u v

namespace MatDecompFormal.Instances

open Matrix
open Polynomial
open MatDecompFormal.Framework
open scoped Polynomial

/-!
# Rational Canonical Form: `K[X]` Module Bridge

This file names the remaining algebraic bridge from the finitely generated
torsion `K[X]`-module structure theorem to the one-step descent oracle consumed
by the square framework.

The descent theorem below is not a new proof path: it obtains the project
`RationalCanonicalStepOracle` from a module-structure bridge and then uses
`exists_rational_canonical_matrix_framework`, so the public route remains the
same square descent template.
-/

/--
The canonical `K[X]`-module attached to a matrix `A`: the underlying `K`-space
is `ι → K`, and `X` acts by `Matrix.toLin' A`.
-/
abbrev RationalCanonicalMatrixPolynomialModule
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : Type _ :=
  Module.AEval' (Matrix.toLin' A)

/--
Concrete module-theoretic source data for the rational-canonical bridge.

The important content is that the canonical `K[X]`-module associated to a
finite matrix is finite and torsion.  Torsion is supplied by Cayley-Hamilton:
the characteristic polynomial of `Matrix.toLin' A` annihilates every vector.
-/
structure RationalCanonicalPolynomialModuleData
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) where
  finite_over_KX :
    Module.Finite K[X] (RationalCanonicalMatrixPolynomialModule K ι A)
  torsion_over_KX :
    Module.IsTorsion K[X] (RationalCanonicalMatrixPolynomialModule K ι A)

/-- The canonical `K[X]`-module attached to a finite matrix is finite. -/
instance rationalCanonicalMatrixPolynomialModule_finite
    {K : Type v} {ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    Module.Finite K[X] (RationalCanonicalMatrixPolynomialModule K ι A) :=
  inferInstance

/--
If the matrix index type is nonempty, the canonical `K[X]`-module is nontrivial.
The proof only transports the nontriviality of the underlying `K`-space
`ι → K` across `Module.AEval'.of`, so it stays over bare `[Field K]`.
-/
theorem rationalCanonicalMatrixPolynomialModule_nontrivial_of_nonempty
    {K : Type v} {ι : Type u} [Field K] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι K) :
    Nontrivial (RationalCanonicalMatrixPolynomialModule K ι A) := by
  classical
  let e := Module.AEval'.of (Matrix.toLin' A)
  have hsrc : Nontrivial (ι → K) := inferInstance
  exact e.injective.nontrivial

/--
The canonical `K[X]`-module attached to a matrix is torsion, by
Cayley-Hamilton.
-/
theorem rationalCanonicalMatrixPolynomialModule_torsion
    {K : Type v} {ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    Module.IsTorsion K[X] (RationalCanonicalMatrixPolynomialModule K ι A) := by
  intro x
  let p : K[X] := (Matrix.toLin' A).charpoly
  have hp_nzd : p ∈ nonZeroDivisors K[X] :=
    (LinearMap.charpoly_monic (Matrix.toLin' A)).mem_nonZeroDivisors
  refine ⟨⟨p, hp_nzd⟩, ?_⟩
  have hpzero : p • x = 0 := by
    apply (Module.AEval'.of (Matrix.toLin' A)).symm.injective
    rw [Module.AEval.of_symm_smul]
    have hEnd : aeval (Matrix.toLin' A) p = 0 := by
      simpa [p] using LinearMap.aeval_self_charpoly (Matrix.toLin' A)
    simpa [hEnd]
  simp [p] at hpzero ⊢
  exact hpzero

/-- Package the finite torsion `K[X]`-module source data for a matrix. -/
def rationalCanonicalPolynomialModuleData
    {K : Type v} {ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    RationalCanonicalPolynomialModuleData K ι A where
  finite_over_KX := rationalCanonicalMatrixPolynomialModule_finite A
  torsion_over_KX := rationalCanonicalMatrixPolynomialModule_torsion A

/-- Associated elements remain associated after taking the same power. -/
theorem associated_pow
    {R : Type v} [CommMonoid R] {a b : R} (h : Associated a b) :
    ∀ n : Nat, Associated (a ^ n) (b ^ n)
  | 0 => by simpa using Associated.refl (1 : R)
  | Nat.succ n => by
      have h₁ : Associated (a ^ n * a) (b ^ n * a) :=
        Associated.mul_right (associated_pow h n) a
      have h₂ : Associated (b ^ n * a) (b ^ n * b) :=
        Associated.mul_left (b ^ n) h
      simpa [pow_succ] using h₁.trans h₂

/--
Associated generators give linearly equivalent quotients by their principal
power spans.
-/
theorem quotient_span_singleton_pow_equiv_of_associated
    {R : Type v} [CommRing R] {a b : R} (h : Associated a b) (n : Nat) :
    Nonempty <|
      (R ⧸ Submodule.span R {b ^ n}) ≃ₗ[R]
        (R ⧸ Submodule.span R {a ^ n}) := by
  classical
  have hpow : Associated (a ^ n) (b ^ n) := associated_pow h n
  have hspan : Submodule.span R {b ^ n} = Submodule.span R {a ^ n} := by
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_span_singleton] at hx ⊢
      rcases hx with ⟨c, rfl⟩
      have hdvd : a ^ n ∣ c * b ^ n :=
        (Associated.dvd_iff_dvd_left hpow).mpr
          ⟨c, by simp [mul_comm]⟩
      rcases hdvd with ⟨d, hd⟩
      exact ⟨d, by simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hd.symm⟩
    · intro hx
      rw [Submodule.mem_span_singleton] at hx ⊢
      rcases hx with ⟨c, rfl⟩
      have hdvd : b ^ n ∣ c * a ^ n :=
        (Associated.dvd_iff_dvd_left hpow.symm).mpr
          ⟨c, by simp [mul_comm]⟩
      rcases hdvd with ⟨d, hd⟩
      exact ⟨d, by simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hd.symm⟩
  exact ⟨Submodule.quotEquivOfEq _ _ hspan⟩

/--
As a `K`-vector space, the quotient `K[X] ⧸ (p)` is definitionally the
`AdjoinRoot p` model used for companion-block power bases.
-/
noncomputable def quotient_span_singleton_equiv_adjoinRoot_restrictScalars
    {K : Type v} [Field K] (p : K[X]) :
    (K[X] ⧸ K[X] ∙ p) ≃ₗ[K] AdjoinRoot p :=
  LinearEquiv.refl K _

/--
Under the standard `K`-linear identification `K[X] ⧸ (p) ≃ AdjoinRoot p`, the
`K[X]` action of `X` becomes multiplication by the adjoined root.
-/
theorem quotient_span_singleton_equiv_adjoinRoot_restrictScalars_X_smul
    {K : Type v} [Field K] (p : K[X])
    (x : K[X] ⧸ K[X] ∙ p) :
    quotient_span_singleton_equiv_adjoinRoot_restrictScalars p ((Polynomial.X : K[X]) • x) =
      AdjoinRoot.root p * quotient_span_singleton_equiv_adjoinRoot_restrictScalars p x := by
  classical
  refine Submodule.Quotient.induction_on _ x ?_
  intro q
  change AdjoinRoot.mk p ((Polynomial.X : K[X]) * q) =
    AdjoinRoot.root p * AdjoinRoot.mk p q
  rw [← AdjoinRoot.mk_X]
  rfl

/-- Equal polynomials give the same `AdjoinRoot` model as a `K`-vector space. -/
noncomputable def adjoinRootLinearEquivOfEq
    {K : Type v} [Field K] {p q : K[X]} (h : p = q) :
    AdjoinRoot p ≃ₗ[K] AdjoinRoot q := by
  subst h
  exact LinearEquiv.refl K _

/--
The equality transport between `AdjoinRoot` models preserves multiplication by
the adjoined root.
-/
theorem adjoinRootLinearEquivOfEq_root_mul
    {K : Type v} [Field K] {p q : K[X]} (h : p = q)
    (x : AdjoinRoot p) :
    adjoinRootLinearEquivOfEq h (AdjoinRoot.root p * x) =
      AdjoinRoot.root q * adjoinRootLinearEquivOfEq h x := by
  subst h
  rfl

/--
Concrete PID decomposition of the canonical `K[X]`-module attached to a matrix.

The index type, irreducible factors, exponents, and linear equivalence are the
data supplied by `Module.equiv_directSum_of_isTorsion`.  This is still module
data, not a direct matrix proof; later bridge layers must turn one cyclic
summand at a time into the one-index head-tail descent step.
-/
structure RationalCanonicalPolynomialModuleDecompositionData
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) where
  idx : Type v
  fintype_idx : Fintype idx
  prime : idx → K[X]
  prime_irreducible : ∀ i, Irreducible (prime i)
  exponent : idx → Nat
  decomposition :
    Nonempty <|
      RationalCanonicalMatrixPolynomialModule K ι A ≃ₗ[K[X]]
        DirectSum idx (fun i => K[X] ⧸ K[X] ∙ prime i ^ exponent i)

/--
Selected effective cyclic summand from the PID decomposition.

The PID theorem may present summands with an exponent field that is not yet
filtered for recursive descent.  This structure records the specific summand
to remove in the next block step, together with the positivity facts needed for
a genuine companion block.
-/
structure RationalCanonicalSelectedCyclicSummand
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) where
  selected : decomposition.idx
  exponent_pos : 0 < decomposition.exponent selected
  cyclic_factor : K[X]
  cyclic_factor_monic : cyclic_factor.Monic
  cyclic_factor_associated :
    Associated cyclic_factor (decomposition.prime selected)
  annihilator : K[X]
  annihilator_eq :
    annihilator = cyclic_factor ^ decomposition.exponent selected
  annihilator_monic : annihilator.Monic
  annihilator_natDegree_pos : 0 < annihilator.natDegree
  quotient_equiv :
    Nonempty <|
      (K[X] ⧸ K[X] ∙ decomposition.prime selected ^ decomposition.exponent selected) ≃ₗ[K[X]]
        (K[X] ⧸ K[X] ∙ cyclic_factor ^ decomposition.exponent selected)

/--
The raw selected PID quotient is `K`-linearly equivalent to the `AdjoinRoot`
model of the normalized selected cyclic factor power.
-/
noncomputable def RationalCanonicalSelectedCyclicSummand.quotientEquivCyclicFactorAdjoinRoot
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    (K[X] ⧸
        K[X] ∙ decomposition.prime selected.selected ^
          decomposition.exponent selected.selected)
      ≃ₗ[K]
        AdjoinRoot
          (selected.cyclic_factor ^ decomposition.exponent selected.selected) := by
  classical
  let eK :
      (K[X] ⧸
          K[X] ∙ decomposition.prime selected.selected ^
            decomposition.exponent selected.selected)
        ≃ₗ[K]
          (K[X] ⧸
            K[X] ∙ selected.cyclic_factor ^
              decomposition.exponent selected.selected) :=
    (Classical.choice selected.quotient_equiv).restrictScalars K
  exact eK.trans
    (quotient_span_singleton_equiv_adjoinRoot_restrictScalars
      (selected.cyclic_factor ^ decomposition.exponent selected.selected))

/--
The raw selected PID quotient is `K`-linearly equivalent to the `AdjoinRoot`
model of the selected monic annihilator.
-/
noncomputable def RationalCanonicalSelectedCyclicSummand.quotientEquivAdjoinRoot
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    (K[X] ⧸
        K[X] ∙ decomposition.prime selected.selected ^
          decomposition.exponent selected.selected)
      ≃ₗ[K] AdjoinRoot selected.annihilator :=
  selected.quotientEquivCyclicFactorAdjoinRoot.trans
    (adjoinRootLinearEquivOfEq selected.annihilator_eq.symm)

/--
The selected quotient-to-normalized-`AdjoinRoot` identification sends the
`K[X]` action of `X` to multiplication by the normalized adjoined root.
-/
theorem RationalCanonicalSelectedCyclicSummand.quotientEquivCyclicFactorAdjoinRoot_X_smul
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (x :
      K[X] ⧸
        K[X] ∙ decomposition.prime selected.selected ^
          decomposition.exponent selected.selected) :
    selected.quotientEquivCyclicFactorAdjoinRoot ((Polynomial.X : K[X]) • x) =
      AdjoinRoot.root
          (selected.cyclic_factor ^ decomposition.exponent selected.selected) *
        selected.quotientEquivCyclicFactorAdjoinRoot x := by
  classical
  let eKX :=
    Classical.choice selected.quotient_equiv
  let p : K[X] :=
    selected.cyclic_factor ^ decomposition.exponent selected.selected
  have he :
      eKX ((Polynomial.X : K[X]) • x) =
        (Polynomial.X : K[X]) • eKX x := by
    simpa using eKX.map_smul (Polynomial.X : K[X]) x
  have hp :
      quotient_span_singleton_equiv_adjoinRoot_restrictScalars p
          ((Polynomial.X : K[X]) • (eKX x)) =
        AdjoinRoot.root p *
          quotient_span_singleton_equiv_adjoinRoot_restrictScalars p (eKX x) :=
    quotient_span_singleton_equiv_adjoinRoot_restrictScalars_X_smul p (eKX x)
  simpa [RationalCanonicalSelectedCyclicSummand.quotientEquivCyclicFactorAdjoinRoot,
    p, eKX, he] using hp

/--
The selected quotient-to-`AdjoinRoot` identification sends the `K[X]` action of
`X` to multiplication by the selected adjoined root.
-/
theorem RationalCanonicalSelectedCyclicSummand.quotientEquivAdjoinRoot_X_smul
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (x :
      K[X] ⧸
        K[X] ∙ decomposition.prime selected.selected ^
          decomposition.exponent selected.selected) :
    selected.quotientEquivAdjoinRoot ((Polynomial.X : K[X]) • x) =
      AdjoinRoot.root selected.annihilator *
        selected.quotientEquivAdjoinRoot x := by
  classical
  let p : K[X] :=
    selected.cyclic_factor ^ decomposition.exponent selected.selected
  let e := selected.quotientEquivCyclicFactorAdjoinRoot
  have hcyc :
      e ((Polynomial.X : K[X]) • x) =
        AdjoinRoot.root p * e x := by
    simpa [e, p] using
      selected.quotientEquivCyclicFactorAdjoinRoot_X_smul x
  have hroot :=
    adjoinRootLinearEquivOfEq_root_mul selected.annihilator_eq.symm (e x)
  change
    adjoinRootLinearEquivOfEq selected.annihilator_eq.symm (e ((Polynomial.X : K[X]) • x)) =
      AdjoinRoot.root selected.annihilator *
        adjoinRootLinearEquivOfEq selected.annihilator_eq.symm (e x)
  rw [hcyc]
  exact hroot

/--
Named obligation for selecting the next nontrivial cyclic summand from the PID
decomposition of a nonzero matrix module.
-/
structure RationalCanonicalSelectedCyclicSummandBridge
    (K : Type v) [Field K] : Type (max (u + 1) (v + 1)) where
  select :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) →
            RationalCanonicalSelectedCyclicSummand K ι A decomposition

/--
Purely combinatorial choice of an effective summand from the PID decomposition.
Once such an index and positive exponent are known, the monic selected summand
payload is constructed by `rationalCanonicalSelectedCyclicSummandOfIndex`.
-/
structure RationalCanonicalEffectiveSummandIndex
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) where
  selected : decomposition.idx
  exponent_pos : 0 < decomposition.exponent selected

/-- Named obligation for choosing only the effective PID summand index. -/
structure RationalCanonicalEffectiveSummandIndexBridge
    (K : Type v) [Field K] : Type (max (u + 1) (v + 1)) where
  choose :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) →
            RationalCanonicalEffectiveSummandIndex K ι A decomposition

/-- Quotienting a ring by the principal submodule generated by `1` is subsingleton. -/
theorem subsingleton_quotient_span_one
    (R : Type v) [CommRing R] :
    Subsingleton (R ⧸ R ∙ (1 : R)) := by
  refine ⟨?_⟩
  intro x y
  refine Submodule.Quotient.induction_on _ x ?_
  intro x'
  refine Submodule.Quotient.induction_on _ y ?_
  intro y'
  apply (Submodule.Quotient.eq (R ∙ (1 : R))).mpr
  rw [Submodule.mem_span_singleton]
  exact ⟨x' - y', by simp⟩

/--
If all PID exponents are zero, every cyclic quotient in the decomposition is
subsingleton.
-/
theorem rationalCanonicalDecomposition_quotient_subsingleton_of_all_exponents_zero
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A)
    (hall_zero : ∀ i, decomposition.exponent i = 0) :
    ∀ i, Subsingleton
      (K[X] ⧸ K[X] ∙ decomposition.prime i ^ decomposition.exponent i) := by
  intro i
  have hp : decomposition.prime i ^ decomposition.exponent i = 1 := by
    rw [hall_zero i, pow_zero]
  rw [hp]
  exact subsingleton_quotient_span_one K[X]

/-- A direct sum of subsingleton summands is subsingleton. -/
theorem directSum_subsingleton_of_forall_subsingleton
    {ι : Type u} {β : ι → Type v} [∀ i, AddCommMonoid (β i)]
    [∀ i, Subsingleton (β i)] :
    Subsingleton (DirectSum ι β) := by
  refine ⟨?_⟩
  intro x y
  ext i
  exact Subsingleton.elim (x i) (y i)

/--
Split a finite product of dependent modules into one selected coordinate and
the product over the complementary indices.  This is the product-level helper
used below for the corresponding direct-sum decomposition.
-/
noncomputable def piSelectedComplementEquiv
    (R : Type v) [Semiring R]
    {ι : Type u} [DecidableEq ι]
    (β : ι → Type v) [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    (selected : ι) :
    ((i : ι) → β i) ≃ₗ[R]
      β selected × ((j : { i : ι // i ≠ selected }) → β j.1) where
  toFun f := (f selected, fun j => f j.1)
  invFun p i := by
    by_cases h : i = selected
    · subst h
      exact p.1
    · exact p.2 ⟨i, h⟩
  map_add' := by
    intro f g
    ext i <;> simp
  map_smul' := by
    intro c f
    ext i <;> simp
  left_inv := by
    intro f
    funext i
    by_cases h : i = selected
    · subst h
      simp
    · simp [h]
  right_inv := by
    intro p
    ext j
    · simp
    · dsimp
      split_ifs with h
      · exact False.elim (j.2 h)
      · rfl

/--
Split a finite direct sum into the selected summand and the direct sum over its
complement.  For rational canonical form this is the module-level entrance to
removing one PID cyclic summand as a companion block.
-/
noncomputable def directSumSelectedComplementEquiv
    (R : Type v) [Semiring R]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (β : ι → Type v) [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    (selected : ι) :
    DirectSum ι β ≃ₗ[R]
      β selected × DirectSum { i : ι // i ≠ selected } (fun j => β j.1) :=
  (DirectSum.linearEquivFunOnFintype R ι β).trans <|
    (piSelectedComplementEquiv R β selected).trans <|
      LinearEquiv.prodCongr (LinearEquiv.refl R (β selected))
        (DirectSum.linearEquivFunOnFintype R
          { i : ι // i ≠ selected } (fun j => β j.1)).symm

/--
The raw `K[X]`-linear selected/complement split before identifying the selected
quotient with `AdjoinRoot` over `K`.
-/
noncomputable def rationalCanonicalSelectedRawAmbientSplit
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    RationalCanonicalMatrixPolynomialModule K ι A ≃ₗ[K[X]]
      (K[X] ⧸ K[X] ∙
          decomposition.prime selected.selected ^
            decomposition.exponent selected.selected) ×
        DirectSum { i : decomposition.idx // i ≠ selected.selected }
          (fun j => K[X] ⧸ K[X] ∙ decomposition.prime j.1 ^ decomposition.exponent j.1) := by
  classical
  letI : Fintype decomposition.idx := decomposition.fintype_idx
  exact
    (Classical.choice decomposition.decomposition).trans <|
      directSumSelectedComplementEquiv K[X]
        (fun i : decomposition.idx =>
          K[X] ⧸ K[X] ∙ decomposition.prime i ^ decomposition.exponent i)
        selected.selected

/--
Split the canonical matrix `K[X]`-module, after a PID decomposition and selected
effective summand, into the selected `AdjoinRoot` cyclic block and the remaining
PID summands.  This is the ambient module equivalence from which the eventual
matrix change-of-basis data for the cyclic block step should be built.
-/
noncomputable def rationalCanonicalSelectedAmbientSplit
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    RationalCanonicalMatrixPolynomialModule K ι A ≃ₗ[K]
      AdjoinRoot selected.annihilator ×
        DirectSum { i : decomposition.idx // i ≠ selected.selected }
          (fun j => K[X] ⧸ K[X] ∙ decomposition.prime j.1 ^ decomposition.exponent j.1) := by
  classical
  exact
    (rationalCanonicalSelectedRawAmbientSplit selected).restrictScalars K |>.trans <|
      LinearEquiv.prodCongr selected.quotientEquivAdjoinRoot
        (LinearEquiv.refl K
          (DirectSum { i : decomposition.idx // i ≠ selected.selected }
            (fun j =>
              K[X] ⧸ K[X] ∙ decomposition.prime j.1 ^ decomposition.exponent j.1)))

/-- The complementary PID summands after removing the selected cyclic summand. -/
abbrev RationalCanonicalSelectedTailModule
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Type v :=
  DirectSum { i : decomposition.idx // i ≠ selected.selected }
    (fun j => K[X] ⧸ K[X] ∙ decomposition.prime j.1 ^ decomposition.exponent j.1)

/--
The raw tail component is invariant under the `X` action because the raw split
is `K[X]`-linear.
-/
theorem rationalCanonicalSelectedRawAmbientSplit_tail_X_smul
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (m : RationalCanonicalMatrixPolynomialModule K ι A) :
    (rationalCanonicalSelectedRawAmbientSplit selected ((Polynomial.X : K[X]) • m)).2 =
      ((Polynomial.X : K[X]) •
        ((rationalCanonicalSelectedRawAmbientSplit selected m).2 :
          RationalCanonicalSelectedTailModule selected)) := by
  classical
  simpa using congrArg Prod.snd
    ((rationalCanonicalSelectedRawAmbientSplit selected).map_smul (Polynomial.X : K[X]) m)

/--
The raw selected quotient component is invariant under the `X` action because
the raw split is `K[X]`-linear.
-/
theorem rationalCanonicalSelectedRawAmbientSplit_head_X_smul
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (m : RationalCanonicalMatrixPolynomialModule K ι A) :
    (rationalCanonicalSelectedRawAmbientSplit selected ((Polynomial.X : K[X]) • m)).1 =
      ((Polynomial.X : K[X]) •
        ((rationalCanonicalSelectedRawAmbientSplit selected m).1 :
          K[X] ⧸
            K[X] ∙ decomposition.prime selected.selected ^
              decomposition.exponent selected.selected)) := by
  classical
  simpa using congrArg Prod.fst
    ((rationalCanonicalSelectedRawAmbientSplit selected).map_smul (Polynomial.X : K[X]) m)

/--
The selected `AdjoinRoot` head component of the ambient split turns the `X`
action into multiplication by the selected root.
-/
theorem rationalCanonicalSelectedAmbientSplit_head_X_smul
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (m : RationalCanonicalMatrixPolynomialModule K ι A) :
    (rationalCanonicalSelectedAmbientSplit selected ((Polynomial.X : K[X]) • m)).1 =
      AdjoinRoot.root selected.annihilator *
        (rationalCanonicalSelectedAmbientSplit selected m).1 := by
  classical
  let raw := rationalCanonicalSelectedRawAmbientSplit selected
  let q := selected.quotientEquivAdjoinRoot
  have hraw :
      (raw ((Polynomial.X : K[X]) • m)).1 =
        (Polynomial.X : K[X]) • (raw m).1 :=
    rationalCanonicalSelectedRawAmbientSplit_head_X_smul selected m
  have hq :
      q ((Polynomial.X : K[X]) • (raw m).1) =
        AdjoinRoot.root selected.annihilator * q (raw m).1 :=
    selected.quotientEquivAdjoinRoot_X_smul (raw m).1
  change q (raw ((Polynomial.X : K[X]) • m)).1 =
    AdjoinRoot.root selected.annihilator * q (raw m).1
  rw [hraw]
  exact hq

/--
The tail component of the selected ambient split remains `K[X]`-linear for the
`X` action.
-/
theorem rationalCanonicalSelectedAmbientSplit_tail_X_smul
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (m : RationalCanonicalMatrixPolynomialModule K ι A) :
    (rationalCanonicalSelectedAmbientSplit selected ((Polynomial.X : K[X]) • m)).2 =
      ((Polynomial.X : K[X]) •
        ((rationalCanonicalSelectedAmbientSplit selected m).2 :
          RationalCanonicalSelectedTailModule selected)) := by
  classical
  let raw := rationalCanonicalSelectedRawAmbientSplit selected
  change (raw ((Polynomial.X : K[X]) • m)).2 =
    (Polynomial.X : K[X]) • (raw m).2
  exact rationalCanonicalSelectedRawAmbientSplit_tail_X_smul selected m

/-- The `K`-linear tail operator induced by multiplication by `X`. -/
noncomputable def rationalCanonicalSelectedTailXLinearMap
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    RationalCanonicalSelectedTailModule selected →ₗ[K]
      RationalCanonicalSelectedTailModule selected :=
  { toFun := fun y => (Polynomial.X : K[X]) • y
    map_add' := by
      intro x y
      exact smul_add (Polynomial.X : K[X]) x y
    map_smul' := by
      intro c y
      exact (smul_comm c (Polynomial.X : K[X]) y).symm }

/--
Pointwise head-coordinate form of the original matrix operator in selected/tail
split coordinates.
-/
theorem rationalCanonicalSelectedAmbientSplit_conj_toLin_head
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (x : AdjoinRoot selected.annihilator × RationalCanonicalSelectedTailModule selected) :
    (rationalCanonicalSelectedAmbientSplit selected
      (Module.AEval'.of (Matrix.toLin' A)
        ((Matrix.toLin' A)
          ((Module.AEval'.of (Matrix.toLin' A)).symm
            ((rationalCanonicalSelectedAmbientSplit selected).symm x))))).1 =
      AdjoinRoot.root selected.annihilator * x.1 := by
  classical
  let m : RationalCanonicalMatrixPolynomialModule K ι A :=
    (rationalCanonicalSelectedAmbientSplit selected).symm x
  have hm :
      Module.AEval'.of (Matrix.toLin' A)
          ((Matrix.toLin' A)
            ((Module.AEval'.of (Matrix.toLin' A)).symm m)) =
        (Polynomial.X : K[X]) • m := by
    rw [← Module.AEval'.X_smul_of]
    rw [LinearEquiv.apply_symm_apply]
  have hhead :=
    rationalCanonicalSelectedAmbientSplit_head_X_smul selected m
  rw [← hm] at hhead
  have hxsplit : rationalCanonicalSelectedAmbientSplit selected m = x := by
    exact LinearEquiv.apply_symm_apply
      (rationalCanonicalSelectedAmbientSplit selected) x
  rw [hxsplit] at hhead
  exact hhead

/--
Pointwise tail-coordinate form of the original matrix operator in selected/tail
split coordinates.
-/
theorem rationalCanonicalSelectedAmbientSplit_conj_toLin_tail
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (x : AdjoinRoot selected.annihilator × RationalCanonicalSelectedTailModule selected) :
    (rationalCanonicalSelectedAmbientSplit selected
      (Module.AEval'.of (Matrix.toLin' A)
        ((Matrix.toLin' A)
          ((Module.AEval'.of (Matrix.toLin' A)).symm
            ((rationalCanonicalSelectedAmbientSplit selected).symm x))))).2 =
      rationalCanonicalSelectedTailXLinearMap selected x.2 := by
  classical
  let m : RationalCanonicalMatrixPolynomialModule K ι A :=
    (rationalCanonicalSelectedAmbientSplit selected).symm x
  have hm :
      Module.AEval'.of (Matrix.toLin' A)
          ((Matrix.toLin' A)
            ((Module.AEval'.of (Matrix.toLin' A)).symm m)) =
        (Polynomial.X : K[X]) • m := by
    rw [← Module.AEval'.X_smul_of]
    rw [LinearEquiv.apply_symm_apply]
  have htail :=
    rationalCanonicalSelectedAmbientSplit_tail_X_smul selected m
  rw [← hm] at htail
  have hxsplit : rationalCanonicalSelectedAmbientSplit selected m = x := by
    exact LinearEquiv.apply_symm_apply
      (rationalCanonicalSelectedAmbientSplit selected) x
  rw [hxsplit] at htail
  simpa [rationalCanonicalSelectedTailXLinearMap] using htail

/--
The tail module is finite-dimensional over `K`: it is the second projection of
the selected ambient split of the finite canonical matrix module.
-/
noncomputable def rationalCanonicalSelectedTailModule_finite
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Module.Finite K (RationalCanonicalSelectedTailModule selected) := by
  classical
  let split := rationalCanonicalSelectedAmbientSplit selected
  haveI : Module.Finite K (RationalCanonicalMatrixPolynomialModule K ι A) := by
    exact Module.Finite.equiv (Module.AEval'.of (Matrix.toLin' A))
  let proj :
      RationalCanonicalMatrixPolynomialModule K ι A →ₗ[K]
        RationalCanonicalSelectedTailModule selected :=
    (LinearMap.snd K (AdjoinRoot selected.annihilator)
      (RationalCanonicalSelectedTailModule selected)).comp split.toLinearMap
  have hsurj : Function.Surjective proj := by
    intro y
    refine ⟨split.symm (0, y), ?_⟩
    change (split (split.symm (0, y))).2 = y
    rw [LinearEquiv.apply_symm_apply]
  exact Module.Finite.of_surjective proj hsurj

/-- A canonical noncomputable basis of the complementary tail module. -/
noncomputable def rationalCanonicalSelectedTailBasis
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Module.Basis
      (Module.Basis.ofVectorSpaceIndex K (RationalCanonicalSelectedTailModule selected))
      K (RationalCanonicalSelectedTailModule selected) :=
  Module.Basis.ofVectorSpace K (RationalCanonicalSelectedTailModule selected)

/--
The basis of the canonical matrix module obtained from the selected AdjoinRoot
power basis and an arbitrary vector-space basis of the complementary tail.
-/
noncomputable def rationalCanonicalSelectedAmbientBasis
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Module.Basis
      (Fin selected.annihilator.natDegree ⊕
        Module.Basis.ofVectorSpaceIndex K (RationalCanonicalSelectedTailModule selected))
      K (RationalCanonicalMatrixPolynomialModule K ι A) := by
  classical
  let split := rationalCanonicalSelectedAmbientSplit selected
  let headBasis :
      Module.Basis (Fin selected.annihilator.natDegree) K
        (AdjoinRoot selected.annihilator) :=
    (AdjoinRoot.powerBasis' selected.annihilator_monic).basis
  let tailBasis :
      Module.Basis
        (Module.Basis.ofVectorSpaceIndex K (RationalCanonicalSelectedTailModule selected))
        K (RationalCanonicalSelectedTailModule selected) :=
    rationalCanonicalSelectedTailBasis selected
  exact (headBasis.prod tailBasis).map split.symm

/--
The same selected/tail basis transported from the canonical `K[X]`-module back
to the underlying vector space `ι → K`.
-/
noncomputable def rationalCanonicalSelectedVectorBasis
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Module.Basis
      (Fin selected.annihilator.natDegree ⊕
        Module.Basis.ofVectorSpaceIndex K (RationalCanonicalSelectedTailModule selected))
      K (ι → K) :=
  (rationalCanonicalSelectedAmbientBasis selected).map
    (Module.AEval'.of (Matrix.toLin' A)).symm

/-- A finite-index basis of the complementary tail module. -/
noncomputable def rationalCanonicalSelectedTailFinBasis
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Module.Basis (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))
      K (RationalCanonicalSelectedTailModule selected) := by
  classical
  haveI : Module.Finite K (RationalCanonicalSelectedTailModule selected) :=
    rationalCanonicalSelectedTailModule_finite selected
  haveI : Module.Free K (RationalCanonicalSelectedTailModule selected) :=
    Module.Free.of_basis (rationalCanonicalSelectedTailBasis selected)
  exact Module.finBasis K (RationalCanonicalSelectedTailModule selected)

/--
Fin-indexed version of the selected/tail basis on the underlying vector space.
This index shape is closer to the eventual block-step matrix data.
-/
noncomputable def rationalCanonicalSelectedVectorFinBasis
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Module.Basis
      (Fin selected.annihilator.natDegree ⊕
        Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))
      K (ι → K) := by
  classical
  let split := rationalCanonicalSelectedAmbientSplit selected
  let headBasis :
      Module.Basis (Fin selected.annihilator.natDegree) K
        (AdjoinRoot selected.annihilator) :=
    (AdjoinRoot.powerBasis' selected.annihilator_monic).basis
  let tailBasis := rationalCanonicalSelectedTailFinBasis selected
  exact (headBasis.prod tailBasis).map
    (split.symm.trans (Module.AEval'.of (Matrix.toLin' A)).symm)

/-- Definitional form of the Fin-indexed selected/tail vector basis. -/
theorem rationalCanonicalSelectedVectorFinBasis_eq_prod_map
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    rationalCanonicalSelectedVectorFinBasis selected =
      (((AdjoinRoot.powerBasis' selected.annihilator_monic).basis).prod
        (rationalCanonicalSelectedTailFinBasis selected)).map
          ((rationalCanonicalSelectedAmbientSplit selected).symm.trans
            (Module.AEval'.of (Matrix.toLin' A)).symm) :=
  rfl

/--
Columns of the selected/tail vector-space basis in the standard function basis.
This is the rectangular basis matrix before choosing an ambient index
equivalence to turn it into the square change-of-basis matrix `P`.
-/
noncomputable def rationalCanonicalSelectedBasisMatrix
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Matrix ι
      (Fin selected.annihilator.natDegree ⊕
        Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))) K :=
  (Pi.basisFun K ι).toMatrix (rationalCanonicalSelectedVectorFinBasis selected)

/--
The selected companion block indices plus the Fin-indexed tail basis have the
same cardinality as the ambient matrix index.
-/
theorem rationalCanonicalSelectedVectorFinBasis_card_eq
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Fintype.card
      (Fin selected.annihilator.natDegree ⊕
        Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))) =
      Fintype.card ι := by
  classical
  have hb := Module.finrank_eq_card_basis (rationalCanonicalSelectedVectorFinBasis selected)
  have hfun : Module.finrank K (ι → K) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card K
  exact hb.symm.trans hfun

/-- A noncomputable index equivalence from the selected/tail basis index to `ι`. -/
noncomputable def rationalCanonicalSelectedIndexEquiv
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    (Fin selected.annihilator.natDegree ⊕
      Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))) ≃ ι :=
  Fintype.equivOfCardEq (rationalCanonicalSelectedVectorFinBasis_card_eq selected)

/-- The selected/tail vector-space basis reindexed by the ambient matrix index. -/
noncomputable def rationalCanonicalSelectedReindexedBasis
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Module.Basis ι K (ι → K) :=
  (rationalCanonicalSelectedVectorFinBasis selected).reindex
    (rationalCanonicalSelectedIndexEquiv selected)

/--
Square change-of-basis matrix whose columns are the selected/tail basis vectors
in standard coordinates.  This is the candidate `P` for the cyclic block step.
-/
noncomputable def rationalCanonicalSelectedSquareBasisMatrix
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Matrix ι ι K :=
  (Pi.basisFun K ι).toMatrix (rationalCanonicalSelectedReindexedBasis selected)

/-- Inverse candidate for `rationalCanonicalSelectedSquareBasisMatrix`. -/
noncomputable def rationalCanonicalSelectedSquareBasisMatrixInv
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Matrix ι ι K :=
  (rationalCanonicalSelectedReindexedBasis selected).toMatrix (Pi.basisFun K ι)

/-- The selected square basis matrix is invertible. -/
theorem rationalCanonicalSelectedSquareBasisMatrix_inverse
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    HasMatrixInverse
      (rationalCanonicalSelectedSquareBasisMatrix selected)
      (rationalCanonicalSelectedSquareBasisMatrixInv selected) := by
  classical
  let bStd := Pi.basisFun K ι
  let bSel := rationalCanonicalSelectedReindexedBasis selected
  change HasMatrixInverse (bStd.toMatrix bSel) (bSel.toMatrix bStd)
  constructor
  · simpa using (Module.Basis.toMatrix_mul_toMatrix bSel bStd bSel)
  · simpa using (Module.Basis.toMatrix_mul_toMatrix bStd bSel bStd)

/--
Matrix of `Matrix.toLin' A` in the selected/tail basis.  The following theorem
identifies this matrix with the explicit similarity `Pinv * A * P`.
-/
noncomputable def rationalCanonicalSelectedBasisLinearMapMatrix
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Matrix ι ι K :=
  LinearMap.toMatrix
    (rationalCanonicalSelectedReindexedBasis selected)
    (rationalCanonicalSelectedReindexedBasis selected)
    (Matrix.toLin' A)

/--
The selected-basis matrix is exactly the explicit similarity transform built
from the square basis matrix and its inverse.
-/
theorem rationalCanonicalSelectedBasisLinearMapMatrix_eq_similarity
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    rationalCanonicalSelectedBasisLinearMapMatrix selected =
      rationalCanonicalSelectedSquareBasisMatrixInv selected * A *
        rationalCanonicalSelectedSquareBasisMatrix selected := by
  classical
  let bStd := Pi.basisFun K ι
  let bSel := rationalCanonicalSelectedReindexedBasis selected
  change LinearMap.toMatrix bSel bSel (Matrix.toLin' A) =
    bSel.toMatrix bStd * A * bStd.toMatrix bSel
  have hstd : LinearMap.toMatrix bStd bStd (Matrix.toLin' A) = A := by
    rw [← Matrix.toLin_eq_toLin']
    exact LinearMap.toMatrix_toLin bStd bStd A
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (b := bSel) (b' := bStd) (c := bSel) (c' := bStd) (f := Matrix.toLin' A)
  rw [hstd] at h
  exact h.symm

/--
Split equivalence from the ambient matrix index to the selected companion-block
indices followed by the Fin-indexed tail basis.
-/
noncomputable def rationalCanonicalSelectedSplitIndex
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    ι ≃ (Fin selected.annihilator.natDegree) ⊕ₗ
      (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))) :=
  (rationalCanonicalSelectedIndexEquiv selected).symm.trans
    (sumToLexEquiv (Fin selected.annihilator.natDegree)
      (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))))

/--
The selected-basis linear-map matrix reindexed into explicit selected/tail block
shape.  The remaining block-equation proof identifies this with a block diagonal
matrix whose head is the AdjoinRoot companion action.
-/
noncomputable def rationalCanonicalSelectedSplitLinearMapMatrix
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Matrix
      ((Fin selected.annihilator.natDegree) ⊕ₗ
        (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))))
      ((Fin selected.annihilator.natDegree) ⊕ₗ
        (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))) K :=
  Matrix.reindex (rationalCanonicalSelectedSplitIndex selected)
    (rationalCanonicalSelectedSplitIndex selected)
    (rationalCanonicalSelectedBasisLinearMapMatrix selected)

/--
The selected split matrix is the matrix of `Matrix.toLin' A` in the Fin-indexed
selected/tail basis, reindexed from the raw sum to the lexicographic sum.
-/
theorem rationalCanonicalSelectedSplitLinearMapMatrix_eq_vectorFinBasis
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    rationalCanonicalSelectedSplitLinearMapMatrix selected =
      Matrix.reindex
        (sumToLexEquiv
          (Fin selected.annihilator.natDegree)
          (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))))
        (sumToLexEquiv
          (Fin selected.annihilator.natDegree)
          (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))))
        (LinearMap.toMatrix
          (rationalCanonicalSelectedVectorFinBasis selected)
          (rationalCanonicalSelectedVectorFinBasis selected)
          (Matrix.toLin' A)) := by
  classical
  let β :=
    (Fin selected.annihilator.natDegree) ⊕
      Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))
  let b : Module.Basis β K (ι → K) :=
    rationalCanonicalSelectedVectorFinBasis selected
  let e : β ≃ ι :=
    rationalCanonicalSelectedIndexEquiv selected
  let s :
      β ≃
        (Fin selected.annihilator.natDegree) ⊕ₗ
          Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)) :=
    sumToLexEquiv
      (Fin selected.annihilator.natDegree)
      (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))
  ext i j
  simp [rationalCanonicalSelectedSplitLinearMapMatrix,
    rationalCanonicalSelectedBasisLinearMapMatrix,
    rationalCanonicalSelectedReindexedBasis,
    rationalCanonicalSelectedSplitIndex,
    Matrix.reindex_apply, LinearMap.toMatrix_apply,
    Module.Basis.reindex_apply]

/--
In selected/tail product coordinates, the original matrix operator is
conjugate to root multiplication on the selected `AdjoinRoot` factor and the
`X` action on the tail.
-/
theorem rationalCanonicalSelectedVectorFinBasis_conj_toLin
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (x : AdjoinRoot selected.annihilator × RationalCanonicalSelectedTailModule selected) :
    ((rationalCanonicalSelectedAmbientSplit selected).symm.trans
        (Module.AEval'.of (Matrix.toLin' A)).symm).symm
      ((Matrix.toLin' A)
        (((rationalCanonicalSelectedAmbientSplit selected).symm.trans
            (Module.AEval'.of (Matrix.toLin' A)).symm) x)) =
      (AdjoinRoot.root selected.annihilator * x.1,
        rationalCanonicalSelectedTailXLinearMap selected x.2) := by
  classical
  let split := rationalCanonicalSelectedAmbientSplit selected
  let e := Module.AEval'.of (Matrix.toLin' A)
  apply Prod.ext
  · change
      (split
        (e
          ((Matrix.toLin' A)
            (e.symm (split.symm x))))).1 =
        AdjoinRoot.root selected.annihilator * x.1
    simpa [split, e] using
      rationalCanonicalSelectedAmbientSplit_conj_toLin_head selected x
  · change
      (split
        (e
          ((Matrix.toLin' A)
            (e.symm (split.symm x))))).2 =
        rationalCanonicalSelectedTailXLinearMap selected x.2
    simpa [split, e] using
      rationalCanonicalSelectedAmbientSplit_conj_toLin_tail selected x

/-- The selected head-head block is root multiplication in the power basis. -/
theorem rationalCanonicalSelectedVectorFinBasis_head_head
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (i j : Fin selected.annihilator.natDegree) :
    (LinearMap.toMatrix
      (rationalCanonicalSelectedVectorFinBasis selected)
      (rationalCanonicalSelectedVectorFinBasis selected)
      (Matrix.toLin' A)) (Sum.inl i) (Sum.inl j) =
      ((Algebra.leftMulMatrix
          (AdjoinRoot.powerBasis' selected.annihilator_monic).basis)
        (AdjoinRoot.powerBasis' selected.annihilator_monic).gen) i j := by
  classical
  let split := rationalCanonicalSelectedAmbientSplit selected
  let e := Module.AEval'.of (Matrix.toLin' A)
  let headBasis :
      Module.Basis (Fin selected.annihilator.natDegree) K
        (AdjoinRoot selected.annihilator) :=
    (AdjoinRoot.powerBasis' selected.annihilator_monic).basis
  let tailBasis := rationalCanonicalSelectedTailFinBasis selected
  let prodBasis := headBasis.prod tailBasis
  let F :
      (AdjoinRoot selected.annihilator × RationalCanonicalSelectedTailModule selected)
        ≃ₗ[K] (ι → K) :=
    split.symm.trans e.symm
  have hb :
      rationalCanonicalSelectedVectorFinBasis selected = prodBasis.map F := by
    rfl
  rw [hb]
  rw [LinearMap.toMatrix_apply]
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  simp only [Module.Basis.map_apply]
  change
    (prodBasis.repr
      (F.symm ((Matrix.toLin' A) (F (prodBasis (Sum.inl j)))))) (Sum.inl i) =
    (headBasis.repr
      ((AdjoinRoot.powerBasis' selected.annihilator_monic).gen * headBasis j)) i
  have hFsymm :
      F.symm ((Matrix.toLin' A) (F (prodBasis (Sum.inl j)))) =
        (AdjoinRoot.root selected.annihilator * (prodBasis (Sum.inl j)).1,
          rationalCanonicalSelectedTailXLinearMap selected
            (prodBasis (Sum.inl j)).2) := by
    simpa [F, split, e] using
      rationalCanonicalSelectedVectorFinBasis_conj_toLin selected
        (prodBasis (Sum.inl j))
  rw [hFsymm]
  rw [Module.Basis.prod_repr_inl]
  rw [Module.Basis.prod_apply_inl_fst]
  rfl

/-- The head coordinate of the image of a tail basis vector is zero. -/
theorem rationalCanonicalSelectedVectorFinBasis_head_tail_zero
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (i : Fin selected.annihilator.natDegree)
    (j : Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))) :
    (LinearMap.toMatrix
      (rationalCanonicalSelectedVectorFinBasis selected)
      (rationalCanonicalSelectedVectorFinBasis selected)
      (Matrix.toLin' A)) (Sum.inl i) (Sum.inr j) = 0 := by
  classical
  let split := rationalCanonicalSelectedAmbientSplit selected
  let e := Module.AEval'.of (Matrix.toLin' A)
  let headBasis :
      Module.Basis (Fin selected.annihilator.natDegree) K
        (AdjoinRoot selected.annihilator) :=
    (AdjoinRoot.powerBasis' selected.annihilator_monic).basis
  let tailBasis := rationalCanonicalSelectedTailFinBasis selected
  let prodBasis := headBasis.prod tailBasis
  let F :
      (AdjoinRoot selected.annihilator × RationalCanonicalSelectedTailModule selected)
        ≃ₗ[K] (ι → K) :=
    split.symm.trans e.symm
  have hb :
      rationalCanonicalSelectedVectorFinBasis selected = prodBasis.map F := by
    rfl
  rw [hb]
  rw [LinearMap.toMatrix_apply]
  simp only [Module.Basis.map_apply]
  change
    (prodBasis.repr
      (F.symm ((Matrix.toLin' A) (F (prodBasis (Sum.inr j)))))) (Sum.inl i) = 0
  have hFsymm :
      F.symm ((Matrix.toLin' A) (F (prodBasis (Sum.inr j)))) =
        (AdjoinRoot.root selected.annihilator * (prodBasis (Sum.inr j)).1,
          rationalCanonicalSelectedTailXLinearMap selected
            (prodBasis (Sum.inr j)).2) := by
    simpa [F, split, e] using
      rationalCanonicalSelectedVectorFinBasis_conj_toLin selected
        (prodBasis (Sum.inr j))
  rw [hFsymm]
  rw [Module.Basis.prod_repr_inl]
  rw [Module.Basis.prod_apply_inr_fst]
  simp

/-- The tail coordinate of the image of a head basis vector is zero. -/
theorem rationalCanonicalSelectedVectorFinBasis_tail_head_zero
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition)
    (i : Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))
    (j : Fin selected.annihilator.natDegree) :
    (LinearMap.toMatrix
      (rationalCanonicalSelectedVectorFinBasis selected)
      (rationalCanonicalSelectedVectorFinBasis selected)
      (Matrix.toLin' A)) (Sum.inr i) (Sum.inl j) = 0 := by
  classical
  let split := rationalCanonicalSelectedAmbientSplit selected
  let e := Module.AEval'.of (Matrix.toLin' A)
  let headBasis :
      Module.Basis (Fin selected.annihilator.natDegree) K
        (AdjoinRoot selected.annihilator) :=
    (AdjoinRoot.powerBasis' selected.annihilator_monic).basis
  let tailBasis := rationalCanonicalSelectedTailFinBasis selected
  let prodBasis := headBasis.prod tailBasis
  let F :
      (AdjoinRoot selected.annihilator × RationalCanonicalSelectedTailModule selected)
        ≃ₗ[K] (ι → K) :=
    split.symm.trans e.symm
  have hb :
      rationalCanonicalSelectedVectorFinBasis selected = prodBasis.map F := by
    rfl
  rw [hb]
  rw [LinearMap.toMatrix_apply]
  simp only [Module.Basis.map_apply]
  change
    (prodBasis.repr
      (F.symm ((Matrix.toLin' A) (F (prodBasis (Sum.inl j)))))) (Sum.inr i) = 0
  have hFsymm :
      F.symm ((Matrix.toLin' A) (F (prodBasis (Sum.inl j)))) =
        (AdjoinRoot.root selected.annihilator * (prodBasis (Sum.inl j)).1,
          rationalCanonicalSelectedTailXLinearMap selected
            (prodBasis (Sum.inl j)).2) := by
    simpa [F, split, e] using
      rationalCanonicalSelectedVectorFinBasis_conj_toLin selected
        (prodBasis (Sum.inl j))
  rw [hFsymm]
  rw [Module.Basis.prod_repr_inr]
  rw [Module.Basis.prod_apply_inl_snd]
  simp [rationalCanonicalSelectedTailXLinearMap]

/-- Head block of the selected/tail split matrix. -/
noncomputable def rationalCanonicalSelectedSplitHead
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
  Matrix (Fin selected.annihilator.natDegree)
    (Fin selected.annihilator.natDegree) K :=
  (rationalCanonicalSelectedSplitLinearMapMatrix selected).toBlocks₁₁

/-- Tail block of the selected/tail split matrix. -/
noncomputable def rationalCanonicalSelectedSplitTail
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    Matrix (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))
      (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))) K :=
  (rationalCanonicalSelectedSplitLinearMapMatrix selected).toBlocks₂₂

/--
Named remaining block equation for the selected/tail matrix.  The final
polynomial block bridge must prove this equation from the `K[X]`-linearity of
the PID decomposition and the AdjoinRoot power basis.
-/
def RationalCanonicalSelectedSplitBlockEquation
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) : Prop :=
  rationalCanonicalSelectedSplitLinearMapMatrix selected =
    rationalCanonicalBlockDiagLex
      (rationalCanonicalSelectedSplitHead selected)
      (rationalCanonicalSelectedSplitTail selected)

/--
Concrete certificate that the selected PID summand has already been identified
with the selected/tail matrix split.  This isolates the only non-mechanical
algebra still needed for the polynomial block bridge:

* the head block is the companion block for the selected annihilator;
* the selected/tail split matrix has zero off-diagonal blocks.
-/
structure RationalCanonicalSelectedBlockStepCertificate
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A)
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) where
  head_companion :
    SingleCompanionBlockForm
      (rationalCanonicalSelectedSplitHead selected)
      selected.annihilator
  block_eq :
    RationalCanonicalSelectedSplitBlockEquation selected

/--
Finer selected/tail matrix statement.  This is equivalent to the selected split
being block diagonal, but exposes the actual proof obligations as off-diagonal
zero blocks.
-/
structure RationalCanonicalSelectedSplitBlockCertificate
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) where
  toBlocks₁₂_zero :
    (rationalCanonicalSelectedSplitLinearMapMatrix selected).toBlocks₁₂ = 0
  toBlocks₂₁_zero :
    (rationalCanonicalSelectedSplitLinearMapMatrix selected).toBlocks₂₁ = 0

/-- Off-diagonal zero blocks imply the selected/tail block-diagonal equation. -/
theorem rationalCanonicalSelectedSplitBlockEquation_of_certificate
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    {selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition}
    (certificate : RationalCanonicalSelectedSplitBlockCertificate selected) :
    RationalCanonicalSelectedSplitBlockEquation selected := by
  classical
  let M := rationalCanonicalSelectedSplitLinearMapMatrix selected
  change M =
    rationalCanonicalBlockDiagLex M.toBlocks₁₁ M.toBlocks₂₂
  rw [← Matrix.fromBlocks_toBlocks M]
  rw [certificate.toBlocks₁₂_zero, certificate.toBlocks₂₁_zero]
  ext i j <;> cases i <;> cases j <;>
    simp [rationalCanonicalBlockDiagLex, Matrix.reindex_apply]

/--
Head action certificate: the selected head block is exactly multiplication by
the adjoined root in the standard power basis.
-/
def RationalCanonicalSelectedHeadCompanionCertificate
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) : Prop :=
  rationalCanonicalSelectedSplitHead selected =
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' selected.annihilator_monic).basis)
      (AdjoinRoot.powerBasis' selected.annihilator_monic).gen

/-- The head action certificate supplies the companion-block proof. -/
theorem rationalCanonicalSelected_head_companion_of_certificate
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    {selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition}
    (certificate : RationalCanonicalSelectedHeadCompanionCertificate selected) :
    SingleCompanionBlockForm
      (rationalCanonicalSelectedSplitHead selected)
      selected.annihilator := by
  rw [certificate]
  exact singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis
    selected.annihilator selected.annihilator_monic
    selected.annihilator_natDegree_pos

/-- The selected split head is exactly multiplication by the AdjoinRoot root. -/
theorem rationalCanonicalSelectedHeadCompanionCertificate_concrete
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    RationalCanonicalSelectedHeadCompanionCertificate selected := by
  classical
  ext i j
  have hmatrix :=
    rationalCanonicalSelectedSplitLinearMapMatrix_eq_vectorFinBasis selected
  have hentry := congrFun (congrFun hmatrix (Sum.inl i)) (Sum.inl j)
  simpa [RationalCanonicalSelectedHeadCompanionCertificate,
    rationalCanonicalSelectedSplitHead, Matrix.toBlocks₁₁, Matrix.reindex_apply]
    using hentry.trans
      (rationalCanonicalSelectedVectorFinBasis_head_head selected i j)

/-- The selected/tail split matrix has zero off-diagonal blocks. -/
theorem rationalCanonicalSelectedSplitBlockCertificate_concrete
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    RationalCanonicalSelectedSplitBlockCertificate selected := by
  classical
  constructor
  · ext i j
    have hmatrix :=
      rationalCanonicalSelectedSplitLinearMapMatrix_eq_vectorFinBasis selected
    have hentry := congrFun (congrFun hmatrix (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.toBlocks₁₂, Matrix.reindex_apply]
      using hentry.trans
        (rationalCanonicalSelectedVectorFinBasis_head_tail_zero selected i j)
  · ext i j
    have hmatrix :=
      rationalCanonicalSelectedSplitLinearMapMatrix_eq_vectorFinBasis selected
    have hentry := congrFun (congrFun hmatrix (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₂₁, Matrix.reindex_apply]
      using hentry.trans
        (rationalCanonicalSelectedVectorFinBasis_tail_head_zero selected i j)

/--
Finer algebraic certificate for the selected block step.  It separates the proof
that the selected block is the AdjoinRoot companion action from the proof that
the selected/tail split has zero off-diagonal blocks.
-/
structure RationalCanonicalSelectedAlgebraicBlockCertificate
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A)
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) where
  head :
    RationalCanonicalSelectedHeadCompanionCertificate selected
  split :
    RationalCanonicalSelectedSplitBlockCertificate selected

/-- Concrete selected algebraic block certificate from the PID selected split. -/
noncomputable def rationalCanonicalSelectedAlgebraicBlockCertificate
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    RationalCanonicalSelectedAlgebraicBlockCertificate K ι A decomposition selected where
  head := rationalCanonicalSelectedHeadCompanionCertificate_concrete selected
  split := rationalCanonicalSelectedSplitBlockCertificate_concrete selected

/-- The finer algebraic certificate supplies the selected block-step certificate. -/
def rationalCanonicalSelectedBlockStepCertificateOfAlgebraicCertificate
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    {selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition}
    (certificate :
      RationalCanonicalSelectedAlgebraicBlockCertificate K ι A decomposition selected) :
    RationalCanonicalSelectedBlockStepCertificate K ι A decomposition selected where
  head_companion :=
    rationalCanonicalSelected_head_companion_of_certificate certificate.head
  block_eq :=
    rationalCanonicalSelectedSplitBlockEquation_of_certificate certificate.split

/--
In a positive-dimensional matrix module, the PID decomposition must contain a
summand with positive exponent.
-/
theorem rationalCanonicalDecomposition_exists_positive_exponent
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) :
    ∃ i, 0 < decomposition.exponent i := by
  classical
  by_contra hnone
  have hall_zero : ∀ i, decomposition.exponent i = 0 := by
    intro i
    exact Nat.eq_zero_of_not_pos (by
      intro hpos
      exact hnone ⟨i, hpos⟩)
  have hsub_each :
      ∀ i, Subsingleton
        (K[X] ⧸ K[X] ∙ decomposition.prime i ^ decomposition.exponent i) :=
    rationalCanonicalDecomposition_quotient_subsingleton_of_all_exponents_zero
      decomposition hall_zero
  letI :
      ∀ i, Subsingleton
        (K[X] ⧸ K[X] ∙ decomposition.prime i ^ decomposition.exponent i) :=
    hsub_each
  have hds : Subsingleton
      (DirectSum decomposition.idx
        (fun i => K[X] ⧸ K[X] ∙ decomposition.prime i ^ decomposition.exponent i)) :=
    directSum_subsingleton_of_forall_subsingleton
  rcases decomposition.decomposition with ⟨e⟩
  have hMsub : Subsingleton (RationalCanonicalMatrixPolynomialModule K ι A) :=
    e.toEquiv.subsingleton
  have hnontriv := rationalCanonicalMatrixPolynomialModule_nontrivial_of_nonempty A
  exact (not_subsingleton_iff_nontrivial.mpr hnontriv) hMsub

/--
The effective summand index required by the selected-summand bridge is already
forced by the PID decomposition of any nonempty canonical matrix module.
-/
noncomputable def rationalCanonicalEffectiveSummandIndexOfDecomposition
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι K}
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) :
    RationalCanonicalEffectiveSummandIndex K ι A decomposition := by
  classical
  let h := rationalCanonicalDecomposition_exists_positive_exponent A decomposition
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/--
Concrete effective-index bridge obtained from the PID decomposition.  It is
noncomputable only because the PID decomposition and the positive exponent are
chosen classically.
-/
noncomputable def rationalCanonicalEffectiveSummandIndexBridge
    (K : Type v) [Field K] :
    RationalCanonicalEffectiveSummandIndexBridge.{u, v} K where
  choose := fun _A _data decomposition =>
    rationalCanonicalEffectiveSummandIndexOfDecomposition decomposition

/--
Constructor for a selected cyclic summand from a concrete PID decomposition
index.  It uses polynomial normalization internally under `classical`, while
the public signature remains over bare `[Field K]`.
-/
noncomputable def rationalCanonicalSelectedCyclicSummandOfIndex
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A)
    (selected : decomposition.idx)
    (exponent_pos : 0 < decomposition.exponent selected) :
    RationalCanonicalSelectedCyclicSummand K ι A decomposition := by
  classical
  let p : K[X] := decomposition.prime selected
  let q : K[X] := normalize p
  have hp_irred : Irreducible p := decomposition.prime_irreducible selected
  have hp_ne_zero : p ≠ 0 := hp_irred.ne_zero
  have hq_monic : q.Monic := by
    simpa [q, p] using Polynomial.monic_normalize hp_ne_zero
  have hq_assoc : Associated q p := by
    rw [← normalize_eq_normalize_iff_associated]
    simp [q, p, normalize_idem]
  let annihilator : K[X] := q ^ decomposition.exponent selected
  have hann_monic : annihilator.Monic := by
    simpa [annihilator] using hq_monic.pow (decomposition.exponent selected)
  have hq_natDegree_pos : 0 < q.natDegree := by
    exact (hq_assoc.irreducible_iff.mpr hp_irred).natDegree_pos
  have hann_natDegree_pos : 0 < annihilator.natDegree := by
    change 0 < (q ^ decomposition.exponent selected).natDegree
    rw [hq_monic.natDegree_pow]
    exact Nat.mul_pos exponent_pos hq_natDegree_pos
  exact
    { selected := selected
      exponent_pos := exponent_pos
      cyclic_factor := q
      cyclic_factor_monic := hq_monic
      cyclic_factor_associated := hq_assoc
      annihilator := annihilator
      annihilator_eq := rfl
      annihilator_monic := hann_monic
      annihilator_natDegree_pos := hann_natDegree_pos
      quotient_equiv :=
        quotient_span_singleton_pow_equiv_of_associated hq_assoc
          (decomposition.exponent selected) }

/-- An effective-index bridge canonically supplies the full selected-summand bridge. -/
noncomputable def rationalCanonicalSelectedCyclicSummandBridgeOfEffectiveIndexBridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalEffectiveSummandIndexBridge.{u, v} K) :
    RationalCanonicalSelectedCyclicSummandBridge.{u, v} K where
  select := fun A data decomposition =>
    let chosen := bridge.choose A data decomposition
    rationalCanonicalSelectedCyclicSummandOfIndex
      decomposition chosen.selected chosen.exponent_pos

/--
Variable-size cyclic block data extracted from the PID decomposition.

This is the mathematically correct one-step payload for rational canonical
form over an arbitrary field: a cyclic summand of degree `d` contributes a
`d × d` companion block, and the recursive slice is the complementary summand.
The existing square driver consumes one-index head-tail steps, so this data is
kept separate from `RationalCanonicalModuleStepData` until a block-size descent
driver is added.
-/
structure RationalCanonicalCyclicBlockStepData
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) where
  blockIdx : Type u
  [fintype_blockIdx : Fintype blockIdx]
  [decEq_blockIdx : DecidableEq blockIdx]
  [linearOrder_blockIdx : LinearOrder blockIdx]
  tailIdx : Type u
  [fintype_tailIdx : Fintype tailIdx]
  [decEq_tailIdx : DecidableEq tailIdx]
  [linearOrder_tailIdx : LinearOrder tailIdx]
  P : Matrix ι ι K
  Pinv : Matrix ι ι K
  inverse_P : HasMatrixInverse P Pinv
  cyclic_annihilator : K[X]
  cyclic_annihilator_monic : cyclic_annihilator.Monic
  cyclic_blockSize : Nat
  cyclic_blockSize_pos : 0 < cyclic_blockSize
  cyclic_blockSize_eq_natDegree : cyclic_blockSize = cyclic_annihilator.natDegree
  block_card_eq : Fintype.card blockIdx = cyclic_blockSize
  head : Matrix blockIdx blockIdx K
  head_companion : SingleCompanionBlockForm head cyclic_annihilator
  tail : Matrix tailIdx tailIdx K
  splitIndex : ι ≃ blockIdx ⊕ₗ tailIdx
  block_eq :
    Matrix.reindex splitIndex splitIndex (Pinv * A * P) =
      rationalCanonicalBlockDiagLex head tail

attribute [instance] RationalCanonicalCyclicBlockStepData.fintype_blockIdx
attribute [instance] RationalCanonicalCyclicBlockStepData.decEq_blockIdx
attribute [instance] RationalCanonicalCyclicBlockStepData.linearOrder_blockIdx
attribute [instance] RationalCanonicalCyclicBlockStepData.fintype_tailIdx
attribute [instance] RationalCanonicalCyclicBlockStepData.decEq_tailIdx
attribute [instance] RationalCanonicalCyclicBlockStepData.linearOrder_tailIdx

/--
Build the full cyclic-block descent step once the selected/tail certificate is
available.  The change-of-basis matrices, inverse proof, split index, tail
matrix, block size, and progress numerology all come from the selected-summand
basis construction above.
-/
noncomputable def rationalCanonicalCyclicBlockStepDataOfSelectedCertificate
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    {selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition}
    (certificate :
      RationalCanonicalSelectedBlockStepCertificate K ι A decomposition selected) :
    RationalCanonicalCyclicBlockStepData K ι A := by
  let liftSplit :
      (Fin selected.annihilator.natDegree) ⊕ₗ
          (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))) ≃
        (ULift.{u, 0} (Fin selected.annihilator.natDegree)) ⊕ₗ
          (ULift.{u, 0}
            (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))) :=
    (sumToLexEquiv
        (Fin selected.annihilator.natDegree)
        (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))).symm.trans <|
      (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm).trans <|
        sumToLexEquiv
          (ULift.{u, 0} (Fin selected.annihilator.natDegree))
          (ULift.{u, 0}
            (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected))))
  exact {
  blockIdx := ULift.{u, 0} (Fin selected.annihilator.natDegree)
  fintype_blockIdx := inferInstance
  decEq_blockIdx := inferInstance
  linearOrder_blockIdx := inferInstance
  tailIdx :=
    ULift.{u, 0} (Fin (Module.finrank K (RationalCanonicalSelectedTailModule selected)))
  fintype_tailIdx := inferInstance
  decEq_tailIdx := inferInstance
  linearOrder_tailIdx := inferInstance
  P := rationalCanonicalSelectedSquareBasisMatrix selected
  Pinv := rationalCanonicalSelectedSquareBasisMatrixInv selected
  inverse_P := rationalCanonicalSelectedSquareBasisMatrix_inverse selected
  cyclic_annihilator := selected.annihilator
  cyclic_annihilator_monic := selected.annihilator_monic
  cyclic_blockSize := selected.annihilator.natDegree
  cyclic_blockSize_pos := selected.annihilator_natDegree_pos
  cyclic_blockSize_eq_natDegree := rfl
  block_card_eq := by
    simp
  head :=
    Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm
      (rationalCanonicalSelectedSplitHead selected)
  head_companion :=
    singleCompanionBlockForm_reindex Equiv.ulift.symm certificate.head_companion
  tail :=
    Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm
      (rationalCanonicalSelectedSplitTail selected)
  splitIndex :=
    (rationalCanonicalSelectedSplitIndex selected).trans liftSplit
  block_eq := by
    have hsim := rationalCanonicalSelectedBasisLinearMapMatrix_eq_similarity selected
    have hcombine :
        Matrix.reindex
            ((rationalCanonicalSelectedSplitIndex selected).trans liftSplit)
            ((rationalCanonicalSelectedSplitIndex selected).trans liftSplit)
            (rationalCanonicalSelectedBasisLinearMapMatrix selected) =
          Matrix.reindex liftSplit liftSplit
            (rationalCanonicalSelectedSplitLinearMapMatrix selected) := by
      rw [← reindex_reindex
        (rationalCanonicalSelectedSplitIndex selected)
        (rationalCanonicalSelectedSplitIndex selected)
        liftSplit liftSplit
        (rationalCanonicalSelectedBasisLinearMapMatrix selected)]
      rfl
    change
      Matrix.reindex
          ((rationalCanonicalSelectedSplitIndex selected).trans liftSplit)
          ((rationalCanonicalSelectedSplitIndex selected).trans liftSplit)
          (rationalCanonicalSelectedSquareBasisMatrixInv selected * A *
            rationalCanonicalSelectedSquareBasisMatrix selected) =
        rationalCanonicalBlockDiagLex
          (Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm
            (rationalCanonicalSelectedSplitHead selected))
          (Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm
            (rationalCanonicalSelectedSplitTail selected))
    rw [← hsim]
    rw [hcombine]
    rw [certificate.block_eq]
    exact rationalCanonicalBlockDiagLex_reindex Equiv.ulift.symm Equiv.ulift.symm
      (rationalCanonicalSelectedSplitHead selected)
      (rationalCanonicalSelectedSplitTail selected)
  }

/--
Canonical companion-head block data attached to a selected cyclic summand.

This is the portion of `RationalCanonicalCyclicBlockStepData` that follows
directly from the selected annihilator polynomial.  The remaining block-step
bridge must still embed this block as an invariant direct summand of the
original matrix module and construct the complementary tail similarity.
-/
structure RationalCanonicalSelectedCompanionBlock
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A)
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) where
  blockIdx : Type u
  [fintype_blockIdx : Fintype blockIdx]
  [decEq_blockIdx : DecidableEq blockIdx]
  [linearOrder_blockIdx : LinearOrder blockIdx]
  head : Matrix blockIdx blockIdx K
  head_companion : SingleCompanionBlockForm head selected.annihilator
  block_card_eq_natDegree :
    Fintype.card blockIdx = selected.annihilator.natDegree

attribute [instance] RationalCanonicalSelectedCompanionBlock.fintype_blockIdx
attribute [instance] RationalCanonicalSelectedCompanionBlock.decEq_blockIdx
attribute [instance] RationalCanonicalSelectedCompanionBlock.linearOrder_blockIdx

/--
The selected annihilator polynomial supplies a standard companion head block,
indexed in the ambient universe by `ULift (Fin annihilator.natDegree)`.
-/
noncomputable def rationalCanonicalSelectedCompanionBlock
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K}
    {decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A}
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) :
    RationalCanonicalSelectedCompanionBlock K ι A decomposition selected := by
  classical
  let headFin : Matrix (Fin selected.annihilator.natDegree)
      (Fin selected.annihilator.natDegree) K :=
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' selected.annihilator_monic).basis)
      (AdjoinRoot.powerBasis' selected.annihilator_monic).gen
  let head : Matrix (ULift.{u, 0} (Fin selected.annihilator.natDegree))
      (ULift.{u, 0} (Fin selected.annihilator.natDegree)) K :=
    Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm headFin
  exact
    { blockIdx := ULift.{u, 0} (Fin selected.annihilator.natDegree)
      fintype_blockIdx := inferInstance
      decEq_blockIdx := inferInstance
      linearOrder_blockIdx := inferInstance
      head := head
      head_companion := by
        simpa [head, headFin] using
          singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis_ulift
            (p := selected.annihilator)
            selected.annihilator_monic
            selected.annihilator_natDegree_pos
      block_card_eq_natDegree := by
        simp }

/--
The PID structure theorem supplies a direct sum of cyclic prime-power quotient
modules for the canonical finite torsion `K[X]`-module.
-/
noncomputable def rationalCanonicalPolynomialModuleDecompositionData
    {K : Type v} {ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K)
    (data : RationalCanonicalPolynomialModuleData K ι A :=
      rationalCanonicalPolynomialModuleData A) :
    RationalCanonicalPolynomialModuleDecompositionData K ι A := by
  classical
  letI : Module.Finite K[X] (RationalCanonicalMatrixPolynomialModule K ι A) :=
    data.finite_over_KX
  let h :=
    Module.equiv_directSum_of_isTorsion
      (R := K[X]) (M := RationalCanonicalMatrixPolynomialModule K ι A)
      data.torsion_over_KX
  let idx : Type v := Classical.choose h
  let h_idx := Classical.choose_spec h
  let fintype_idx : Fintype idx := Classical.choose h_idx
  let h_fintype := Classical.choose_spec h_idx
  let prime : idx → K[X] := Classical.choose h_fintype
  let h_prime := Classical.choose_spec h_fintype
  let prime_irreducible : ∀ i, Irreducible (prime i) := Classical.choose h_prime
  let h_irreducible := Classical.choose_spec h_prime
  let exponent : idx → Nat := Classical.choose h_irreducible
  let decomposition := Classical.choose_spec h_irreducible
  exact
    { idx := idx
      fintype_idx := fintype_idx
      prime := prime
      prime_irreducible := prime_irreducible
      exponent := exponent
      decomposition := decomposition }

/--
Data for one rational-canonical descent step extracted from the `K[X]`-module
attached to a matrix.

The fields record the similarity putting the matrix in a state where the head
cyclic summand can be removed.  The explicit `head` and `headTailBlockEq`
fields say that after this similarity and the project head-tail reindexing, the
matrix is a block diagonal one-index companion head and recursive tail slice.
The raw lift predicate consumed by the descent driver is derived from this
structured block data.
-/
structure RationalCanonicalModuleStepData
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) where
  P : Matrix ι ι K
  Pinv : Matrix ι ι K
  inverse_P : HasMatrixInverse P Pinv
  cyclic_annihilator : K[X]
  cyclic_annihilator_monic : cyclic_annihilator.Monic
  cyclic_blockSize : Nat
  cyclic_blockSize_pos : 0 < cyclic_blockSize
  cyclic_blockSize_eq_natDegree : cyclic_blockSize = cyclic_annihilator.natDegree
  head : Matrix Unit Unit K
  headTailBlockEq :
    Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι))
        (Pinv * A * P) =
      rationalCanonicalBlockDiagLex head
        (rationalCanonicalTailSlice ι (Pinv * A * P))

/--
Convert the explicit one-index head-tail block equation in module-step data into
the structured readiness payload consumed by the descent lift.
-/
def RationalCanonicalModuleStepData.headTailReady
    {K : Type v} {ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι K}
    (data : RationalCanonicalModuleStepData K ι A) :
    RationalCanonicalHeadTailBlockReady K ι (data.Pinv * A * data.P) :=
  rationalCanonicalHeadTailBlockReady_of_unit_block_eq
    data.head data.headTailBlockEq

/--
Named obligation: the `K[X]` module-structure theorem supplies the cyclic
summand data needed at every nonempty finite square matrix.

Future work should construct this bridge from `Module.equiv_directSum_of_isTorsion`
or the stronger invariant-factor form over `K[X]`, then identify the selected
cyclic summand with the head companion block.
-/
structure RationalCanonicalModuleStructureBridge
    (K : Type v) [Field K] : Type (max (u + 1) v) where
  stepData :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) → RationalCanonicalModuleStepData K ι A

/--
More specific bridge obligation: the step data must be constructed from the
canonical finite torsion `K[X]`-module attached to the matrix, not from an
arbitrary oracle.  The PID decomposition data is passed explicitly so this
bridge cannot hide the module-structure theorem behind an unstructured marker.
-/
structure RationalCanonicalPolynomialModuleBridge
    (K : Type v) [Field K] : Type (max (u + 1) (v + 1)) where
  stepData :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          RationalCanonicalPolynomialModuleDecompositionData K ι A →
          RationalCanonicalModuleStepData K ι A

/-- A polynomial-module bridge specializes to the module-structure bridge. -/
noncomputable def rationalCanonicalModuleStructureBridgeOfPolynomialModuleBridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalPolynomialModuleBridge.{u, v} K) :
    RationalCanonicalModuleStructureBridge.{u, v} K where
  stepData := fun A =>
    let data := rationalCanonicalPolynomialModuleData A
    bridge.stepData A data (rationalCanonicalPolynomialModuleDecompositionData A data)

/--
Convert the module-structure bridge into the exact one-step oracle required by
the square descent strategy.
-/
noncomputable def rationalCanonicalStepOracleOfModuleBridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalModuleStructureBridge.{u, v} K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    RationalCanonicalStepOracle K ι where
  P := fun A => (bridge.stepData A).P
  Pinv := fun A => (bridge.stepData A).Pinv
  inverse_P := fun A => (bridge.stepData A).inverse_P
  liftReady := fun A =>
    rationalCanonicalLiftReady_of_headTailBlockReady
      (bridge.stepData A).headTailReady

/--
The matrix rational-canonical theorem obtained from a `K[X]` module-structure
bridge.  The proof is routed through the project square descent framework.
-/
theorem exists_rational_canonical_matrix_module_bridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalModuleStructureBridge.{u, v} K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A := by
  let oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        RationalCanonicalStepOracle K κ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      rationalCanonicalStepOracleOfModuleBridge bridge (ι := κ)
  exact exists_rational_canonical_matrix_framework (K := K) (oracle := oracle) A

/--
Module-bridge theorem with explicit rational-canonical block witness data.

Route:
`RationalCanonicalModuleStructureBridge` →
`RationalCanonicalStepOracle` →
`exists_rational_canonical_matrix_framework` →
`RationalCanonicalBlockData`.
-/
theorem rationalCanonicalBlockData_module_bridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalModuleStructureBridge.{u, v} K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    RationalCanonicalBridgeBlockData "module-structure-bridge" A :=
  rationalCanonicalBridgeBlockData_of_blockData "module-structure-bridge"
    (rationalCanonicalBlockData_of_hasRationalCanonical
      (exists_rational_canonical_matrix_module_bridge bridge A))

/--
Matrix rational-canonical theorem from the concrete polynomial-module bridge.
The proof still routes through the square descent framework after converting
the bridge to `RationalCanonicalModuleStructureBridge`.
-/
theorem exists_rational_canonical_matrix_polynomial_module_bridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalPolynomialModuleBridge.{u, v} K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A :=
  exists_rational_canonical_matrix_module_bridge
    (rationalCanonicalModuleStructureBridgeOfPolynomialModuleBridge bridge) A

/--
Polynomial-module bridge theorem with explicit rational-canonical block witness
data.  This is bridge-heavy algebraic data, not an executable canonical-form
algorithm trace.
-/
theorem rationalCanonicalBlockData_polynomial_module_bridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalPolynomialModuleBridge.{u, v} K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    RationalCanonicalBridgeBlockData "polynomial-module-bridge" A :=
  rationalCanonicalBridgeBlockData_of_blockData "polynomial-module-bridge"
    (rationalCanonicalBlockData_of_hasRationalCanonical
      (exists_rational_canonical_matrix_polynomial_module_bridge bridge A))

/--
Finite-dimensional linear-operator entry point, obtained by choosing a
`ULift (Fin (finrank K V))` basis, converting the operator to a matrix, and
then using the matrix theorem above.  The matrix theorem is the square
descent-template result, so this wrapper does not bypass the recursive driver.
-/
theorem exists_rational_canonical_form_module_bridge
    {K : Type v} {V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (bridge : RationalCanonicalModuleStructureBridge.{u, v} K)
    (T : V →ₗ[K] V) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      HasRationalCanonical
        (K := K) (ι := ULift.{u, 0} (Fin (Module.finrank K V)))
        (LinearMap.toMatrix b b T) := by
  classical
  let b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V :=
    (Module.finBasis K V).reindex Equiv.ulift.symm
  exact ⟨b, exists_rational_canonical_matrix_module_bridge
    (K := K) (ι := ULift.{u, 0} (Fin (Module.finrank K V))) bridge
    (LinearMap.toMatrix b b T)⟩

end MatDecompFormal.Instances
