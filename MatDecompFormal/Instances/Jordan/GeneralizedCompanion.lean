/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Jordan.Generalized

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open scoped Polynomial

/-!
# Companion Powers and Generalized Jordan Blocks

This file proves the local algebraic obligation `C(p^k) ~ J(p^k)`.
-/

/-- The ordinary power-basis degree represented by one grouped `p`-power coordinate. -/
def companionPowerBasisDegree
    {K : Type u} [Field K] (p : K[X]) {k : Nat}
    (x : generalizedBlockCoord p k) : Nat :=
  (x.1 : Nat) * p.natDegree + (x.2 : Nat)

/--
The polynomial represented by one grouped basis coordinate: `p^a * X^r`.
The intended column order for `C(p^k) ~ J(p^k)` is indexed by `(a, r)`.
-/
noncomputable def companionPowerBasisPolynomial
    {K : Type u} [Field K] (p : K[X]) {k : Nat}
    (x : generalizedBlockCoord p k) : K[X] :=
  p ^ (x.1 : Nat) * Polynomial.X ^ (x.2 : Nat)

/-- Coefficient matrix from the grouped `p`-power basis to the ordinary power basis. -/
noncomputable def companionPowerBasisChange
    {K : Type u} [Field K] (p : K[X]) (k : Nat) :
    Matrix (Fin (p ^ k).natDegree) (generalizedBlockCoord p k) K :=
  fun i x => (companionPowerBasisPolynomial p x).coeff (i : Nat)

/-- The grouped coordinate degree is below the degree of `p^k`. -/
theorem companionPowerBasisDegree_lt_natDegree_pow
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic)
    (x : generalizedBlockCoord p k) :
    companionPowerBasisDegree p x < (p ^ k).natDegree := by
  rw [hp_monic.natDegree_pow]
  unfold companionPowerBasisDegree
  have hx1 : (x.1 : Nat) < k := x.1.2
  have hx2 : (x.2 : Nat) < p.natDegree := x.2.2
  have hsucc : (x.1 : Nat) + 1 ≤ k := Nat.succ_le_of_lt hx1
  calc
    (x.1 : Nat) * p.natDegree + (x.2 : Nat)
        < (x.1 : Nat) * p.natDegree + p.natDegree := Nat.add_lt_add_left hx2 _
    _ = ((x.1 : Nat) + 1) * p.natDegree := by
          rw [Nat.succ_mul]
    _ ≤ k * p.natDegree := Nat.mul_le_mul_right _ hsucc

/-- The grouped degree map is injective when `p` has positive degree. -/
theorem companionPowerBasisDegree_injective
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hpdeg : 0 < p.natDegree) :
    Function.Injective (companionPowerBasisDegree (K := K) p (k := k)) := by
  intro x y hxy
  unfold companionPowerBasisDegree at hxy
  have hx2 : (x.2 : Nat) < p.natDegree := x.2.2
  have hy2 : (y.2 : Nat) < p.natDegree := y.2.2
  have hmod :
      ((x.1 : Nat) * p.natDegree + (x.2 : Nat)) % p.natDegree =
        ((y.1 : Nat) * p.natDegree + (y.2 : Nat)) % p.natDegree := by
    rw [hxy]
  have hxmod :
      ((x.1 : Nat) * p.natDegree + (x.2 : Nat)) % p.natDegree =
        (x.2 : Nat) := by
    calc
      ((x.1 : Nat) * p.natDegree + (x.2 : Nat)) % p.natDegree
          = (p.natDegree * (x.1 : Nat) + (x.2 : Nat)) % p.natDegree := by
              rw [Nat.mul_comm]
      _ = (x.2 : Nat) % p.natDegree := by
              rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      _ = (x.2 : Nat) := Nat.mod_eq_of_lt hx2
  have hymod :
      ((y.1 : Nat) * p.natDegree + (y.2 : Nat)) % p.natDegree =
        (y.2 : Nat) := by
    calc
      ((y.1 : Nat) * p.natDegree + (y.2 : Nat)) % p.natDegree
          = (p.natDegree * (y.1 : Nat) + (y.2 : Nat)) % p.natDegree := by
              rw [Nat.mul_comm]
      _ = (y.2 : Nat) % p.natDegree := by
              rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      _ = (y.2 : Nat) := Nat.mod_eq_of_lt hy2
  have hcoord2 : (x.2 : Nat) = (y.2 : Nat) := by
    simpa [hxmod, hymod] using hmod
  have hmul :
      (x.1 : Nat) * p.natDegree = (y.1 : Nat) * p.natDegree := by
    omega
  have hcoord1 : (x.1 : Nat) = (y.1 : Nat) :=
    Nat.eq_of_mul_eq_mul_right hpdeg hmul
  apply Prod.ext
  · exact Fin.ext hcoord1
  · exact Fin.ext hcoord2

/-- The grouped basis coordinates are in bijection with the ordinary power-basis degrees. -/
noncomputable def companionPowerBasisDegreeEquiv
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p) :
    generalizedBlockCoord p k ≃ Fin (p ^ k).natDegree :=
  Equiv.ofBijective
    (fun x =>
      ⟨companionPowerBasisDegree p x,
        companionPowerBasisDegree_lt_natDegree_pow hp_monic x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨
      by
        intro x y hxy
        apply companionPowerBasisDegree_injective (K := K) (p := p)
          (k := k) hp_irred.natDegree_pos
        exact congrArg Fin.val hxy,
      by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
          hp_monic.natDegree_pow]
        simp
    ⟩)

@[simp] theorem companionPowerBasisDegreeEquiv_apply
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p)
    (x : generalizedBlockCoord p k) :
    (companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
      hp_monic hp_irred x : Nat) =
      companionPowerBasisDegree p x :=
  rfl

/-- The grouped basis polynomial has the expected degree. -/
theorem companionPowerBasisPolynomial_natDegree
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (x : generalizedBlockCoord p k) :
    (companionPowerBasisPolynomial p x).natDegree =
      companionPowerBasisDegree p x := by
  classical
  unfold companionPowerBasisPolynomial companionPowerBasisDegree
  rw [(hp_monic.pow (x.1 : Nat)).natDegree_mul (Polynomial.monic_X.pow (x.2 : Nat))]
  rw [hp_monic.natDegree_pow, Polynomial.natDegree_X_pow]

/-- Coefficients above the grouped basis degree vanish. -/
theorem companionPowerBasisChange_eq_zero_of_degree_lt
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (i : Fin (p ^ k).natDegree)
    (x : generalizedBlockCoord p k)
    (hix : companionPowerBasisDegree p x < (i : Nat)) :
    companionPowerBasisChange p k i x = 0 := by
  unfold companionPowerBasisChange
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((companionPowerBasisPolynomial_natDegree hp_monic x).trans_lt hix)

/-- The leading coefficient of every grouped basis polynomial is `1`. -/
theorem companionPowerBasisChange_degree_eq_one
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic)
    (x : generalizedBlockCoord p k) :
    companionPowerBasisChange p k
      ⟨companionPowerBasisDegree p x,
        companionPowerBasisDegree_lt_natDegree_pow hp_monic x⟩ x = 1 := by
  classical
  unfold companionPowerBasisChange companionPowerBasisPolynomial companionPowerBasisDegree
  rw [Polynomial.coeff_mul_X_pow]
  have hdeg : (p ^ (x.1 : Nat)).natDegree = (x.1 : Nat) * p.natDegree :=
    hp_monic.natDegree_pow (x.1 : Nat)
  simpa [hdeg] using (hp_monic.pow (x.1 : Nat)).coeff_natDegree

/--
After ordering columns by their grouped degree, the coefficient change matrix
has determinant `1`.
-/
theorem companionPowerBasisChange_reindex_det
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p) :
    ((Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree))
      (companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
        hp_monic hp_irred)
      (companionPowerBasisChange p k) :
        Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K)).det = (1 : K) := by
  classical
  let e := companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
    hp_monic hp_irred
  let q : Fin (p ^ k).natDegree → K[X] :=
    fun i => companionPowerBasisPolynomial p (e.symm i)
  have hdeg : ∀ i, (q i).natDegree = i := by
    intro i
    have h := companionPowerBasisPolynomial_natDegree hp_monic (e.symm i)
    have he : companionPowerBasisDegree p (e.symm i) = (i : Nat) := by
      exact congrArg Fin.val (e.apply_symm_apply i)
    exact h.trans he
  have hmonic : ∀ i, (q i).Monic := by
    intro i
    simpa [q, companionPowerBasisPolynomial] using
      (hp_monic.pow ((e.symm i).1 : Nat)).mul
        (Polynomial.monic_X.pow ((e.symm i).2 : Nat))
  simpa [Matrix.reindex_apply, companionPowerBasisChange, q, e] using
    Matrix.det_matrixOfPolynomials q hdeg hmonic

/-- The grouped coefficient change matrix is invertible. -/
theorem companionPowerBasisChange_invertible
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p) :
    InvertibleMatrix ((Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree))
      (companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
        hp_monic hp_irred)
      (companionPowerBasisChange p k) :
        Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K)) := by
  classical
  change IsUnit ((Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree))
      (companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
        hp_monic hp_irred)
      (companionPowerBasisChange p k) :
        Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K))
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [companionPowerBasisChange_reindex_det hp_monic hp_irred]
  exact isUnit_one

/--
Each column of the grouped coefficient matrix is the standard `AdjoinRoot`
power-basis coordinate vector of the corresponding polynomial.
-/
theorem companionPowerBasisChange_reindex_apply_eq_powerBasis_repr
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p)
    (i : Fin (p ^ k).natDegree) (x : Fin (p ^ k).natDegree) :
    ((Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree))
      (companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
        hp_monic hp_irred)
      (companionPowerBasisChange p k) :
        Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K) i x) =
      ((AdjoinRoot.powerBasis' (hp_monic.pow k)).basis.repr
        (AdjoinRoot.mk (p ^ k)
          (companionPowerBasisPolynomial p
            ((companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
              hp_monic hp_irred).symm x)))) i := by
  classical
  let e := companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
    hp_monic hp_irred
  let q : K[X] := companionPowerBasisPolynomial p (e.symm x)
  have hqnat :
      q.natDegree = companionPowerBasisDegree p (e.symm x) := by
    simpa [q] using companionPowerBasisPolynomial_natDegree hp_monic (e.symm x)
  have hdeglt : q.degree < (p ^ k).degree := by
    exact Polynomial.degree_lt_degree (by
      simpa [q, hqnat, e] using companionPowerBasisDegree_lt_natDegree_pow hp_monic (e.symm x))
  have hmod : q %ₘ (p ^ k) = q := by
    rw [Polynomial.modByMonic_eq_self_iff (hp_monic.pow k)]
    exact hdeglt
  change
    ((Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree))
      (companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
        hp_monic hp_irred)
      (companionPowerBasisChange p k) :
        Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K) i x) =
      ((AdjoinRoot.powerBasisAux' (hp_monic.pow k)).repr
        (AdjoinRoot.mk (p ^ k)
          (companionPowerBasisPolynomial p
            ((companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
              hp_monic hp_irred).symm x)))) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk, hmod]
  simp [Matrix.reindex_apply, companionPowerBasisChange, q, e]

/--
The reindexed grouped coefficient matrix is the power-basis coordinate matrix
of the grouped `AdjoinRoot` columns.
-/
theorem companionPowerBasisChange_reindex_eq_powerBasis_toMatrix
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p) :
    let e := companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
      hp_monic hp_irred
    let v : Fin (p ^ k).natDegree → AdjoinRoot (p ^ k) :=
      fun j => AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p (e.symm j))
    (AdjoinRoot.powerBasis' (hp_monic.pow k)).basis.toMatrix v =
      (Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree)) e
        (companionPowerBasisChange p k) :
          Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K) := by
  classical
  intro e v
  ext i j
  rw [Module.Basis.toMatrix_apply]
  exact (companionPowerBasisChange_reindex_apply_eq_powerBasis_repr
    hp_monic hp_irred i j).symm

/-- The companion matrix is root multiplication in the standard `AdjoinRoot` power basis. -/
theorem companionMatrixFin_eq_adjoinRoot_leftMulMatrix_powerBasis
    {K : Type u} [Field K] {p : K[X]} (hp_monic : p.Monic) :
    companionMatrixFin p =
      (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp_monic).basis)
        (AdjoinRoot.powerBasis' hp_monic).gen := by
  ext i j
  have hminpolyGen : (AdjoinRoot.powerBasis' hp_monic).minpolyGen = p := by
    rw [PowerBasis.minpolyGen_eq]
    rw [AdjoinRoot.powerBasis'_gen]
    simpa [hp_monic.leadingCoeff] using (AdjoinRoot.minpoly_root hp_monic.ne_zero)
  rw [PowerBasis.leftMulMatrix]
  change
    companionMatrixFin p i j =
      (if (j : Nat) + 1 = (AdjoinRoot.powerBasis' hp_monic).dim then
        -((AdjoinRoot.powerBasis' hp_monic).minpolyGen).coeff (i : Nat)
      else if (i : Nat) = (j : Nat) + 1 then 1 else 0)
  simp only [hminpolyGen, AdjoinRoot.powerBasis'_dim]
  by_cases hlast : (j : Nat) + 1 = p.natDegree
  · have hnot_shift : ¬(j : Nat) + 1 = (i : Nat) := by
      intro hji
      have hi_eq : (i : Nat) = p.natDegree := by omega
      exact Nat.ne_of_lt i.2 hi_eq
    unfold companionMatrixFin
    rw [if_pos hlast, if_neg hnot_shift]
    have hjlast : (j : Nat) = p.natDegree - 1 := by omega
    rw [if_pos hjlast]
  · have hnot_last : ¬(j : Nat) = p.natDegree - 1 := by
      intro hj
      have : (j : Nat) + 1 = p.natDegree := by omega
      exact hlast this
    by_cases hshift : (i : Nat) = (j : Nat) + 1
    · have hshift' : (j : Nat) + 1 = (i : Nat) := by omega
      unfold companionMatrixFin
      rw [if_neg hlast, if_pos hshift', if_pos hshift]
    · have hshift' : ¬(j : Nat) + 1 = (i : Nat) := by omega
      unfold companionMatrixFin
      rw [if_neg hlast, if_neg hshift', if_neg hnot_last, if_neg hshift]

/-- Multiplication by the adjoined root is multiplication by `X` before quotienting. -/
theorem adjoinRoot_root_mul_mk
    {K : Type u} [Field K] (q f : K[X]) :
    AdjoinRoot.root q * AdjoinRoot.mk q f =
      AdjoinRoot.mk q (Polynomial.X * f) := by
  rw [← AdjoinRoot.mk_X, ← RingHom.map_mul]

/--
In `AdjoinRoot (p ^ k)`, multiplying the grouped basis vector `p^a X^(deg p - 1)`
by the adjoined root expands through the monic relation for `p`.
-/
theorem adjoinRoot_mk_monic_degree_relation
    {K : Type u} [Field K] {p : K[X]} {k a : Nat}
    (hp : p.Monic) :
    AdjoinRoot.mk (p ^ k) (p ^ a * Polynomial.X ^ p.natDegree) =
      AdjoinRoot.mk (p ^ k) (p ^ (a + 1)) -
        ∑ i ∈ Finset.range p.natDegree,
          p.coeff i •
            AdjoinRoot.mk (p ^ k) (p ^ a * Polynomial.X ^ i) := by
  have hmul : p ^ a * Polynomial.X ^ p.natDegree =
      p ^ (a + 1) -
        ∑ i ∈ Finset.range p.natDegree,
          Polynomial.C (p.coeff i) * (p ^ a * Polynomial.X ^ i) := by
    have hX : Polynomial.X ^ p.natDegree =
        p - ∑ i ∈ Finset.range p.natDegree,
          Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
      have hp_sum := hp.as_sum
      nth_rewrite 2 [hp_sum]
      abel
    calc
      p ^ a * Polynomial.X ^ p.natDegree
          = p ^ a * (p - ∑ i ∈ Finset.range p.natDegree,
            Polynomial.C (p.coeff i) * Polynomial.X ^ i) := by rw [hX]
      _ = p ^ (a + 1) -
          ∑ i ∈ Finset.range p.natDegree,
            Polynomial.C (p.coeff i) * (p ^ a * Polynomial.X ^ i) := by
          rw [mul_sub, Finset.mul_sum]
          have hpowa : p ^ a * p = p ^ (a + 1) := by rw [pow_succ]
          rw [hpowa]
          congr 1
          apply Finset.sum_congr rfl
          intro i _hi
          ring
  rw [hmul]
  simp [Algebra.smul_def]

/-- `Fin`-indexed form of `adjoinRoot_mk_monic_degree_relation`. -/
theorem adjoinRoot_mk_monic_degree_relation_fin
    {K : Type u} [Field K] {p : K[X]} {k a : Nat}
    (hp : p.Monic) :
    AdjoinRoot.mk (p ^ k) (p ^ a * Polynomial.X ^ p.natDegree) =
      AdjoinRoot.mk (p ^ k) (p ^ (a + 1)) -
        ∑ i : Fin p.natDegree,
          p.coeff (i : Nat) •
            AdjoinRoot.mk (p ^ k) (p ^ a * Polynomial.X ^ (i : Nat)) := by
  rw [adjoinRoot_mk_monic_degree_relation (p := p) (k := k) (a := a) hp]
  congr 1
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

/-- Away from the last companion column, root multiplication just shifts `X^r` to `X^(r+1)`. -/
theorem generalizedJordanBlock_action_nonlast
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (a : Fin k) (r : Fin p.natDegree)
    (hr : (r : Nat) + 1 < p.natDegree) :
    ∑ y : generalizedBlockCoord p k,
        generalizedJordanBlock p k y (a, r) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y) =
      AdjoinRoot.mk (p ^ k)
        (companionPowerBasisPolynomial p (a, ⟨(r : Nat) + 1, hr⟩)) := by
  classical
  let target : generalizedBlockCoord p k := (a, ⟨(r : Nat) + 1, hr⟩)
  rw [Fintype.sum_eq_single target]
  · simp [target, generalizedJordanBlock, companionMatrixFin,
      companionPowerBasisPolynomial]
  · intro y hy
    rcases y with ⟨b, s⟩
    by_cases hba : b = a
    · subst b
      have hsne : s ≠ ⟨(r : Nat) + 1, hr⟩ := by
        intro hs
        apply hy
        simp [target, hs]
      have hnot : ¬ (r : Nat) + 1 = (s : Nat) := by
        intro hrs
        exact hsne (Fin.ext hrs.symm)
      have hnotlast : ¬ (r : Nat) = p.natDegree - 1 := by omega
      simp [generalizedJordanBlock, companionMatrixFin,
        companionPowerBasisPolynomial, hnot, hnotlast]
    · simp [generalizedJordanBlock, generalizedJordanConnector,
        companionPowerBasisPolynomial, hba]
      intro _hsucc _hs0 hlast
      exact False.elim ((ne_of_lt hr) hlast)

/-- The diagonal companion part of a last grouped column contributes the lower coefficients. -/
theorem generalizedJordanBlock_action_last_diagonal
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (a : Fin k) (r : Fin p.natDegree)
    (hrlast : (r : Nat) + 1 = p.natDegree) :
    ∑ y : generalizedBlockCoord p k,
        (if y.1 = a then companionMatrixFin p y.2 r else 0) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y) =
      -∑ s : Fin p.natDegree,
          p.coeff (s : Nat) •
            AdjoinRoot.mk (p ^ k) (p ^ (a : Nat) * Polynomial.X ^ (s : Nat)) := by
  classical
  have hpos : 0 < p.natDegree := Nat.lt_of_le_of_lt (Nat.zero_le _) r.2
  have hnot_shift_last : ∀ s : Fin p.natDegree,
      ¬ p.natDegree - 1 + 1 = (s : Nat) := by
    intro s hs
    have hsdeg : (s : Nat) = p.natDegree := by omega
    exact Nat.ne_of_lt s.2 hsdeg
  have hrlast' : (r : Nat) = p.natDegree - 1 := by omega
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single a]
  · simp [companionMatrixFin, companionPowerBasisPolynomial, hrlast',
      hnot_shift_last]
  · intro b hba
    simp [hba]

/-- The off-diagonal connector of a last grouped column advances to the next `p`-power. -/
theorem generalizedJordanBlock_action_last_connector
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (a : Fin k) (r : Fin p.natDegree)
    (hrlast : (r : Nat) + 1 = p.natDegree)
    (hanot : (a : Nat) + 1 < k) :
    ∑ y : generalizedBlockCoord p k,
        ((if (a : Nat) + 1 = (y.1 : Nat) then
            generalizedJordanConnector p.natDegree y.2 r
          else 0 : K)) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y) =
      AdjoinRoot.mk (p ^ k) (p ^ ((a : Nat) + 1)) := by
  classical
  have hpdeg_pos : 0 < p.natDegree := by omega
  rw [Fintype.sum_eq_single
    ((⟨(a : Nat) + 1, hanot⟩ : Fin k), (⟨0, hpdeg_pos⟩ : Fin p.natDegree))]
  · simp [generalizedJordanConnector, companionPowerBasisPolynomial, hrlast]
  · intro y hy
    rcases y with ⟨b, s⟩
    by_cases hb : (a : Nat) + 1 = (b : Nat)
    · have hbfin : b = ⟨(a : Nat) + 1, hanot⟩ := Fin.ext hb.symm
      subst b
      have hsne : s ≠ ⟨0, hpdeg_pos⟩ := by
        intro hs
        apply hy
        cases hs
        rfl
      have hs0 : ¬ (s : Nat) = 0 := by
        intro hs
        exact hsne (Fin.ext hs)
      have hconnzero : (generalizedJordanConnector p.natDegree s r : K) = 0 := by
        unfold generalizedJordanConnector
        rw [if_neg]
        intro h
        exact hs0 h.1
      rw [if_pos hb, hconnzero, zero_smul]
    · rw [if_neg hb, zero_smul]

/-- Last grouped columns with a following layer combine the companion tail and connector. -/
theorem generalizedJordanBlock_action_last_not_top
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (a : Fin k) (r : Fin p.natDegree)
    (hrlast : (r : Nat) + 1 = p.natDegree)
    (hanot : (a : Nat) + 1 < k) :
    ∑ y : generalizedBlockCoord p k,
        generalizedJordanBlock p k y (a, r) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y) =
      AdjoinRoot.mk (p ^ k) (p ^ ((a : Nat) + 1)) -
        ∑ s : Fin p.natDegree,
          p.coeff (s : Nat) •
            AdjoinRoot.mk (p ^ k) (p ^ (a : Nat) * Polynomial.X ^ (s : Nat)) := by
  classical
  have hsplit :
      (∑ y : generalizedBlockCoord p k,
        generalizedJordanBlock p k y (a, r) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y)) =
      (∑ y : generalizedBlockCoord p k,
        (if y.1 = a then companionMatrixFin p y.2 r else 0) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y)) +
      (∑ y : generalizedBlockCoord p k,
        ((if (a : Nat) + 1 = (y.1 : Nat) then
            generalizedJordanConnector p.natDegree y.2 r
          else 0 : K)) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _hy
    by_cases hya : y.1 = a
    · have hnotconn : ¬ (a : Nat) + 1 = (y.1 : Nat) := by
        rw [hya]
        omega
      simp [generalizedJordanBlock, hya]
    · by_cases hyconn : (a : Nat) + 1 = (y.1 : Nat)
      · simp [generalizedJordanBlock, hya, hyconn]
      · simp [generalizedJordanBlock, hya, hyconn]
  rw [hsplit]
  rw [generalizedJordanBlock_action_last_diagonal (a := a) (r := r) hrlast]
  rw [generalizedJordanBlock_action_last_connector (a := a) (r := r) hrlast hanot]
  abel

/-- Last grouped columns in the top layer have no connector contribution. -/
theorem generalizedJordanBlock_action_last_top
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (a : Fin k) (r : Fin p.natDegree)
    (hrlast : (r : Nat) + 1 = p.natDegree)
    (halast : (a : Nat) + 1 = k) :
    ∑ y : generalizedBlockCoord p k,
        generalizedJordanBlock p k y (a, r) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y) =
      -∑ s : Fin p.natDegree,
          p.coeff (s : Nat) •
            AdjoinRoot.mk (p ^ k) (p ^ (a : Nat) * Polynomial.X ^ (s : Nat)) := by
  classical
  have hsplit :
      (∑ y : generalizedBlockCoord p k,
        generalizedJordanBlock p k y (a, r) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y)) =
      (∑ y : generalizedBlockCoord p k,
        (if y.1 = a then companionMatrixFin p y.2 r else 0) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y)) := by
    apply Finset.sum_congr rfl
    intro y _hy
    by_cases hya : y.1 = a
    · have hnotconn : ¬ (a : Nat) + 1 = (y.1 : Nat) := by
        rw [hya]
        omega
      simp [generalizedJordanBlock, hya]
    · have hnotconn : ¬ (a : Nat) + 1 = (y.1 : Nat) := by
        intro h
        have hyk : (y.1 : Nat) = k := by omega
        exact Nat.ne_of_lt y.1.2 hyk
      simp [generalizedJordanBlock, hya, hnotconn]
  rw [hsplit]
  exact generalizedJordanBlock_action_last_diagonal (a := a) (r := r) hrlast

/-- Multiplication by the adjoined root has generalized-Jordan columns in the grouped basis. -/
theorem generalizedJordanBlock_grouped_action
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp : p.Monic) (x : generalizedBlockCoord p k) :
    AdjoinRoot.root (p ^ k) *
        AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p x) =
      ∑ y : generalizedBlockCoord p k,
        generalizedJordanBlock p k y x •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y) := by
  classical
  rcases x with ⟨a, r⟩
  rw [adjoinRoot_root_mul_mk]
  by_cases hrlast : (r : Nat) + 1 = p.natDegree
  · have hXpow : ((Polynomial.X : K[X]) ^ ((r : Nat) + 1)) =
        (Polynomial.X : K[X]) ^ p.natDegree := by
      exact congrArg (fun n => ((Polynomial.X : K[X]) ^ n)) hrlast
    have hX : Polynomial.X * (p ^ (a : Nat) * Polynomial.X ^ (r : Nat)) =
        p ^ (a : Nat) * Polynomial.X ^ p.natDegree := by
      calc
        Polynomial.X * (p ^ (a : Nat) * Polynomial.X ^ (r : Nat))
            = p ^ (a : Nat) * Polynomial.X ^ ((r : Nat) + 1) := by ring
        _ = p ^ (a : Nat) * Polynomial.X ^ p.natDegree := by rw [hXpow]
    rw [companionPowerBasisPolynomial, hX]
    by_cases hanot : (a : Nat) + 1 < k
    · rw [generalizedJordanBlock_action_last_not_top (a := a) (r := r) hrlast hanot]
      exact adjoinRoot_mk_monic_degree_relation_fin
        (p := p) (k := k) (a := (a : Nat)) hp
    · have halast : (a : Nat) + 1 = k := by omega
      rw [generalizedJordanBlock_action_last_top (a := a) (r := r) hrlast halast]
      have hrel := adjoinRoot_mk_monic_degree_relation_fin
        (p := p) (k := k) (a := (a : Nat)) hp
      have hpkzero : AdjoinRoot.mk (p ^ k) (p ^ ((a : Nat) + 1)) = 0 := by
        rw [halast]
        exact (AdjoinRoot.mk_self : AdjoinRoot.mk (p ^ k) (p ^ k) = 0)
      rw [hpkzero] at hrel
      simpa using hrel
  · have hrlt : (r : Nat) + 1 < p.natDegree := by omega
    rw [generalizedJordanBlock_action_nonlast (a := a) (r := r) hrlt]
    simp [companionPowerBasisPolynomial]
    ring

/-- Reindexed grouped action as a column-vector identity. -/
theorem generalizedJordanBlock_reindexed_column_action
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p) :
    let e := companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
      hp_monic hp_irred
    let v : Fin (p ^ k).natDegree → AdjoinRoot (p ^ k) :=
      fun j => AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p (e.symm j))
    let J : Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K :=
      Matrix.reindex e e (generalizedJordanBlock p k)
    (fun j => AdjoinRoot.root (p ^ k) * v j) =
      (fun j => ∑ y : Fin (p ^ k).natDegree, J y j • v y) := by
  classical
  intro e v J
  funext j
  have h := generalizedJordanBlock_grouped_action hp_monic (e.symm j)
  rw [h]
  change (∑ y : generalizedBlockCoord p k,
        generalizedJordanBlock p k y (e.symm j) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y)) =
      ∑ y : Fin (p ^ k).natDegree,
        generalizedJordanBlock p k (e.symm y) (e.symm j) •
          AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p (e.symm y))
  exact Fintype.sum_equiv e
    (fun y => generalizedJordanBlock p k y (e.symm j) •
      AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p y))
    (fun y => generalizedJordanBlock p k (e.symm y) (e.symm j) •
      AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p (e.symm y)))
    (by intro x; simp)

/-- Coordinates of a finite linear combination of columns are obtained by right
multiplication by the coefficient matrix. -/
lemma basis_toMatrix_linearCombination_columns
    {K : Type u} [Field K]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Type*} [AddCommGroup M] [Module K M]
    (b : Module.Basis ι K M) (v : κ → M) (J : Matrix κ κ K) :
    b.toMatrix (fun j => ∑ y : κ, J y j • v y) = b.toMatrix v * J := by
  classical
  ext i j
  rw [Matrix.mul_apply, Module.Basis.toMatrix_apply]
  simp [Module.Basis.toMatrix_apply, map_sum, map_smul, smul_eq_mul, mul_comm]

/-- The grouped coefficient change matrix intertwines `C(p^k)` with `J(p,k)`. -/
theorem companionPowerBasisChange_intertwines
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p) :
    let e := companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
      hp_monic hp_irred
    let P : Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K :=
      Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree)) e
        (companionPowerBasisChange p k)
    let J : Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K :=
      Matrix.reindex e e (generalizedJordanBlock p k)
    companionMatrixFin (p ^ k) * P = P * J := by
  classical
  intro e P J
  let b := (AdjoinRoot.powerBasis' (hp_monic.pow k)).basis
  let v : Fin (p ^ k).natDegree → AdjoinRoot (p ^ k) :=
    fun j => AdjoinRoot.mk (p ^ k) (companionPowerBasisPolynomial p (e.symm j))
  have hP : b.toMatrix v = P := by
    simpa [b, v, P, e] using
      companionPowerBasisChange_reindex_eq_powerBasis_toMatrix
        (K := K) (p := p) (k := k) hp_monic hp_irred
  have hleft : companionMatrixFin (p ^ k) =
      Algebra.leftMulMatrix b (AdjoinRoot.root (p ^ k)) := by
    simpa [b, AdjoinRoot.powerBasis'_gen] using
      companionMatrixFin_eq_adjoinRoot_leftMulMatrix_powerBasis
        (K := K) (p := p ^ k) (hp_monic.pow k)
  have hsmul : (fun j => AdjoinRoot.root (p ^ k) * v j) =
      fun j => ∑ y : Fin (p ^ k).natDegree, J y j • v y := by
    simpa [v, J, e] using
      generalizedJordanBlock_reindexed_column_action
        (K := K) (p := p) (k := k) hp_monic hp_irred
  calc
    companionMatrixFin (p ^ k) * P
        = Algebra.leftMulMatrix b (AdjoinRoot.root (p ^ k)) * b.toMatrix v := by
            rw [hleft, ← hP]
    _ = b.toMatrix (fun j => AdjoinRoot.root (p ^ k) • v j) := by
            exact (Module.Basis.toMatrix_smul (AdjoinRoot.root (p ^ k)) b v).symm
    _ = b.toMatrix (fun j => AdjoinRoot.root (p ^ k) * v j) := by rfl
    _ = b.toMatrix (fun j => ∑ y : Fin (p ^ k).natDegree, J y j • v y) := by
            rw [hsmul]
    _ = P * J := by
            rw [basis_toMatrix_linearCombination_columns b v J, hP]

/-- The standard companion matrix of `p^k` has generalized Jordan form. -/
theorem companionMatrixFin_power_hasGeneralizedJordan
    {K : Type u} [Field K] {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p) (hk : 0 < k) :
    HasGeneralizedJordanMatrix (companionMatrixFin (p ^ k)) := by
  classical
  let e := companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
    hp_monic hp_irred
  let P : Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K :=
    Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree)) e
      (companionPowerBasisChange p k)
  let J : Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K :=
    Matrix.reindex e e (generalizedJordanBlock p k)
  have hP : InvertibleMatrix P := by
    simpa [P, e] using companionPowerBasisChange_invertible
      (K := K) (p := p) (k := k) hp_monic hp_irred
  have hJ : IsGeneralizedJordanMatrix J := by
    exact isGeneralizedJordanMatrix_reindex (K := K) (ι := generalizedBlockCoord p k)
      (κ := Fin (p ^ k).natDegree) e
      (isGeneralizedJordanMatrix_generalizedJordanBlock p k hp_monic hp_irred hk)
  have hEq : companionMatrixFin (p ^ k) * P = P * J := by
    simpa [P, J, e] using companionPowerBasisChange_intertwines
      (K := K) (p := p) (k := k) hp_monic hp_irred
  refine ⟨P, J, hP, hJ, ?_⟩
  haveI : Invertible P := hP.invertible
  calc
    companionMatrixFin (p ^ k)
        = companionMatrixFin (p ^ k) * (P * P⁻¹) := by
            rw [Matrix.mul_inv_of_invertible]
            simp
    _ = (companionMatrixFin (p ^ k) * P) * P⁻¹ := by rw [Matrix.mul_assoc]
    _ = (P * J) * P⁻¹ := by rw [hEq]
    _ = P * J * P⁻¹ := by rw [Matrix.mul_assoc]

/--
Universe-lifted generalized-Jordan data for a reindexed single generalized
block.  This is the packaging step needed when a companion block is indexed by
an arbitrary finite type rather than `Fin (p^k).natDegree`.
-/
theorem isGeneralizedJordanMatrix_reindex_single_generalizedBlock
    {K : Type u} {ι : Type v} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {p : K[X]} {k : Nat}
    (hp_monic : p.Monic) (hp_irred : Irreducible p) (hk : 0 < k)
    (eC : ι ≃ Fin (p ^ k).natDegree) :
    IsGeneralizedJordanMatrix
      (Matrix.reindex eC.symm eC.symm
        (Matrix.reindex
          (companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
            hp_monic hp_irred)
          (companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
            hp_monic hp_irred)
          (generalizedJordanBlock p k))) := by
  classical
  let e := companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
    hp_monic hp_irred
  let blockTy := ULift.{v, 0} (Fin 1)
  let ueq := Equiv.uniqueSigma (fun _ : blockTy => generalizedBlockCoord p k)
  let blockEquiv : ι ≃ (b : blockTy) × generalizedBlockCoord p k :=
    eC.trans (e.symm.trans ueq.symm)
  refine ⟨{
    block := blockTy
    poly := fun _ => p
    poly_monic := fun _ => hp_monic
    poly_irreducible := fun _ => hp_irred
    exponent := fun _ => k
    exponent_pos := fun _ => hk
    total_size := ?_
    blockIndexEquiv := blockEquiv
    block_form := ?_
  }⟩
  · rw [Fintype.card_congr eC]
    simp [blockTy, hp_monic.natDegree_pow]
  · ext x y
    rcases x with ⟨bx, ix⟩
    rcases y with ⟨bY, iy⟩
    have hbx : bx = default := Subsingleton.elim _ _
    have hbY : bY = default := Subsingleton.elim _ _
    subst bx
    subst bY
    have hueq_ix : ueq ⟨(default : blockTy), ix⟩ = ix := rfl
    have hueq_iy : ueq ⟨(default : blockTy), iy⟩ = iy := rfl
    simp [blockEquiv, blockTy, e, ueq, Matrix.reindex_apply,
      Matrix.blockDiagonal', hueq_ix, hueq_iy]

/--
A companion block for `p^k`, where `p` is monic irreducible and `k > 0`, has
generalized Jordan form.
-/
theorem companion_power_hasGeneralizedJordan
    {K : Type u} {ι : Type v} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]} (k : Nat)
    (hp_monic : p.Monic)
    (hp_irred : Irreducible p)
    (hk : 0 < k)
    (hC : SingleCompanionBlockForm C (p ^ k)) :
    HasGeneralizedJordanMatrix C := by
  classical
  rcases hC.2.2.2 with ⟨eC, heC⟩
  let e := companionPowerBasisDegreeEquiv (K := K) (p := p) (k := k)
    hp_monic hp_irred
  let Pstd : Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K :=
    Matrix.reindex (Equiv.refl (Fin (p ^ k).natDegree)) e
      (companionPowerBasisChange p k)
  let Jstd : Matrix (Fin (p ^ k).natDegree) (Fin (p ^ k).natDegree) K :=
    Matrix.reindex e e (generalizedJordanBlock p k)
  let P : Matrix ι ι K := Matrix.reindex eC.symm eC.symm Pstd
  let J : Matrix ι ι K := Matrix.reindex eC.symm eC.symm Jstd
  have hPstd : InvertibleMatrix Pstd := by
    simpa [Pstd, e] using companionPowerBasisChange_invertible
      (K := K) (p := p) (k := k) hp_monic hp_irred
  have hP : InvertibleMatrix P := by
    exact invertibleMatrix_reindex eC.symm hPstd
  have hJ : IsGeneralizedJordanMatrix J := by
    simpa [J, Jstd, e] using
      isGeneralizedJordanMatrix_reindex_single_generalizedBlock
        (K := K) (ι := ι) (p := p) (k := k) hp_monic hp_irred hk eC
  have hEqStd : companionMatrixFin (p ^ k) * Pstd = Pstd * Jstd := by
    simpa [Pstd, Jstd, e] using companionPowerBasisChange_intertwines
      (K := K) (p := p) (k := k) hp_monic hp_irred
  refine ⟨P, J, hP, hJ, ?_⟩
  haveI : Invertible Pstd := hPstd.invertible
  have hStdSim : companionMatrixFin (p ^ k) = Pstd * Jstd * Pstd⁻¹ := by
    calc
      companionMatrixFin (p ^ k)
          = companionMatrixFin (p ^ k) * (Pstd * Pstd⁻¹) := by
              rw [Matrix.mul_inv_of_invertible]
              simp
      _ = (companionMatrixFin (p ^ k) * Pstd) * Pstd⁻¹ := by rw [Matrix.mul_assoc]
      _ = (Pstd * Jstd) * Pstd⁻¹ := by rw [hEqStd]
      _ = Pstd * Jstd * Pstd⁻¹ := by rw [Matrix.mul_assoc]
  haveI : Invertible P := hP.invertible
  have hPinv : P⁻¹ = Matrix.reindex eC.symm eC.symm Pstd⁻¹ := by
    apply Matrix.inv_eq_right_inv
    have h := congrArg (Matrix.reindex eC.symm eC.symm)
      (Matrix.mul_inv_of_invertible Pstd)
    simp [P, Matrix.submatrix_mul_equiv] at h ⊢
  have hCback : Matrix.reindex eC.symm eC.symm (companionMatrixFin (p ^ k)) = C := by
    have h := congrArg (Matrix.reindex eC.symm eC.symm) heC
    simpa [reindex_reindex] using h.symm
  calc
    C = Matrix.reindex eC.symm eC.symm (companionMatrixFin (p ^ k)) := hCback.symm
    _ = Matrix.reindex eC.symm eC.symm (Pstd * Jstd * Pstd⁻¹) := by rw [hStdSim]
    _ = P * J * P⁻¹ := by
        simp [P, J, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]

/-- The one-layer generalized block index is just the companion-block index. -/
noncomputable def generalizedJordanBlockOneEquiv
    {K : Type u} [Field K] (p : K[X]) :
    generalizedBlockCoord p 1 ≃ Fin p.natDegree where
  toFun x := x.2
  invFun i := (0, i)
  left_inv := by
    intro x
    apply Prod.ext
    · apply Fin.ext
      omega
    · rfl
  right_inv := by
    intro i
    rfl

/--
For exponent one, the generalized Jordan block is exactly the companion block
after dropping the unique chain coordinate.
-/
theorem generalizedJordanBlock_one_reindex_companionMatrixFin
    {K : Type u} [Field K] (p : K[X]) :
    Matrix.reindex (generalizedJordanBlockOneEquiv p)
      (generalizedJordanBlockOneEquiv p)
      (generalizedJordanBlock p 1) =
        companionMatrixFin p := by
  ext i j
  simp [Matrix.reindex_apply, generalizedJordanBlockOneEquiv,
    generalizedJordanBlock]

/-- Concrete exponent-one case of the companion-power/generalized-Jordan theorem. -/
theorem companion_power_one_hasGeneralizedJordan
    {K : Type u} {ι : Type v} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (hp_monic : p.Monic)
    (hp_irred : Irreducible p)
    (hC : SingleCompanionBlockForm C (p ^ (1 : Nat))) :
    HasGeneralizedJordanMatrix C := by
  classical
  have hCp : SingleCompanionBlockForm C p := by
    simpa using hC
  rcases hCp.2.2.2 with ⟨e, he⟩
  refine ⟨1, C, invertibleMatrix_one, ?_, ?_⟩
  · refine ⟨{
      block := PUnit
      poly := fun _ => p
      poly_monic := fun _ => hp_monic
      poly_irreducible := fun _ => hp_irred
      exponent := fun _ => 1
      exponent_pos := fun _ => by decide
      total_size := ?_
      blockIndexEquiv :=
        e.trans <|
          (generalizedJordanBlockOneEquiv p).symm.trans <|
            (Equiv.uniqueSigma
              (fun _ : PUnit => generalizedBlockCoord p 1)).symm
      block_form := ?_
    }⟩
    · simpa using hCp.2.2.1
    · ext x y
      rcases x with ⟨bx, ix⟩
      rcases y with ⟨bY, iy⟩
      cases bx
      cases bY
      have hentry :=
        congrFun (congrFun he ((generalizedJordanBlockOneEquiv p) ix))
          ((generalizedJordanBlockOneEquiv p) iy)
      have hgen :=
        congrFun
          (congrFun (generalizedJordanBlock_one_reindex_companionMatrixFin p)
            ((generalizedJordanBlockOneEquiv p) ix))
          ((generalizedJordanBlockOneEquiv p) iy)
      simpa [Matrix.reindex_apply, Matrix.blockDiagonal',
        Equiv.uniqueSigma_apply] using hentry.trans hgen.symm
  · simp

end MatDecompFormal.Instances
