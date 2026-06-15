import Mathlib.Data.Complex.Basic
import MatDecompFormal.Instances.Jordan.GeneralizedExistence

universe u v

namespace MatDecompFormal.Instances

open Matrix
open scoped Polynomial

/-!
# Split Specialization from Generalized to Ordinary Jordan Form

This file isolates the conversion from generalized Jordan data to ordinary
Jordan data under a split characteristic polynomial.
-/

/-- Characteristic polynomial of a block-triangular matrix as a product over all block labels. -/
theorem blockTriangular_charpoly_fintype
    {R α ι : Type u} [CommRing R]
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [LinearOrder α]
    {M : Matrix ι ι R} {b : ι → α}
    (h : M.BlockTriangular b) :
    M.charpoly = ∏ a : α, (M.toSquareBlock b a).charpoly := by
  simp only [Matrix.charpoly, h.charmatrix.det_fintype,
    Matrix.charmatrix_toSquareBlock]

/-- Collapse the degree-one generalized-block coordinate to a reversed chain index. -/
noncomputable def linearGeneralizedJordanBlockEquiv
    {K : Type u} [Field K] (lam : K) (k : Nat) :
    generalizedBlockCoord ((Polynomial.X - Polynomial.C lam) : K[X]) k ≃ Fin k where
  toFun x := Fin.rev x.1
  invFun i :=
    (Fin.rev i,
      ⟨0, by
        simp⟩)
  left_inv := by
    intro x
    apply Prod.ext
    · exact Fin.rev_rev x.1
    · apply Fin.ext
      have hx : (x.2 : Nat) = 0 := by
        have hlt : (x.2 : Nat) < 1 := by
          simpa [Polynomial.natDegree_X_sub_C] using x.2.2
        omega
      exact hx.symm
  right_inv := by
    intro i
    exact Fin.rev_rev i

/-- The connector in a linear generalized block is the scalar `1`. -/
theorem generalizedJordanConnector_linear_coord
    {K : Type u} [Field K] (lam : K)
    (i j : Fin (((Polynomial.X - Polynomial.C lam) : K[X]).natDegree)) :
    generalizedJordanConnector
      (((Polynomial.X - Polynomial.C lam) : K[X]).natDegree) i j = 1 := by
  have hi : (i : Nat) = 0 := by
    have hlt : (i : Nat) < 1 := by
      simpa [Polynomial.natDegree_X_sub_C] using i.2
    omega
  have hj : (j : Nat) = 0 := by
    have hlt : (j : Nat) < 1 := by
      simpa [Polynomial.natDegree_X_sub_C] using j.2
    omega
  simp [generalizedJordanConnector, hi, hj]

/-- The companion block of `X - C lam` is the one-by-one matrix `[lam]`. -/
theorem companionMatrixFin_linear_coord
    {K : Type u} [Field K] (lam : K)
    (i j : Fin (((Polynomial.X - Polynomial.C lam) : K[X]).natDegree)) :
    companionMatrixFin ((Polynomial.X - Polynomial.C lam) : K[X]) i j = lam := by
  have hi : (i : Nat) = 0 := by
    have hlt : (i : Nat) < 1 := by
      simpa [Polynomial.natDegree_X_sub_C] using i.2
    omega
  have hj : (j : Nat) = 0 := by
    have hlt : (j : Nat) < 1 := by
      simpa [Polynomial.natDegree_X_sub_C] using j.2
    omega
  simp [companionMatrixFin, hi, hj]

/--
For a linear polynomial, the generalized Jordan block is the ordinary Jordan
block after reversing the chain index and forgetting the unique degree-one
coordinate.
-/
theorem generalizedJordanBlock_linear_reindex_jordanBlock
    {K : Type u} [Field K] (lam : K) (k : Nat) :
    generalizedJordanBlock ((Polynomial.X - Polynomial.C lam) : K[X]) k =
      Matrix.reindex
        (linearGeneralizedJordanBlockEquiv lam k).symm
        (linearGeneralizedJordanBlockEquiv lam k).symm
        (jordanBlock lam k) := by
  classical
  ext i j
  have hcomp :
      companionMatrixFin ((Polynomial.X - Polynomial.C lam) : K[X]) i.2 j.2 = lam :=
    companionMatrixFin_linear_coord lam i.2 j.2
  by_cases hdiag : i.1 = j.1
  · have hrev : Fin.rev i.1 = Fin.rev j.1 := by simp [hdiag]
    simp [generalizedJordanBlock, Matrix.reindex_apply, jordanBlock,
      linearGeneralizedJordanBlockEquiv, hdiag, hcomp]
  · by_cases hsub : (j.1 : Nat) + 1 = (i.1 : Nat)
    · have hsuper : ((Fin.rev i.1 : Fin k) : Nat) + 1 = (Fin.rev j.1 : Fin k) := by
        rw [Fin.val_rev, Fin.val_rev]
        omega
      have hsuper_raw :
          k - ((i.1 : Nat) + 1) + 1 = k - ((j.1 : Nat) + 1) := by
        simpa [Fin.val_rev] using hsuper
      have hrev_ne : Fin.rev i.1 ≠ Fin.rev j.1 := by
        intro h
        exact hdiag (Fin.rev_injective h)
      simp only [generalizedJordanBlock, hdiag, hsub, ↓reduceIte]
      have hright :
          (Matrix.reindex
            (linearGeneralizedJordanBlockEquiv lam k).symm
            (linearGeneralizedJordanBlockEquiv lam k).symm
            (jordanBlock lam k)) i j = 1 := by
        simp [Matrix.reindex_apply, jordanBlock,
          linearGeneralizedJordanBlockEquiv, hrev_ne, hsuper_raw]
      rw [hright]
      have hi : (i.2 : Nat) = 0 := by
        have hlt : (i.2 : Nat) < 1 := by
          simpa [Polynomial.natDegree_X_sub_C] using i.2.2
        omega
      have hj : (j.2 : Nat) = 0 := by
        have hlt : (j.2 : Nat) < 1 := by
          simpa [Polynomial.natDegree_X_sub_C] using j.2.2
        omega
      simp [generalizedJordanConnector, hi, hj]
    · have hsuper_not :
          ¬ ((Fin.rev i.1 : Fin k) : Nat) + 1 = (Fin.rev j.1 : Fin k) := by
        intro hsuper
        rw [Fin.val_rev, Fin.val_rev] at hsuper
        omega
      have hsuper_raw_not :
          ¬ k - ((i.1 : Nat) + 1) + 1 = k - ((j.1 : Nat) + 1) := by
        intro hraw
        exact hsuper_not (by
          simpa [Fin.val_rev] using hraw)
      have hrev_ne : Fin.rev i.1 ≠ Fin.rev j.1 := by
        intro h
        exact hdiag (Fin.rev_injective h)
      simp [generalizedJordanBlock, Matrix.reindex_apply, jordanBlock,
        linearGeneralizedJordanBlockEquiv, hdiag, hsub, hrev_ne,
        hsuper_raw_not]

/-- A generalized block for `X - C lam` is already an ordinary Jordan matrix. -/
theorem generalizedJordanBlock_linear_hasJordan
    {K : Type u} [Field K] (lam : K) (k : Nat) (hk : 0 < k) :
    HasJordanMatrix
      (generalizedJordanBlock ((Polynomial.X - Polynomial.C lam) : K[X]) k) := by
  rw [generalizedJordanBlock_linear_reindex_jordanBlock lam k]
  exact hasJordanMatrix_reindex_jordanBlock
    (K := K)
    (ι := generalizedBlockCoord ((Polynomial.X - Polynomial.C lam) : K[X]) k)
    lam k hk (linearGeneralizedJordanBlockEquiv lam k)

/-- Generalized blocks have characteristic polynomial `p ^ k`. -/
theorem generalizedJordanBlock_charpoly
    {K : Type u} [Field K] (p : K[X]) (k : Nat)
    (hp_monic : p.Monic) (hpdeg : 0 < p.natDegree) :
    (generalizedJordanBlock p k).charpoly = p ^ k := by
  classical
  let b : generalizedBlockCoord p k → (Fin k)ᵒᵈ :=
    OrderDual.toDual ∘ fun i => i.1
  have htri :
      (generalizedJordanBlock p k).BlockTriangular b := by
    intro i j hji
    simp only [b, Function.comp_apply] at hji
    simp only [OrderDual.toDual_lt_toDual] at hji
    have hne : i.1 ≠ j.1 := by
      intro h
      exact (lt_irrefl j.1) (h ▸ hji)
    have hnot : ¬ (j.1 : Nat) + 1 = (i.1 : Nat) := by
      intro hsucc
      omega
    simp [generalizedJordanBlock, hne, hnot]
  rw [htri.charpoly]
  have himage : Finset.image b Finset.univ = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    refine Finset.mem_image.mpr ?_
    refine ⟨(OrderDual.ofDual x, ⟨0, hpdeg⟩), Finset.mem_univ _, ?_⟩
    simp [b]
  rw [himage]
  trans ∏ _x : (Fin k)ᵒᵈ, p
  · apply Finset.prod_congr rfl
    intro x _hx
    let e :
        {i : generalizedBlockCoord p k // b i = x} ≃ Fin p.natDegree := {
      toFun := fun i => i.1.2
      invFun := fun j => ⟨(OrderDual.ofDual x, j), by simp [b]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        rcases i with ⟨i, hi⟩
        apply Prod.ext
        · simpa [b] using (congrArg OrderDual.ofDual hi).symm
        · rfl
      right_inv := by
        intro j
        rfl
    }
    have hmat :
        Matrix.reindex e e
          ((generalizedJordanBlock p k).toSquareBlock b x) =
            companionMatrixFin p := by
      ext i j
      simp [e, Matrix.reindex_apply, Matrix.toSquareBlock_def,
        generalizedJordanBlock, b]
    have hchar :=
      Matrix.charpoly_reindex e
        ((generalizedJordanBlock p k).toSquareBlock b x)
    rw [hmat] at hchar
    rw [← hchar]
    exact companionMatrixFin_charpoly (K := K) hp_monic
  · rw [Finset.prod_const]
    simp

/-- Characteristic polynomial of a block diagonal matrix of generalized blocks. -/
theorem generalizedJordanBlockData_model_charpoly
    {K : Type u} [Field K]
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β]
    (poly : β → K[X]) (exponent : β → Nat)
    (hpoly_monic : ∀ b, (poly b).Monic)
    (hpoly_irred : ∀ b, Irreducible (poly b)) :
    (Matrix.blockDiagonal' fun b =>
      generalizedJordanBlock (poly b) (exponent b)).charpoly =
        ∏ b : β, (poly b) ^ exponent b := by
  classical
  let blockIndex :
      ((b : β) × generalizedBlockCoord (poly b) (exponent b)) → β :=
    fun i => i.1
  have htri :
      (Matrix.blockDiagonal' fun b =>
        generalizedJordanBlock (poly b) (exponent b)).BlockTriangular blockIndex :=
    Matrix.blockTriangular_blockDiagonal' fun b =>
      generalizedJordanBlock (poly b) (exponent b)
  rw [blockTriangular_charpoly_fintype htri]
  apply Finset.prod_congr rfl
  intro b _hb
  let e :
      {i : (b : β) × generalizedBlockCoord (poly b) (exponent b) //
        blockIndex i = b} ≃ generalizedBlockCoord (poly b) (exponent b) := {
    toFun := by
      intro i
      rcases i with ⟨⟨b', coord⟩, hb'⟩
      dsimp [blockIndex] at hb'
      subst b'
      exact coord
    invFun := fun i => ⟨⟨b, i⟩, rfl⟩
    left_inv := by
      intro i
      apply Subtype.ext
      rcases i with ⟨⟨b', coord⟩, hb'⟩
      dsimp [blockIndex] at hb'
      subst b'
      rfl
    right_inv := by
      intro i
      rfl
  }
  let M :=
    (Matrix.blockDiagonal' fun b =>
      generalizedJordanBlock (poly b) (exponent b)).toSquareBlock blockIndex b
  have hmat :
      Matrix.reindex e e M =
        generalizedJordanBlock (poly b) (exponent b) := by
    ext i j
    simp [M, e, Matrix.reindex_apply, Matrix.toSquareBlock_def, blockIndex,
      Matrix.blockDiagonal']
  have hcharM :
      M.charpoly = (generalizedJordanBlock (poly b) (exponent b)).charpoly := by
    have hcharReindex := Matrix.charpoly_reindex e M
    have hcharEq := congrArg Matrix.charpoly hmat
    exact hcharReindex.symm.trans hcharEq
  exact hcharM.trans
    (generalizedJordanBlock_charpoly (poly b) (exponent b)
      (hpoly_monic b) (hpoly_irred b).natDegree_pos)

/--
Characteristic polynomial recorded by generalized Jordan block data.

This is the public bookkeeping theorem tying the diagonal generalized-Jordan
block polynomials to the characteristic polynomial of the whole model matrix:
the characteristic polynomial is the product of the recorded elementary factors
`poly b ^ exponent b`.
-/
theorem generalizedJordanBlockData_charpoly
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {J : Matrix ι ι K}
    (d : GeneralizedJordanBlockData J) :
    J.charpoly = ∏ b : d.block, (d.poly b) ^ d.exponent b := by
  classical
  letI : LinearOrder d.block := d.linearOrder_block
  have hcharReindex :
      (Matrix.reindex d.blockIndexEquiv d.blockIndexEquiv J).charpoly =
        J.charpoly :=
    Matrix.charpoly_reindex d.blockIndexEquiv J
  have hcharBlocks :
      (Matrix.blockDiagonal' fun b =>
        generalizedJordanBlock (d.poly b) (d.exponent b)).charpoly =
        ∏ b : d.block, (d.poly b) ^ d.exponent b :=
    generalizedJordanBlockData_model_charpoly
      d.poly d.exponent d.poly_monic d.poly_irreducible
  rw [← hcharReindex, d.block_form, hcharBlocks]

/-- Cast-aware version of `generalizedJordanBlock_linear_reindex_jordanBlock`. -/
theorem generalizedJordanBlock_linear_reindex_jordanBlock_of_eq
    {K : Type u} [Field K] {p : K[X]} (lam : K) (k : Nat)
    (hp : p = (Polynomial.X - Polynomial.C lam : K[X])) :
    generalizedJordanBlock p k =
      Matrix.reindex
        (((Equiv.cast (by rw [hp])) :
            generalizedBlockCoord p k ≃
              generalizedBlockCoord ((Polynomial.X - Polynomial.C lam) : K[X]) k).trans
          (linearGeneralizedJordanBlockEquiv lam k)).symm
        (((Equiv.cast (by rw [hp])) :
            generalizedBlockCoord p k ≃
              generalizedBlockCoord ((Polynomial.X - Polynomial.C lam) : K[X]) k).trans
          (linearGeneralizedJordanBlockEquiv lam k)).symm
        (jordanBlock lam k) := by
  subst p
  simpa using generalizedJordanBlock_linear_reindex_jordanBlock lam k

/--
Generalized Jordan data whose block polynomials are already written as linear
factors is ordinary Jordan data.
-/
theorem isJordanMatrix_of_generalizedJordanBlockData_linear
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {J : Matrix ι ι K}
    (d : GeneralizedJordanBlockData J)
    (lam : d.block → K)
    (hpoly : ∀ b, d.poly b = (Polynomial.X - Polynomial.C (lam b) : K[X])) :
    IsJordanMatrix J := by
  classical
  let blockEquiv (b : d.block) :
      generalizedBlockCoord (d.poly b) (d.exponent b) ≃ Fin (d.exponent b) :=
    ((Equiv.cast (by rw [hpoly b])) :
      generalizedBlockCoord (d.poly b) (d.exponent b) ≃
        generalizedBlockCoord ((Polynomial.X - Polynomial.C (lam b)) : K[X])
          (d.exponent b)).trans
      (linearGeneralizedJordanBlockEquiv (lam b) (d.exponent b))
  let fiberEquiv :
      ((b : d.block) × generalizedBlockCoord (d.poly b) (d.exponent b)) ≃
        ((b : d.block) × Fin (d.exponent b)) := {
    toFun := fun x => ⟨x.1, blockEquiv x.1 x.2⟩
    invFun := fun x => ⟨x.1, (blockEquiv x.1).symm x.2⟩
    left_inv := by
      intro x
      rcases x with ⟨b, i⟩
      simp [blockEquiv]
    right_inv := by
      intro x
      rcases x with ⟨b, i⟩
      simp [blockEquiv]
  }
  refine ⟨{
    block := d.block
    eigenvalue := lam
    blockSize := d.exponent
    blockSize_pos := d.exponent_pos
    total_size := ?_
    blockIndexEquiv := d.blockIndexEquiv.trans fiberEquiv
    block_form := ?_
  }⟩
  · have hsum :
        (∑ b, d.exponent b * (d.poly b).natDegree) =
          ∑ b, d.exponent b := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [hpoly b]
      simp
    simpa [hsum] using d.total_size
  · ext x y
    have hentry :=
      congrFun (congrFun d.block_form (fiberEquiv.symm x)) (fiberEquiv.symm y)
    rcases x with ⟨bx, ix⟩
    rcases y with ⟨bY, iy⟩
    by_cases hblock : bx = bY
    · subst bY
      have hblock' : (fiberEquiv.symm ⟨bx, ix⟩).1 = (fiberEquiv.symm ⟨bx, iy⟩).1 := by
        rfl
      have hgen :
          generalizedJordanBlock (d.poly bx) (d.exponent bx) =
            Matrix.reindex
              (blockEquiv bx).symm
              (blockEquiv bx).symm
              (jordanBlock (lam bx) (d.exponent bx)) := by
        exact generalizedJordanBlock_linear_reindex_jordanBlock_of_eq
          (lam bx) (d.exponent bx) (hpoly bx)
      simpa [Matrix.reindex_apply, Matrix.blockDiagonal', fiberEquiv, hblock',
        hgen] using hentry
    · have hblock' : (fiberEquiv.symm ⟨bx, ix⟩).1 ≠ (fiberEquiv.symm ⟨bY, iy⟩).1 := by
        simpa [fiberEquiv] using hblock
      simpa [Matrix.reindex_apply, Matrix.blockDiagonal', fiberEquiv, hblock,
        hblock'] using hentry

/--
Similarity-level conversion when the generalized target already records
linear block polynomials.
-/
theorem hasJordanMatrix_of_generalizedJordanBlockData_linear
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A J P : Matrix ι ι K}
    (hP : InvertibleMatrix P)
    (d : GeneralizedJordanBlockData J)
    (hA : A = P * J * P⁻¹)
    (lam : d.block → K)
    (hpoly : ∀ b, d.poly b = (Polynomial.X - Polynomial.C (lam b) : K[X])) :
    HasJordanMatrix A := by
  exact ⟨P, J, hP,
    isJordanMatrix_of_generalizedJordanBlockData_linear d lam hpoly, hA⟩

/-- Each recorded generalized block polynomial divides the characteristic polynomial. -/
theorem generalizedJordanBlockData_poly_dvd_charpoly
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {J : Matrix ι ι K}
    (d : GeneralizedJordanBlockData J) (b : d.block) :
    d.poly b ∣ J.charpoly := by
  classical
  letI : LinearOrder d.block := d.linearOrder_block
  have hchar :
      J.charpoly = ∏ b : d.block, (d.poly b) ^ d.exponent b :=
    generalizedJordanBlockData_charpoly d
  rw [hchar]
  have hpow : d.poly b ∣ (d.poly b) ^ d.exponent b :=
    dvd_pow_self (d.poly b) (d.exponent_pos b).ne'
  exact hpow.trans
    (Finset.dvd_prod_of_mem (fun b => (d.poly b) ^ d.exponent b)
      (Finset.mem_univ b))

/-- A monic irreducible split polynomial over the base field is linear. -/
theorem exists_eq_X_sub_C_of_monic_irreducible_splits
    {K : Type u} [Field K] {p : K[X]}
    (hp_monic : p.Monic)
    (hp_irred : Irreducible p)
    (hp_split : p.Splits (RingHom.id K)) :
    ∃ lam : K, p = (Polynomial.X - Polynomial.C lam : K[X]) := by
  have hdeg : p.degree = 1 :=
    Polynomial.degree_eq_one_of_irreducible_of_splits hp_irred hp_split
  have hnat : p.natDegree = 1 := by
    exact Polynomial.natDegree_eq_of_degree_eq_some hdeg
  refine ⟨-p.coeff 0, ?_⟩
  calc
    p = Polynomial.X + Polynomial.C (p.coeff 0) :=
      hp_monic.eq_X_add_C hnat
    _ = Polynomial.X - Polynomial.C (-p.coeff 0) := by
      simp

/-- Generalized Jordan witnesses specialize to ordinary Jordan witnesses under splitting. -/
theorem hasJordanMatrix_of_hasGeneralizedJordanMatrix_of_splits
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K}
    (hG : HasGeneralizedJordanMatrix A)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  classical
  rcases hG with ⟨P, J, hP, hJ, hA⟩
  rcases hJ with ⟨d⟩
  have hsplitJ : J.charpoly.Splits (RingHom.id K) := by
    have hchar :
        J.charpoly = A.charpoly := by
      have hsim :
          (P⁻¹ * A * P).charpoly = A.charpoly :=
        jordan_similarity_charpoly hP
      have hconj : P⁻¹ * A * P = J := by
        haveI : Invertible P := hP.invertible
        rw [hA]
        simp [Matrix.mul_assoc]
      simpa [hconj] using hsim
    rwa [hchar]
  choose lam hpoly using fun b =>
    exists_eq_X_sub_C_of_monic_irreducible_splits
      (d.poly_monic b)
      (d.poly_irreducible b)
      (Polynomial.splits_of_splits_of_dvd
        (RingHom.id K)
        (Matrix.charpoly_monic J).ne_zero
        hsplitJ
        (generalizedJordanBlockData_poly_dvd_charpoly d b))
  exact hasJordanMatrix_of_generalizedJordanBlockData_linear
    hP d hA lam hpoly

/--
Bridge converting generalized Jordan witnesses to ordinary Jordan witnesses
under the user-facing split characteristic-polynomial hypothesis.
-/
structure JordanSplitSpecializationBridge
    (K : Type u) [Field K] : Type (u + 1) where
  hasJordanMatrix_of_hasGeneralizedJordanMatrix_of_splits :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
      {A : Matrix ι ι K},
      HasGeneralizedJordanMatrix A →
        A.charpoly.Splits (RingHom.id K) →
          HasJordanMatrix A

/-- Bridge-routed generalized-to-ordinary split specialization theorem. -/
theorem hasJordanMatrix_of_hasGeneralizedJordanMatrix_of_splits_bridge
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (_bridge : JordanSplitSpecializationBridge K)
    {A : Matrix ι ι K}
    (hG : HasGeneralizedJordanMatrix A)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A :=
  hasJordanMatrix_of_hasGeneralizedJordanMatrix_of_splits hG hsplit

/--
Framework-routed split theorem conditional only on the generalized Jordan
block-driver bridge.  The generalized-to-ordinary split specialization is
concrete.
-/
theorem exists_jordan_matrix_of_splits_generalized_bridge
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (generalizedBridge : GeneralizedJordanBlockDriverBridge K)
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A :=
  hasJordanMatrix_of_hasGeneralizedJordanMatrix_of_splits
    (exists_generalized_jordan_matrix_framework_bridge generalizedBridge A)
    hsplit

/--
Bridge-routed split theorem with explicit final ordinary Jordan block data.
The characteristic-polynomial splitting hypothesis remains a theorem argument.
-/
theorem jordanBlockData_of_splits_generalized_bridge
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (generalizedBridge : GeneralizedJordanBlockDriverBridge K)
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    JordanBlockData A :=
  jordanBlockData_of_hasJordanMatrix
    (exists_jordan_matrix_of_splits_generalized_bridge
      generalizedBridge A hsplit)

/--
Same-universe split theorem through the concrete RCF prime-power generalized
driver.  The public theorem below removes the framework's index-universe
restriction by reindexing through `ULift (Fin _)`.
-/
theorem exists_jordan_matrix_of_splits_same_universe
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A :=
  hasJordanMatrix_of_hasGeneralizedJordanMatrix_of_splits
    (exists_generalized_jordan_matrix A)
    hsplit

/--
Public split theorem.  The descent driver is instantiated on a same-universe
`ULift (Fin _)` model and transported back to the user's matrix index.
-/
theorem exists_jordan_matrix_of_splits
    {K : Type u} {ι : Type v} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  classical
  let e : ι ≃ ULift.{u, 0} (Fin (Fintype.card ι)) :=
    (Fintype.equivFin ι).trans Equiv.ulift.symm
  letI : LinearOrder (ULift.{u, 0} (Fin (Fintype.card ι))) :=
    LinearOrder.lift' ULift.down (fun x y h => by
      cases x
      cases y
      simp at h
      simp [h])
  have hchar :
      (Matrix.reindex e e A).charpoly.Splits (RingHom.id K) := by
    rw [Matrix.charpoly_reindex e A]
    exact hsplit
  have hReindexed :
      HasJordanMatrix (Matrix.reindex e e A) :=
    exists_jordan_matrix_of_splits_same_universe (Matrix.reindex e e A) hchar
  have hBack := hasJordanMatrix_reindex_universe (e := e.symm) hReindexed
  simpa [e, MatDecompFormal.Framework.reindex_reindex, Function.comp_def] using hBack

/--
Public split theorem with explicit final ordinary Jordan block data.
The split hypothesis is visible, matching the mathematical requirement over a
general field.
-/
theorem jordanBlockData_of_splits
    {K : Type u} {ι : Type v} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    JordanBlockData A :=
  jordanBlockData_of_hasJordanMatrix
    (exists_jordan_matrix_of_splits A hsplit)

/-- Jordan form exists for matrices over algebraically closed fields. -/
theorem exists_jordan_matrix_algClosed
    {K : Type u} {ι : Type v} [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasJordanMatrix A :=
  exists_jordan_matrix_of_splits A (IsAlgClosed.splits A.charpoly)

/-- Jordan block data exists for matrices over algebraically closed fields. -/
theorem jordanBlockData_algClosed
    {K : Type u} {ι : Type v} [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    JordanBlockData A :=
  jordanBlockData_of_splits A (IsAlgClosed.splits A.charpoly)

/-- Jordan form exists for complex matrices. -/
theorem exists_jordan_matrix_complex
    {ι : Type v} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasJordanMatrix A :=
  exists_jordan_matrix_algClosed A

/-- Jordan block data exists for complex matrices. -/
theorem jordanBlockData_complex
    {ι : Type v} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    JordanBlockData A :=
  jordanBlockData_algClosed A

/-- An invertible matrix over a field has unit determinant. -/
lemma invertibleMatrix_det_isUnit
    {K ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι K} (hP : InvertibleMatrix P) :
    IsUnit P.det := by
  change IsUnit P at hP
  rw [Matrix.isUnit_iff_isUnit_det] at hP
  exact hP

/--
A matrix-level Jordan similarity for the matrix of an operator can be absorbed
into a basis change, producing a basis in which the operator matrix itself is
Jordan.
-/
lemma exists_basis_toMatrix_eq_jordan_of_similarity
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b₀ : Module.Basis ι K V) (T : V →ₗ[K] V)
    {P J : Matrix ι ι K} (hP : InvertibleMatrix P)
    (hEq : LinearMap.toMatrix b₀ b₀ T = P * J * P⁻¹) :
    ∃ b : Module.Basis ι K V, LinearMap.toMatrix b b T = J := by
  classical
  have hPdet : IsUnit P.det := invertibleMatrix_det_isUnit hP
  let eP : V ≃ₗ[K] V := Matrix.toLinearEquiv b₀ P hPdet
  let b : Module.Basis ι K V := b₀.map eP
  refine ⟨b, ?_⟩
  have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (b := b) (b' := b₀) (c := b) (c' := b₀) (f := T)
  have hePmat : LinearMap.toMatrix b₀ b₀ (eP : V →ₗ[K] V) = P := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have happ := Matrix.toLinearEquiv_apply b₀ P hPdet (b₀ j)
    have hrepr : (b₀.repr ((eP : V →ₗ[K] V) (b₀ j))) i =
        (b₀.repr (((Matrix.toLin b₀ b₀) P) (b₀ j))) i := by
      exact congrArg (fun x => (b₀.repr x) i) happ
    rw [hrepr]
    rw [← LinearMap.toMatrix_apply]
    exact congrFun (congrFun (LinearMap.toMatrix_toLin b₀ b₀ P) i) j
  have hb0_to_b : b₀.toMatrix b = P := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    change (b₀.repr ((eP : V →ₗ[K] V) (b₀ j))) i = P i j
    simpa [LinearMap.toMatrix_apply] using congrFun (congrFun hePmat i) j
  have hb_to_b0 : b.toMatrix b₀ = P⁻¹ := by
    have hmul : b.toMatrix b₀ * b₀.toMatrix b = 1 := by
      simp
    have hmul' : b.toMatrix b₀ * P = 1 := by
      simpa [hb0_to_b] using hmul
    exact (Matrix.inv_eq_left_inv hmul').symm
  calc
    LinearMap.toMatrix b b T =
        b.toMatrix b₀ * LinearMap.toMatrix b₀ b₀ T * b₀.toMatrix b := by
          exact hchange.symm
    _ = P⁻¹ * (P * J * P⁻¹) * P := by rw [hb_to_b0, hb0_to_b, hEq]
    _ = J := by
      haveI : Invertible P := hP.invertible
      simp [Matrix.mul_assoc]

/-- Jordan form exists for finite-dimensional linear maps whose charpoly splits. -/
theorem exists_jordan_form_of_splits
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [Module.Free K V] [Module.Finite K V]
    (T : V →ₗ[K] V)
    (hsplit : T.charpoly.Splits (RingHom.id K)) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      IsJordanMatrix (LinearMap.toMatrix b b T) := by
  classical
  let b₀ : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V :=
    (Module.finBasis K V).reindex Equiv.ulift.symm
  have hsplitMat : (LinearMap.toMatrix b₀ b₀ T).charpoly.Splits (RingHom.id K) := by
    rw [LinearMap.charpoly_toMatrix]
    exact hsplit
  rcases exists_jordan_matrix_of_splits (LinearMap.toMatrix b₀ b₀ T) hsplitMat with
    ⟨P, J, hP, hJ, hEq⟩
  rcases exists_basis_toMatrix_eq_jordan_of_similarity b₀ T hP hEq with ⟨b, hb⟩
  exact ⟨b, by simpa [hb] using hJ⟩

/-- Jordan form exists for finite-dimensional linear maps over algebraically closed fields. -/
theorem exists_jordan_form_algClosed
    {K : Type u} {V : Type v} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
    (T : V →ₗ[K] V) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      IsJordanMatrix (LinearMap.toMatrix b b T) :=
  exists_jordan_form_of_splits T (IsAlgClosed.splits T.charpoly)

/-- Jordan form exists for finite-dimensional complex linear maps. -/
theorem exists_jordan_form_complex
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (T : V →ₗ[ℂ] V) :
    ∃ b : Module.Basis (ULift.{0, 0} (Fin (Module.finrank ℂ V))) ℂ V,
      IsJordanMatrix (LinearMap.toMatrix b b T) :=
  exists_jordan_form_algClosed T

/--
Bridge-routed final split theorem shape.  This theorem is intentionally
suffixed because both the generalized block-driver bridge and the split
specialization bridge remain explicit proof infrastructure.
-/
theorem exists_jordan_matrix_of_splits_framework_bridge
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (generalizedBridge : GeneralizedJordanBlockDriverBridge K)
    (_splitBridge : JordanSplitSpecializationBridge K)
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A :=
  exists_jordan_matrix_of_splits_generalized_bridge generalizedBridge A hsplit

end MatDecompFormal.Instances
