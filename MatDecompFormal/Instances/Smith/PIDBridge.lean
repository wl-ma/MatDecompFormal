import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Smith.Existence

universe u v w

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Smith PID Bridge

Mathlib's PID Smith normal form is currently stated for submodules of finite
free modules.  The matrix-level theorem in this project needs an additional
bridge: translate a rectangular matrix into a linear map/submodule statement,
extract the Smith bases, and repackage the basis changes as the explicit
matrices required by `HasSmithNormalForm`.

This file exposes the mathlib SNF data under the Smith namespace and packages
the strengthened submodule result as the project's PID matrix theorem.
-/

/--
The available PID Smith normal-form data from mathlib for a submodule of a
finite free module.

This is not yet the project's matrix theorem; it is the authoritative PID
source that the future matrix bridge should consume.
-/
noncomputable def pidSubmoduleSmithNormalForm
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type w) [Finite ι]
    (b : Module.Basis ι R M) (N : Submodule R M) :
    Σ n : ℕ, Module.Basis.SmithNormalForm N ι n :=
  N.smithNormalForm b

/-- Existential wrapper around `pidSubmoduleSmithNormalForm`. -/
theorem exists_pid_submodule_smith_normal_form
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type w) [Finite ι]
    (b : Module.Basis ι R M) (N : Submodule R M) :
    ∃ n : ℕ, Nonempty (Module.Basis.SmithNormalForm N ι n) := by
  let snf := pidSubmoduleSmithNormalForm R M ι b N
  exact ⟨snf.1, ⟨snf.2⟩⟩

/-- A total divisibility chain along the natural order of `Fin n`. -/
def FinDividesChain {R : Type u} [Dvd R] {n : ℕ} (a : Fin n → R) : Prop :=
  ∀ i j : Fin n, (i : Nat) ≤ (j : Nat) → a i ∣ a j

/--
Mathlib Smith data plus an explicit invariant-factor chain.

This is the local strengthened PID target: mathlib supplies the diagonal basis
shape, while this wrapper records the ordered divisibility proof required by
this project's `SmithNormalFormData`.
-/
structure SmithNormalFormWithChain
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (ι : Type w) (n : ℕ) where
  snf : Module.Basis.SmithNormalForm N ι n
  chain : FinDividesChain snf.a

lemma finDividesChain_adjacent {R : Type u} [Dvd R] {n : ℕ} {a : Fin n → R}
    (h : FinDividesChain a) :
    ∀ k : Fin n, (hnext : (k : Nat) + 1 < n) →
      a k ∣ a ⟨(k : Nat) + 1, hnext⟩ := by
  intro k hnext
  exact h k ⟨(k : Nat) + 1, hnext⟩ (Nat.le_succ _)

lemma finDividesChain_cons {R : Type u} [Monoid R] {n : ℕ}
    {a0 : R} {a : Fin n → R}
    (hhead : ∀ i : Fin n, a0 ∣ a i)
    (htail : FinDividesChain a) :
    FinDividesChain (Fin.cons a0 a) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          exact dvd_refl a0
      | succ j =>
          simpa using hhead j
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          exact False.elim ((Nat.not_succ_le_zero (i : Nat)) hij)
      | succ j =>
          have hij' : (i : Nat) ≤ (j : Nat) := Nat.succ_le_succ_iff.mp hij
          simpa using htail i j hij'

section PIDChain

open Submodule.IsPrincipal Set Submodule

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

omit [IsDomain R] in
/--
The maximal projection used in mathlib's PID free-module argument divides the
tail coordinates that occur after the pivot is split off.

The extra hypotheses are exactly the tail situation: `y` maps to the generator,
`z` lies in the kernel of the maximal projection, and the auxiliary coordinate
functional vanishes on `y`.
-/
theorem generator_maximal_submoduleImage_dvd_of_tail
    {N O : Submodule R M} (hNO : N ≤ O) {ϕ : O →ₗ[R] R}
    (hϕ : ∀ ψ : O →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal]
    {y : M} (yN : y ∈ N)
    (ϕy_eq : ϕ ⟨y, hNO yN⟩ = generator (ϕ.submoduleImage N))
    {z : M} (zN : z ∈ N)
    (hzϕ : ϕ ⟨z, hNO zN⟩ = 0)
    (ψ : O →ₗ[R] R) :
    ψ ⟨y, hNO yN⟩ = 0 →
    generator (ϕ.submoduleImage N) ∣ ψ ⟨z, hNO zN⟩ := by
  intro hψy
  let a : R := generator (ϕ.submoduleImage N)
  let x : R := ψ ⟨z, hNO zN⟩
  let d : R := generator (Submodule.span R {a, x})
  have d_dvd_left : d ∣ a :=
    (mem_iff_generator_dvd _).mp (subset_span (mem_insert _ _))
  have d_dvd_right : d ∣ x :=
    (mem_iff_generator_dvd _).mp (subset_span (mem_insert_of_mem _ (mem_singleton _)))
  have hspan_a_le_d : Ideal.span ({a} : Set R) ≤ Ideal.span ({d} : Set R) :=
    Ideal.span_singleton_le_span_singleton.mpr d_dvd_left
  obtain ⟨r₁, r₂, d_eq⟩ : ∃ r₁ r₂ : R, d = r₁ * a + r₂ * x := by
    obtain ⟨r₁, r₂', hr₂', hr₁⟩ :=
      mem_span_insert.mp
        (IsPrincipal.generator_mem (Submodule.span R {a, x}))
    obtain ⟨r₂, rfl⟩ := mem_span_singleton.mp hr₂'
    exact ⟨r₁, r₂, hr₁⟩
  let ψ' : O →ₗ[R] R := r₁ • ϕ + r₂ • ψ
  have hspan_d_le_psi : Ideal.span ({d} : Set R) ≤ ψ'.submoduleImage N := by
    rw [Ideal.span_le, singleton_subset_iff, SetLike.mem_coe,
      LinearMap.mem_submoduleImage_of_le hNO]
    let yzN : y + z ∈ N := N.add_mem yN zN
    have hyz_eq :
        (⟨y + z, hNO yzN⟩ : O) = ⟨y, hNO yN⟩ + ⟨z, hNO zN⟩ := by
      ext
      rfl
    have hphi_yz : ϕ ⟨y + z, hNO yzN⟩ = a := by
      calc
        ϕ ⟨y + z, hNO yzN⟩ =
            ϕ (⟨y, hNO yN⟩ + ⟨z, hNO zN⟩) :=
              congrArg (fun t : O => ϕ t) hyz_eq
        _ = a := by
          rw [map_add, ϕy_eq, hzϕ, add_zero]
    have hpsi_yz : ψ ⟨y + z, hNO yzN⟩ = x := by
      calc
        ψ ⟨y + z, hNO yzN⟩ =
            ψ (⟨y, hNO yN⟩ + ⟨z, hNO zN⟩) :=
              congrArg (fun t : O => ψ t) hyz_eq
        _ = x := by
          rw [map_add, hψy, zero_add]
    refine ⟨y + z, yzN, ?_⟩
    change r₁ * ϕ ⟨y + z, hNO yzN⟩ +
        r₂ * ψ ⟨y + z, hNO yzN⟩ = d
    rw [d_eq]
    simp [hphi_yz, hpsi_yz]
  have hphi_le_psi : ϕ.submoduleImage N ≤ ψ'.submoduleImage N := by
    rw [← span_singleton_generator (ϕ.submoduleImage N)]
    exact hspan_a_le_d.trans hspan_d_le_psi
  have hpsi_le_phi : ψ'.submoduleImage N ≤ ϕ.submoduleImage N :=
    (not_lt_iff_le_imp_ge.mp (hϕ ψ')) hphi_le_psi
  have hd_mem : d ∈ ϕ.submoduleImage N :=
    hpsi_le_phi (hspan_d_le_psi (Submodule.mem_span_singleton_self d))
  exact dvd_trans ((mem_iff_generator_dvd _).mp hd_mem) d_dvd_right

end PIDChain

section StrengthenedPIDSubmodule

open Submodule.IsPrincipal Set Submodule Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/--
Local strengthened version of mathlib's `Submodule.basis_of_pid_aux`.

It exposes the extra divisibility fact needed for invariant factors: the head
coefficient chosen by the PID maximal-projection argument divides every
coefficient in the recursively constructed tail.
-/
theorem submodule_basis_of_pid_aux_with_chain {ι : Type*} [Finite ι]
    {O : Type*} [AddCommGroup O] [Module R O]
    (M N : Submodule R O) (b'M : Basis ι R M)
    (N_bot : N ≠ ⊥) (N_le_M : N ≤ M) :
    ∃ y ∈ M, ∃ a : R, a • y ∈ N ∧ ∃ M' ≤ M, ∃ N' ≤ N,
      N' ≤ M' ∧ (∀ (c : R) (z : O), z ∈ M' → c • y + z = 0 → c = 0) ∧
      (∀ (c : R) (z : O), z ∈ N' → c • a • y + z = 0 → c = 0) ∧
      ∀ (n') (bN' : Basis (Fin n') R N'),
        ∃ bN : Basis (Fin (n' + 1)) R N,
          ∀ (m') (hn'm' : n' ≤ m') (bM' : Basis (Fin m') R M'),
            ∃ (hnm : n' + 1 ≤ m' + 1) (bM : Basis (Fin (m' + 1)) R M),
              ∀ as : Fin n' → R,
                (∀ i : Fin n',
                  (bN' i : O) = as i • (bM' (Fin.castLE hn'm' i) : O)) →
                  ∃ as' : Fin (n' + 1) → R,
                    (∀ i : Fin (n' + 1),
                      (bN i : O) = as' i • (bM (Fin.castLE hnm i) : O)) ∧
                    as' = Fin.cons a as ∧
                    ∀ i : Fin n', a ∣ as i := by
  have : ∃ ϕ : M →ₗ[R] R,
      ∀ ψ : M →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N := by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _
        (show (Set.range fun ψ : M →ₗ[R] R ↦ ψ.submoduleImage N).Nonempty from
          ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩)
    obtain ⟨ϕ, rfl⟩ := Set.mem_range.mp P_eq
    exact ⟨ϕ, fun ψ hψ ↦ P_max _ ⟨_, rfl⟩ hψ⟩
  let ϕ := this.choose
  have ϕ_max := this.choose_spec
  let a := generator (ϕ.submoduleImage N)
  have a_mem : a ∈ ϕ.submoduleImage N := generator_mem _
  by_cases a_zero : a = 0
  · have := eq_bot_of_generator_maximal_submoduleImage_eq_zero b'M N_le_M ϕ_max a_zero
    contradiction
  obtain ⟨y, yN, ϕy_eq⟩ := (LinearMap.mem_submoduleImage_of_le N_le_M).mp a_mem
  have hdvd : ∀ i, a ∣ b'M.coord i ⟨y, N_le_M yN⟩ := fun i ↦
    generator_maximal_submoduleImage_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i)
  choose c hc using hdvd
  cases nonempty_fintype ι
  let y' : O := ∑ i, c i • b'M i
  have y'M : y' ∈ M := M.sum_mem fun i _ ↦ M.smul_mem (c i) (b'M i).2
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M i :=
    Subtype.ext
      (show y' = M.subtype _ by
        simp only [map_sum, map_smul]
        rfl)
  have a_smul_y' : a • y' = y := by
    refine Subtype.mk_eq_mk.mp (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩ from ?_)
    rw [← b'M.sum_repr ⟨y, N_le_M yN⟩, mk_y', Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← MulAction.mul_smul, ← hc]
    rfl
  refine ⟨y', y'M, a, a_smul_y'.symm ▸ yN, ?_⟩
  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 :=
    mul_left_cancel₀ a_zero
      (calc
        a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', _⟩ := (ϕ.map_smul a ⟨y', y'M⟩).symm
        _ = ϕ ⟨y, N_le_M yN⟩ := by simp only [a_smul_y']
        _ = a := ϕy_eq
        _ = a * 1 := (mul_one a).symm)
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ ≠ 0 := by simpa only [ϕy'_eq] using one_ne_zero
  let M' : Submodule R O := (LinearMap.ker ϕ).map M.subtype
  let N' : Submodule R O := (LinearMap.ker (ϕ.comp (inclusion N_le_M))).map N.subtype
  have M'_le_M : M' ≤ M := M.map_subtype_le (LinearMap.ker ϕ)
  have N'_le_M' : N' ≤ M' := by
    intro x hx
    simp only [N', mem_map, LinearMap.mem_ker] at hx ⊢
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩
  have N'_le_N : N' ≤ N := N.map_subtype_le (LinearMap.ker (ϕ.comp (inclusion N_le_M)))
  refine ⟨M', M'_le_M, N', N'_le_N, N'_le_M', ?_⟩
  have y'_ortho_M' : ∀ (c : R), ∀ z ∈ M', c • y' + z = 0 → c = 0 := by
    intro c x xM' hc
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := Submodule.mem_map.mp xM'
    rw [LinearMap.mem_ker] at hx'
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := by
      exact @Subtype.coe_injective O (· ∈ M) _ _ hc
    simpa only [LinearMap.map_add, LinearMap.map_zero, LinearMap.map_smul, smul_eq_mul, add_zero,
      mul_eq_zero, ϕy'_ne_zero, hx', or_false] using congr_arg ϕ hc'
  have ay'_ortho_N' : ∀ (c : R), ∀ z ∈ N', c • a • y' + z = 0 → c = 0 := by
    intro c z zN' hc
    refine (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') ?_)).resolve_left a_zero
    rw [mul_comm, MulAction.mul_smul, hc]
  refine ⟨y'_ortho_M', ay'_ortho_N', fun n' bN' ↦ ⟨?_, ?_⟩⟩
  · refine Basis.mkFinConsOfLE y yN bN' N'_le_N ?_ ?_
    · intro c z zN' hc
      refine ay'_ortho_N' c z zN' ?_
      rwa [← a_smul_y'] at hc
    · intro z zN
      obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ :=
        generator_submoduleImage_dvd_of_mem N_le_M ϕ zN
      refine ⟨-b, Submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, ?_, ?_⟩⟩
      · refine LinearMap.mem_ker.mpr
          (show ϕ (⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩) = 0 from ?_)
        rw [LinearMap.map_sub, LinearMap.map_smul, hb, ϕy_eq, smul_eq_mul, mul_comm, sub_self]
      · simp only [sub_eq_add_neg, neg_smul, coe_subtype]
  intro m' hn'm' bM'
  let hnm : n' + 1 ≤ m' + 1 := Nat.succ_le_succ hn'm'
  let bM : Basis (Fin (m' + 1)) R M := by
    refine Basis.mkFinConsOfLE y' y'M bM' M'_le_M y'_ortho_M' ?_
    intro z zM
    refine ⟨-ϕ ⟨z, zM⟩, ⟨⟨z, zM⟩ - ϕ ⟨z, zM⟩ • ⟨y', y'M⟩, LinearMap.mem_ker.mpr ?_, ?_⟩⟩
    · rw [LinearMap.map_sub, LinearMap.map_smul, ϕy'_eq, smul_eq_mul, mul_one, sub_self]
    · rw [LinearMap.map_sub, LinearMap.map_smul, sub_eq_add_neg, neg_smul]
      rfl
  refine ⟨hnm, bM, ?_⟩
  intro as h
  refine ⟨Fin.cons a as, ?_, rfl, ?_⟩
  · intro i
    rw [Basis.coe_mkFinConsOfLE, Basis.coe_mkFinConsOfLE]
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp only [Fin.cons_zero, Fin.castLE_zero]
      exact a_smul_y'.symm
    · rw [Fin.castLE_succ]
      simpa [Submodule.coe_inclusion] using h i
  · intro i
    let tailIdx : Fin (m' + 1) := (Fin.castLE hn'm' i).succ
    let ψ : M →ₗ[R] R := bM.coord tailIdx
    have hψ_y : ψ ⟨y, N_le_M yN⟩ = 0 := by
      have hy_eq : (⟨y, N_le_M yN⟩ : M) = a • ⟨y', y'M⟩ := by
        ext
        exact a_smul_y'.symm
      have hy'_basis : (⟨y', y'M⟩ : M) = bM 0 := by
        ext
        rw [Basis.coe_mkFinConsOfLE]
        simp
      rw [hy_eq, hy'_basis]
      simp [ψ, tailIdx]
    have zN' : ((bN' i : N') : O) ∈ N' := (bN' i).2
    have zN : ((bN' i : N') : O) ∈ N := N'_le_N zN'
    have hzϕ : ϕ ⟨(bN' i : O), N_le_M zN⟩ = 0 := by
      change (ϕ.comp (inclusion N_le_M)) ⟨(bN' i : O), zN⟩ = 0
      obtain ⟨x, hxker, hxeq⟩ := Submodule.mem_map.mp zN'
      rw [LinearMap.mem_ker] at hxker
      have hxsub : (⟨(bN' i : O), zN⟩ : N) = x := by
        ext
        exact hxeq.symm
      simpa [hxsub] using hxker
    have hψ_z : ψ ⟨(bN' i : O), N_le_M zN⟩ = as i := by
      have hz_eq : (⟨(bN' i : O), N_le_M zN⟩ : M) = as i • bM tailIdx := by
        ext
        rw [h i]
        congr 1
        rw [Basis.coe_mkFinConsOfLE]
        simp [tailIdx]
      rw [hz_eq]
      simp [ψ, tailIdx]
    have hdiv :=
      generator_maximal_submoduleImage_dvd_of_tail
        (R := R) (M := O) (N := N) (O := M)
        N_le_M ϕ_max yN ϕy_eq zN hzϕ ψ hψ_y
    simpa [hψ_z] using hdiv

/--
Strengthened version of mathlib's `Submodule.exists_smith_normal_form_of_le`
which also returns an ordered divisibility chain for the coefficients.
-/
theorem Submodule.exists_smith_normal_form_of_le_with_chain
    {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (N O : Submodule R M) (N_le_O : N ≤ O) :
    ∃ (n o : ℕ) (hno : n ≤ o)
      (bO : Module.Basis (Fin o) R O)
      (bN : Module.Basis (Fin n) R N)
      (a : Fin n → R),
      (∀ i, (bN i : M) = a i • bO (Fin.castLE hno i)) ∧
      FinDividesChain a := by
  cases nonempty_fintype ι
  induction O using Submodule.inductionOnRank b generalizing N with
  | ih M0 ih =>
      obtain ⟨m, b'M⟩ := M0.basisOfPid b
      by_cases N_bot : N = ⊥
      · subst N_bot
        refine ⟨0, m, Nat.zero_le _, b'M, Module.Basis.empty _, finZeroElim,
          ?_, ?_⟩
        · intro i
          exact False.elim (Nat.not_lt_zero _ i.2)
        · intro i
          exact False.elim (Nat.not_lt_zero _ i.2)
      obtain ⟨y, hy, a, _, M', M'_le_M, N', _, N'_le_M', y_ortho, _, h⟩ :=
        submodule_basis_of_pid_aux_with_chain M0 N b'M N_bot N_le_O
      obtain ⟨n', m', hn'm', bM', bN', as', has', hchain'⟩ :=
        ih M' M'_le_M y hy y_ortho N' N'_le_M'
      obtain ⟨bN, h'⟩ := h n' bN'
      obtain ⟨hmn, bM, h''⟩ := h' m' hn'm' bM'
      obtain ⟨as, has, has_eq, hhead⟩ := h'' as' has'
      refine ⟨_, _, hmn, bM, bN, as, has, ?_⟩
      rw [has_eq]
      exact finDividesChain_cons hhead hchain'

/-- Existence wrapper for the strengthened submodule Smith normal form. -/
theorem Submodule.exists_smithNormalFormWithChain
    {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (b : Module.Basis ι R M) (N : Submodule R M) :
    ∃ n : ℕ, Nonempty (SmithNormalFormWithChain N ι n) := by
  classical
  rcases
    Submodule.exists_smith_normal_form_of_le_with_chain (R := R) b N ⊤ le_top
    with ⟨n, o, hno, bO, bN, a, hsnf, hchain⟩
  let bO' := bO.map (LinearEquiv.ofTop _ rfl)
  let e := bO'.indexEquiv b
  refine ⟨n, ⟨?_⟩⟩
  refine
    { snf :=
        { bM := bO'.reindex e
          bN := bN
          f := (Fin.castLEEmb hno).trans e.toEmbedding
          a := a
          snf := ?_ }
      chain := hchain }
  intro i
  simp only [bO', hsnf, Module.Basis.map_apply, LinearEquiv.ofTop_apply,
    Module.Basis.reindex_apply, Equiv.toEmbedding_apply, Function.Embedding.trans_apply,
    Fin.castLEEmb_apply, Equiv.symm_apply_apply]

end StrengthenedPIDSubmodule

section ChangeOfBasis

variable {R : Type u} [CommRing R]

/--
Mathlib's basis-change matrices carry an `Invertible` instance. This repackages
that instance into the explicit inverse witness used by this project.
-/
lemma gaussInvertibleMatrix_basis_toMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M]
    (b b' : Module.Basis ι R M) :
    GaussInvertibleMatrix (b.toMatrix b') := by
  classical
  letI : Invertible (b.toMatrix b') := Module.Basis.invertibleToMatrix b b'
  refine ⟨⅟(b.toMatrix b'), ?_, ?_⟩
  · exact invOf_mul_self (b.toMatrix b')
  · exact mul_invOf_self (b.toMatrix b')

/--
Changing both domain and codomain bases is represented by multiplication by
explicit basis-change matrices around the original matrix.

This is the core mechanical bridge needed after obtaining Smith bases from
mathlib's PID submodule normal form.
-/
theorem basis_change_toMatrix_eq_mul
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (bm bm' : Module.Basis m R M) (bn bn' : Module.Basis n R N)
    (f : M →ₗ[R] N) :
    LinearMap.toMatrix bm' bn' f =
      bn'.toMatrix bn * LinearMap.toMatrix bm bn f * bm.toMatrix bm' := by
  classical
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    bm' bm bn' bn f).symm

/--
Specialized basis-change formula for a concrete matrix over the standard
function-module bases.
-/
theorem basis_change_toMatrix_eq_mul_standard
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (bm' : Module.Basis m R (m → R)) (bn' : Module.Basis n R (n → R))
    (A : Matrix m n R) :
    LinearMap.toMatrix bn' bm' (Matrix.toLin' A) =
      bm'.toMatrix (Pi.basisFun R m) * A * (Pi.basisFun R n).toMatrix bn' := by
  classical
  have h :=
    basis_change_toMatrix_eq_mul
      (R := R) (Pi.basisFun R n) bn' (Pi.basisFun R m) bm' (Matrix.toLin' A)
  rw [h]
  rw [← Matrix.toLin_eq_toLin']
  rw [LinearMap.toMatrix_toLin]

end ChangeOfBasis

section RangeFactorization

variable {R : Type u} [CommRing R]

/-- A linear map factors through the inclusion of its range. -/
theorem linearMap_eq_range_subtype_comp_rangeRestrict
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    f = (LinearMap.range f).subtype.comp f.rangeRestrict :=
  rfl

/--
Matrix form of the range factorization `f = range(f).subtype ∘ f.rangeRestrict`.

The left factor is an inclusion matrix for the range submodule; the right
factor is the matrix of the surjection onto that range.
-/
theorem linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict
    {m n r : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (bm : Module.Basis m R M) (bn : Module.Basis n R N)
    (f : M →ₗ[R] N)
    (br : Module.Basis r R (LinearMap.range f)) :
    LinearMap.toMatrix bm bn f =
      LinearMap.toMatrix br bn (LinearMap.range f).subtype *
        LinearMap.toMatrix bm br f.rangeRestrict := by
  classical
  have h :=
    LinearMap.toMatrix_comp bm br bn (LinearMap.range f).subtype f.rangeRestrict
  simpa [← linearMap_eq_range_subtype_comp_rangeRestrict f] using h

/--
Standard-basis matrix form of the range factorization of a concrete matrix.
-/
theorem matrix_eq_range_subtype_mul_rangeRestrict
    {m n r : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A))) :
    A =
      LinearMap.toMatrix br (Pi.basisFun R m) (LinearMap.range (Matrix.toLin' A)).subtype *
        LinearMap.toMatrix (Pi.basisFun R n) br (Matrix.toLin' A).rangeRestrict := by
  classical
  have h :=
    linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict
      (R := R) (bm := Pi.basisFun R n) (bn := Pi.basisFun R m)
      (f := Matrix.toLin' A) (br := br)
  have hstd :
      LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R m) (Matrix.toLin' A) = A := by
    rw [← Matrix.toLin_eq_toLin']
    exact LinearMap.toMatrix_toLin (Pi.basisFun R n) (Pi.basisFun R m) A
  rwa [hstd] at h

/--
Writing a concrete matrix map in a reindexed standard column basis reindexes the
columns of the original matrix.
-/
theorem toMatrix_reindex_standard_domain_eq_reindex
    {m n n' : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (A : Matrix m n R) (e : n ≃ n') :
    LinearMap.toMatrix ((Pi.basisFun R n).reindex e) (Pi.basisFun R m)
        (Matrix.toLin' A) =
      Matrix.reindex (Equiv.refl m) e A := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  rw [Matrix.toLin'_apply]
  rw [Module.Basis.reindex_apply]
  rw [Pi.basisFun_repr]
  rw [Matrix.reindex_apply]
  rw [Pi.basisFun_apply]
  rw [Matrix.mulVec_single_one]
  rfl

end RangeFactorization

section SubmoduleMatrix

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {N : Submodule R M} {rank : ℕ}

/-- Lift finite Smith-rank indices into the same universe as the ambient basis index. -/
abbrev PIDSmithRankIdx (rank : ℕ) : Type u :=
  ULift.{u, 0} (Fin rank)

/-- Equivalence between mathlib's `Fin rank` Smith index and the local lifted index. -/
def pidSmithRankEquiv (rank : ℕ) : Fin rank ≃ ULift.{u, 0} (Fin rank) :=
  Equiv.ulift.symm

/--
Mathlib's submodule Smith normal form gives a rectangular diagonal matrix for
the inclusion map `N.subtype`, when written in the Smith bases. To target the
project's strengthened Smith predicate, the invariant-factor chain is supplied
explicitly as `hchain`.
-/
noncomputable def smithNormalFormData_of_basisSmithNormalForm
    (snf : Module.Basis.SmithNormalForm N ι rank)
    (hchain : ∀ k : Fin rank, (hnext : (k : Nat) + 1 < rank) →
      snf.a k ∣ snf.a ⟨(k : Nat) + 1, hnext⟩) :
    SmithNormalFormData (R := R) (m := ι) (n := PIDSmithRankIdx rank)
      (fun i (j : PIDSmithRankIdx rank) =>
        LinearMap.toMatrix snf.bN snf.bM N.subtype i j.down) where
  r := PIDSmithRankIdx rank
  fintype_r := inferInstance
  order :=
    (finCongr (by simp [PIDSmithRankIdx])).trans (pidSmithRankEquiv rank)
  row := fun k => snf.f k.down
  col := fun k => k
  diag := fun k => snf.a k.down
  row_injective := by
    intro a b h
    cases a
    cases b
    exact congrArg ULift.up (snf.f.injective h)
  col_injective := by
    intro a b h
    exact h
  entry_diag := by
    intro k
    rw [LinearMap.toMatrix_apply]
    have hrepr :
        (snf.bM.repr ((snf.bN k.down : N) : M)) (snf.f k.down) =
          snf.a k.down := by
      simpa using
        congrArg (fun x : M => snf.bM.repr x (snf.f k.down)) (snf.snf k.down)
    exact hrepr
  entry_zero := by
    intro i j h
    have hne : snf.f j.down ≠ i := by
      specialize h j
      simpa using h
    rw [LinearMap.toMatrix_apply]
    change (snf.bM.repr ((snf.bN j.down : N) : M)) i = 0
    rw [snf.snf j.down]
    simp [hne]
  divides_chain := by
    intro k hnext
    let e : Fin (Fintype.card (PIDSmithRankIdx rank)) ≃ Fin rank :=
      finCongr (by simp [PIDSmithRankIdx])
    have hnext' : (e k : Nat) + 1 < rank := by
      simpa [e, finCongr, PIDSmithRankIdx] using hnext
    simpa [e, finCongr, PIDSmithRankIdx] using hchain (e k) hnext'

/--
The matrix of the inclusion map in mathlib Smith bases satisfies this project's
local Smith normal-form predicate once the invariant-factor chain is supplied.
-/
theorem isSmithNormalForm_of_basisSmithNormalForm
    (snf : Module.Basis.SmithNormalForm N ι rank)
    (hchain : ∀ k : Fin rank, (hnext : (k : Nat) + 1 < rank) →
      snf.a k ∣ snf.a ⟨(k : Nat) + 1, hnext⟩) :
    IsSmithNormalForm (R := R) (m := ι) (n := PIDSmithRankIdx rank)
      (fun i (j : PIDSmithRankIdx rank) =>
        LinearMap.toMatrix snf.bN snf.bM N.subtype i j.down) :=
  ⟨smithNormalFormData_of_basisSmithNormalForm snf hchain⟩

/--
Reindexed version of `isSmithNormalForm_of_basisSmithNormalForm`, using an
actual basis indexed by `PIDSmithRankIdx rank`.
-/
theorem isSmithNormalForm_of_basisSmithNormalForm_reindex
    (snf : Module.Basis.SmithNormalForm N ι rank)
    (hchain : ∀ k : Fin rank, (hnext : (k : Nat) + 1 < rank) →
      snf.a k ∣ snf.a ⟨(k : Nat) + 1, hnext⟩) :
    IsSmithNormalForm
      (LinearMap.toMatrix
        (snf.bN.reindex (pidSmithRankEquiv rank)) snf.bM N.subtype) := by
  classical
  have hmat :
      LinearMap.toMatrix
          (snf.bN.reindex (pidSmithRankEquiv rank)) snf.bM N.subtype =
        (fun i (j : PIDSmithRankIdx rank) =>
          LinearMap.toMatrix snf.bN snf.bM N.subtype i j.down) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.reindex_apply, pidSmithRankEquiv]
  rw [hmat]
  exact isSmithNormalForm_of_basisSmithNormalForm snf hchain

/--
Mathlib's submodule Smith normal form, together with an explicit
invariant-factor chain, gives a full project-level Smith witness for the
inclusion matrix `N.subtype`, written with an arbitrary ambient basis on rows
and the Smith basis of `N` on columns.

This is the verified range-inclusion half of the PID matrix bridge. The
remaining bridge from an arbitrary matrix `A` to this inclusion matrix still
has to account for the map onto its range and the original column type.
-/
theorem hasSmithNormalForm_subtype_matrix_of_basisSmithNormalForm
    (b : Module.Basis ι R M)
    (snf : Module.Basis.SmithNormalForm N ι rank)
    (hchain : ∀ k : Fin rank, (hnext : (k : Nat) + 1 < rank) →
      snf.a k ∣ snf.a ⟨(k : Nat) + 1, hnext⟩) :
  HasSmithNormalForm
      (LinearMap.toMatrix
        (snf.bN.reindex (pidSmithRankEquiv rank)) b N.subtype) := by
  classical
  let bN := snf.bN.reindex (pidSmithRankEquiv rank)
  let A := LinearMap.toMatrix bN b N.subtype
  let D := LinearMap.toMatrix bN snf.bM N.subtype
  refine ⟨snf.bM.toMatrix b, 1, D,
    gaussInvertibleMatrix_basis_toMatrix snf.bM b,
    gaussInvertibleMatrix_one,
    ?_, ?_⟩
  · exact isSmithNormalForm_of_basisSmithNormalForm_reindex snf hchain
  · have hchange :
        D = snf.bM.toMatrix b * A * bN.toMatrix bN := by
      exact basis_change_toMatrix_eq_mul bN bN b snf.bM N.subtype
    simp [A, D, bN] at hchange ⊢

end SubmoduleMatrix

/--
Column basis data for a map already written as a projection on basis vectors.

This is the controlled local form of the next kernel-complement step: once PID
module theory supplies a basis of the original column module whose first block
maps to the range basis and whose second block lies in the kernel, the matrix is
definitionally the left projection `[I 0]`.
-/
structure ProjectionBasisData
    (R : Type u) [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P) : Type (u + 1) where
  basis : Module.Basis (r ⊕ k) R M
  map_inl : ∀ i : r, f (basis (Sum.inl i)) = br i
  map_inr : ∀ i : k, f (basis (Sum.inr i)) = 0

/--
A projection-compatible basis writes a linear map as the explicit left
projection matrix `[I 0]`.
-/
theorem toMatrix_projectionBasisData_eq_leftProjection
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (data : ProjectionBasisData R f br) :
    LinearMap.toMatrix data.basis br f =
      smithLeftProjection (R := R) (n := r) (κ := k) := by
  classical
  ext i j
  cases j with
  | inl j =>
      rw [LinearMap.toMatrix_apply]
      rw [data.map_inl]
      rw [Module.Basis.repr_self_apply]
      by_cases h : i = j
      · simp [smithLeftProjection, h]
      · have hji : j ≠ i := fun hji => h hji.symm
        simp [smithLeftProjection, h, hji]
  | inr j =>
      rw [LinearMap.toMatrix_apply]
      rw [data.map_inr]
      simp [smithLeftProjection]

/--
Split-product data for constructing a projection-compatible basis.

The missing PID module-theory step can target this structure: provide an
equivalence between the original column module and `P × K` such that the map
to `P` is the first projection on the basis vectors.
-/
structure ProjectionSplitEquivData
    (R : Type u) [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r : Type u} [Fintype r] [DecidableEq r]
    (f : M →ₗ[R] P) (br : Module.Basis r R P) : Type (u + 1) where
  kerIdx : Type u
  fintype_kerIdx : Fintype kerIdx
  decidableEq_kerIdx : DecidableEq kerIdx
  K : Type u
  addCommGroup_K : AddCommGroup K
  module_K : Module R K
  basis_K : Module.Basis kerIdx R K
  splitEquiv : M ≃ₗ[R] P × K
  map_inl : ∀ i : r,
    f (splitEquiv.symm (LinearMap.inl R P K (br i))) = br i
  map_inr : ∀ i : kerIdx,
    f (splitEquiv.symm (LinearMap.inr R P K (basis_K i))) = 0

attribute [instance] ProjectionSplitEquivData.fintype_kerIdx
attribute [instance] ProjectionSplitEquivData.decidableEq_kerIdx
attribute [instance] ProjectionSplitEquivData.addCommGroup_K
attribute [instance] ProjectionSplitEquivData.module_K

/--
The kernel-valued complement map associated to a right inverse `s` of `f`.

It sends `x` to `x - s (f x)`, which lies in `ker f`. Keeping this as a
separate linear map avoids unfolding the full split equivalence in later
proofs.
-/
noncomputable def kernelComplementMapOfRightInverse
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    M →ₗ[R] LinearMap.ker f where
  toFun x := by
    refine ⟨x - s (f x), ?_⟩
    have hfs : f (s (f x)) = f x := by
      have hpoint := congrArg (fun g : P →ₗ[R] P => g (f x)) hs
      simpa using hpoint
    simp [hfs]
  map_add' x y := by
    ext
    simp [map_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' a x := by
    ext
    simp [map_smul, smul_sub]

/--
A right inverse of `f` splits the domain as `P × ker f`.

The first projection of this equivalence is definitionally controlled by
`linearEquivProdKerOfRightInverse_fst_comp`, which is the shape needed by the
projection-split bridge.
-/
noncomputable def linearEquivProdKerOfRightInverse
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    M ≃ₗ[R] P × LinearMap.ker f where
  toLinearMap := LinearMap.prod f (kernelComplementMapOfRightInverse f s hs)
  invFun y := s y.1 + y.2.1
  left_inv x := by
    simp [kernelComplementMapOfRightInverse]
  right_inv y := by
    ext
    · have hfs : f (s y.1) = y.1 := by
        have hpoint := congrArg (fun g : P →ₗ[R] P => g y.1) hs
        simpa using hpoint
      simp [hfs]
    · have hfs : f (s y.1) = y.1 := by
        have hpoint := congrArg (fun g : P →ₗ[R] P => g y.1) hs
        simpa using hpoint
      have hfy : f (s y.1 + y.2.1) = y.1 := by
        simp [map_add, hfs]
      simp [kernelComplementMapOfRightInverse, hfy, add_sub_cancel_left]

/-- The split equivalence from a right inverse has first projection `f`. -/
theorem linearEquivProdKerOfRightInverse_fst_comp
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    (LinearMap.fst R P (LinearMap.ker f)).comp
        (linearEquivProdKerOfRightInverse f s hs).toLinearMap = f := by
  ext x
  rfl

/--
A split equivalence whose first projection is the original map supplies the
projection equations required by `ProjectionSplitEquivData`.

This is the preferred target for the remaining PID module-theory step: construct
`e : M ≃ₗ[R] P × K` and prove `fst ∘ e = f`, instead of proving the two
basis-vector equations directly.
-/
noncomputable def projectionSplitEquivData_of_fst_comp
    {R : Type u} [CommRing R]
    {M P K : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] [AddCommGroup K] [Module R K]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (bk : Module.Basis k R K)
    (e : M ≃ₗ[R] P × K)
    (he : (LinearMap.fst R P K).comp e.toLinearMap = f) :
    ProjectionSplitEquivData R f br where
  kerIdx := k
  fintype_kerIdx := inferInstance
  decidableEq_kerIdx := inferInstance
  K := K
  addCommGroup_K := inferInstance
  module_K := inferInstance
  basis_K := bk
  splitEquiv := e
  map_inl := by
    intro i
    have hpoint :=
      congrArg (fun g : M →ₗ[R] P =>
        g (e.symm (LinearMap.inl R P K (br i)))) he
    simpa using hpoint.symm
  map_inr := by
    intro i
    have hpoint :=
      congrArg (fun g : M →ₗ[R] P =>
        g (e.symm (LinearMap.inr R P K (bk i)))) he
    simpa using hpoint.symm

/--
A right inverse of `f` plus a basis of `ker f` supplies
`ProjectionSplitEquivData`.

For the PID bridge, the planned source of the right inverse is projectivity of
the range of `Matrix.toLin' A`, and the planned source of the kernel basis is
finite-free PID module theory.
-/
noncomputable def projectionSplitEquivData_of_rightInverse
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (s : P →ₗ[R] M) (hs : f.comp s = LinearMap.id)
    (bk : Module.Basis k R (LinearMap.ker f)) :
    ProjectionSplitEquivData R f br :=
  projectionSplitEquivData_of_fst_comp
    (f := f) (br := br) (bk := bk)
    (linearEquivProdKerOfRightInverse f s hs)
    (linearEquivProdKerOfRightInverse_fst_comp f s hs)

/--
A surjective map onto a module with a basis has a linear right inverse.

This packages the projectivity argument used for range restrictions: a module
with a basis is projective, so any surjection onto it splits.
-/
noncomputable def rightInverseOfSurjectiveOfBasis
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r : Type u} (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (hf : LinearMap.range f = ⊤) :
    {s : P →ₗ[R] M // f.comp s = LinearMap.id} := by
  classical
  haveI : Module.Projective R P := Module.Projective.of_basis br
  let h := f.exists_rightInverse_of_surjective hf
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/--
The range restriction of any map has a linear right inverse after choosing a
basis of the range.
-/
noncomputable def rightInverseOfRangeRestrictOfBasis
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r : Type u}
    (f : M →ₗ[R] P) (br : Module.Basis r R (LinearMap.range f)) :
    {s : LinearMap.range f →ₗ[R] M // f.rangeRestrict.comp s = LinearMap.id} :=
  rightInverseOfSurjectiveOfBasis f.rangeRestrict br (LinearMap.range_rangeRestrict f)

/--
Given a basis of `ker f`, projectivity of a basis on the target supplies the
section needed to build `ProjectionSplitEquivData`.
-/
noncomputable def projectionSplitEquivData_of_kernelBasis
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (hf : LinearMap.range f = ⊤)
    (bk : Module.Basis k R (LinearMap.ker f)) :
    ProjectionSplitEquivData R f br := by
  classical
  let sec := rightInverseOfSurjectiveOfBasis f br hf
  exact projectionSplitEquivData_of_rightInverse
    (f := f) (br := br) sec.val sec.property bk

/--
PID basis for the kernel of the range restriction of a finite matrix.

This is the kernel-basis input required by
`projectionSplitEquivData_of_kernelBasis`.
-/
noncomputable def kernelBasisOfRangeRestrictPid
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix m n R) :
    Σ k : ℕ, Module.Basis (Fin k) R
      (LinearMap.ker (Matrix.toLin' A).rangeRestrict) :=
  Submodule.basisOfPid (Pi.basisFun R n)
    (LinearMap.ker (Matrix.toLin' A).rangeRestrict)

/--
Construct the projection-split data for a range restriction, assuming only the
range basis from the Smith normal-form data. The remaining global bridge still
has to identify the original finite column index with the product of range and
kernel indices.
-/
noncomputable def projectionSplitEquivDataOfRangeRestrictPid
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n r : Type u} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A))) :
    ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict br := by
  classical
  let kb := kernelBasisOfRangeRestrictPid (R := R) A
  exact projectionSplitEquivData_of_kernelBasis
    (R := R)
    (M := n → R)
    (P := LinearMap.range (Matrix.toLin' A))
    (r := r)
    (k := PIDSmithRankIdx kb.1)
    (f := (Matrix.toLin' A).rangeRestrict)
    (br := br)
    (hf := LinearMap.range_rangeRestrict (Matrix.toLin' A))
    (bk := kb.2.reindex (pidSmithRankEquiv kb.1))

/--
The basis carried by split-product data determines the finite column-index
equivalence required by the matrix bridge.
-/
noncomputable def indexEquivOfProjectionSplitEquivData
    {R : Type u} [CommRing R] [InvariantBasisNumber R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {n r : Type u} [Fintype r] [DecidableEq r]
    (bn : Module.Basis n R M) (br : Module.Basis r R P)
    {f : M →ₗ[R] P}
    (data : ProjectionSplitEquivData R f br) :
    n ≃ r ⊕ data.kerIdx :=
  bn.indexEquiv ((br.prod data.basis_K).map data.splitEquiv.symm)

/--
Column-index equivalence for a matrix range restriction after constructing the
PID projection-split data.
-/
noncomputable def colEquivOfProjectionSplitEquivData
    {R : Type u} [CommRing R] [InvariantBasisNumber R]
    {m n r : Type u} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A)))
    (data : ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict br) :
    n ≃ r ⊕ data.kerIdx :=
  indexEquivOfProjectionSplitEquivData
    (R := R) (M := n → R) (P := LinearMap.range (Matrix.toLin' A))
    (bn := Pi.basisFun R n) (br := br) data

/-- A split-product equivalence supplies a projection-compatible basis. -/
noncomputable def projectionBasisData_of_splitEquivData
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r : Type u} [Fintype r] [DecidableEq r]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (data : ProjectionSplitEquivData R f br) :
    ProjectionBasisData (k := data.kerIdx) R f br where
  basis := (br.prod data.basis_K).map data.splitEquiv.symm
  map_inl := by
    intro i
    rw [Module.Basis.map_apply]
    rw [Module.Basis.prod_apply]
    exact data.map_inl i
  map_inr := by
    intro i
    rw [Module.Basis.map_apply]
    rw [Module.Basis.prod_apply]
    exact data.map_inr i

/--
Column-side data saying that the surjection from the original column module
onto the range is in split form `[I 0]` after a column basis change.

This is the remaining kernel-complement/basis-extension content needed to turn
the range-inclusion Smith witness into a Smith witness for the original matrix.
-/
structure SmithRangeSplitBasisData
    (R : Type u) [CommRing R]
    {m n r : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A))) :
    Type (u + 1) where
  kerIdx : Type u
  fintype_kerIdx : Fintype kerIdx
  decidableEq_kerIdx : DecidableEq kerIdx
  colEquiv : n ≃ r ⊕ kerIdx
  colBasis : Module.Basis (r ⊕ kerIdx) R (n → R)
  rangeRestrict_matrix :
    LinearMap.toMatrix colBasis br (Matrix.toLin' A).rangeRestrict =
      smithLeftProjection (R := R) (n := r) (κ := kerIdx)

attribute [instance] SmithRangeSplitBasisData.fintype_kerIdx
attribute [instance] SmithRangeSplitBasisData.decidableEq_kerIdx

/--
Projection-compatible basis data for the range restriction supplies the
column-side split data needed by the matrix bridge.
-/
noncomputable def smithRangeSplitBasisData_of_projectionBasisData
    {R : Type u} [CommRing R]
    {m n r k : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    [Fintype k] [DecidableEq k]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A)))
    (colEquiv : n ≃ r ⊕ k)
    (data :
      ProjectionBasisData (k := k) R (Matrix.toLin' A).rangeRestrict br) :
    SmithRangeSplitBasisData R A br where
  kerIdx := k
  fintype_kerIdx := inferInstance
  decidableEq_kerIdx := inferInstance
  colEquiv := colEquiv
  colBasis := data.basis
  rangeRestrict_matrix :=
    toMatrix_projectionBasisData_eq_leftProjection (Matrix.toLin' A).rangeRestrict br data

/--
Split-product data for the range restriction supplies the column-side split
data needed by the matrix bridge.
-/
noncomputable def smithRangeSplitBasisData_of_projectionSplitEquivData
    {R : Type u} [CommRing R]
    {m n r : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A)))
    (data :
      ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict br)
    (colEquiv : n ≃ r ⊕ ProjectionSplitEquivData.kerIdx data) :
    SmithRangeSplitBasisData R A br :=
  smithRangeSplitBasisData_of_projectionBasisData
    (A := A) (br := br) (colEquiv := colEquiv)
    (projectionBasisData_of_splitEquivData
      (Matrix.toLin' A).rangeRestrict br data)

/--
If the column-side range restriction is split as `[I 0]`, then the original
matrix inherits the Smith witness for its range inclusion.
-/
theorem hasSmithNormalForm_of_range_snf_and_splitBasis
    {R : Type u} [CommRing R]
    {m n r : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A)))
    (hIncl :
      HasSmithNormalForm
        (LinearMap.toMatrix br (Pi.basisFun R m)
          (LinearMap.range (Matrix.toLin' A)).subtype))
    (split : SmithRangeSplitBasisData R A br) :
    HasSmithNormalForm A := by
  classical
  let Acol : Matrix m (r ⊕ split.kerIdx) R :=
    LinearMap.toMatrix br (Pi.basisFun R m)
        (LinearMap.range (Matrix.toLin' A)).subtype *
      LinearMap.toMatrix split.colBasis br (Matrix.toLin' A).rangeRestrict
  have hAcol_append :
      Acol =
        smithAppendZeroCols (κ := split.kerIdx)
          (LinearMap.toMatrix br (Pi.basisFun R m)
            (LinearMap.range (Matrix.toLin' A)).subtype) := by
    simp [Acol, split.rangeRestrict_matrix, matrix_mul_smithLeftProjection]
  have hAcol_smith : HasSmithNormalForm Acol := by
    rw [hAcol_append]
    exact hasSmithNormalForm_appendZeroCols (κ := split.kerIdx) hIncl
  let bStdCol := (Pi.basisFun R n).reindex split.colEquiv
  have hAcol_factor :
      LinearMap.toMatrix split.colBasis (Pi.basisFun R m) (Matrix.toLin' A) = Acol := by
    have hfactor :=
      linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict
        (R := R) (bm := split.colBasis) (bn := Pi.basisFun R m)
        (f := Matrix.toLin' A) (br := br)
    exact hfactor
  have hAcol_basis :
      Acol =
        Matrix.reindex (Equiv.refl m) split.colEquiv A *
          bStdCol.toMatrix split.colBasis := by
    have hchange :
        LinearMap.toMatrix split.colBasis (Pi.basisFun R m) (Matrix.toLin' A) =
          LinearMap.toMatrix bStdCol (Pi.basisFun R m) (Matrix.toLin' A) *
            bStdCol.toMatrix split.colBasis := by
      simpa [bStdCol] using
        basis_change_toMatrix_eq_mul
          (R := R) bStdCol split.colBasis
          (Pi.basisFun R m) (Pi.basisFun R m) (Matrix.toLin' A)
    have hstd :
        LinearMap.toMatrix bStdCol (Pi.basisFun R m) (Matrix.toLin' A) =
          Matrix.reindex (Equiv.refl m) split.colEquiv A := by
      simpa [bStdCol] using
        toMatrix_reindex_standard_domain_eq_reindex A split.colEquiv
    rw [← hAcol_factor, hchange, hstd]
  have hReindexed :
      HasSmithNormalForm (Matrix.reindex (Equiv.refl m) split.colEquiv A) := by
    have hAcol_transport :
        Acol =
          (1 : Matrix m m R) * Matrix.reindex (Equiv.refl m) split.colEquiv A *
            bStdCol.toMatrix split.colBasis := by
      simpa [Matrix.mul_assoc] using hAcol_basis
    exact smith_transport_twoSidedUnits
      (1 : Matrix m m R) (bStdCol.toMatrix split.colBasis)
      (Matrix.reindex (Equiv.refl m) split.colEquiv A) Acol
      gaussInvertibleMatrix_one (gaussInvertibleMatrix_basis_toMatrix bStdCol split.colBasis)
      hAcol_transport hAcol_smith
  have hBack := smith_reindex (R := R) (m := m) (n := r ⊕ split.kerIdx)
    (m' := m) (n' := n) (Equiv.refl m) split.colEquiv.symm hReindexed
  simpa [Matrix.reindex_apply] using hBack

/--
Combine mathlib's Smith normal form for the range inclusion, an explicit
invariant-factor chain, and split-product column data for the range restriction.

This packages all already-verified matrix bridge pieces. The remaining PID
module-theory obligation is to construct the supplied `ProjectionSplitEquivData`
and the finite index equivalence for the original column module.
-/
theorem hasSmithNormalForm_of_basisSmithNormalForm_and_projectionSplit
    {R : Type u} [CommRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R)
    {rank : ℕ}
    (snf :
      Module.Basis.SmithNormalForm
        (LinearMap.range (Matrix.toLin' A)) m rank)
    (hchain : ∀ k : Fin rank, (hnext : (k : Nat) + 1 < rank) →
      snf.a k ∣ snf.a ⟨(k : Nat) + 1, hnext⟩)
    (split :
      ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict
        (snf.bN.reindex (pidSmithRankEquiv rank)))
    (colEquiv : n ≃ ULift.{u, 0} (Fin rank) ⊕ split.kerIdx) :
    HasSmithNormalForm A := by
  classical
  let br := snf.bN.reindex (pidSmithRankEquiv rank)
  have hIncl :
      HasSmithNormalForm
        (LinearMap.toMatrix br (Pi.basisFun R m)
          (LinearMap.range (Matrix.toLin' A)).subtype) := by
    simpa [br] using
      hasSmithNormalForm_subtype_matrix_of_basisSmithNormalForm
        (R := R) (M := (m → R)) (ι := m)
        (N := LinearMap.range (Matrix.toLin' A))
        (b := Pi.basisFun R m) (snf := snf) hchain
  let splitData :=
    smithRangeSplitBasisData_of_projectionSplitEquivData
      (A := A) (br := br) split colEquiv
  exact hasSmithNormalForm_of_range_snf_and_splitBasis
    (A := A) (br := br) hIncl splitData

/--
Mathlib's range Smith normal form plus an invariant-factor chain gives the
project-level matrix Smith witness. The column-side split data is constructed
locally from the PID range-restriction split and is not a public assumption.
-/
theorem hasSmithNormalForm_of_basisSmithNormalForm
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R)
    {rank : ℕ}
    (snf :
      Module.Basis.SmithNormalForm
        (LinearMap.range (Matrix.toLin' A)) m rank)
    (hchain : ∀ k : Fin rank, (hnext : (k : Nat) + 1 < rank) →
      snf.a k ∣ snf.a ⟨(k : Nat) + 1, hnext⟩) :
    HasSmithNormalForm A := by
  classical
  let br := snf.bN.reindex (pidSmithRankEquiv rank)
  let split := projectionSplitEquivDataOfRangeRestrictPid (R := R) (A := A) br
  let colEquiv := colEquivOfProjectionSplitEquivData (R := R) (A := A) br split
  exact hasSmithNormalForm_of_basisSmithNormalForm_and_projectionSplit
    (A := A) (snf := snf) hchain split colEquiv

/--
Strengthened mathlib range Smith normal form gives the project-level matrix
Smith witness without exposing a caller-supplied chain or projection split.
-/
theorem hasSmithNormalForm_of_basisSmithNormalFormWithChain
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R)
    {rank : ℕ}
    (snf :
      SmithNormalFormWithChain
        (LinearMap.range (Matrix.toLin' A)) m rank) :
    HasSmithNormalForm A :=
  hasSmithNormalForm_of_basisSmithNormalForm
    (A := A) (snf := snf.snf) (finDividesChain_adjacent snf.chain)

section FrameworkRoute

lemma gaussInvertibleMatrix_perm
    {R : Type u} [Semiring R]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    GaussInvertibleMatrix
      (((Equiv.toPEquiv σ).toMatrix : Matrix ι ι R)) := by
  refine ⟨((Equiv.toPEquiv σ.symm).toMatrix : Matrix ι ι R), ?_, ?_⟩
  · have h :=
      (PEquiv.toMatrix_trans (Equiv.toPEquiv σ.symm) (Equiv.toPEquiv σ)
        (α := R)).symm
    simpa [← Equiv.toPEquiv_trans, Equiv.symm_trans_self] using h
  · have h :=
      (PEquiv.toMatrix_trans (Equiv.toPEquiv σ) (Equiv.toPEquiv σ.symm)
        (α := R)).symm
    simpa [← Equiv.toPEquiv_trans, Equiv.self_trans_symm] using h

lemma swap_headTail_entry₁₁
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    (a : α) (i : Unit) :
  (Equiv.swap (headElem (α := α)) a)
      ((headTailEquiv (α := α)).symm (Sum.inl i)) = a := by
  cases i
  simp

lemma swap_headTail_entry₂₂
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    (a : α) (i : { x : α // x ≠ headElem (α := α) }) :
    (Equiv.swap (headElem (α := α)) a)
      ((headTailEquiv (α := α)).symm (Sum.inr i)) =
        (Equiv.swap (headElem (α := α)) a) i.1 := by
  simp

lemma smithNormalFormData_eq_zero_of_card_eq_zero
    {R : Type u} [Semiring R]
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {D : Matrix m n R} (data : SmithNormalFormData D)
    (hcard : Fintype.card data.r = 0) :
    D = 0 := by
  classical
  ext i j
  apply data.entry_zero
  intro k
  haveI : IsEmpty data.r := Fintype.card_eq_zero_iff.mp hcard
  exact False.elim (IsEmpty.false k)

lemma smithNormalFormData_first_dvd
    {R : Type u} [CommSemiring R]
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {D : Matrix m n R} (data : SmithNormalFormData D)
    (hcard : 0 < Fintype.card data.r)
    (j : Fin (Fintype.card data.r)) :
    data.diag (data.order ⟨0, hcard⟩) ∣ data.diag (data.order j) := by
  classical
  have h :
      ∀ t (ht : t < Fintype.card data.r),
        data.diag (data.order ⟨0, hcard⟩) ∣
          data.diag (data.order ⟨t, ht⟩) := by
    intro t
    induction t with
    | zero =>
        intro ht
        exact dvd_rfl
    | succ t ih =>
        intro ht
        have htprev : t < Fintype.card data.r := Nat.lt_of_succ_lt ht
        exact dvd_trans (ih htprev) (data.divides_chain ⟨t, htprev⟩ ht)
  exact h j.1 j.2

theorem exists_smith_descent_step_of_hasSmithNormalForm
    {R : Type u} [CommSemiring R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    {A : Matrix m n R} (hA : HasSmithNormalForm A) :
    ∃ P : Matrix m m R, ∃ Q : Matrix n n R,
      GaussInvertibleMatrix P ∧
      GaussInvertibleMatrix Q ∧
      SmithDescentReady R m n (P * A * Q) := by
  classical
  rcases hA with ⟨P₀, Q₀, D, hP₀, hQ₀, hD, hEq⟩
  rcases hD with ⟨data⟩
  by_cases hcard0 : Fintype.card data.r = 0
  · refine ⟨P₀, Q₀, hP₀, hQ₀, ?_⟩
    have hDzero := smithNormalFormData_eq_zero_of_card_eq_zero data hcard0
    have hPAQ_zero : P₀ * A * Q₀ = 0 := by
      rw [← hEq, hDzero]
    rw [hPAQ_zero]
    exact smithDescentReady_of_zero R m n
  · have hcard : 0 < Fintype.card data.r := Nat.pos_of_ne_zero hcard0
    let k₀ : data.r := data.order ⟨0, hcard⟩
    let row₀ : m := data.row k₀
    let col₀ : n := data.col k₀
    let σr : Equiv.Perm m := Equiv.swap (headElem (α := m)) row₀
    let σc : Equiv.Perm n := Equiv.swap (headElem (α := n)) col₀
    let Pr : Matrix m m R := (Equiv.toPEquiv σr).toMatrix
    let Qc : Matrix n n R := (Equiv.toPEquiv σc).toMatrix
    have hPr : GaussInvertibleMatrix Pr := by
      simpa [Pr] using gaussInvertibleMatrix_perm (R := R) σr
    have hQc : GaussInvertibleMatrix Qc := by
      simpa [Qc] using gaussInvertibleMatrix_perm (R := R) σc
    have hready : SmithDescentReady R m n (Pr * D * Qc) := by
      dsimp [SmithDescentReady]
      refine ⟨data.diag k₀, ?_, ?_, ?_, ?_⟩
      · ext i j
        cases i
        cases j
        simpa [Pr, Qc, σr, σc, k₀, row₀, col₀,
          PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
          Matrix.toBlocks₁₁, Matrix.reindex_apply, swap_headTail_entry₁₁]
          using data.entry_diag k₀
      · ext i j
        have hzero : D (σr (headElem (α := m))) (σc j.1) = 0 := by
          apply data.entry_zero
          intro k
          by_cases hk : k = k₀
          · subst k
            right
            have hσhead : σc (headElem (α := n)) = col₀ := by
              simp [σc, col₀]
            have hcol_ne : σc j.1 ≠ col₀ := by
              intro h
              have hj : j.1 = headElem (α := n) := σc.injective (by
                simpa [hσhead] using h)
              exact j.2 hj
            exact fun h => hcol_ne h.symm
          · left
            intro hrow
            have hrow' : data.row k = data.row k₀ := by
              simpa [σr, row₀] using hrow
            exact hk (data.row_injective hrow')
        cases i
        simpa [Pr, Qc, σr, σc, Matrix.toBlocks₁₂, Matrix.reindex_apply,
          PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
          headTailEquiv_symm_apply_inl, headTailEquiv_symm_apply_inr]
          using hzero
      · ext i j
        have hzero : D (σr i.1) (σc (headElem (α := n))) = 0 := by
          apply data.entry_zero
          intro k
          by_cases hk : k = k₀
          · subst k
            left
            have hσhead : σr (headElem (α := m)) = row₀ := by
              simp [σr, row₀]
            have hrow_ne : σr i.1 ≠ row₀ := by
              intro h
              have hi : i.1 = headElem (α := m) := σr.injective (by
                simpa [hσhead] using h)
              exact i.2 hi
            exact fun h => hrow_ne h.symm
          · right
            intro hcol
            have hcol' : data.col k = data.col k₀ := by
              simpa [σc, col₀] using hcol
            exact hk (data.col_injective hcol')
        cases j
        simpa [Pr, Qc, σr, σc, Matrix.toBlocks₂₁, Matrix.reindex_apply,
          PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
          headTailEquiv_symm_apply_inl, headTailEquiv_symm_apply_inr]
          using hzero
      · intro i j
        have hdiv : data.diag k₀ ∣ D (σr i.1) (σc j.1) := by
          by_cases hpos :
              ∃ k : data.r, data.row k = σr i.1 ∧ data.col k = σc j.1
          · rcases hpos with ⟨k, hrow, hcol⟩
            have hentry : D (σr i.1) (σc j.1) = data.diag k := by
              rw [← hrow, ← hcol]
              exact data.entry_diag k
            rw [hentry]
            simpa [k₀] using
              smithNormalFormData_first_dvd data hcard (data.order.symm k)
          · have hzero : D (σr i.1) (σc j.1) = 0 := by
              apply data.entry_zero
              intro k
              by_cases hrow : data.row k = σr i.1
              · right
                intro hcol
                exact hpos ⟨k, hrow, hcol⟩
              · left
                exact hrow
            rw [hzero]
            exact dvd_zero _
        simpa [Pr, Qc, σr, σc, Matrix.toBlocks₂₂, Matrix.reindex_apply,
          PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
          headTailEquiv_symm_apply_inr]
          using hdiv
    refine ⟨Pr * P₀, Q₀ * Qc, hPr.mul hP₀, hQ₀.mul hQc, ?_⟩
    have hrewrite : (Pr * P₀) * A * (Q₀ * Qc) = Pr * D * Qc := by
      calc
        (Pr * P₀) * A * (Q₀ * Qc) = Pr * (P₀ * A * Q₀) * Qc := by
          simp [Matrix.mul_assoc]
        _ = Pr * D * Qc := by
          rw [← hEq]
    simpa [hrewrite] using hready

/--
Direct PID bridge to a project-level matrix Smith witness.

The invariant-factor chain is constructed by the local strengthened PID
submodule theorem above. This theorem is kept as an auxiliary source for the
PID one-step oracle below; the public theorem routes final assembly back through
the rectangular descent framework.
-/
theorem exists_smith_normal_form_pid_bridge_direct
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A := by
  classical
  obtain ⟨rank, ⟨snf⟩⟩ :=
    Submodule.exists_smithNormalFormWithChain
      (R := R) (b := Pi.basisFun R m)
      (N := LinearMap.range (Matrix.toLin' A))
  exact hasSmithNormalForm_of_basisSmithNormalFormWithChain
    (A := A) (rank := rank) snf

/--
PID one-step oracle used by the framework route.

This oracle is intentionally nonconstructive: for each current matrix it first
uses the direct PID Smith existence bridge, then extracts the head-tail
readiness data required by the rectangular Smith driver. It is an oracle source
for a framework-routed existence proof, not a computable local Smith reduction
algorithm.
-/
noncomputable def smithStepOracle_pid
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    SmithStepOracle R m n := by
  classical
  let step (A : Matrix m n R) :=
    exists_smith_descent_step_of_hasSmithNormalForm
      (exists_smith_normal_form_pid_bridge_direct (R := R) A)
  exact
    { P := fun A => Classical.choose (step A)
      Q := fun A => Classical.choose (Classical.choose_spec (step A))
      invertible_P := by
        intro A
        exact (Classical.choose_spec (Classical.choose_spec (step A))).1
      invertible_Q := by
        intro A
        exact (Classical.choose_spec (Classical.choose_spec (step A))).2.1
      descentReady := by
        intro A
        exact (Classical.choose_spec (Classical.choose_spec (step A))).2.2 }

/--
PID-scope Smith normal form routed through the rectangular descent framework.

The PID bridge supplies the one-step `SmithStepOracle` by extracting readiness
from complete PID Smith witnesses; the final decomposition is assembled by
`exists_smith_normal_form_framework_oracle`.
-/
theorem exists_smith_normal_form_pid_framework
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A := by
  exact exists_smith_normal_form_framework_oracle
    (R := R)
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        smithStepOracle_pid (R := R) p q)
    A

/--
Public PID-scope Smith normal form theorem.

The public route is framework-routed: PID module theory supplies a one-step
oracle, and the rectangular Smith driver assembles the final witness. This is
an existence formalization, not a constructive Smith elimination algorithm.
-/
theorem exists_smith_normal_form
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A :=
  exists_smith_normal_form_pid_framework A

end FrameworkRoute

end MatDecompFormal.Instances
