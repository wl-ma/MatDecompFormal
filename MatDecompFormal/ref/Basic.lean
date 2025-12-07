import Mathlib

open Nat Matrix Classical Eq

section Eliminator

variable  {X : Type*}(r : X → X → Prop)(S : X → Prop)(h : X → Prop)
/--
注意只会在X的子集上定义
最小“消元算子”：只保证一步把 `x` 拉入 `S`，并与 `x` 具有关系 `r`.
-/
structure ElimOp where
  (E  : {x : X // h x} → X)
  (hS  : ∀ x, S (E x))
  (hr  : ∀ x, r (E x) x)
-- 只要不满足h₁的但在h₂的部分满足S，我就可以将这一部分设为id，请帮我写这个函数ElimOp r S h₁ → ElimOp r S h₂
namespace ElimOp

variable {r} {S₁ S₂ h₁ h₂ : X → Prop} (E₁ : ElimOp r S₁ h₁) (E₂ : ElimOp r S₂ h₂)
/--
`comp`：复合两个消元算子。

先用 `E₁ : ElimOp r S₁ h₁`，再用 `E₂ : ElimOp r S₂ h₂`。
只要 `S₁ ⊆ h₂`（使得 `E₁` 的输出满足 `E₂` 的前置），
再配合 `r` 的传递性，就得到新的 `ElimOp r S₂ h₁`。
-/
def comp (S₁_sub_h₂ : ∀ {x : X}, S₁ x → h₂ x) (r_trans : IsTrans X r) : ElimOp r S₂ h₁ :=
{ E  := fun x => E₂.E ⟨E₁.E x, S₁_sub_h₂ (E₁.hS x)⟩,
  hS := fun x => E₂.hS ⟨E₁.E x, S₁_sub_h₂ (E₁.hS x)⟩,
  hr := fun x => r_trans.1 _ _ _ (E₂.hr ⟨E₁.E x, S₁_sub_h₂ (E₁.hS x)⟩) (E₁.hr x) }

/--
有时你只知道“对 `E₁` 的**实际输出**满足 `h₂`”，
即提供 `toNext : ∀ x, h₂ (E₁.E x)`，
而不要求整体包含关系 `S₁ ⊆ h₂`。此时也能复合：
-/
def compOnImage (toNext : ∀ x : {x // h₁ x}, h₂ (E₁.E x)) (r_trans : IsTrans X r)
  : ElimOp r S₂ h₁ :=
{ E  := fun x => E₂.E ⟨E₁.E x, toNext x⟩,
  hS := fun x => E₂.hS ⟨E₁.E x, toNext x⟩,
  hr := fun x => r_trans.1 _ _ _ (E₂.hr ⟨E₁.E x, toNext x⟩) (E₁.hr x) }

/--
`promote`：把 `ElimOp r S h₁` 提升成 `ElimOp r S h₂`。

思路：对 `x : {x // h₂ x}`，若 `h₁ x` 则用原算子 `E₁`；
若 `¬ h₁ x` 但我们知道 `x ∈ S`，则取恒等 `id` 分支（此时需 `r` 在 `S` 上自反）。

参数：
* `cover : ∀ x, h₂ x → (h₁ x ∨ S x)`
* `r_refl_on_S : ∀ x, S x → r x x` —— 在 `S` 上 `r` 自反，保证 id 分支的关系证据。
-/
noncomputable def promote {S} (E₁ : ElimOp r S h₁)
    (cover : ∀ x, h₂ x → ¬ h₁ x → S x)(r_refl_on_S : ∀ x, S x → r x x): ElimOp r S h₂ where
  E  := fun x =>
    if h : h₁ x then E₁.E ⟨x.1, h⟩
    else x.1
  hS := by
    intro x
    by_cases h : h₁ x
    · simp [h, E₁.hS]
    simp [h, cover x.1 x.2 h]
  hr := by
    intro x
    by_cases h : h₁ x
    · simp [h, E₁.hr]
    simp [h, r_refl_on_S x.1 (cover x.1 x.2 h)]

end ElimOp

-- 注意零因子
-- 具体构造，性质很重要
-- household在复数上
-- 野心不要太大，有时候就是得实数和复数
-- 广义逆用代数定义，少依赖其他分支
-- 计划做那些工作？
end Eliminator

section induction
section


variable {X : Type*}

/-- 在允许的同尺寸变换 `r` 下，命题 `P` 可搬运。 -/
def Transport (r : X → X → Prop) (P : X → Prop) : Prop :=
  ∀ (x y), r x y → P x → P y

/--
`equivSliceInduction`
* `μ : X → ℕ` 为度量，作为归纳的良基来源；
* `r`：同尺寸“允许变换”（不必是等价关系，但通常是）；
* `S`：可切片谓词(可以理解为semi标准型)；`slice`：切片算子；
* `bridge`：在可切片态与其切片之间，命题 `P` 可搬运；
* `reachμ`：若 `μ x > 0`，则存在 `x'` 等价于 `x` 且 `x' ∈ S`，并且切片严格减小；
* `baseμ`：`μ x = 0` 的基例。
-/
theorem equivSliceInduction (μ : X → Nat) {r : X → X → Prop} {P : X → Prop}
    (trans  : Transport r P) (S : X → Prop)
    (slice  : ∀ {x}, S x → X) (bridge : ∀ {x} (hx : S x),  P (slice hx) → P x)
    (reachμ : ∀ {x}, μ x > 0 → ∃ y , ∃ (hy : S y), r y x ∧ μ (slice hy) < μ x)
    (baseμ  : ∀ {x}, μ x = 0 → P x) :
  ∀ x, P x := by
  intro x
  apply WellFounded.fix (r := fun x y => μ x < μ y)
    (WellFounded.onFun wellFounded_lt)
  intro x' hx'
  rcases (Nat.eq_zero_or_pos <| μ x') with h | h
  · exact baseμ h
  have := reachμ h
  apply trans this.choose x' this.choose_spec.choose_spec.1
  apply bridge this.choose_spec.choose
  apply hx' _ this.choose_spec.choose_spec.2

theorem equivSliceInduction_simp (μ : X → Nat) {r : X → X → Prop} {P S: X → Prop}
    (trans  : Transport r P) (slice : {x : X // μ x > 0} → X)
    (bridge : ∀ x,  S x.1 → P (slice x) → P x)
    (reachμ : ∀ {x}, μ x > 0 → ∃ y : {x : X // μ x > 0} , S y ∧ r y x ∧ μ (slice y) < μ x)
    (baseμ  : ∀ {x}, μ x = 0 → P x) :
    ∀ x, P x := by
  intro x
  apply WellFounded.fix (r := fun x y => μ x < μ y)
    (WellFounded.onFun wellFounded_lt)
  intro x' hx'
  rcases (Nat.eq_zero_or_pos <| μ x') with h | h
  · exact baseμ h
  have := reachμ h
  apply trans this.choose x' this.choose_spec.2.1
  apply bridge _  this.choose_spec.1 (hx' _ this.choose_spec.2.2)


theorem equivSliceInduction_simp_base (b : Nat)
    (μ : X → Nat) {r : X → X → Prop} {P S: X → Prop}
    (trans  : Transport r P) (slice : {x : X // μ x > b} → X)
    (bridge : ∀ x,  S x.1 → P (slice x) → P x)
    (reachμ : ∀ {x}, μ x > b → ∃ y : {x : X // μ x > b} , S y ∧ r y x ∧ μ (slice y) < μ x)
    (baseμ  : ∀ {x}, μ x ≤ b → P x) :
    ∀ x, μ x ≥ b → P x := by
  intro x hx
  apply WellFounded.fix (r := fun x y => μ x - b  < μ y - b)
    (WellFounded.onFun wellFounded_lt)
  intro x' hx'
  rcases (Nat.eq_zero_or_pos <| μ x' - b) with h | h
  · apply baseμ <| Nat.le_of_sub_eq_zero h

  rcases reachμ (Nat.lt_of_sub_pos h) with ⟨y, hys, hyr, hsy⟩
  apply trans y x' hyr
  apply bridge _  hys
  by_cases htb : μ (slice y) < b
  · apply baseμ (le_of_succ_le htb)
  apply hx'
  simp at htb
  exact Nat.sub_lt_sub_right htb hsy




  -- apply hx'
  -- apply Nat.sub_lt_sub_right htb hsy
  -- apply?


  -- apply bridge

  -- apply baseμ
  -- apply trans y x' hyr
  -- apply bridge _  hys
  -- apply hx'
  -- refine Nat.sub_lt_sub_right ?_ hsy







  -- a < b
  -- b - d > 0
  -- a - d < b - d
  -- refine Nat.sub_lt_sub_right ?_ ?_
  -- apply?



  -- (hx' _ this.choose_spec.2.2)
    -- intro x hb
    -- refine equivSliceInduction_simp (S := S) (fun x ↦ μ x - b) trans ?_ ?_ ?_ ?_ x
    -- · exact fun i ↦ slice ⟨i.1, Nat.lt_of_sub_pos i.2⟩

    -- · intro y hsy hp
    --   exact bridge ⟨y.1, Nat.lt_of_sub_pos y.2⟩ hsy hp
    -- · intro y hy
    --   rcases reachμ (Nat.lt_of_sub_pos hy) with ⟨z, hzs, hzr, hzf⟩
    --   have := z.2
    --   let uy : { x // (fun x ↦ μ x - b) x > 0 } := ⟨z.1, zero_lt_sub_of_lt z.2⟩
    --   use uy
    --   constructor
    --   · exact hzs
    --   constructor
    --   · exact hzr
    --   simp
    --   refine Nat.sub_lt_sub_right ?_ hzf
    --   simp [uy]
    --   sorry













end

section

variable {X : Type*} (μ : X → Nat)
/-- `μ` 对关系 `r` 的单调性：沿 `r` 不增。多数矩阵场景可取更强的相等。 -/
def MuMono  (r : X → X → Prop) : Prop :=
  ∀ {y x}, r y x → μ y ≤ μ x

/-- 切片系统的进展性：在 `S` 上切片严格递降 -/
def SliceProgress (S : X → Prop) (slice : ∀ {x}, S x → X) : Prop :=
  ∀ {x} (hx : S x), μ (slice hx) < μ x

/-- 切片系统的进展性：在 `S` 上切片严格递降 -/
def SlicePro (slice : { x // μ x > 0 } → X) : Prop :=
  ∀ x, μ (slice x) < μ x

variable  {r : X → X → Prop} {S : X → Prop}

/-- 用最小 `ElimOp` + 度量单调性 + 切片进展性生成 `reachμ`。 -/
lemma reachμ_of_ElimOp_Slice
    (slice : ∀ {x}, S x → X) (E : ElimOp r S (fun x ↦ μ x > 0))
    (mono  : MuMono μ r) (prog  : SliceProgress μ S @slice) :
  ∀ {x}, μ x > 0 →
    ∃ y, ∃ (hy : S y), r y x ∧ μ (slice hy) < μ x := by
  intro y hy
  let x : {x : X // μ x > 0} := ⟨y, hy⟩
  exact ⟨E.E x, E.hS x, E.hr x, lt_of_lt_of_le (prog (E.hS x)) (mono (E.hr x))⟩

/-- 以最小 `ElimOp` 结合 `MuMono` 与 `SliceProgress`  -/
theorem equivSliceInduction_viaElimOp
    (P S : X → Prop) (trans  : Transport r P)
    (slice  : ∀ {x}, S x → X)
    (bridge : ∀ {x} (hx : S x),  P (slice hx) → P x)
    (E      : ElimOp r S (fun x ↦ μ x > 0))
    (mono : MuMono μ r) (prog : SliceProgress μ S (@slice))
    (baseμ  : ∀ {x}, μ x = 0 → P x) :
  ∀ x, P x := equivSliceInduction μ
          trans S slice bridge (fun {_} a ↦ reachμ_of_ElimOp_Slice μ slice E mono prog a) baseμ

variable {P h: X → Prop}

lemma reachμ_of_ElimOp_Slice_simp
    (slice : { x // μ x > 0 } → X) (E : ElimOp r S (fun x ↦ μ x > 0))
    (mono  : MuMono μ r) (prog  : SlicePro μ slice)
    (hsh : ∀ x, S x → μ x > 0) :
  ∀ {x}, μ x > 0 →
    ∃ y : { x // μ x > 0 }, S y ∧ r y x ∧ μ (slice y) < μ x := by
  intro y hy
  let x : { x // μ x > 0} := ⟨y, hy⟩
  let u : { x // μ x > 0} := ⟨E.E x, hsh _ (E.hS x)⟩
  refine ⟨u , E.hS x, E.hr x, lt_of_lt_of_le (prog u) (mono (E.hr x))⟩



theorem equivSliceInduction_viaElimOp_simp
    (trans  : Transport r P)
    (slice  : { x // μ x > 0 } → X)
    (bridge : ∀ x, S x.1 → P (slice x) → P x)
    (E      : ElimOp r S (fun x ↦ μ x > 0))
    (mono : MuMono μ r) (prog : SlicePro μ slice)
    (baseμ  : ∀ {x}, μ x = 0 → P x)
    (hsh : ∀ x, S x → μ x > 0) :
  ∀ x, P x := equivSliceInduction_simp μ
          trans slice bridge (fun {_} a ↦ reachμ_of_ElimOp_Slice_simp μ slice E mono prog hsh a) baseμ


-- lemma reachμ_of_ElimOp_Slice_simp_base
--     (slice : { x // μ x > b } → X) (E : ElimOp r S (fun x ↦ μ x > b))
--     (mono  : MuMono μ r) (prog  : SlicePro μ slice)
--     (hsh : ∀ x, S x → μ x > 0) :
--   ∀ {x}, μ x > 0 →
--     ∃ y : { x // μ x > 0 }, S y ∧ r y x ∧ μ (slice y) < μ x := by
--   intro y hy
--   let x : { x // μ x > 0} := ⟨y, hy⟩
--   let u : { x // μ x > 0} := ⟨E.E x, hsh _ (E.hS x)⟩
--   refine ⟨u , E.hS x, E.hr x, lt_of_lt_of_le (prog u) (mono (E.hr x))⟩

-- theorem equivSliceInduction_viaElimOp_simp_base
--     (b : Nat)
--     (trans  : Transport r P)
--     (slice  : { x // μ x > b } → X)
--     (bridge : ∀ x, S x.1 → P (slice x) → P x)
--     (E      : ElimOp r S (fun x ↦ μ x > b))
--     (mono : MuMono μ r) (prog : SlicePro μ slice)
--     (baseμ  : ∀ {x}, μ x = b → P x)
--     (hsh : ∀ x, S x → μ x > 0) :
--   ∀ x, P x := equivSliceInduction_simp_base b μ
--           trans slice bridge (fun {_} a ↦ reachμ_of_ElimOp_Slice_simp μ slice E mono prog hsh a) baseμ

end

section MatObj

/-- 统一封装“行数、列数、矩阵本体”的对象。 -/
@[ext, class] structure MatObjsize where (m n : ℕ)

@[ext, class] structure MatObj (R : Type*) extends size : MatObjsize where
  (A : Matrix (Fin m) (Fin n) R)

section

class FamilyMulAction {I} (G : I → Type*) [∀ mn, Monoid (G mn)] (T : I → Type*) where
    FM : ∀ i, MulAction (G i) (T i)

namespace MatObj

variable {R : Type*} {G : MatObjsize → Type*}

variable [∀ mn, Monoid (G mn)] [f :  FamilyMulAction G (fun mn ↦ Matrix (Fin mn.1) (Fin mn.2) R)]

@[simp]
instance [s : MatObjsize] : MulAction (G s) (Matrix (Fin s.m) (Fin s.n) R) := f.FM s

@[simp]
instance [s : MatObjsize] [x : MatObj R] [hs : Fact (x.size = s)] :
    Coe (Matrix (Fin (MatObjsize.m x.size)) (Fin (MatObjsize.n x.size)) R)
      (Matrix (Fin (MatObjsize.m s)) (Fin (MatObjsize.n s)) R) where
  coe A := cast (by simp [hs.1]) A

/-- 作用提升到 `MatObj` 层（只在同尺寸上定义）。 -/
@[simp] def _root_.MatrixFiberMulAction.smulObj (s : MatObjsize)
    (x : MatObj R) (hs : Fact (x.size = s)) (g : G s) : MatObj R :=
  MatObj.mk s (g • x.A)


@[simp]
abbrev MatObjwithsize (R) (s : MatObjsize) := {y : MatObj R // y.size = s}

@[simp]
instance [s : MatObjsize] : SMul (G s) (MatObjwithsize R s) where
  smul g y := ⟨MatrixFiberMulAction.smulObj s y.1 ⟨y.2⟩ g, rfl⟩

/-- `smulObj` 保持尺寸（定义等同），便于 `simp`。 -/
@[simp] lemma smulObj_m  (x : MatObj R) (g : G x.size) :
    (g • (⟨x , rfl⟩ : MatObjwithsize R x.size)).1.m = x.m := rfl

@[simp] lemma smulObj_n  (x : MatObj R) (g : G x.size) :
    (g • (⟨x , rfl⟩ : MatObjwithsize R x.size)).1.n = x.n := rfl

lemma eq_A_of_eq {x y : MatObj R} (h : Fact (x.size = y.size))
  (ha : x.A = y.A) : x = y := by
  ext
  · simp [h.1]
  · simp [h.1]
  exact heq_of_eqRec_eq (cast (by simp [h.1]) h.1) ha


lemma MatObjwithsize.one_smul {s : MatObjsize} {x : MatObj R} (hs : x.size = s) :
  (1 : G s) • (⟨x , hs⟩ : MatObjwithsize R s) = ⟨x, hs⟩ := by
  cases hs
  simp [HSMul.hSMul]
  apply eq_A_of_eq ⟨by simp⟩
  · simp
    exact (f.FM x.size).one_smul (A x)


lemma MatObjwithsize.mul_smul {s : MatObjsize} {g : MatObj R} (hs : g.size = s )(x y : G s) :
   (x * y) • (⟨g, hs⟩ :  MatObjwithsize R s) = x • y • (⟨g, hs⟩ :  MatObjwithsize R s) := by
  cases hs
  simpa [HSMul.hSMul] using (f.FM g.size).mul_smul x y (A g)

@[simp]
instance [s : MatObjsize] : MulAction (G s) (MatObjwithsize R s) where
  smul := (· • ·)
  one_smul x :=  MatObjwithsize.one_smul x.2
  mul_smul x y g := MatObjwithsize.mul_smul g.2 x y

@[simp]
instance [s : MatObjsize] : Coe (MatObjwithsize R s) (MatObj R) where
  coe A := A.1

@[simp]
def MatObjwithsize.mkMat (x : MatObj R) : (MatObjwithsize R x.size) :=
  ⟨x, rfl⟩

open MatObjwithsize

/-- “一步允许变换”：`y` 由某个同纤维变换作用得到。 -/
def RelAct (f : FamilyMulAction G (fun mn ↦ Matrix (Fin mn.1) (Fin mn.2) R)) (y x : MatObj R) :
  Prop := ∃ g : G x.size, y = (g • (mkMat x)).1

/-- “存在某个同纤维变换使得性质 P 成立”。 -/
def ExistsAfter (f :  FamilyMulAction G (fun mn ↦ Matrix (Fin mn.1) (Fin mn.2) R))
  (P : MatObj R → Prop) (x : MatObj R) : Prop :=
  ∃ g : G x.size, P (g • (mkMat x)).1

end MatObj

/-- **关键搬运律**：由 fiber 作用生成的关系，给“存在式”命题的 Transport。 -/
lemma transport_from_FiberMulAction {R : Type*} {G : MatObjsize → Type*} [∀ mn, Monoid (G mn)]
   (f : FamilyMulAction G (fun s ↦ Matrix (Fin s.m) (Fin s.n) R))
   (P : MatObj R → Prop) :
    Transport (MatObj.RelAct f) (MatObj.ExistsAfter f P) := by
  intro x y hrel hPy
  rcases hrel with ⟨g, rfl⟩
  simp [MatObj.ExistsAfter] at hPy
  rcases hPy with ⟨h, Hy⟩
  refine ⟨h * g, ?_⟩
  rwa [MulAction.mul_smul]

end

section

open MatObj

open MatObjwithsize

variable {R : Type*} {G : MatObjsize → Type*} [∀ mn, Monoid (G mn)]
  (f : FamilyMulAction G (fun s ↦ Matrix (Fin s.m) (Fin s.n) R))
  (S : MatObj R → Prop)
-- /-- S 与 slice（右下/尾主块） -/
-- def SliceProgress {X} (μ : X → Nat) (S : X → Prop) (slice : ∀ {x}, S x → X) : Prop :=
--   ∀ {x} (hx : S x), μ (slice hx) < μ x

variable (G) {S} in
/-- 把对子问题的变换（在 slice 的尺寸上）提升为原尺寸上的变换。 -/
def Lift (μ : MatObj R → Nat) (slice : {x // μ x > 0} → MatObj R) :=
  ∀ x, G (slice x).size → G x.1.size

-- structure ElimOp where
  -- (E  : {x : X // h x} → X)
  -- (hS  : ∀ x, S (E x))
  -- (hr  : ∀ x, r (E x) x)
/-- 提升的正确性：P 在切片经 g 成立 ⇒ P 在原对象经 lift g 成立。 -/
def LiftSpec' (μ : MatObj R → Nat) (P : MatObj R → Prop)
  (slice : {x // μ x > 0} → MatObj R)
  (lift : Lift G μ slice)
  (E : {x // μ x > 0} → MatObj R) : Prop :=
  ∀ {x} (g : G (slice x).size), x.1 ∈ (E '' Set.univ) →
    P (g • (mkMat (slice x))).1 → P ((lift x g) • (mkMat x)).1

def LiftSpec (μ : MatObj R → Nat) (S P : MatObj R → Prop)
  (slice : {x // μ x > 0} → MatObj R)
  (lift : Lift G μ slice) : Prop :=
  ∀ {x} (g : G (slice x).size), S x.1 →
    P (g • (mkMat (slice x))).1 → P ((lift x g) • (mkMat x)).1
-- g • (mkMat (slice hx))).1 → P ((lift hx g) • (mkMat x)).1
lemma bridge_existsAfter (μ : MatObj R → Nat) (S P : MatObj R → Prop)
  (slice : {x // μ x > 0} → MatObj R)
  (lift : Lift G μ slice) (lspec : LiftSpec f μ S P slice lift) :
  ∀ x, S x.1 → ExistsAfter f P (slice x) → ExistsAfter f P x := by
  intro x sx hx; rcases hx with ⟨g, Hg⟩
  exact ⟨lift _ g, lspec g sx Hg⟩

end

section


open MatObj

open MatObjwithsize

variable {R : Type*} {G : MatObjsize → Type*} [(mn : MatObjsize) → Monoid (G mn)]
  (f : FamilyMulAction G fun mn ↦ Matrix (Fin (MatObjsize.m mn)) (Fin (MatObjsize.n mn)) R)

/-- 若“一步消元”确为“选一个群元 `gE x` 后作用一次”，
    且作用后落入 `S`，即可生成最小消元算子。 -/
def ElimOp.fromAction (S : MatObj R → Prop) (h : MatObj R → Prop)
  (gE : (x : {x : MatObj R // h x}) → G x.1.size)
  (intoS : ∀ x, S ((gE x) • (mkMat x.1)).1) :
  ElimOp (RelAct f) S h :=
{ E  := fun x => ((gE x) • (mkMat x.1)).1
, hS := by intro x; simpa using intoS x
, hr := by intro x; exact ⟨gE x, rfl⟩ }

open MatObj

/-- 面向 `MatObj` 的“存在式”特化：一行得到 `∃ g，同纤维 Good(g • x)`。 -/
theorem equivSliceInduction_viaElimOp_exists_mat
    (μ : MatObj R → Nat) (S : MatObj R → Prop)
    (slice : {x // μ x > 0} → MatObj R)
    (Good : MatObj R → Prop)
    (lift : Lift G μ slice)
    (lspec : LiftSpec f μ S Good slice lift)
    (E : ElimOp (RelAct f) S (fun x => μ x > 0))
    (mono : MuMono μ (RelAct f))
    (prog : SlicePro μ slice)
    (baseμ : ∀ {x}, μ x = 0 → ExistsAfter f Good x)
    (hsh : ∀ x, S x → μ x > 0) :
  ∀ x, ExistsAfter f Good x :=
  equivSliceInduction_viaElimOp_simp μ (transport_from_FiberMulAction f Good)
    slice  (bridge_existsAfter f μ S Good slice lift lspec)  E mono prog baseμ hsh


end

namespace MatObj

open MatObj

open MatObjwithsize

variable {R : Type*} {G : MatObjsize → Type*}
variable [∀ mn, Monoid (G mn)]
variable (f : FamilyMulAction G (fun mn ↦ Matrix (Fin mn.1) (Fin mn.2) R))

/--
便捷版：用“一步作用”直接生成消元算子并套用存在式归纳结论。

只需提供：
* `gE : {x // μ x.1 > 0} → G (size x.1)`：一步选取的纤维内变换；
* `intoS`：作用一次后落入 `S`；
* `mono`：`μ` 对 `RelAct` 单调（不增）；
* `prog`：在 `S` 上切片严格递降；
* `lift, lspec`：把对子问题的变换升格为原对象的变换并保持 `Good`；
* `baseμ`：基例（`μ x = 0`）的存在式见证。
-/
theorem equivSliceInduction_viaAction_exists_mat
    (μ : MatObj R → Nat) (S : MatObj R → Prop)
    (slice : {x : MatObj R // μ x > 0} → MatObj R)
    (Good : MatObj R → Prop)
    (lift : Lift G μ slice)
    -- lift的矩阵一般有结构，所以我们lift的构造需要依赖于消元算子
    -- 比如rank为r的矩阵我们进行到 r + 1 行，接下来就不用lift了因为全是0
    --  ∀ x, G (slice x).size → G x.1.size
    --  x 0 0 = 0 → x = 0
    -- (gE x) • (mkMat x.1)

    (lspec : LiftSpec f μ S Good slice lift)
    (gE : (x : {x : MatObj R // μ x > 0}) → G x.1.size)
    (intoS : ∀ x, S ((gE x) • (mkMat x.1)).1)
    (mono : MuMono μ (RelAct f))
    (prog : SlicePro μ slice)
    (baseμ : ∀ {x}, μ x = 0 → ExistsAfter f Good x)
    (hsh : ∀ x, S x → μ x > 0) :
  ∀ x, ExistsAfter f Good x := equivSliceInduction_viaElimOp_exists_mat f
      μ S (@slice) Good lift lspec (ElimOp.fromAction f
      S (fun x => μ x > 0) gE intoS) mono prog (by intro; exact baseμ) hsh

end MatObj


namespace MatObj

variable {R : Type*}

section slice
/-- 移除矩阵的第一行和第一列（行列数各减1）。要求矩阵至少有一行一列。 -/
@[simp]
def remove_first_row_and_col (x : MatObj R) : MatObj R where
  m := x.m - 1
  n := x.n - 1
  A := x.A.submatrix (fun t => ⟨t.1, lt_of_lt_pred t.2⟩) (fun t => ⟨t.1, lt_of_lt_pred t.2⟩)

@[simp]
lemma remove_first_row_and_col_n {x : MatObj R} :
  x.remove_first_row_and_col.n = x.n - 1 := rfl

@[simp]
lemma remove_first_row_and_col_m {x : MatObj R}  :
  x.remove_first_row_and_col.n = x.n - 1 := rfl

end slice

section SameSize

variable {R : Type*} {x y z : MatObj R}

/-- 由等式 `x = y` 得到 `SameSize x y` -/
instance ofEq [h : Fact (x = y)] : x.size = y.size := by
  cases h.1;
  rfl

lemma refl : x.size = x.size := rfl

/-- 对称与传递（方便组合使用）。 -/
lemma symm (hxy : x.size = y.size) : y.size = x.size := by
  simp [hxy]

lemma trans (hxy : x.size = y.size) (hyz : y.size = z.size) : x.size = z.size := by
  simp [hxy, hyz]

end SameSize

/-- 在 *给定* 尺寸一致的证据下，允许从 `x` 尺寸矩阵**自动**转到 `y` 尺寸矩阵。-/
instance [x : MatObj R] [y : MatObj R][h : Fact (x.size = y.size)] :
    Coe (Matrix (Fin x.m) (Fin x.n) R) (Matrix (Fin y.m) (Fin y.n) R) where
  coe A := cast (by simp [h.1]) A

instance [x : MatObj R] [y : MatObj R][h : Fact (x = y)] :
  Fact (x.size = y.size) := by
  apply Fact.mk
  rw [h.1]

/-- 从 `h : x = y` 推出 `x.A` 与 `y.A` 在 `y` 尺寸下可比且相等。 -/
lemma eq_A_of_eq' [x : MatObj R] [y : MatObj R] (h : Fact (x = y)):
    x.A  = y.A := by
  simp [cast]
  sorry

/-- 把“定长矩阵上的性质” `Q`（依赖 m,n）提升为 `MatObj` 上的性质。 -/
def liftP (Q : ∀ {m n}, Matrix (Fin m) (Fin n) R → Prop) :
  MatObj R → Prop := fun x => Q x.A

def μ (x : MatObj R) : ℕ := x.m * x.n

end MatObj

end MatObj

#check finCongr
noncomputable def Matrix.GeneralLinearGroup.congr (R){m l}
    [Fintype m][DecidableEq m][Fintype l][DecidableEq l] [CommRing R] (h : m = l) :
    GL m R = GL l R  := by
  sorry

section BiGLFamilyMulAction

-- variable (m n R : Type*)
-- [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n][CommRing R]
variable (R : Type) [CommRing R]

#check MatObj.equivSliceInduction_viaAction_exists_mat

/-- 双侧作用群：`G_L × G_R`. -/
@[simp] def BiGL  (R : Type) [CommRing R] : MatObjsize → Type :=
    fun i : MatObjsize ↦ (GL (Fin i.m) R) × (GL (Fin (i.n)) R)

instance (R : Type) [CommRing R] : (i : MatObjsize) → Monoid (BiGL R i) :=
  fun _ => Prod.instMonoid

instance {i} : MulAction (BiGL R i) (Matrix (Fin (i.m)) (Fin (i.n)) R) where
  smul gh A := gh.1.1 * A * gh.2.2
  one_smul := by
    intro A; simp [HSMul.hSMul]
  mul_smul := by
    intro g₁ g₂ A
    simp [HSMul.hSMul, Matrix.mul_assoc]

instance {i} : DistribMulAction (BiGL R i) (Matrix (Fin (i.m)) (Fin (i.n)) R) where
  smul_zero := by
    intro a
    simp only [HSMul.hSMul, SMul.smul, Matrix.mul_zero, Units.inv_eq_val_inv, Matrix.coe_units_inv,
      Matrix.zero_mul]
  smul_add := by
    intro a x y
    simp only [HSMul.hSMul, SMul.smul, Matrix.mul_add, Units.inv_eq_val_inv, Matrix.coe_units_inv,
      Matrix.add_mul]

/-- 双侧作用：`(g,h) ▷ A = g · A · h⁻¹`. -/
instance fma : @FamilyMulAction MatObjsize (BiGL R) _ (fun i : MatObjsize  ↦ Matrix (Fin (i.m)) (Fin (i.n)) R) where
    FM := @instMulActionBiGLMatrixFinMN R _

end BiGLFamilyMulAction

variable {R : Type*}

section S_col_row_one_Ready

/-- Gauss 风格“可切片谓词”：“首列首行除第一个外为 0”。 -/
class S_col_row_one_Ready [Zero R] [One R] (x : MatObj R) : Prop where
  hm : NeZero x.m
  hn : NeZero x.n
  hfm : ∀ i : Fin x.m, i.1 > 0 → x.A i 0 = 0
  hfn : ∀ j : Fin x.n, j.1 > 0 → x.A 0 j = 0
  -- h11 : x.A 0 0 = 1

namespace S_col_row_one_Ready

instance [Zero R] [One R] {x : MatObj R} [hx : S_col_row_one_Ready x]: NeZero x.m := hx.hm

instance [Zero R] [One R]{x : MatObj R} [hx :S_col_row_one_Ready x] : NeZero x.n := hx.hn


lemma S_col1Ready_prog [Zero R] :
    SlicePro (X := MatObj R) MatObj.μ (fun x => MatObj.remove_first_row_and_col x.1) := by
  intro x
  have := x.2
  simp [MatObj.μ] at  *
  exact Nat.mul_lt_mul'' (by simp [this.1]) (by simp [this.2])

end S_col_row_one_Ready

end S_col_row_one_Ready

section lift
-- lift : Lift G μ slice
#check Lift

open MatObj
variable (R : Type)

/-- Equivalence between `Fin n` and the direct sum `Fin 1 ⊕ Fin (n-1)` when n > 0 -/
def finSplitEquiv {n} (hn : n > 0) : Fin n ≃ Fin 1 ⊕ Fin (n - 1) :=
    (finCongr (m := 1 + (n - 1)) (add_sub_of_le hn).symm).trans finSumFinEquiv.symm

/-- Embed a smaller matrix into a larger one by adding a 1 in top-left corner and zeros elsewhere -/
@[simp]
def matrixEmbedding [Zero R]{n} (hn : n > 0)
      (r : Matrix (Fin 1) (Fin 1) R)
      (x : Matrix (Fin (n - 1)) (Fin (n - 1)) R) :
     Matrix (Fin n) (Fin n) R :=
  (fromBlocks r 0 0 x).submatrix (finSplitEquiv hn) (finSplitEquiv hn)

/-- Lift an invertible (n-1)×(n-1) matrix to an invertible n×n matrix -/
def invertibleLift [CommRing R] {n} (hn : n > 0)
    (r : GL (Fin 1) R) (x : GL (Fin (n - 1)) R) : GL (Fin n) R where
  val := matrixEmbedding R hn r.1 x.1
  inv := matrixEmbedding R hn r.2 x.2
  val_inv := by
    simp only [matrixEmbedding, Units.inv_eq_val_inv, coe_units_inv, ---inv_subsingleton,
      submatrix_mul_equiv, fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.zero_mul,
      isUnits_det_units, mul_nonsing_inv, zero_add, fromBlocks_one, submatrix_one_equiv]
  inv_val := by
    simp only [matrixEmbedding, Units.inv_eq_val_inv, coe_units_inv, ---inv_subsingleton,
      submatrix_mul_equiv, fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.zero_mul]
    simp only [isUnits_det_units, nonsing_inv_mul, zero_add]
    simp

instance [Zero R] {x : { x : MatObj R// MatObj.μ x > 0 }} : NeZero x.1.m := by
  have := x.2
  simp [μ] at this
  exact NeZero.of_pos this.1

instance [Zero R] {x : { x : MatObj R// MatObj.μ x > 0 }} : NeZero x.1.n := by
  have := x.2
  simp [μ] at this
  exact NeZero.of_pos this.2
@[simp]
lemma aux_aux [Ring R] : !![(1 : R)] = 1 := by
  funext i j
  rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  simp only [Fin.isValue, of_apply, cons_val',
    cons_val_fin_one, one_apply_eq]

#check IsUnit
def aux [CommRing R] (r : Units R): GL (Fin 1) R where
  val := !![r.1]
  inv := !![r.2]
  val_inv := by simp;
  inv_val := by simp;

-- 左上角是0的话还得有一个permutation，保持I_r在左上角
-- 但是本质上这个是不应该证明的，因为我们做的过程中已经可以保证I_r在左上角
-- 需要思考

/-- Gaussian lifting operation that preserves matrix properties -/
noncomputable def GaussLift [CommRing R]:
  Lift (R := R) (BiGL R) μ (fun x => remove_first_row_and_col x.1) :=
  fun x hx =>
    if hxa : IsUnit (x.1.A 0 0) then
      ⟨invertibleLift R (Nat.pos_of_mul_pos_right x.2) 1 hx.1,
           invertibleLift R (Nat.pos_of_mul_pos_left x.2) (aux R hxa.choose) hx.2⟩
    else
      ⟨invertibleLift R (Nat.pos_of_mul_pos_right x.2) 1 hx.1,
           invertibleLift R (Nat.pos_of_mul_pos_left x.2) 1 hx.2⟩
end lift

section Good

def rankStdBlock (K : Type*) [Zero K] [One K]
    (m n r : ℕ) : Matrix (Fin m) (Fin n) K :=
  fun i j => if (i : ℕ) < r ∧ (j : ℕ) < r ∧ i.1 = j.1 then 1
          else 0
#eval rankStdBlock ℕ 5 5 4
-- def rank_normal_form
end Good

section LiftSpec
open MatObj MatObjsize MatObjwithsize
-- (lspec : LiftSpec f μ Good slice lift)

variable (R : Type) [CommRing R]
-- 先构造消元算子！！！

theorem GaussliftSpec : LiftSpec (fma R) MatObj.μ S_col_row_one_Ready
    (fun x ↦ MatObj.A x = rankStdBlock R (MatObjsize.m x.size) (MatObjsize.n x.size) (MatObj.A x).rank)
    (fun x ↦ x.1.remove_first_row_and_col) (GaussLift R) := by
  -- simp only [LiftSpec]

  intro x g hs hg
  by_cases hxa : IsUnit (x.1.A 0 0)
  · simp [GaussLift, HSMul.hSMul, SMul.smul, hxa] at *
    funext i j
    by_cases hra : i < (A x.1).rank ∧ j < (A x.1).rank ∧ i = j.1
    · simp [rankStdBlock, hra, invertibleLift, finSplitEquiv]
      sorry

    sorry
  sorry


  -- simp [GaussLift, HSMul.hSMul, SMul.smul] at hg


end LiftSpec
variable (R : Type) [CommRing R]

#check MatObj.equivSliceInduction_viaAction_exists_mat (fma R) MatObj.μ S_col_row_one_Ready
  (fun x => MatObj.remove_first_row_and_col x.1)
  (fun x => x.A = rankStdBlock R x.m x.n x.A.rank)
  (GaussLift R) _

example : (a : Nat) → (b : Nat) → a + b = b + a :=
  fun x y => Nat.add_comm x y
structure RingI where
  t : Type
  c : Ring t
noncomputable instance RingI_inst
   {l}[Fintype l] : Ring (Matrix l l ℝ) := by
  exact instRing

example {α} (a b c : α) [LT α]
  (hab : a < b)(hbc : b < c) : a < c := by
 sorry
#check Matrix.det
-- (a b c : ℝ)→ (hab : a < b)→ (hbc : b < c) →  a < c

-- {α : Type u_1} → [Preorder α] → {a b c : α} →  a < b → b < c → a < c


-- example (l : Type) : RingI  :=
--   ⟨Matrix l l ℝ ,
--   by
--     infer_instance
--   ⟩
