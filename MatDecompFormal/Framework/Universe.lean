/-
Copyright (c) 2026 Wanli Ma, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanli Ma, Zichen Wang
-/
import Mathlib

namespace MatDecompFormal.Framework

/-!
# Matrix Universe

This file defines the framework's universe types using only `Type*`,
existing instances, and thin wrapper structures. The recursive framework
should reason about index types directly.
-/

/-- A rectangular matrix universe packaged directly as a structure. -/
structure RectUniverse (R : Type*) where
  ι : Type*
  [fintype_ι : Fintype ι]
  [decEq_ι : DecidableEq ι]
  [linOrder_ι : LinearOrder ι]
  κ : Type*
  [fintype_κ : Fintype κ]
  [decEq_κ : DecidableEq κ]
  [linOrder_κ : LinearOrder κ]
  A : Matrix ι κ R

attribute [instance] RectUniverse.fintype_ι RectUniverse.decEq_ι RectUniverse.linOrder_ι
attribute [instance] RectUniverse.fintype_κ RectUniverse.decEq_κ RectUniverse.linOrder_κ
namespace RectUniverse

@[simp] def ofMatrix {R : Type*} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (A : Matrix ι κ R) : RectUniverse R :=
  { ι := ι, κ := κ, A := A }

end RectUniverse

/-- Positive rectangular universe objects are those whose row/column cardinals are nonzero. -/
abbrev PosRectUniverse (R : Type*) :=
  { x : RectUniverse R // 0 < Fintype.card x.ι ∧ 0 < Fintype.card x.κ }

/-- A square matrix universe packaged directly as a structure. -/
structure SquareUniverse (R : Type*) where
  ι : Type*
  [fintype_ι : Fintype ι]
  [decEq_ι : DecidableEq ι]
  [linOrder_ι : LinearOrder ι]
  A : Matrix ι ι R

attribute [instance] SquareUniverse.fintype_ι SquareUniverse.decEq_ι SquareUniverse.linOrder_ι

namespace SquareUniverse

@[simp] def ofMatrix {R : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) : SquareUniverse R :=
  { ι := ι, A := A }

end SquareUniverse

/-- Positive-dimensional square universe objects. -/
abbrev PosSquareUniverse (R : Type*) :=
  { x : SquareUniverse R // 0 < Fintype.card x.ι }

end MatDecompFormal.Framework
