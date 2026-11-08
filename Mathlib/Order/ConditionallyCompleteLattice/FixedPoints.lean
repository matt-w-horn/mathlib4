/-
Copyright (c) 2026 Matthew W. Horn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew W. Horn
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.FixedPoints

/-!
# Knaster–Tarski in a conditionally complete lattice

`OrderHom.nextFixed f x hx` is the least fixed point above a postfixed point `x` of a monotone
self-map `f` of a complete lattice. Its value is `sInf {y | x ≤ y ∧ f y ≤ y}`, which makes sense in
a conditionally complete lattice as soon as some prefixed point of `f` lies above `x`. This file
defines that infimum as `nextFixedPt f x` for an arbitrary `f : α → α` and proves that it is the
least fixed point of `f` above `x` when `f` is monotone on `Set.Ici x` (`isLeast_nextFixedPt`).
On a complete lattice it is `OrderHom.nextFixed` (`OrderHom.coe_nextFixed`).

The anchor `x` is the only parameter: a prefixed point `b` above `x` is a hypothesis, and
`nextFixedPt f x` does not depend on the choice of `b`. This is what distinguishes the result from
applying `OrderHom.lfp` to the restriction of `f` to `Set.Icc x b` with `Set.Icc.completeLattice`.

## Main definitions

* `nextFixedPt f a`: `sInf {x | a ≤ x ∧ f x ≤ x}`, the least fixed point of `f` above `a`.
* `prevFixedPt f b`: `sSup {x | x ≤ b ∧ x ≤ f x}`, the greatest fixed point of `f` below `b`.

## Main results

* `isLeast_nextFixedPt`, `isGreatest_prevFixedPt`: Knaster–Tarski above `a` and below `b`.
* `nextFixedPt_mono`, `prevFixedPt_mono`: monotone in the map and in the anchor, with no
  monotonicity of the map required.
* `OrderHom.coe_nextFixed`, `OrderHom.coe_prevFixed`: the complete lattice case is
  `OrderHom.nextFixed` and `OrderHom.prevFixed`.

## Implementation notes

The map is an unbundled `f : α → α` because monotonicity is only needed on `Set.Ici a`, and
`nextFixedPt f a` is a junk value when `f` has no prefixed point above `a`. In a lattice that is
not linear, monotonicity on `Set.Icc a b` alone does not suffice for `isLeast_nextFixedPt`
(prefixed points above `a` need not be comparable with `b`); `monotone_comp_clampIcc` turns
monotonicity on `Set.Icc a b` into global monotonicity by precomposing with the clamp onto
`Set.Icc a b`, without changing the fixed points in `Set.Icc a b`.

## Tags

fixed point, Knaster-Tarski, conditionally complete lattice
-/

@[expose] public section

open Function (IsFixedPt)
open Set

variable {α : Type*} [ConditionallyCompleteLattice α] {f g : α → α} {a b x : α}

/-- The infimum of the prefixed points of `f` above `a`. This is the least fixed point of `f` above
`a` when `f` is monotone on `Ici a`, `a ≤ f a`, and some prefixed point of `f` lies above `a`
(`isLeast_nextFixedPt`). -/
def nextFixedPt (f : α → α) (a : α) : α := sInf {x | a ≤ x ∧ f x ≤ x}

/-- The supremum of the postfixed points of `f` below `b`. This is the greatest fixed point of `f`
below `b` when `f` is monotone on `Iic b`, `f b ≤ b`, and some postfixed point of `f` lies below `b`
(`isGreatest_prevFixedPt`). -/
@[to_dual existing] def prevFixedPt (f : α → α) (b : α) : α := sSup {x | x ≤ b ∧ x ≤ f x}

@[to_dual prevFixedPt_le]
theorem le_nextFixedPt (hb : ∃ b, a ≤ b ∧ f b ≤ b) : a ≤ nextFixedPt f a :=
  le_csInf hb fun _ hx ↦ hx.1

@[to_dual le_prevFixedPt]
theorem nextFixedPt_le (hax : a ≤ x) (hfx : f x ≤ x) : nextFixedPt f a ≤ x :=
  csInf_le ⟨a, fun _ hy ↦ hy.1⟩ ⟨hax, hfx⟩

/-- `nextFixedPt` is monotone in the map and in the anchor. This compares the defining infima, so
it needs no monotonicity of `f` or `g`. -/
@[to_dual (reorder := a₁ a₂, f g) (rename := a₁ → b₂, a₂ → b₁, f ↔ g)
  /-- `prevFixedPt` is monotone in the map and in the anchor. This compares the defining suprema,
  so it needs no monotonicity of `f` or `g`. -/]
theorem nextFixedPt_mono {a₁ a₂ : α} (ha : a₁ ≤ a₂) (hfg : ∀ x, a₂ ≤ x → f x ≤ g x)
    (hb : ∃ b, a₂ ≤ b ∧ g b ≤ b) : nextFixedPt f a₁ ≤ nextFixedPt g a₂ :=
  csInf_le_csInf ⟨a₁, fun _ hy ↦ hy.1⟩ hb fun _ hx ↦ ⟨ha.trans hx.1, (hfg _ hx.1).trans hx.2⟩

/-- **Knaster–Tarski above a point** in a conditionally complete lattice: if `f` is monotone on
`Ici a`, `a ≤ f a`, and some prefixed point of `f` lies above `a`, then `nextFixedPt f a` is the
least fixed point of `f` above `a`. -/
@[to_dual /-- **Knaster–Tarski below a point** in a conditionally complete lattice: if `f` is
  monotone on `Iic b`, `f b ≤ b`, and some postfixed point of `f` lies below `b`, then
  `prevFixedPt f b` is the greatest fixed point of `f` below `b`. -/]
theorem isLeast_nextFixedPt (hm : MonotoneOn f (Ici a)) (ha : a ≤ f a)
    (hb : ∃ b, a ≤ b ∧ f b ≤ b) : IsLeast {x | a ≤ x ∧ IsFixedPt f x} (nextFixedPt f a) := by
  have hap : a ≤ nextFixedPt f a := le_nextFixedPt hb
  have h₁ : f (nextFixedPt f a) ≤ nextFixedPt f a :=
    le_csInf hb fun x hx ↦ (hm hap hx.1 (nextFixedPt_le hx.1 hx.2)).trans hx.2
  have haf : a ≤ f (nextFixedPt f a) := ha.trans (hm (mem_Ici.2 le_rfl) hap hap)
  exact ⟨⟨hap, h₁.antisymm (nextFixedPt_le haf (hm haf hap h₁))⟩,
    fun _ hx ↦ nextFixedPt_le hx.1 hx.2.le⟩

@[to_dual]
theorem isFixedPt_nextFixedPt (hm : MonotoneOn f (Ici a)) (ha : a ≤ f a)
    (hb : ∃ b, a ≤ b ∧ f b ≤ b) : IsFixedPt f (nextFixedPt f a) :=
  (isLeast_nextFixedPt hm ha hb).1.2

/-- The orbit of the anchor stays below the least fixed point above it. -/
@[to_dual prevFixedPt_le_iterate
  /-- The orbit of the anchor stays above the greatest fixed point below it. -/]
theorem iterate_le_nextFixedPt (hm : MonotoneOn f (Ici a)) (ha : a ≤ f a)
    (hb : ∃ b, a ≤ b ∧ f b ≤ b) (n : ℕ) : f^[n] a ≤ nextFixedPt f a := by
  have hfix := isFixedPt_nextFixedPt hm ha hb
  suffices h : a ≤ f^[n] a ∧ f^[n] a ≤ nextFixedPt f a from h.2
  induction n with
  | zero => exact ⟨le_rfl, le_nextFixedPt hb⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ha.trans (hm (mem_Ici.2 le_rfl) ih.1 ih.1),
      (hm ih.1 (le_nextFixedPt hb) ih.2).trans_eq hfix.eq⟩

/-- The least fixed point above `a` is at most the greatest fixed point below `b`, when `f` is
monotone on `Ici a`. See `nextFixedPt_le_prevFixedPt'` for monotonicity on `Iic b` instead. -/
@[to_dual (reorder := a b) (rename := a ↔ b) nextFixedPt_le_prevFixedPt'
  /-- The least fixed point above `a` is at most the greatest fixed point below `b`, when `f` is
  monotone on `Iic b`. See `nextFixedPt_le_prevFixedPt` for monotonicity on `Ici a` instead. -/]
theorem nextFixedPt_le_prevFixedPt (hm : MonotoneOn f (Ici a)) (ha : a ≤ f a) (hab : a ≤ b)
    (hb : f b ≤ b) : nextFixedPt f a ≤ prevFixedPt f b :=
  le_prevFixedPt (nextFixedPt_le hab hb) (isFixedPt_nextFixedPt hm ha ⟨b, hab, hb⟩).ge

section Clamp

variable {β : Type*} [Lattice β] {f : β → β} {a b x : β}

/-- Precomposing with the clamp `x ↦ (x ⊔ a) ⊓ b` onto `Icc a b` turns a map that is monotone on
`Icc a b` into a monotone map, in any lattice. -/
theorem monotone_comp_clampIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) :
    Monotone fun x ↦ f ((x ⊔ a) ⊓ b) := fun _ _ hxy ↦
  hm ⟨le_inf le_sup_right hab, inf_le_right⟩ ⟨le_inf le_sup_right hab, inf_le_right⟩
    (inf_le_inf_right _ (sup_le_sup_right hxy _))

/-- The clamped map has the same fixed points in `Icc a b` as `f`, and no others, when `f` maps
`Icc a b` into itself. -/
theorem isFixedPt_comp_clampIcc_iff (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsFixedPt (fun x ↦ f ((x ⊔ a) ⊓ b)) x ↔ x ∈ Icc a b ∧ IsFixedPt f x := by
  have hclamp : ∀ x ∈ Icc a b, (x ⊔ a) ⊓ b = x := fun x hx ↦ by
    rw [sup_eq_left.2 hx.1, inf_eq_left.2 hx.2]
  constructor
  · intro hx
    have hmem : x ∈ Icc a b := hx.eq ▸ hf ⟨le_inf le_sup_right hab, inf_le_right⟩
    exact ⟨hmem, by simpa [IsFixedPt, hclamp x hmem] using hx⟩
  · rintro ⟨hmem, hx⟩
    simpa [IsFixedPt, hclamp x hmem] using hx

end Clamp

namespace OrderHom

variable {β : Type*} [CompleteLattice β] (f : β →o β)

/-- On a complete lattice, `OrderHom.nextFixed` is `nextFixedPt`. -/
theorem coe_nextFixed {x : β} (hx : x ≤ f x) : (f.nextFixed x hx : β) = nextFixedPt f x := by
  change sInf {y | (const β x ⊔ f) y ≤ y} = sInf {y | x ≤ y ∧ f y ≤ y}
  congr 1
  ext y
  exact sup_le_iff

/-- On a complete lattice, `OrderHom.prevFixed` is `prevFixedPt`. -/
theorem coe_prevFixed {x : β} (hx : f x ≤ x) : (f.prevFixed x hx : β) = prevFixedPt f x := by
  change sSup {y | y ≤ (const β x ⊓ f) y} = sSup {y | y ≤ x ∧ y ≤ f y}
  congr 1
  ext y
  exact le_inf_iff

end OrderHom
