-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FillsBool.lean: the seven tests behind `declKOf` as one Bool, and when a list
of declared rounds is what `fillL` returns.

`FillsK m t₀ t₁ t₂` (FillOpens.lean) reads of m three numbers (how many rounds of each plan draw
positions) and the shape. `fillsB` has these as arguments, so at written values it names no m and
can be evaluated.

  `fillsB n₀ n₁ n₂ S t₀ t₁ t₂`: the seven tests.
  `fillsK_iff`: `FillsK` is `fillsB` at m's own three numbers and shape.
  `fillsK_of`: `FillsK` from four equations at m, three counts at the plans so named, and `fillsB`
    there.
  `fillL_self`, `fillL_eq_of`: a list R of declared rounds is what `fillL`
    (Johnson/Unfolds/FillLaw.lean) returns at R's entries and at the lists that R's rounds of
    positions carry, if every other round of R opens neither a stored table nor a tree.

Limits. General: no written value stands here, and nothing is evaluated. That `fillsB` says yes
anywhere is not shown. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.FillOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open Johnson.Unfolds (fillL)
open VerifiableInference.Desc.Key

/-! ## The seven tests as one Bool -/

/-- `FillsK`'s seven tests, at three numbers of rounds that draw positions, a shape and three lists
of trees. -/
def fillsB (n₀ n₁ n₂ : Nat) (S : LinShape) (t₀ t₁ t₂ : List (Sent × Nat)) : Bool :=
  n₀ == (noStored (onceOpens t₀)).length &&
  n₁ == (sharedOpens S t₁).length &&
  n₂ == (noStored (secondOpens S (fun t => t.tag == .indexMask) t₀ t₁ t₂)).length &&
  noneBare (noStored (onceOpens t₀)) &&
  noneBare (sharedOpens S t₁) &&
  noneBare (noStored (secondOpens S (fun t => t.tag == .indexMask) t₀ t₁ t₂)) &&
  allOpened t₀ t₁ t₂ ((noStored (onceOpens t₀)).flatMap (·.1)) ((sharedOpens S t₁).flatMap (·.1))
    ((noStored (secondOpens S (fun t => t.tag == .indexMask) t₀ t₁ t₂)).flatMap (·.1))

/-- `FillsK` is `fillsB` at m's own numbers and shape. -/
theorem fillsK_iff (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) :
    FillsK m t₀ t₁ t₂ ↔ fillsB (drawing (plan₀ m).rounds) (drawing (plan₁ m).rounds)
      (drawing (plan₂ m).rounds) (shapeK m) t₀ t₁ t₂ = true := by
  unfold fillsB
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact ⟨⟨⟨⟨⟨⟨h.count₀, h.count₁⟩, h.count₂⟩, h.bare₀⟩, h.bare₁⟩, h.bare₂⟩, h.opened⟩
  · rintro ⟨⟨⟨⟨⟨⟨c₀, c₁⟩, c₂⟩, b₀⟩, b₁⟩, b₂⟩, o⟩
    exact ⟨c₀, c₁, c₂, b₀, b₁, b₂, o⟩

/-- **`FillsK` from equations at m and facts that name no m.** -/
theorem fillsK_of (m : Made) (P₀ P₁ P₂ : Fmt.Plan) (S : LinShape) (n₀ n₁ n₂ : Nat)
    (t₀ t₁ t₂ : List (Sent × Nat)) (p₀ : plan₀ m = P₀) (p₁ : plan₁ m = P₁) (p₂ : plan₂ m = P₂)
    (pS : shapeK m = S)
    (d₀ : (P₀.rounds.filter fun e => Fmt.kindOf e.name == some .positions).length = n₀)
    (d₁ : (P₁.rounds.filter fun e => Fmt.kindOf e.name == some .positions).length = n₁)
    (d₂ : (P₂.rounds.filter fun e => Fmt.kindOf e.name == some .positions).length = n₂)
    (h : fillsB n₀ n₁ n₂ S t₀ t₁ t₂ = true) : FillsK m t₀ t₁ t₂ := by
  subst p₀ p₁ p₂ pS d₀ d₁ d₂
  exact (fillsK_iff m t₀ t₁ t₂).2 h

/-! ## When a list of declared rounds is what `fillL` returns -/

/-- At its own entries and at the lists that its rounds of positions carry, `fillL` returns R, if
every other round of R opens neither a stored table nor a tree. -/
theorem fillL_self (R : List Fmt.DeclaredRound)
    (ho : (R.all fun r => Fmt.kindOf r.entry.name == some .positions ||
      (r.stored.isEmpty && r.opens.isEmpty)) = true) :
    fillL (R.map (·.entry)) ((R.filter fun r => Fmt.kindOf r.entry.name == some .positions).map
      fun r => (r.opens, r.stored)) = R := by
  induction R with
  | nil => simp [fillL]
  | cons r R ih =>
    rw [List.all_cons, Bool.and_eq_true] at ho
    have ih' := ih ho.2
    cases h : (Fmt.kindOf r.entry.name == some .positions) with
    | true =>
      rw [List.map_cons, List.filter_cons, if_pos h, List.map_cons, fillL_draws _ _ _ h, ih']
    | false =>
      have hn : ¬ (Fmt.kindOf r.entry.name == some .positions) = true := by
        rw [h]
        decide
      have hr := ho.1
      rw [h, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff, List.isEmpty_iff] at hr
      rw [List.map_cons, List.filter_cons, if_neg hn, fillL_other _ _ h, ih', ← hr.1, ← hr.2]

/-- **A list of declared rounds is what `fillL` returns**, if its entries are es, its rounds that
draw positions carry the plan's lists in order, and every other round of it opens neither a stored
table nor a tree. -/
theorem fillL_eq_of (es : List Fmt.Entry) (plan : List (List Told × List Fmt.Stored))
    (R : List Fmt.DeclaredRound) (he : R.map (·.entry) = es)
    (hd : (R.filter fun r => Fmt.kindOf r.entry.name == some .positions).map
      (fun r => (r.opens, r.stored)) = plan)
    (ho : (R.all fun r => Fmt.kindOf r.entry.name == some .positions ||
      (r.stored.isEmpty && r.opens.isEmpty)) = true) : fillL es plan = R := by
  subst he hd
  exact fillL_self R ho

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.fillsK_iff
#print axioms Johnson.AtFull.KeyBack.fillsK_of
#print axioms Johnson.AtFull.KeyBack.fillL_self
#print axioms Johnson.AtFull.KeyBack.fillL_eq_of
