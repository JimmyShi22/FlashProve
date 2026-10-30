-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeatNarrows.lean: WHAT A SEAT LAYS AROUND A KIND'S BLOCK NARROWS IT: the guard on
one seat of the carried record (Johnson/Desc/SeatGuard.lean: `Block.guarded`), a guard on the
record's mark behind `decide`, another name. Small lemmas with their proofs.

Why. A law at a kind's block b is carried to the piece that holds `below B'`, B' what is seated, by
`goodIn_of_narrows` (Johnson/Desc/Sound/MergeNarrowMakers.lean), under "B' narrows b". Here that
premise is paid for the two tests that the first chain's seat lays.

Main names:
  `underR_iff_narrows`: `Block.UnderR` (Johnson/Desc/Sound/SeatGuardChain.lean) and `Block.Narrows`
    (Johnson/Desc/Sound/MergeNarrow.lean) are one notion, typed twice in two files: by unfolding.
  `guarded_narrows`: (b.guarded same but).Narrows b.
  `markGuard b`: b with a refusal behind its `decide` where the record behind bears a mark.
    `markGuard_narrows`, `markGuard_unmarked`: it narrows b; behind its yes there is no mark.
  `seat_narrows`: the guard on a seat around the guard on the mark under another name narrows b.
  `seat_planOk`: and has b's test on the plan.

Limits: `markGuard` is typed here after a seat's own text in a
separate root beside the library: that the seat's term IS `markGuard b` under a name is to be held
there, by unfolding. Rounds and `decide` alone. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Desc.Sound.MergeNarrowMakers
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

theorem underR_iff_narrows (b' b : Block S Cl) : b'.UnderR b ↔ b'.Narrows b := Iff.rfl

theorem guarded_narrows (same : S → S → Bool) (but : Place → Bool) (b : Block S Cl) :
    (b.guarded same but).Narrows b := guarded_underR same but b

/-- A block with a refusal behind its `decide` where the record behind bears a mark. -/
def markGuard (b : Block First.S Cl) : Block First.S Cl :=
  { b with decide := fun s rs gs =>
      (b.decide s rs gs).bind fun t =>
        match t.failed with
        | none => .ok t
        | some m => .error ("marked: " ++ m) }

theorem markGuard_yes (b : Block First.S Cl) (s : First.S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (t : First.S)
    (h : (markGuard b).decide s rs gs = .ok t) :
    b.decide s rs gs = .ok t ∧ t.failed = none := by
  have h' : ((b.decide s rs gs).bind fun t =>
      match t.failed with
      | none => .ok t
      | some m => .error ("marked: " ++ m)) = .ok t := h
  cases hd : b.decide s rs gs with
  | error e => rw [hd] at h'; cases h'
  | ok u =>
    rw [hd] at h'
    have h2 : (match u.failed with
      | none => (.ok u : Except String First.S)
      | some m => .error ("marked: " ++ m)) = .ok t := h'
    split at h2
    · rename_i hu
      cases h2
      exact ⟨rfl, hu⟩
    · cases h2

theorem markGuard_narrows (b : Block First.S Cl) : (markGuard b).Narrows b :=
  ⟨rfl, fun s rs gs t h => (markGuard_yes b s rs gs t h).1⟩

theorem markGuard_unmarked (b : Block First.S Cl) (s : First.S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (t : First.S)
    (h : (markGuard b).decide s rs gs = .ok t) :
    t.failed = none := (markGuard_yes b s rs gs t h).2

/-- **What the first chain's seat lays around a kind's block narrows it.** -/
theorem seat_narrows (same : First.S → First.S → Bool) (but : Place → Bool)
    (b : Block First.S Cl) (n : String) :
    (Block.guarded same but { markGuard b with name := n }).Narrows b :=
  (guarded_narrows same but _).trans
    ((Block.Same.narrows (⟨rfl, rfl⟩ : ({ markGuard b with name := n } :
      Block First.S Cl).Same (markGuard b))).trans (markGuard_narrows b))

/-- The seat's two tests and its name leave the block's test on the plan as it is. -/
theorem seat_planOk (same : First.S → First.S → Bool) (but : Place → Bool)
    (b : Block First.S Cl) (n : String) :
    (Block.guarded same but { markGuard b with name := n }).planOk = b.planOk := rfl

#print axioms guarded_narrows
#print axioms markGuard_yes
#print axioms seat_narrows

end VerifiableInference.Desc
