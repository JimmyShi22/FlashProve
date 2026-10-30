-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/StepLaws/RoundsFit.lean: WHAT Block.step's TEST ON THE VIEW ASKS: roundsFit
(Johnson/Desc/Block.lean), clause
by clause, as an «if and only if».

StepLaws.lean takes roundsFit as a name, but for its length and its cut at an append. So no law held
its seven clauses
fast: a clause struck from the text left every law compiling (shown by a fault
planted as a test).
  RoundFits    one declared round against one round of the view: the seven clauses
  roundsFit_iff   roundsFit ds rs = true if and only if the two lists are as long as each other and
  fit round by round
No soundness is claimed.
-/
import Johnson.Desc.Block
import Mathlib.Data.List.Forall2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- One declared round against one round of the view. -/
structure RoundFits (d : Fmt.DeclaredRound) (r : Fmt.RoundView) : Prop where
  /-- the items shown are the declared ones, but for the roots -/
  items : r.vals.map itemOf = d.items.filter (· != .root)
  /-- as many elements as the entry says -/
  elems : r.drawn.elems.length = d.entry.drawE
  /-- as many positions -/
  count : r.drawn.poss.length = d.entry.poss
  /-- as many matrix entries -/
  trits : r.drawn.trits.length = d.entry.trits
  /-- every position is below 2 ^ logN -/
  below : ∀ x ∈ r.drawn.poss, x < 2 ^ d.entry.logN
  /-- every matrix entry is -1, 0 or 1 -/
  three : ∀ t ∈ r.drawn.trits, t = -1 ∨ t = 0 ∨ t = 1
  /-- the test on the elements that must not be 0 -/
  nz : drawsMarkedNonzeroHaveNonzeroWords d r = true

theorem roundsFit_iff : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true ↔ List.Forall₂ RoundFits ds rs
  | [], [] => by simp [roundsFit]
  | [], _ :: _ => by simp [roundsFit]
  | _ :: _, [] => by simp [roundsFit]
  | d :: ds, r :: rs => by
    rw [List.forall₂_cons, ← roundsFit_iff ds rs]
    simp only [roundsFit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
      Bool.or_eq_true]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩, g⟩, h⟩, i⟩
      exact ⟨⟨a, b, c, e, f, fun t ht => by
        rcases g t ht with (x | x) | x
        · exact Or.inl x
        · exact Or.inr (Or.inl x)
        · exact Or.inr (Or.inr x), h⟩, i⟩
    · rintro ⟨⟨a, b, c, e, f, g, h⟩, i⟩
      exact ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩, fun t ht => by
        rcases g t ht with x | x | x
        · exact Or.inl (Or.inl x)
        · exact Or.inl (Or.inr x)
        · exact Or.inr x⟩, h⟩, i⟩

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.roundsFit_iff
