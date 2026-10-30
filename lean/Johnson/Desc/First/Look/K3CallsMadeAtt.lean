-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No state of the verifier is shown at which the kind's decide accepts.
Johnson/Desc/First/Look/K3CallsMadeAtt.lean: the lookup on an ATTENTION link's calls: AN ACCEPT OF
THE KIND's decide MAKES THE ATTENTION CALLER's OWN PUBLIC TEST look (lookAttB,
Johnson/Desc/First/Att/Door/PubK5.lean) ON THE STATE BEHIND, with no premise on the rounds' words:
both homes of what the lookup returned are laid by one writer with one value (hearLook), so the test
"they hold one thing" compares a value with itself; the last claim names no entry of a virtual row,
and every slot that it names lies below the ledger's number of slots and is filled (K3Left). The
sister of K3CallsMade.lean. Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: Desc.K3.block's decide at Desc.K3.seatCalls claim; the test lookAttB.
USER: Johnson/Desc/Sound/MgAt/K3CallsOthers.lean (look_att_made).
  Meant: the kind's debt "what the sub-protocol makes" at a step on the state.
LETTERS: those of K3CallsMade.lean.

Main names: `zipAll_self` · `sameEnt_self`, `sameAff_self`, `sameAffs_self`, `sameHeardB_self` ·
  `look_att_made`.

Limits. Attention alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsMade
import Johnson.Desc.First.Att.Door.PubK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.K3 (k3OnIn)
open VerifiableInference.Desc.First.Look
open H2K5.Door (sameEnt sameAff sameAffs sameHeardB lookAttB lookAttUpTo)

/-- A list zipped with itself passes every test that each member passes against itself. -/
theorem zipAll_self {α : Type} (f : α → α → Bool) (hf : ∀ a, f a a = true) :
    ∀ l : List α, ((l.zip l).all fun x => f x.1 x.2) = true
  | [] => rfl
  | a :: l => by
    rw [List.zip_cons_cons, List.all_cons, hf a, zipAll_self f hf l]
    rfl

theorem sameEnt_self (a : Ent) : sameEnt a a = true := by
  simp [sameEnt]

theorem sameAff_self (a : Aff) : sameAff a a = true := by
  unfold sameAff
  rw [zipAll_self sameEnt sameEnt_self]
  simp

theorem sameAffs_self (a : Array Aff) : sameAffs a a = true := by
  unfold sameAffs
  rw [zipAll_self sameAff sameAff_self]
  simp

/-- **A value holds one thing with itself.** -/
theorem sameHeardB_self (g : Forest.Heard) : sameHeardB g g = true := by
  unfold sameHeardB
  rw [sameShapeAll_refl, sameAffs_self, sameAff_self, sameAff_self]
  simp

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

/-- **look, at an attention segment.** -/
theorem look_att_made (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) {a : Desc.First.AttOwn} (hh : s.here = .att a) :
    lookAttB s' = true := by
  obtain ⟨F, F', g, rs', -, -, hn0, -, -, e, -, -, L, -⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  unfold lookAttB lookAttUpTo
  rw [e, put_att g F' hh hn0]
  show (sameHeardB g g && g.cEnd.ents.isEmpty &&
    g.cEnd.slots.toList.all fun x => Decidable.decide (x.1 < F'.ns) && F'.gotF.getD x.1 false) =
      true
  rw [sameHeardB_self, L.cEndEnts, Bool.and_eq_true]
  refine ⟨rfl, ?_⟩
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨h1, h2⟩ := L.cEndFilled x hx
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true h1, h2⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.sameHeardB_self
#print axioms VerifiableInference.OnPublicFiles.look_att_made
