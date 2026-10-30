-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3DigitsSameBelow.lean: THE LOOKUP ON A LINK's DIGITS: AN ACCEPT OF THE
WHOLE SEATED SUB-PROTOCOL (the kind's rounds AND THEN the step without a round) TURNS NOTHING UNDER
A SLOT BELOW THE LEDGER's NEXT SLOT IN FRONT: in another file's own term SameAt
(Johnson/Road/K4/Slots/HearSpares.lean: filled alike, the same value, the same factor). The rounds:
decide_out (Johnson/Top/H/Keep/PadBelow.lean), whose conclusion is that term's text; the
step without a round lays the list of claims alone (quietAt_ledger,
Johnson/Desc/First/Look/K3DigitsSeatedLeaves.lean). By calls alone. NO SOUNDNESS IS CLAIMED.

OBJECT: K3.theStated's block at the digits' address: its decide, from state to state.
USER: k4StaysBelow_of_digits (Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean): there it gives the
  clause "below next nothing turns" of K4StaysBelow (Johnson/Road/K4/InT/RunsSameK4.lean).
LETTERS: those of k3_digits_step_pass (Johnson/Desc/First/Look/K3DigitsPass.lean); F: the ledger in
  front.

Main name: `k3_digits_step_sameBelow`.

Limits. Below the next slot in front alone (decide_out also speaks of the slots from the next slot
behind on: not carried here).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.PadBelow
import Johnson.Top.H.K3SeatFits
import Johnson.Desc.First.Look.K3DigitsSeatedYes
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves
import Johnson.Road.K4.Slots.HearSpares

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look
open OnBytes.Desc.First.K4.Slots (SameAt)

/-- **Below the next slot in front nothing turns.** -/
theorem k3_digits_step_sameBelow {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) :
    ∃ G, s₂.fork? = some G ∧ ∀ j, j < F.next → SameAt F G j := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  obtain ⟨F0, x, hF0, e, hO⟩ :=
    decide_out (Desc.K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  have hF0' : s.fork? = some F0 := hF0
  obtain rfl : F = F0 := Option.some.inj (hF.symm.trans hF0')
  obtain ⟨-, -, -, hn, -, -⟩ :=
    decide_ok (Desc.K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  have hG : s'.fork? = some x.2 := by
    rw [e]
    exact seatDigits_keeps claim s x.1 x.2 (by rw [hF0]; rfl) hn
  have hB : ∀ j, j < F.next → SameAt F x.2 j := fun j hj => (hO hS).2 j (Or.inl hj)
  rcases hstep with e2 | ⟨f, hf, hfs⟩
  · rw [e2]
    exact ⟨x.2, hG, hB⟩
  · obtain ⟨F₂, c, h1, h2, -⟩ := quietAt_ledger X i f hf s' s₂ hfs
    obtain rfl : x.2 = F₂ := Option.some.inj (hG.symm.trans h1)
    exact ⟨_, h2, fun j hj => (hB j hj).trans ⟨Iff.rfl, rfl, rfl⟩⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_sameBelow
