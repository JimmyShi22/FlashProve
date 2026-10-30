-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SenderOwn.lean: the kind "the code switch" (K2): THE OWN DATA
THAT THE KIND's LOT HANDS A SWITCH, UNDER A NAME, AND WHAT A RETURN OF THE LOT's TEXT
`switchRowsLaid` (Honest/K2/ScriptLots.lean) SAYS. A light file: over ScriptLots.lean and the small
tools alone. One abbreviation; two statements with their proofs.

  `senderOwn`, `switchWit_own`   the own data that `switchWit` (Honest/K2/Half.lean) hands the
                 sender: an abbreviation of its text, tied to it with no premise
  `rowsLaid_inv`   what a return of `switchRowsLaid` says: the closing returned Wl, and `rowsAll`
                 returned V at `mainRows` of Wl and `senderOwn`

Kin of `rowsLaid_inv`: `rows_of_laid` (Honest/K2/Law/MaskTxt.lean) opens the same return and says
less: that there are main rows M at which `rowsAll` returned V; here M is named, with the closing's
return.

Limits. It unfolds a text. `rowsLaid_inv`'s end takes the hand c apart into two of its components:
c.2.2, what is carried, goes to the closing; c.1, the own cut, goes to `rowsAll`. Each goes there
undivided, and nothing inside it is looked at. That `switchRowsLaid` returns is a premise. The
closing is a letter. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (mainRows)
open Reads

variable {W₀ Rc Xi Tr : Type}

/-- The own data that `switchWit` hands the sender: an abbreviation of its text. -/
abbrev senderOwn (D : RowData) (Rd : Readers) (p : SwitchPlace) : Nat → Nat → Nat → Cb.Gl.E :=
  fun m b j => asRow ((p.others.getD m default).shape.mainDeg == 3) (D.at_ Rd [] (p.ownAddr m) b j)

theorem switchWit_own (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (w : Local W₀ Rc Xi Tr) :
    (switchWit D readers closing p w).own = senderOwn (D w.x) (readers w) p := rfl

/-- What a return of `switchRowsLaid` says. -/
theorem rowsLaid_inv {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {closing : Closing} {p : SwitchPlace}
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} {w : Local W₀ Rc Xi Tr}
    {h : List Fmt.Drawn} {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w h = .ok V) :
    ∃ Wl, closing p (D w.x) (readers w) (h.take (h.length - 0))
        (Stretch.carried p.carries c.2.2) = .ok Wl ∧
      rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)
        (mainRows p.sizes Wl (senderOwn (D w.x) (readers w) p)) c.1 = .ok V := by
  unfold switchRowsLaid at hV
  split at hV
  · cases hV
  · split at hV
    · cases hV
    · obtain ⟨M, hM, hR⟩ := bind_ok' hV
      obtain ⟨Wl, hW, rfl⟩ := map_ok hM
      exact ⟨Wl, hW, hR⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.senderOwn
#print axioms ProofFile.Honest.K2.Law.switchWit_own
#print axioms ProofFile.Honest.K2.Law.rowsLaid_inv
