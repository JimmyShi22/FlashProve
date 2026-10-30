-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/Four8Slots.lean: The kind "lookup" (K3), at the lookup on the approximate range
proof's digits: EVERY SLOT THAT A FORM OF THE FOUR CLAIMS four8 tl g
(Johnson/Desc/First/Batch/Law/K8Four.lean) NAMES
LIES IN THE WINDOW OF THE SUMCHECK OVER THE LEAVES OR IS THERE AND FILLED: in the ledger that an
accept of the digits' decision leaves, and in every later ledger. Statements and proofs: joinings.

OBJECT: K9L.four8; Fo.Tp.PadNames (Johnson/Top/H/Keep/PadNamed.lean); K3.block's decide at
  K3.seatDigits.
Used by Johnson/Desc/First/Link/Law/FourBehindDigits.lean.
LETTERS: tl, g, F', G, H free; claim, piece, laid, before, p, guests, s, s', rs, cols, F: the
  digits'.
Compiled with the whole library.

Main names:
  four8_slots: from PadNames g F' and a later ledger G: IN THE SIGNS OF THE SECOND HALF OF THE
    PREMISE hOk4 OF k8_four (K8Four.lean:174-176): K4Values.InWin (winOf g.leaves) x.1 ∨ Filled G
    x.1.
  four8_noEnts: none of the four forms names an entry: so whatever is asked of "every entry that a
    form of the four names" holds.
  k3_digits_four: AT AN ACCEPT OF THE DIGITS' DECISION: what was heard, the ledger left, and the
    clause at every ledger later than that.

Why. The four forms name: (1) a constant less g.cEnd: g.cEnd's slots · (2) g.leaves.rowForm oneE
{}: the window's slots and those of g.leaves.start · (3) the slot g.sBit · (4) a constant: none.
PadNames says of g.cEnd, g.sBit and g.leaves.start that they name slots alone that are there and
filled.

Limits. The promise's public item lookOut says nothing of this: no clause of K3.k3OnOut says that a
slot is filled. That what is heard in front of the batching is still that g, and that the ledger
there is later than the one left, is for the caller to show.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Top.H.Keep.K3Named
import Johnson.Top.H.K3SeatFits
import Johnson.Desc.First.Look.K3SeatLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_mono slotsIn_ofConst slotsIn_empty slotsIn_sub
  slotsIn_rowForm)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (seatDigits seatDigits_reads)
open VerifiableInference.Desc.K9L (four8)
open VerifiableInference.Desc.K4Values (winOf)
open OnBytes.Road.Rows (bare_ofConst bare_slot bare_addMul bare_rowForm)
open _root_.Fo.Tp (PadNames In bare_ents)

/-- **The four claims' forms name the window's slots and filled slots alone.** -/
theorem four8_slots {g : Forest.Heard} {F' G : Fork} (N : PadNames g F')
    (L : _root_.Fo.Later F' G) (tl : HTailF2) :
    ∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
      Desc.K4Values.InWin (winOf g.leaves) x.1 ∨ Filled G x.1 := by
  have up : ∀ j, In F' j → Desc.K4Values.InWin (winOf g.leaves) j ∨ Filled G j := fun j h =>
    Or.inr (L.keep j h.2).1
  intro cl hcl
  show SlotsIn (fun j => Desc.K4Values.InWin (winOf g.leaves) j ∨ Filled G j) cl.form
  simp only [four8, List.mem_cons, List.mem_nil_iff, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl
  · exact slotsIn_sub (slotsIn_ofConst _) (slotsIn_mono up N.cEnd.2)
  · exact slotsIn_rowForm _ _
      (fun i hi => Or.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩)
      (slotsIn_mono up N.start.2) slotsIn_empty
  · exact slotsIn_mono up N.sBit.2
  · exact slotsIn_ofConst _

/-- **None of the four forms names an entry.** -/
theorem four8_noEnts {g : Forest.Heard} {F' : Fork} (N : PadNames g F') (tl : HTailF2) :
    ∀ cl ∈ four8 tl g, cl.form.ents = #[] := by
  intro cl hcl
  simp only [four8, List.mem_cons, List.mem_nil_iff, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl
  · exact bare_ents (bare_addMul (subE zeroE oneE) (bare_ofConst _) N.cEnd.1)
  · exact bare_ents (bare_rowForm _ _ N.start.1)
  · exact bare_ents (bare_slot _)
  · exact bare_ents (bare_ofConst _)

/-- **AT AN ACCEPT OF THE DIGITS' DECISION.** -/
theorem k3_digits_four {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) :
    ∃ g G, (seatDigits claim).heard s' = some g ∧ s'.fork? = some G ∧
      (∀ tl, ∀ cl ∈ four8 tl g, cl.form.ents = #[]) ∧
      ∀ H, _root_.Fo.Later G H → ∀ tl, ∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
        Desc.K4Values.InWin (winOf g.leaves) x.1 ∨ Filled H x.1 := by
  obtain ⟨F1, y, hF1, hn, e, hN⟩ :=
    decide_named (seatDigits claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((seatDigits claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  refine ⟨y.1, y.2, ?_, ?_, four8_noEnts (hN hS), fun H L tl => four8_slots (hN hS) L tl⟩
  · rw [e]
    exact seatDigits_reads claim s y.1 y.2 hsome hn
  · rw [e]
    exact seatDigits_keeps claim s y.1 y.2 hsome hn

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.four8_slots
#print axioms VerifiableInference.OnPublicFiles.four8_noEnts
#print axioms VerifiableInference.OnPublicFiles.k3_digits_four
