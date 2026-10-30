-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/FourAtHead.lean: THREE OF THE DOOR'S FOUR FACTS (`FourFacts`, Johnson/Desc/Last/ShapeDoorFold.lean)
AT EVERY STATE REACHED ALONG THE ONE HEAD'S FIRST CHAIN (`P5J.AtMg`, Johnson/P5J/AtMg.lean), FROM THE HEAD ALONE: the
statement is tidy, the book fits, the pending rows' weights are in order. A joining of three payers that stand at
library paths. Statements with their proofs.

Main names (namespace `VerifiableInference.Desc.Last`).
  `flat_planOk_at`: each sub-protocol of the head's first chain passes its own test on the plan (from h.laid.planOk:
    `Meaning.K2.flat_planOkT`).
  `tidy_at_head`: `Meaning.K2.tidy_paid` (Johnson/Desc/AtSeats/Fit/TidyPaid.lean) speaks of "some Z, A, B, c" that
    spell the description: HERE THEY ARE THE HEAD'S OWN Zp AND cF: Z by the one public part of the files, c by the
    description's own first chain.
  **`three_at_reach`**: at every border k and every state q reached by the sub-protocols with the test "every word is
    below the prime" in front, without a mark: tidy4B q.2.st ∧ bookFitsB q.2.book ∧ weightsB q.2.
  **`four_of_own`**: with `ownSitsB V q.2` beside: `FourFacts V q.2`.

What stays a premise. The head. In `four_of_own`: the fourth fact.
Limits. It reads neither `AtMg.rc` nor `AtMg.rch`: so it stands whatever these two are. Nothing on soundness or on
hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorFold
import Johnson.IMR.AtReach
import Johnson.LTPileR.AtGate
import Johnson.Desc.AtSeats.Fit.TidyPaid
import Johnson.P5J.AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Last
open OnBytes OnBytes.Maker
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- Each sub-protocol of the head's first chain passes its own test on the plan. -/
theorem flat_planOk_at (h : P5J.AtMg o Z D r Zp Np cF) : ∀ b ∈ cF.blocksInOrder, b.planOk = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact Meaning.K2.flat_planOkT O.desc h.laid.planOk

/-- The statement is tidy at every state reached along the head's own first chain. -/
theorem tidy_at_head (h : P5J.AtMg o Z D r Zp Np cF) (k : ℕ) (a : ProofFile.InstPub × First.S)
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) : Means.Tidy a.2.st := by
  obtain ⟨Z', A, B, c, hZ, e, t⟩ := Meaning.K2.tidy_paid h.laid.value h.laid.planOk
  obtain rfl : Z' = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  have hh : HEq (c : Chain First.S ProofFile.Cl) cF :=
    congr_arg_heq (fun F : FileDescription ProofFile.Inst => F.first) e.symm
  obtain rfl : c = cF := eq_of_heq hh
  exact t k a hr

/-- **Three of the four facts, from the head alone.** -/
theorem three_at_reach (h : P5J.AtMg o Z D r Zp Np cF) (k : ℕ) (q : ProofFile.InstPub × First.S)
    (hr : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) k q) (hm : q.2.failed = none) :
    Means.tidy4B q.2.st = true ∧ Sound.bookFitsB q.2.book = true ∧ First.weightsB q.2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := flat_planOk_at h
  exact ⟨Means.tidy4B_iff.2 (tidy_at_head h k q (reach_raw hr)),
    Meaning.K2.bookFits_field O hp (fun k a => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
      (fun _ _ h => h) k q (reach_raw hr) hm,
    Meaning.K2.weights_at_open O hp 0 k q (reach_raw hr)⟩

/-- **All four, the fourth handed in.** -/
theorem four_of_own (h : P5J.AtMg o Z D r Zp Np cF) (k : ℕ) (q : ProofFile.InstPub × First.S)
    (hr : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) k q) (hm : q.2.failed = none)
    {V : OwnSeats} (hO : ownSitsB V q.2 = true) : FourFacts V q.2 :=
  ⟨(three_at_reach h k q hr hm).1, (three_at_reach h k q hr hm).2.1,
    (three_at_reach h k q hr hm).2.2, hO⟩

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.flat_planOk_at
#print axioms VerifiableInference.Desc.Last.tidy_at_head
#print axioms VerifiableInference.Desc.Last.three_at_reach
#print axioms VerifiableInference.Desc.Last.four_of_own
