-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/DueData.lean: at the description's own data every typed verifier's
message passes `Draws.due`. Suppose that `FileDescription.data` (Johnson/Desc/BlockSlot.lean) returns the
data D of the file's rounds. Then the challenges of any verifier's message of the file's rounds,
read as Honest/Frame.lean's lists (`drawsAt`, Honest/Law/StratWords.lean), pass `Draws.due`
(Honest/Frame.lean). This holds at a challenge kit that satisfies three clauses, and so at the kit
of the release's field.

  `due_at_data`   at a kit that satisfies the three clauses
  `due_at_two`    at the kit of the release's field

The proofs use `kinds_of_data` (Honest/Law/DataKinds.lean), `due_typed` (Honest/Law/Due.lean) and
`kit_two` (Honest/Law/KitTwo.lean).

Limits.
  * That no declared round draws more non-zero elements than elements (`hz`) is a hypothesis: an
    executable test on the description.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.DataKinds
import Johnson.Desc.ProofFile.Honest.Law.KitTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD chainsOf)
open _root_.Run.PQ (CK)
open _root_.Run (ckP)

variable {Xi TF TJ T3 : Type}

theorem due_at_data (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D)
    (hz : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) : (drawsAt C D tF tJ t3 ρ).due F = true := by
  obtain ⟨k1, k2, k3, hs⟩ := kinds_of_data h
  exact due_typed C hC D tF tJ t3 k1 k2 k3 hz hs ρ

theorem due_at_two (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D)
    (hz : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE)
    (ρ : Iop.Rho (chainsOf (ckP .two) D tF tJ t3).sh) :
    (drawsAt (ckP .two) D tF tJ t3 ρ).due F = true :=
  due_at_data (ckP .two) kit_two tF tJ t3 h hz ρ

end ProofFile.Honest

#print axioms ProofFile.Honest.due_at_data
#print axioms ProofFile.Honest.due_at_two
