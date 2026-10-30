-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeptCopiesWritten.lean: the kind "the code switch" (K2): WHAT
SHAPES THE KEPT COPIES HAVE, AT THE WRITTEN PLACES AND UNDER THE HEAD: at each of the 25 places the
kept members' shapes are the shapes of the messages that take their rows, one for one; and each of
the 36 such messages has no mask row, lies over the base field and has one answer. PUBLIC DATA
ALONE. Two definitions: a test, and what bends the data for its controls. Six statements with their
proofs: five closed facts, four of them controls, one to each clause of the test; and the first
carried to the head's own list.

  `keptCopiesOk`              the test, at a list of places
  `bendKept`                  the places with every kept shape turned, for the controls
  `keptCopies_written`        IT ACCEPTS AT THE WRITTEN PLACES: with the two counts beside it
  `keptCopies_rejects_mask`   it rejects where every kept shape and copy is given a mask row
  `keptCopies_rejects_field`  it rejects where every one is laid over the extension field
  `keptCopies_rejects_two`    it rejects where every one is given a second answer
  `keptCopies_rejects_shape`  it rejects where the kept shapes alone are given a main row more
  `keptCopies_at_head`        the first, at `switchPlaces`, under the head and the opening

Why. A laying's mask rows hold coins of that sending (`laidRows`, Honest/K2/Law/Laid.lean): had a
kept copy a mask row, its text there and its sender's could not be one. `copy_txt_is_senders_e`,
`copy_txt_is_senders_f` (Honest/K2/Law/CopyIsSenders.lean, CopyIsSendersF.lean) speak of main rows
alone, and each over one field: by this file, together with its sister
Honest/K2/Law/KeptCopyShape.lean (message 1 + i of a sending has the shape of target number i), it
is the second that meets the plan's copies. Neither is called here. Kin, not called: the sealed
`KeptFits` (Johnson/Top/H0/Tw/K2/TargetMeans.lean), what the verifier's own test on a target means
for an old shape and its copy's: no mask row at either; equal numbers of main rows and of answers;
one field; one message length. It is weaker than this test's equation of shapes (the two codes'
numbers may differ there), and it leaves open which field.

Limits. FIVE CLOSED FACTS BY EVALUATION IN LEAN's KERNEL. The full size; `placesW` is the closed
list of Honest/K2/Law/PlacesWritten.lean, and `places_at_head` (there) carries it to the head's own.
THE COUNTS STAND IN THE SAME STATEMENT: 25 places, 36 copies: so the test does not run over nothing.
It reads shapes: not leaf classes, not the flag "kept again", not codes' lengths. That message 1 + i
of a switch's sending has the shape of target number i is not proved here: the sister has it.
Nothing on a prover, a coin or a run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST**, at a list of places: the kept members' shapes are the targets' shapes, one
for one; each target has no mask row, lies over the base field, and has one answer. -/
def keptCopiesOk (ps : List SwitchPlace) : Bool :=
  ps.all fun p =>
    (p.sizes.kept == p.sizes.target.kept.toList.map (·.shape)) &&
      p.sizes.target.kept.all fun t =>
        t.shape.maskRows == 0 && t.shape.mainDeg == 1 && t.shape.answers == 1

/-- The places with every kept shape turned by f; where `both`, every target's shape too. -/
def bendKept (f : OnBytes.OracleShape → OnBytes.OracleShape) (both : Bool)
    (ps : List SwitchPlace) : List SwitchPlace :=
  ps.map fun p => { p with sizes := { p.sizes with
    kept := p.sizes.kept.map f
    target := { p.sizes.target with
      kept := if both then p.sizes.target.kept.map fun t => { t with shape := f t.shape }
        else p.sizes.target.kept } } }

/-- **The test accepts at the written places**, of which there are 25, with 36 kept copies. -/
theorem keptCopies_written :
    placesW.length = 25 ∧ (placesW.map fun p => p.sizes.target.kept.size).sum = 36 ∧
      keptCopiesOk placesW = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **Four controls.** A mask row at every kept shape and copy. -/
theorem keptCopies_rejects_mask :
    keptCopiesOk (bendKept (fun s => { s with maskRows := 1 }) true placesW) = false := by
  decide +kernel

/-- Every kept shape and copy over the extension field. -/
theorem keptCopies_rejects_field :
    keptCopiesOk (bendKept (fun s => { s with mainDeg := 3 }) true placesW) = false := by
  decide +kernel

/-- A second answer at every kept shape and copy. -/
theorem keptCopies_rejects_two :
    keptCopiesOk (bendKept (fun s => { s with answers := 2 }) true placesW) = false := by
  decide +kernel

/-- One main row more at the kept shapes alone. -/
theorem keptCopies_rejects_shape :
    keptCopiesOk (bendKept (fun s => { s with mainRows := s.mainRows + 1 }) false placesW) =
      false := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening**, at the kind's own list of places. -/
theorem keptCopies_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (switchPlaces Zp Bs.G₀).length = 25 ∧
      ((switchPlaces Zp Bs.G₀).map fun p => p.sizes.target.kept.size).sum = 36 ∧
      keptCopiesOk (switchPlaces Zp Bs.G₀) = true := by
  rw [places_at_head h O]
  exact keptCopies_written

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.keptCopiesOk
#print axioms ProofFile.Honest.K2.Law.bendKept
#print axioms ProofFile.Honest.K2.Law.keptCopies_written
#print axioms ProofFile.Honest.K2.Law.keptCopies_rejects_mask
#print axioms ProofFile.Honest.K2.Law.keptCopies_rejects_field
#print axioms ProofFile.Honest.K2.Law.keptCopies_rejects_two
#print axioms ProofFile.Honest.K2.Law.keptCopies_rejects_shape
#print axioms ProofFile.Honest.K2.Law.keptCopies_at_head
