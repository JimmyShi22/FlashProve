-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SegmentsAtFront.lean: the kind "the code switch" (K2): THE
CODES AND THE TWO CODES' NUMBERS OF EVERY SEGMENT THAT `segmentsOf` MAKES (Honest/K2/AtPlan.lean)
ARE THOSE OF A SWITCH's FRONT AND ITS CARRIED ROWS. Two statements with their proofs: calls; no
definition.

  `segmentsOf_sizes` `Sg ∈ segmentsOf Z G` ⊢ Sg.sizes' codes, code and maskCode are G.first's codes
                    and its shape's two numbers
  `segmentsOf_at_front` at an opening, at a front with `FrontTies Z fx`
                    (Johnson/Desc/K2/Honest/Returns/FrontTiesReached.lean), for `Sg ∈ segmentsOf Z
                    Bs.G₀`: they are fx.st.codes, fx.f.rows.code, fx.f.rows.maskCode: three of the
                    public premises (hc, hcode, hmask) of `claimTrue_at_segmentLeft`
                    (Law/ClaimAtClosing.lean)

By: the library's `prep_facts` (Johnson/IMR/MsgsPlaces.lean), `Open.first`
(Johnson/IMR/SeatOpen.lean) · `FrontTies`' fields codes, code, maskCode. NEAR, NOT CALLED:
`segmentsOf_is`, `segments_at_head` (Law/PlacesWritten.lean): under the head the segments are the
written ones: these two laws need no head.

Limits. `FrontTies` is a premise here; FrontTiesReached.lean has it at reached states. Where
`segmentsOf` is empty nothing is said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.K2.Honest.Returns.FrontTiesReached
import Johnson.IMR.MsgsPlaces
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest.Returns (FrontTies)

/-- The codes and the two codes' numbers of every segment that `segmentsOf` makes are the ground's
first part's. -/
theorem segmentsOf_sizes {Z : Pub} {G : Ground} {Sg : SegmentPub} (h : Sg ∈ segmentsOf Z G) :
    Sg.sizes.codes = G.first.codes ∧ Sg.sizes.code = G.first.shape.code ∧
      Sg.sizes.maskCode = G.first.shape.maskCode := by
  unfold segmentsOf at h
  cases hP : P1K2.prepOf Z G with
  | none =>
    rw [hP] at h
    cases h
  | some P =>
    rw [hP] at h
    obtain ⟨e1, e2, -⟩ := Meaning.Carry.prep_facts hP
    obtain ⟨L, -, rfl⟩ := List.mem_map.1 h
    exact ⟨e2, congrArg (·.code) e1, congrArg (·.maskCode) e1⟩

/-- **So they are the front's**: three of the lock's public ties, at every front with
`FrontTies`. -/
theorem segmentsOf_at_front {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) {fx : _root_.Tw.K2.Front} (T : FrontTies Z fx)
    {Sg : SegmentPub} (h : Sg ∈ segmentsOf Z Bs.G₀) :
    Sg.sizes.codes = fx.st.codes ∧ Sg.sizes.code = fx.f.rows.code ∧
      Sg.sizes.maskCode = fx.f.rows.maskCode := by
  obtain ⟨a, b, d⟩ := segmentsOf_sizes h
  rw [O.first] at a b d
  exact ⟨a.trans T.codes.symm, b.trans T.code.symm, d.trans T.maskCode.symm⟩

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.segmentsOf_sizes
#print axioms ProofFile.Honest.K2.segmentsOf_at_front
