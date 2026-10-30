-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FillAtHead.lean: THE FRAME's TWO TYPED FILLINGS OF THE
SEGMENTS' FIRST SENDINGS ARE `K1.firstData` AT THE LETTERS AT WHICH THE PREMISE's FORM `LaysFilling`
(LaysFilling.lean in this folder) IS TYPED. On public data alone. CONDITIONAL: the letters are those
of the hypothesis h, the library's head on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean);
G is the maker's own ground. At all sizes S. IT PAYS NOTHING OF THE SCRIPT. Two theorems, by
unfolding and one law.

What it is for. The form's field lays speaks of `firstData Sz.ref h.𝔇.sent.codes h.𝔇.sent.shape
h.𝔇.sent.layout seat heard`. The frame's files type two fillings: `K2.switchData S Z G`
(Johnson/Desc/ProofFile/Honest/K2/OwnData.lean), at the ground's letters, and `K1.firstFill S q`
(Johnson/Desc/ProofFile/Honest/K1/PlaceFirst.lean). This file says that at one S these are the
form's filling, at the seats at which ReachAtHead.lean pays the form's public field.

Main names:
  `switchData_at`: `K2.switchData S Zp G` is `firstData S` at h.𝔇.sent's three letters, at seat :=
    `K2.switchSeat Zp G`, heard := fun _ => 0.
  `firstFill_at`: `K1.firstFill S Zp.first` is `firstData S` at the same letters, at seat :=
    `K1.firstSeat h.𝔇.sent.shape 0`, heard := fun _ => 0.

How. The ground's "first" is the public part's: `Meaning.K2.blank_first`
(Johnson/IMR/ArraysOpen.lean). The rest by unfolding. Of h its letters `h.𝔇.sent` alone are read.

Limits. ONE S ON BOTH SIDES: the form stands at `Sz.ref`; which S the frame lays is not said here
(see SizesApart.lean in this folder). This file does not import the form: that these are its letters
is read off the form's text. Through its imports the file stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.OwnData
import Johnson.Desc.ProofFile.Honest.K1.PlaceFirst
import Johnson.P5J.MgAtAll
import Johnson.IMR.ArraysOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The switches' own messages' filling, at the form's letters.** Conditional: hG: G is the
maker's own ground. -/
theorem switchData_at (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G) :
    K2.switchData S Zp G =
      K1.firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K2.switchSeat Zp G) fun _ => 0 := by
  have e : G.first = Zp.first := _root_.Meaning.K2.blank_first hG
  unfold K2.switchData
  rw [e]
  rfl

/-- **The first segment's opening's filling, at the form's letters.** -/
theorem firstFill_at (S : Sz) :
    K1.firstFill S Zp.first =
      K1.firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K1.firstSeat h.𝔇.sent.shape 0) fun _ => 0 := rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.switchData_at
#print axioms ProofFile.Honest.K5.firstFill_at
