-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/BookPremAt.lean: WHAT THE READING LAWS THAT GO THROUGH THE STATE's BOOK ASK TOGETHER
(`BookPrem`, Johnson/Desc/Sound/ReadsSortsMg.lean), AND THE FIVE CONGRUENCES ON THE ITEMS `constr
k p` (`HidReads`, Johnson/Desc/Sound/ReadsConstr.lean), AT THE CLOSED CONSTANT. Three theorems:
joinings.
  `AtMgA.𝔇_one h : h.toAtMg.𝔇 h.𝔇 = h.𝔇`: the two spellings of the constant's parameters, at which
    different files speak, are one: by unfolding.
  `AtMgA.bookPrem h FF hseat hbelow i`: the seven fields at border i: the three public tests'
    texts by unfolding; the seat of the index masks' message in the listed seats: hseat; "the
    plan's numbers lie below the listed seats": from hbelow, a test with code
    `planBelowB` (Johnson/Desc/K13/Law/PlanTestsM3.lean), by its `planBelow_withTold`; the facts
    on reached states: five fields of FF.
  `AtMgA.hidReads h hp hDig`: `HidReads h.𝔇 At.links`: base, head, lay and att from
    Johnson/P5J/ReadsHidAt.lean and ReadsHeadAt.lean; digits is handed in (hDig), in the field's
    own text.
Limits: joinings. The head h and FF (the counted head's own field) are premises. hseat AND hbelow
ARE CLOSED TESTS ON PUBLIC DATA, OF WHICH NO EVALUATION IS KNOWN HERE AT THESE
TERMS. hp: evaluated true at both full-size sets of public files. No soundness is claimed.

-/
import Johnson.Desc.Sound.ReadsSortsMg
import Johnson.P5J.ReadsHidAt
import Johnson.P5J.ReadsHeadAt
import Johnson.P5J.FoldAt
import Johnson.Desc.K13.Law.PlanTestsM3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.Sound (BookPrem HidReads SameAt mgBase frameAt allOf)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.K13.Law (planBelowB planBelow_withTold)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {L : Laid}

/-- **The two spellings of the constant's parameters are one**: laying the sixteen closed fields
over the structure that has them already gives that structure. -/
theorem AtMgA.𝔇_one (h : AtMgA o Z D r Zp Np cF x) : h.toAtMg.𝔇 h.𝔇 = h.𝔇 := rfl

/-- **`BookPrem` at the constant.** -/
theorem AtMgA.bookPrem (h : AtMgA o Z D r Zp Np cF x)
    (FF : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps)
    (hseat : L.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index)
    (hbelow : planBelowB L At.ps.length (At.told cF) = true) (i : ℕ) :
    BookPrem
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      h.𝔇 mgBase (msgsOfChain Zp.made.proof.1) L (fun a => a) h.toAtMg.rch i where
  indexIs := fun _ => rfl
  indexThere := fun _ => rfl
  noneSent := fun _ => rfl
  seat := hseat
  below := planBelow_withTold _ At.ps (At.told cF) hbelow
  facts := fun a hr hu =>
    ⟨FF.msgShapes i a hr hu, FF.bookInOrder i a hr hu, FF.seatsCarried i a hr hu,
      FF.pileMasks i a hr hu⟩
  tidy := fun a hr hu => FF.tidy i a hr hu

/-- **`HidReads` at the constant**, the field digits handed in. -/
theorem AtMgA.hidReads (h : AtMgA o Z D r Zp Np cF x) (hp : OffPad.padsAtZ Zp = true)
    (hDig : ∀ k a y w w', k < At.links.length → SameAt h.𝔇 At.links k .lookDigits w w' →
      h.𝔇.digitsPart k a y w → h.𝔇.digitsPart k a y w') :
    HidReads h.𝔇 At.links :=
  ⟨hDig, h.hidReads_base, h.hidReads_head, h.hidReads_lay hp, h.hidReads_att hp⟩

end P5J

#print axioms P5J.AtMgA.𝔇_one
#print axioms P5J.AtMgA.bookPrem
#print axioms P5J.AtMgA.hidReads
