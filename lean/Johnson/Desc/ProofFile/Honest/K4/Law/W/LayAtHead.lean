-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LayAtHead.lean: CONDITIONAL. One statement with its proof.

What is here. UNDER h, the hypothesis on the public files (`P5J.AtMgA`), AND `LaidK4`
(Law/SeatedHead.lean) THE PUBLIC STRUCTURE HAS A LOOKUP's PLACE (`Place`,
Johnson/Desc/First/Look/LookAt.lean) AT THE SEGMENT OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4), with five of its fields: link is the segment's number; fs, the lookup's shape as
the place holds it, is the layout's; lm is the layout's logarithm of the rows of matrix b; the state
from which the lookup starts has 0 as its next slot; ns is the plan's number of entries of the mask
row. So the hypothesis hx (`layAt (P5J.At.X Zp) m = some xl`) of the statements at the thread with
the library's own values (Law/W/ReadersHead.lean, NuCutHead.lean, MatsAreHead.lean,
MaskSixHead.lean, Law/ExchangeTenth.lean and others) names a value that is there: a caller has it by
this statement.
How. One call of the library's `layAt_plan` (Johnson/Road/K4/K4PinsScope.lean) at four fields of
`K4OnX`, which `nine_head` (Law/ElevenHead.lean) has.

Not shown here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). BESIDE h: `LaidK4`, which h gives at each group (`laid_at`,
Law/LaidAtGroup.lean), alone. THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). PUBLIC FACTS ALONE. Its imports reach files under Johnson/Goal/: a program's
walk from import to import, which reads import lines alone and stops unopened at Johnson/Goal/,
ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/:
a floor; they come with h and with Law/ElevenHead.lean. Whether the statement rests, through
`nine_head`, on a statement of such a file has not been traced. A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property. No property is claimed.

  `layAt_laid`   **the place is there, with five of its fields**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead
import Johnson.Road.K4.K4PinsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (layAt_plan parOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (layAt)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h and Lh. **THE LOOKUP's PLACE AT THE SEGMENT IS THERE.** -/
theorem layAt_laid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    ∃ xl, layAt (P5J.At.X Zp) m = some xl ∧ xl.link = m ∧ xl.fs = (P5J.At.X Zp).y.fo ∧
      xl.lm = (P5J.At.X Zp).y.h.lmb ∧ xl.F.next = 0 ∧ xl.ns = (parOf x).hp.ns := by
  have N := nine_head h Lh
  exact layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.layAt_laid
