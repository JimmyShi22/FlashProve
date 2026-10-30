-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexApart.lean: CONDITIONAL. Two statements with their
proofs.

What is here. THE TWELVE ENTRIES OF THE INDEX MASKS' MESSAGE AT WHICH THE LOTS OF THE TWELVE
MEMBERS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) ANSWER ARE TWELVE DIFFERENT
ENTRIES. Under the library's hypothesis on the public files the number of entries taken in front of
the member of group g (`k4IndexTakes Zp g`, Lot/IndexNum.lean) IS g (`k4IndexTakes_is`, from
`takes_written` and `bearing_even`, Law/W/IndexTakes.lean). A number is its quotient and remainder
by any number: so row and place tell the group (`k4IndexEntry_inj`). So another group's lot never
answers where this group's does: by `k4IndexLotG_isSome` (Law/W/IndexLotGIs.lean) a lot answers
inside its own entry's fence alone; no statement here says so of two lots.

  `k4IndexTakes_is`   **in front of the member of group g just g entries are taken.**
  `k4IndexEntry_inj`   **row and place tell the group.**

Not shown here. NOTHING ON ANOTHER KIND's LOT: that the output head's merge's text answers at the
entry of take number 12 is for that kind's files to say; `indexTakes_head` (Law/W/IndexTakes.lean)
has the number alone. NOTHING ON THE SENDER's OWN LOT of this message: that its text agrees with
K4's is not shown. The number of mask rows stays a term of the public part; no numeral is had for
it. The hypotheses: h (the library's `P5J.AtMgA`), g and g' below 12. That h can hold: the side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what
it is worth). THE FULL SIZE ALONE, and the format's second hash function alone. Beneath it stand closed
facts by evaluation in Lean's kernel, which no independent checker has replayed
(Law/W/IndexTakes.lean's). A program's walk from import to import, which reads import lines alone
and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*,
stopped at 43 modules under Johnson/Goal/ and at 6 under Johnson/Bridge/: so these counts are lower
bounds; it met no module under ThirdParty/ or Johnson/D/ and none that begins Cb.Bridge. A LAW, NOT
A PART: no file that defines a part of the proof file's description may import this one. Nothing on
soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexTakes
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.Lot (k4IndexTakes k4IndexRows k4IndexRow k4IndexPlace)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **IN FRONT OF THE MEMBER OF GROUP g JUST g ENTRIES ARE TAKEN.** CONDITIONAL on h and hg. -/
theorem k4IndexTakes_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12) :
    k4IndexTakes Zp g = g := by
  unfold k4IndexTakes
  rw [takes_written h (by omega)]
  exact bearing_even g hg

/-- **ROW AND PLACE TELL THE GROUP.** CONDITIONAL on h, hg, hg', e1 and e2. -/
theorem k4IndexEntry_inj (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g g' : ℕ} (hg : g < 12)
    (hg' : g' < 12) (e1 : k4IndexRow Zp g = k4IndexRow Zp g')
    (e2 : k4IndexPlace Zp g = k4IndexPlace Zp g') : g = g' := by
  unfold k4IndexRow at e1
  unfold k4IndexPlace at e2
  rw [k4IndexTakes_is h hg, k4IndexTakes_is h hg'] at e1 e2
  calc g = k4IndexRows Zp * (g / k4IndexRows Zp) + g % k4IndexRows Zp :=
        (Nat.div_add_mod g _).symm
    _ = k4IndexRows Zp * (g' / k4IndexRows Zp) + g' % k4IndexRows Zp := by rw [e1, e2]
    _ = g' := Nat.div_add_mod g' _

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4IndexTakes_is
#print axioms ProofFile.Honest.K4.W.k4IndexEntry_inj
