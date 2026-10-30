-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/MadeOpen.lean: the code switch: WHAT THE TYPED WITNESS IN FRONT IS AT THE
MADE READINGS OF THE CHAIN's WITNESS: two equations by unfolding, for the tie that closes the kept
members' pins.

Main names:
  `selNew_made`: the new messages of `wtMade` (BehindSig.lean) are the witness's messages (`msgsOf`,
    Johnson/Desc/Sound/MsgSig.lean).
  `selBk_made_open`: the open word's message that the sub-protocol's extractor hands back at
    `wtMade` is, entry by entry, what is read of these messages along iJ.
Limits. Two equations by `rfl`. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.ExtMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT msgsOf)

variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (seat : Fin r.l.length → ℕ × ℕ) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT)

/-- The new messages of the typed witness behind, made of a witness of the table of joints, are that
witness's messages. -/
theorem selNew_made :
    selNew (Letters.plain r H) iJ iQ (wtMade iJ iQ seat arr w) = msgsOf r.cs r.l seat arr w := rfl

/-- **The open word's message that the sub-protocol's extractor hands back there**: entry by entry
what is read of the witness's new messages along iJ. -/
theorem selBk_made_open (j : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
    (Letters.plain r H).oZ).keep r.kp).Sh.Cf.J) :
    (selBk (Letters.plain r H) iJ iQ (wtMade iJ iQ seat arr w)).2.1.1 j =
      (sigOf r.cs r.l).ents (msgsOf r.cs r.l seat arr w) (iJ j) := rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.selNew_made
#print axioms VerifiableInference.Desc.First.K2Caller.selBk_made_open
