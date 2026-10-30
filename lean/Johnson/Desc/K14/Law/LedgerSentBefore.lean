-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSentBefore.lean: the proof of the statement `SentBeforeOwed`
(Johnson/Desc/K14/Law/LedgerSentBeforeOwed.lean): in a tiled row of the shared chain's pieces, the
first without data, the next five along the kind's first five blocks' declared rounds, the three
messages' trees are sent in front of every piece from number 6 on (`SentBefore`). Two theorems:
calls alone.
  sentBefore_of_bases   from the bases of the pieces number 3 and 6 (`BasesOwed`,
                        LedgerBasesOwed.lean): `sb_sh` (Johnson/Desc/Sound/SeamTreesSh.lean) CALLED
                        at lo := the first piece's base.
  sentBefore            **the statement**: at `bases` (LedgerBases.lean).
What is not claimed. That a row is tiled, or that its pieces go along the blocks' rounds. Nothing on
soundness.

-/
import Johnson.Desc.K14.Law.LedgerSentBeforeOwed
import Johnson.Desc.K14.Law.LedgerBases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence (tenantSh sb_sh)
open _root_.Run.PQ (CK)

/-- From the bases of the pieces number 3 and 6. -/
theorem sentBefore_of_bases : BasesOwed → SentBeforeOwed := by
  intro hB Q b1 b2 b3 b4 b5 b6 b7 b8 sentU layU layO hb hw hlU hlO hU hO C Fr P₁ S₂ Cl Cells Tok
    num N f pt x2 x3 x4 x5 x6 rest hN hlo hT hf hA k x hk hx m
  obtain ⟨_, _, e3, _, e6⟩ := hB Q b1 b2 b3 b4 b5 b6 b7 b8 sentU layU layO hb hw hlU hlO C Fr
    (P₁ × S₂) Cl (Wit Cells Tok MsgT) num f pt x2 x3 x4 x5 x6 rest hT hf hA
  exact sb_sh f.base layU layO Q.codes sentU (withOmega Q.S) hlU hlO hU hO N f _ hN hlo hT x3 x6
    rfl rfl e3 e6 k hk x hx m

/-- **The three messages' trees are sent in front of every piece from number 6 on.** -/
theorem sentBefore : SentBeforeOwed := sentBefore_of_bases bases

end Desc.K14.Law

#print axioms Desc.K14.Law.sentBefore_of_bases
#print axioms Desc.K14.Law.sentBefore
