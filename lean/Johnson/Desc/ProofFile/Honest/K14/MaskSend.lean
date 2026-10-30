-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MaskSend.lean: kind K14: THE OWNER's SENTENCE (the field fresh of
the frame's record Good, Honest/Side.lean) AT THE PART OF "send o_u": two of the three statements of
Honest/K14/MaskStated.lean AS THEOREMS; the third, MaskBridge, is a theorem in
Honest/K14/MaskLaw.lean. Each is one call: the implications of Honest/K14/MaskOfRows.lean and
Honest/K14/MaskLaw.lean at the shared sending's owner's sentence at the rows (rowsFreshAny,
Johnson/SendSim/At/FreshWideProofs.lean).

  maskApart       at fixed challenges and fixed positions within the count: over the part's own
                  coins, the first mask's 2 k + 1 coefficients are uniform and independent of what
                  the part shows together with all of o_u's own coins
  maskOwnerLaw    the frame's form: at every book at which the test's fits accepts and GuardClear
                  holds at the guard maskGuard at every spender that spends: the field fresh
  maskOwnerLaw_any, maskOwnerLaw'   **the law with no premise outside the frame's form**: at every
                  k; and at maskOwner A, the value for a list of tests

WHAT IS LEFT, WITH ALL FOUR. That a description's book passes the test is not shown in this file
(under premises: Honest/K14/BookAtU.lean): nothing here says that the field is met or paid at any
book of a description · what the part shows is not all that a run shows of these coins: the fold
that spends the coefficients sends scalars under them, and the part behind it is handed the table
whole; nothing is said here of what these show: so nothing is said of the coefficients in a run ·
the challenges and the positions are fixed before the coins are sampled · one request · they range
over every data, right or wrong, and over stands that no run reaches · that the premises are met
together at one side is not shown in this file.
What they rest on. The premises are those of the statements: Honest/K14/MaskStated.lean names each.
They rest on files that are no part of the release's library: another kind's laws on what a sending
shows (rowsFreshAny and the files beneath it in Johnson/SendSim) and this kind's own. This file
states no goal of the release. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.MaskOfRows
import Johnson.Desc.ProofFile.Honest.K14.MaskLaw
import Johnson.SendSim.At.FreshWideProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- **At "send o_u" the first mask's coefficients are uniform and independent of what the part shows
together with all of o_u's own coins**, at fixed challenges and fixed positions within the count,
over the part's own coins. The statement, with what is left beside it: MaskApart,
Honest/K14/MaskStated.lean. -/
theorem maskApart : MaskApart := maskApart_of_rows OnBytes.SendSim.At.rowsFreshAny

/-- **The owner's law at "send o_u" in the frame's form.** The statement, with what is left beside
it: MaskOwnerLaw, Honest/K14/MaskStated.lean. That a description's book passes the test is not
shown. -/
theorem maskOwnerLaw : MaskOwnerLaw := maskOwnerLaw_of_apart maskApart

/-- **THE LAW WITH NO PREMISE OUTSIDE THE FRAME's FORM**, at every k: the three premises on the
shapes are read off fits, which asks them with code. -/
theorem maskOwnerLaw_any (A : SendPub) (k : Nat) :
    OwnerLaw (maskOwnerTest A k) (MaskFresh A) := by
  intro Bk ord o hmine hf hg
  obtain ⟨-, hfit, hm, ⟨s, hs, rfl⟩, -, -⟩ := maskOwnerFits_gives (A := A) (k := k) hf
  exact maskOwnerLaw A s hfit hm hs Bk ord o hmine hf hg

/-- **The law at the value for a list of tests**: no premise outside the frame's form. -/
theorem maskOwnerLaw' (A : SendPub) : OwnerLaw (maskOwner A) (MaskFresh A) :=
  maskOwnerLaw_any A (maskRounds A)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.maskApart
#print axioms ProofFile.Honest.K14.maskOwnerLaw
#print axioms ProofFile.Honest.K14.maskOwnerLaw_any
#print axioms ProofFile.Honest.K14.maskOwnerLaw'
