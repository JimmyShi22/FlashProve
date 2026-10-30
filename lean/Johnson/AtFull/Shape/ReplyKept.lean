-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReplyKept.lean: UNDER THE HEAD P5J.AtMgA: NO MEMBER OF THE PROOF FILE's OWN
FIRST CHAIN BUT ONE AT A PLACE OF THE KIND K7 TURNS THE REPLY's SEAT: so, with the request's words
(ReqAtHead.lean), the covered positions are behind such a member's yes what they were in front. A
joining of laws; nothing is evaluated.

What it is for. Some of the members' named tests on values read the heard reply and the request's
words and nothing else of the state: S.covered (the reads' member of the head's link; the lookup's
member behind it; the quiet step behind the head's code switch). The reply is a value that the
prover sends; but it is tested where it is heard, at the place of the kind K7. Behind that place
these tests are no matter of the prover's values or of the draws.

By what. The driver lays a guard around every block of the first chain: but at a place of the kind
K7 a yes must leave what the seat's test "same" compares. The library has the law of that guard
(firstChain_flat_leaves, Johnson/Desc/Sound/GuardAtDriver.lean), that the proof file's chain is such
a chain with ProofFile.sameReply for "same" (ProofFile.Law.pure_first_at,
Johnson/Desc/ProofFile/Law/FirstSame.lean; LPFK9.k13_stands, Johnson/LPFK9R/SubsFull.lean), and what
that test compares (IM.sameReply_eq, Johnson/IMR/SeatForm.lean).

  **`reply_kept_at`**: under the head, at every n: a member at number n whose place is not of the
    kind K7: every yes of its step leaves S.out.reply.
  `covered_congr`: S.covered reads the request's words and the reply's seat alone.
  **`covered_kept_at`**: so at such a member S.covered T V says behind every yes what it said in
    front.

Limits. WHICH NUMBERS BEAR A PLACE OF THE KIND K7 IS NOT SAID HERE. That a reply is heard, or that
S.covered returns, at any state is not shown. One member at a time. That the head has a member is
shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.Shape.ReqAtHead
import Johnson.Desc.Sound.GuardAtDriver
import Johnson.Desc.ProofFile.Law.FirstSame
import Johnson.LPFK9R.SubsFull
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName step_iff)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **No member but one at a place of the kind K7 turns the reply's seat.** -/
theorem reply_kept_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n : Nat) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → blk.place.kind ≠ KindName.K7 →
      ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) → s'.out.reply = s.out.reply := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨H, hf, hs, -⟩ := ProofFile.Law.pure_first_at O.chain (LPFK9.k13_stands O)
  intro blk hb hk ft s rs cols s' k hst
  have hm := List.mem_of_getElem? hb
  obtain ⟨_, hd, _⟩ := (step_iff ft blk s s' rs cols k).1 hst
  have hl := VerifiableInference.Desc.First.firstChain_flat_leaves
    (hh := fun t : S => t.out.reply)
    (fun t u e => by
      rw [hs] at e
      exact (IM.sameReply_eq e).symm) hf blk hm
  rcases hl with e | e
  · exact absurd e hk
  · exact e s _ _ s' hd

/-- The covered positions are made of the request's words and the reply's seat alone. -/
theorem covered_congr {s s' : S} (e₁ : s'.req = s.req) (e₂ : s'.out.reply = s.out.reply)
    (T V : Nat) : s'.covered T V = s.covered T V := by
  unfold S.covered S.replyTok?
  rw [e₂]
  cases (s.out.reply.bind fun g => if ofNat g.c0.toNat == g then some g.c0.toNat else none) with
  | none => rfl
  | some y => exact coveredAt_same e₁ T V y

/-- **The covered positions are behind every yes what they were in front**, at a member whose place
is not of the kind K7. -/
theorem covered_kept_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n T V : Nat) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → blk.place.kind ≠ KindName.K7 →
      ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) →
        s'.covered T V = s.covered T V :=
  fun blk hb hk ft s rs cols s' k hs =>
    covered_congr (req_kept_at h n blk hb ft s rs cols s' k hs)
      (reply_kept_at h n blk hb hk ft s rs cols s' k hs) T V

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.reply_kept_at
#print axioms Johnson.AtFull.Shape.covered_congr
#print axioms Johnson.AtFull.Shape.covered_kept_at
