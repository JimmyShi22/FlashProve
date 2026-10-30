-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Sends.lean: THE SENDING THAT THE CODE SWITCH CALLS RETURNS
(`sendByL8`, Johnson/Top/H0/Tw/K2/SendL8.lean); what it returns is a term; and what it leaves of the
statement, message by message. Statements and proofs. NOTHING OF THE SENDING IS PROVED ANEW: the
law is the shared sending's own (`sendP_yes`, Johnson/Prover/Send/FormP.lean; `behind_at`,
`behind_rest`, Johnson/Prover/Send/Form.lean), reached through the library's `sendByL8_iff` and
`sendOpen_iff` (Johnson/Top/H0/Tw/K2C/SendsOpen.lean).

  `sentAt`          what the sending returns, as a term: the shared sending's own state behind
                    (`K1.behind`), the new messages' numbers, the count of answers
  `sendByL8_returns`   PREMISES: Q, the sending as the shared sending's public letter, has the
                    switch's two numbers and announces the switch's messages · the first entry's
                    test on the plan · the first round fits its entry · and `sendP_yes`' own: what
                    stands in front (`SendFront`) · the codes' lengths are powers of two · the first
                    round shows no item and draws just the place's seeds · no factor is spelt by
                    three words 0 · the second round's first items hold the place's answers
  `sentAt_codes`, `sentAt_groups`, `sentAt_size`, `sentAt_old`, `sentAt_new`, `sentAt_ids`   behind
                    the sending: the codes and the groups are as they were · the statement has so
                    many messages more · every message that was there is as it was · the new
                    message number k, as a term (`K1.wr`) · its number is the old size + k

Limits. Nothing here holds Q against the place's numbers. That these facts give what the step behind
the sending asks (Returns/BehindAt.lean, Returns/Read.lean) is not shown here. Nothing on the book.
Nothing on any property.

-/
import Johnson.Prover.Send.FormP
import Johnson.Top.H0.Tw.K2C.SendsOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open Johnson.Prover.Send (SendFront numbers shapeAt sendP_yes behind_at behind_rest)
open VerifiableInference.Desc.First.K2 (sendByL8_iff sendOpen_iff)
open VerifiableInference.Desc.First.Send (planOk1)
open _root_.Tw.K2 (sendByL8)
open _root_.Desc.Plain (DState)

/-- The state in front of the sending, as the shared sending takes it. -/
def frontOfSend (S : Statement) (B : TreeBook) (roots : Nat) : DState Unit := ⟨S, B, roots, [], ()⟩

/-- **What the sending returns**, as a term. -/
def sentAt (Q : K1.Par) (S : Statement) (B : TreeBook) (roots : Nat) (rS rL : Fmt.RoundView) :
    _root_.Tw.K2.Sent :=
  ⟨(K1.behind Q (frontOfSend S B roots) (K1.seedsOf Q rS) (K1.answersIn (K1.cutTo Q rL))).st,
    (K1.behind Q (frontOfSend S B roots) (K1.seedsOf Q rS) (K1.answersIn (K1.cutTo Q rL))).book,
    (K1.behind Q (frontOfSend S B roots) (K1.seedsOf Q rS) (K1.answersIn (K1.cutTo Q rL))).roots,
    numbers Q S.oracles.size, Q.answers⟩

/-- **The sending that the switch calls returns.** -/
theorem sendByL8_returns (P : _root_.Tw.K2.Par9) (Q : K1.Par) (S : Statement) (B : TreeBook)
    (roots : Nat) (notices : Array OracleNotice) (rS rL : Fmt.RoundView)
    (hgp : Q.gp = ⟨P.samples, P.firstTree⟩) (hsent : Q.sent = notices)
    (hplan : planOk1 none notices P.eSeed = true)
    (hfits : _root_.Desc.Plain.fits P.eSeed rS = true)
    (F : SendFront Q (frontOfSend S B roots)) (hl : Q.codes.lengthsOk = true)
    (hdraw : (rS.drawn.elems.map E.ofTriple).length = Q.seeds * (Q.coordinates + 1))
    (f1 : rS.vals = []) (f2 : rS.drawn.poss = []) (f3 : rS.drawn.trits = [])
    (hz : ∀ s ∈ K1.seedsOf Q rS, isZeroE s.2 = false)
    (hn : (K1.answersIn (K1.cutTo Q rL)).length = Q.answers) :
    sendByL8 P S B roots true notices rS rL = .ok (sentAt Q S B roots rS rL) := by
  have h := sendP_yes Q (frontOfSend S B roots) rS rL F hl hdraw f1 f2 f3 hz hn
  rw [hgp, hsent] at h
  refine (sendByL8_iff P S B roots true notices rS rL _).2 ⟨_, _, _, ?_, rfl⟩
  rw [if_pos rfl]
  exact (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).2 ⟨hplan, hfits, _, _, h⟩

variable (Q : K1.Par) (S : Statement) (B : TreeBook) (roots : Nat) (rS rL : Fmt.RoundView)

theorem sentAt_codes : (sentAt Q S B roots rS rL).st.codes = S.codes :=
  (behind_rest Q (frontOfSend S B roots) _ _).1

theorem sentAt_groups : (sentAt Q S B roots rS rL).st.groups = S.groups :=
  (behind_rest Q (frontOfSend S B roots) _ _).2.1

theorem sentAt_size :
    (sentAt Q S B roots rS rL).st.oracles.size = S.oracles.size + Q.sent.size :=
  (behind_rest Q (frontOfSend S B roots) _ _).2.2.2.2.1

/-- Every message that was there is as it was. -/
theorem sentAt_old (o : Nat) (ho : o < S.oracles.size) :
    (sentAt Q S B roots rS rL).st.oracles[o]? = S.oracles[o]? :=
  (behind_rest Q (frontOfSend S B roots) _ _).2.2.2.2.2.1 o ho

/-- The new message number k, as a term. -/
theorem sentAt_new (k : Nat) (hk : k < Q.sent.size) :
    (sentAt Q S B roots rS rL).st.oracles[S.oracles.size + k]? =
      some (K1.wr Q.codes (K1.seedsOf Q rS) (S.oracles.size + k) (shapeAt Q k)
        ((K1.answersIn (K1.cutTo Q rL)).drop (K1.offset Q k))) :=
  behind_at Q (frontOfSend S B roots) _ _ k hk

/-- Its number. -/
theorem sentAt_ids (k : Nat) (hk : k < Q.sent.size) :
    (sentAt Q S B roots rS rL).ids[k]? = some (S.oracles.size + k) := by
  show (numbers Q S.oracles.size)[k]? = _
  unfold numbers
  rw [Array.getElem?_map, Array.getElem?_range]
  simp [hk, Nat.add_comm]

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.sendByL8_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.sentAt_new
#print axioms VerifiableInference.Desc.K2.Honest.Returns.sentAt_ids
