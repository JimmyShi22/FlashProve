-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Accepted.lean.
WHAT IT IS NOT. CONDITIONAL ON TWO STRUCTURES OF PREMISES, K6Seated AND K6Fronted, WHICH ARE SHOWN
HERE OF NO DESCRIPTION OF THE PROTOCOL AND OF NO THREAD (K6Fronted at the library's own letters:
Honest/K6/Law/FrontedAtHead.lean). IT RESTS ON k6_fits (Honest/K6/Law/Plays.lean): it is proved only
where that statement is: its own axioms' line tells. The ends are definitions of the honest side's
frame, premises' forms of its rules: they are none of the library's goals, and no verifier's accept.
Nothing on soundness, on completeness or on hiding.
WHAT IT IS. The debts `AcceptedS` (Honest/Thread/PaysS.lean) and `Accepted`
(Honest/Thread/Pays.lean) at the member of a chain's `Thread` at which the honest side of the
sub-protocol "the output head's own rounds" (K6) stands: from the thread in front, what is said with
it, and the prover's side of the step, the sub-protocol's own step says yes.
  K6Fronted T Said b W m blk   the verifier's side: the member is the seated constant in the dress
                          of the description's first chain (K6MemberIs, Kinds/Law/K6WayUp.lean);
                          wherever the thread holds in front of it, and what is said with it, the
                          state is ready (K6Front, K6/Honest/Law/Returns.lean).
  k6_acceptedS            CONDITIONAL on the two structures: AcceptedS T Said fall b: the thread T,
                          the sentence Said and the fall are variables: neither "nothing of the
                          member stops" nor the fall is spent, and of Said only what K6Fronted's
                          second field spends.
  k6_accepted             CONDITIONAL on the two, the second at the sentence that says nothing:
                          Accepted T fall b.
WHO IS MEANT TO PAY K6Fronted. member: k6_member_at_mg (Kinds/Law/K6WayUpAtSeat.lean). front:
k6Front_of_items (K6/Honest/Law/FrontOfItems.lean), from what the thread's clause on the promise
hands at the border.
CALLED: k6_fits, member_returns, P4.same_of_eq, step_takes (Honest/Thread/Ties.lean), yields_drawn,
play_yields.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Plays
import Johnson.Desc.K6.Honest.Law.Returns
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.Desc.ProofFile.Honest.Thread.Ties
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.Kinds (Head.Par)
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs K6Front)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}

/-- **THE VERIFIER's SIDE AT THE MEMBER NUMBER b**: what the yes of the sub-protocol's own step
wants of the member and of the state in front. Said: the chain's sentence on what earlier rounds
showed: a letter. m: how many slots of the ledger are to be left free behind the member. (What the
sub-protocol opens behind its yes asks one thing more of the member: that it passes its test on the
plan: Kinds/Law/K6OutAtMember.lean.) A definition: a premise's form. Nothing is claimed of it. -/
structure K6Fronted
    (T : Thread Bk VerifiableInference.Desc.First.S Claim (Local W₀ Rc Inst Tr)
      (Local W₀ Rc Inst Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (b : Nat) (W : OnBytes.Model.Verify.Public) (m : Nat)
    (blk : Block VerifiableInference.Desc.First.S Claim) : Prop where
  /-- the member is the seated constant at the public parameters W, link 24, as the description's
  first chain dresses it -/
  member : K6MemberIs W 24 ProofFile.sameReply IM.k6Place blk
  /-- wherever the thread holds in front of the member, and what is said with it, the verifier's
  state is ready -/
  front : ∀ k s r E, ThrS T Said b k s r E → K6Front W m s

variable {T : Thread Bk VerifiableInference.Desc.First.S Claim (Local W₀ Rc Inst Tr)
    (Local W₀ Rc Inst Tr) X Pb}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop}
  {b : Nat} {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
  {blk : Block VerifiableInference.Desc.First.S Claim} {W : OnBytes.Model.Verify.Public} {m : Nat}

/-- **IT IS ACCEPTED, FROM THE PAIR**: the debt `AcceptedS` (Honest/Thread/PaysS.lean) at the member
at which the sub-protocol's half stands, at every letter Said and every letter fall. CONDITIONAL: on
`K6Seated` and `K6Fronted`. -/
theorem k6_acceptedS (Hs : K6Seated T b wit p at_ blk) (Hf : K6Fronted T Said b W m blk)
    (fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String) :
    AcceptedS T Said fall b := by
  intro blk' hb k s r E ds y cols hT hd _ _ hM
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hb)
  have hF := k6_fits T Hs blk hb k r E ds y cols hd hM
  obtain ⟨s', G, hs, _⟩ := VerifiableInference.Desc.Kinds.Head.Law.member_returns Hf.member
    (by decide) (fun _ _ e => P4.same_of_eq e) T.ft (Hf.front k s r E hT) (roundsOf y.1) cols hF
  have hM' := hM
  unfold Thread.Moved at hM'
  obtain ⟨⟨l, _, hy⟩, hc⟩ := hM'
  have hj : 0 = cols.length :=
    step_takes (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc hs
  exact ⟨s', hM, by rw [← hj]; exact hs⟩

/-- The same from the thread alone: the debt `Accepted` (Honest/Thread/Pays.lean). CONDITIONAL: on
`K6Seated`, and on `K6Fronted` at the sentence that says nothing. -/
theorem k6_accepted (Hs : K6Seated T b wit p at_ blk)
    (Hf : K6Fronted T (fun _ _ _ => True) b W m blk)
    (fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String) :
    Accepted T fall b := by
  intro blk' hb k s r E ds y cols hT
  exact k6_acceptedS Hs Hf fall blk' hb k s r E ds y cols ⟨hT, trivial⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_acceptedS
#print axioms ProofFile.Honest.K6.k6_accepted
