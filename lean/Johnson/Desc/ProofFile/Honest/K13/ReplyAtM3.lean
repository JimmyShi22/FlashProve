-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ReplyAtM3.lean: kind K13, the members' batching: THE SENTENCE "the
reply that the verifier's state holds is the one that the instance asks about" (`ReplyIs`,
FromThread.lean of this folder) GOES OVER THE KIND's MEMBER. Statements with their proofs, general
in the thread's parameters.

Why. The weights of the last row on the pile are made of the reply as the verifier heard it: one
sent value, in the clear. The prover's side makes them of the instance. So the ties between the two
sides hold only where the state's reply is the instance's. The sub-protocol that hears the reply
accepts any token; the file's last test alone compares the two. So the sentence has to be carried
along the thread, from the border behind that sub-protocol on, by the field `rides`, member by
member. HERE IS THE KIND's SHARE: its sub-protocol leaves the reply as it was.
Main names:
  `replyIs_withClaim`: the sentence at the state that the kind's sub-protocol leaves.
  `k13_reply_behind`: **from the member's accepted step: the sentence in front gives the sentence
    behind**, at where the prover's run stands behind.
  `k13_rides_reply`: **so the premise on `rides` of `k13_thread_behind` (BehindAtM3.lean) is met at
    every `rides` that says just this sentence at the two borders.**

What is not claimed. That the thread's `rides` has this text, or any. That the sentence holds at the
border behind the sub-protocol that hears the reply. That the other members carry it. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K13.FromThread
import Johnson.Desc.ProofFile.Honest.K13.FromStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (Where atM3)
open VerifiableInference.Desc.K13.Honest (withClaim)
open ProofFile.Honest.FirstThread (Letters)

/-- The sentence at the state that the kind's sub-protocol leaves. -/
theorem replyIs_withClaim {Xi : Type} {asked : Xi → E} {x : Xi} {s : S} (st : Statement)
    (msg : Array OracleNotice) (row : TensorRow) (h : ReplyIs asked x s) :
    ReplyIs asked x (withClaim s st msg row) := ReplyIs.kept rfl h

variable {Bk : ProverCoinCounts} {Cl Cl' W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M) {P : Where}

/-- **From the member's accepted step: the sentence in front gives the sentence behind.** hback: the
member returns only where the kind's own sub-protocol does, with the same state. -/
theorem k13_reply_behind {asked : Xi → E} {blk : Block S Cl} {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hback : ∀ rs gs t', blk.decide s rs gs = .ok t' →
      (atM3 (Cl := Cl') P).decide s rs gs = .ok t')
    (hS : L.thread.Stepped blk k s m En ds y cols s') (h : ReplyIs asked m.st.input.x s) :
    ReplyIs asked y.2.st.input.x s' := by
  obtain ⟨-, t, msg, row, -, -, rfl, e2⟩ := k13_from_yes (Cl' := Cl') hback hS
  rw [e2]
  exact replyIs_withClaim _ msg row h

/-- **The premise on `rides` of `k13_thread_behind`, at a `rides` that says just this sentence at
the two borders.** hin: at the border in front it gives the sentence. hout: at the border behind the
sentence gives it. -/
theorem k13_rides_reply {asked : Xi → E} {b : Nat}
    (hback : ∀ blk, L.thread.bs[b]? = some blk → ∀ s rs gs t', blk.decide s rs gs = .ok t' →
      (atM3 (Cl := Cl') P).decide s rs gs = .ok t')
    (hin : ∀ w s, L.rides b w s → ReplyIs asked w.x s)
    (hout : ∀ w s, ReplyIs asked w.x s → L.rides (b + 1) w s) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En ds y cols s',
      Thr L.thread b k s m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m En ds y cols s' → L.rides (b + 1) y.2.st.input s' :=
  fun blk hb _ s _ _ _ _ _ _ hT _ hS =>
    hout _ _ (k13_reply_behind (Cl' := Cl') L (hback blk hb s) hS (hin _ _ hT.2.2.2.2.2.1))

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.replyIs_withClaim
#print axioms ProofFile.Honest.K13.k13_reply_behind
#print axioms ProofFile.Honest.K13.k13_rides_reply
