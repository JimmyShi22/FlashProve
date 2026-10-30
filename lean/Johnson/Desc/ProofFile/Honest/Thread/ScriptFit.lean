-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ScriptFit.lean: under a continuation a message that has been
sent changes no more. The invariant's clause on the open items is asked at every continuation of
what was heard (Honest/Thread/Thr.lean, `Thread.Items`); the witness of the `Script`
(Honest/Thread/First.lean, `Script.wit`) reads message number n at the first `fixedMsg n` challenges
alone. Here: an executable test on the `Script`, beside `Thread.fits`, whose bound on `fixed` is on
the trees alone: `fixedMsg n` is at most the number of rounds before the border from which on
message n is spoken of; and the lemma: where the test passes and n is below `nMsg`, at that border
and every later one, at a state at which clause (F) holds, that message is the same at what was
heard and at every continuation.

  1  `roundsTo_mono`   more sub-protocols, no fewer rounds
  2  `Script.msgsFit`   the executable test
  3  `wit_msg_more`, `wit_msg_at`   the lemma: general; at a border of a `Thread`

The parameters of the test. `born n`: the border after the sub-protocol that sends message n (the
first at which an item may speak of it). `nMsg`: how many messages are numbered. `front`, `bs`:
those of the `Thread`.

Limits.
  * Nothing compares `born` with the description's own table of sendings, or `fixedMsg` with the
    definition of `msg`.
  * It is none of the library's goals.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Thread.MemberLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block)

/-! ## 1 More sub-protocols, no fewer rounds -/

theorem roundsTo_mono {S Cl : Type} : ∀ (bs : List (Block S Cl)) (a b : Nat), a ≤ b →
    roundsTo bs a ≤ roundsTo bs b
  | [], a, b, _ => by
    unfold roundsTo declsTo
    simp
  | _ :: _, 0, _, _ => Nat.zero_le _
  | _ :: _, _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | x :: l, a + 1, b + 1, h => by
    rw [roundsTo_cons, roundsTo_cons]
    exact Nat.add_le_add_left (roundsTo_mono l a b (Nat.le_of_succ_le_succ h)) _

namespace FirstThread

variable {Bk : ProverCoinCounts} {W Cells Tok M : Type}

/-! ## 2 The test -/

/-- **The executable test**: each numbered message changes no more from the border from which on it
is spoken of. It is a definition: a test on parameters. -/
def Script.msgsFit {S Cl : Type} (Q : Script Bk W Cells Tok M) (front : Nat)
    (bs : List (Block S Cl)) (born : Nat → Nat) (nMsg : Nat) : Bool :=
  (List.range nMsg).all fun n => decide (Q.fixedMsg n ≤ front + roundsTo bs (born n))

/-! ## 3 The lemma -/

/-- Where as many challenges are heard as the message reads, more of them change it no more. -/
theorem wit_msg_more (Q : Script Bk W Cells Tok M) (k : Coins Bk) (w : W)
    (h ds : List Fmt.Drawn) (n : Nat) (hn : Q.fixedMsg n ≤ h.length) :
    (Q.wit k w (h ++ ds)).msg n = (Q.wit k w h).msg n := by
  show Q.msg n k w ((h ++ ds).take (Q.fixedMsg n)) = Q.msg n k w (h.take (Q.fixedMsg n))
  rw [List.take_append_of_le_length hn]

/-- **At a border of a `Thread`, from the message's own: the same at every continuation**, where the
test passes, n is below `nMsg` and (F) holds. -/
theorem wit_msg_at {S Cl V X Pb : Type} (T : Thread Bk S Cl V W X Pb)
    (Q : Script Bk W Cells Tok M) {born : Nat → Nat} {nMsg : Nat}
    (hQ : Q.msgsFit T.front T.bs born nMsg = true) {n b : Nat} (hn : n < nMsg)
    (hb : born n ≤ b) {m : Mid W X} (hF : T.Fit b m) (k : Coins Bk) (ds : List Fmt.Drawn) :
    (Q.wit k m.st.input (m.st.heard ++ ds)).msg n = (Q.wit k m.st.input m.st.heard).msg n := by
  refine wit_msg_more Q k _ _ ds n ?_
  unfold Script.msgsFit at hQ
  have h1 := of_decide_eq_true (List.all_eq_true.1 hQ n (List.mem_range.2 hn))
  rw [T.heard_length hF]
  exact Nat.le_trans h1 (Nat.add_le_add_left (roundsTo_mono T.bs _ _ hb) _)

end FirstThread
end ProofFile.Honest

#print axioms ProofFile.Honest.roundsTo_mono
#print axioms ProofFile.Honest.FirstThread.wit_msg_more
#print axioms ProofFile.Honest.FirstThread.wit_msg_at
