-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K7/Behind.lean: BEHIND THE YES OF THE NEXT TOKEN's MEMBER OF THE FIRST
CHAIN: `BehindS` (Honest/Thread/PaysS.lean): the form and the riders hold behind it, and the step
has left what `keeps` names. General in the thread T, in the letter Said and in the seat's V, at the
first chain's type of states.

  `seat_moved`     what an item is said of turns in the verifier's state alone across a member's
      step: what was handed to the chain is as it was
  `K7Ties T b l G`   THE TIES TO THE THREAD's LETTERS, each in the direction that the law spends:
      `keepsTo`: the member's clause (`K7MemberKeeps`, Honest/K7/Keeps.lean) gives `T.keeps b` ·
      `ridesTo`: the riders in front, the clause and the reply laid give the riders behind ·
      `formTo`: the form in front and the clause give the form behind
  `k7_member_keeps`   the member's clause, from the two halves of the joined step
  `k7_behindS`     **BEHIND ITS YES**

WHOSE THE THREE TIES ARE. `keepsTo` and `ridesTo` are for whoever lays the thread's letters `keeps`
and `rides`. `formTo` IS NO TIE OF THAT SORT: «THE FORM BEHIND» IS OWED BY THE AUTHORS OF THE
MEMBER's OWN KIND, THAT IS, OF THIS FOLDER: IT STANDS HERE AS A NAMED PREMISE AND IS OPEN.

By `behindS_joined` (Honest/Law/NoHouse/JoinDebts.lean), `keepsOpened_of`
(Honest/Law/NoHouse/OpenedKeeps.lean), `play_mid` (Honest/Law/Along.lean), `play_heard`,
`Thread.heard_length` (Honest/Thread/PaysLaw.lean), the library's `step_ok_iff`, and this folder's
files.

Limits. A conditional lemma on our own definitions; none of the library's goals. Nothing shows that
the records' premises hold at a thread. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.Lays
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Seat (LinkFrame)
open ProofFile (Cl)

section
variable {S' Cl' V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S' Cl' V W X Pb}

/-- Across a member's step what was handed to the chain is as it was. -/
theorem seat_moved {b : Nat} {blk : Block S' Cl'} {k : Coins Bk} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn} (hF : T.Fit b m)
    (hM : T.Moved blk k m E ds y cols) (s s' : S') : T.seat k y.2 s' = ((T.seat k m s).1, s') := by
  obtain ⟨⟨L, -, hy⟩, -⟩ := hM
  unfold Thread.seat
  rw [(play_mid _ _ _ _ _ hy).1, play_heard _ _ _ _ _ hy,
    List.take_append_of_le_length (by rw [T.heard_length hF]; exact Nat.le_add_right _ _)]

end

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}

/-- **The ties to the thread's letters.** A hypothesis's form. -/
structure K7Ties (T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb) (b l : Nat)
    (G : Ground) : Prop where
  keepsTo : ∀ s s', K7MemberKeeps G.W.H.tl G.W.hS.V l s s' → T.keeps b s s'
  ridesTo : ∀ v s s', T.rides b v s → K7MemberKeeps G.W.H.tl G.W.hS.V l s s' →
    s'.out.reply = some v.x.asked → T.rides (b + 1) v s'
  /-- OPEN, AND THIS FOLDER's OWN: the form behind -/
  formTo : ∀ p s s', T.form b (p, s) = true ∧ T.formP b (p, s) →
    K7MemberKeeps G.W.H.tl G.W.hS.V l s s' →
    T.form (b + 1) (p, s') = true ∧ T.formP (b + 1) (p, s')

variable {T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb} {b l V : Nat}
  {blk : Block S Cl} {Z : Pub} {G : Ground} {x : Block S Unit} {a : Place} {fs : List LinkFrame}
  {f : LinkFrame}

/-- The member's clause, from the two halves of the joined step. -/
theorem k7_member_keeps (D : K7Made Z G l blk x a fs f) {ft : Nat} {s mid s' : S}
    {R : List Fmt.RoundView} {cols : List OpenedColumn}
    (hs : (x.retype : Block S Cl).step ft s R cols = .ok (mid, cols.length))
    (hm : mid.failed = none) (ho : f.opened mid = .ok s') (h0 : s'.failed = none) :
    K7MemberKeeps G.W.H.tl G.W.hS.V l s s' :=
  ⟨mid, h1Keeps_of_decide D.lot
      (show x.decide s _ _ = .ok mid from
        ((VerifiableInference.Desc.Sound.step_ok_iff ft _ s mid R cols cols.length).1 hs).2.2.2) hm,
    keepsOpened_of D.frames D.frame ho h0⟩

/-- **BEHIND ITS YES.** -/
theorem k7_behindS (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (K : K7Stands T b l V blk) (D : K7Made Z G l blk x a fs f) (Ti : K7Ties T b l G) :
    BehindS T Said b := by
  refine behindS_joined T D.joined D.frames D.frame K.member
    (fun k s m E y mid => (∃ cols, (x.retype : Block S Cl).step T.ft s (roundsOf y.1) cols =
        .ok (mid, cols.length)) ∧ mid.failed = none ∧
      mid.out.reply = some m.st.input.x.asked ∧ y.2.st.input = m.st.input ∧
      ∀ t t', T.seat k y.2 t' = ((T.seat k m t).1, t')) ?_ ?_
  · intro k s m E ds y cols mid hA hd hM hs hm
    exact ⟨⟨cols, hs⟩, hm, k7_mid_reply K D hd hM hs, (play_mid _ _ _ _ _ hM.1.choose_spec.2).1,
      seat_moved hA.1.2.1 hM⟩
  · intro k s m E y mid s' hA hMid ho h0 hsame _
    obtain ⟨⟨cols, hs⟩, hm, hr, hi, hseat⟩ := hMid
    have hK := k7_member_keeps D hs hm ho h0
    have hr' : s'.out.reply = some m.st.input.x.asked := by rw [← IM.sameReply_eq hsame, hr]
    refine ⟨?_, ?_, Ti.keepsTo s s' hK⟩
    · unfold Thread.Form
      rw [hseat s s']
      exact Ti.formTo _ s s' hA.1.2.2.1 hK
    · rw [hi]
      exact Ti.ridesTo _ s s' hA.1.2.2.2.2.2.1 hK hr'

end ProofFile.Honest

#print axioms ProofFile.Honest.seat_moved
#print axioms ProofFile.Honest.k7_member_keeps
#print axioms ProofFile.Honest.k7_behindS
