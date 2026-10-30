-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Stays.lean: WHEN THE FIRST CHAIN's THREE SORTS OF A RIDER's
CLAUSE STAY PAST THE MEMBER "the output head's own rounds" (K6): the debt `StaysBy`
(Honest/Thread/Riders.lean) at `riderHead`, `riderPile`, `riderRoom`, each from one premise: the
thread's clause of `keeps` at the member gives `K6Keeps` (Johnson/Desc/K6/Honest/Law/Keeps.lean).
GENERAL IN THE THREAD. EVERY THEOREM IS CONDITIONAL.

Why it is typed. `staysBy_head` (Honest/Thread/RidersStay.lean) asks that the member leaves "where
the chain stands". This member does not: it lays three fields of the head's own part of the state
anew (the ledger; what its rounds heard; the state of the squares' sumcheck). The general form
`staysBy_head_of` (Honest/Thread/RidersStayH.lean) asks what `K6Keeps` gives: it is called here. So
a fact on that part stays past this member if it reads none of the three.

  `k6_staysBy_head`   CONDITIONAL: and P does not read the three fields
  `k6_staysBy_three`, `k6_staysBy_sized`   at four facts
  `k6_staysBy_pile`, `k6_staysBy_room`   by `staysBy_pile`, `staysBy_room`: the member leaves the
                      statement and what goes on to the later chains

Riders.lean's head names in words five facts at which it means `riderHead`. Read as
`a.opened = true`, `a.t.isSome = true`, `a.claim.isSome = true` (OUR READING OF THE WORDS "opened",
"the tables are laid", "the claim is laid"), three of them read none of the three fields:
`k6_staysBy_three`. "What the head's rounds heard is laid" is laid by this member
(Honest/K6/Law/Lays.lean). "The ledger has its sizes" reads the ledger: `k6_staysBy_head` does not
serve; `K6Keeps` holds "a later ledger", which keeps the sizes: `k6_staysBy_sized`.

ON THE PREMISE hk. It runs from the thread's clause to `K6Keeps`. The law on what stands behind this
member (Honest/K6/Law/Behind.lean) takes the other direction: wherever `K6Keeps` holds, so does the
clause. Together they say that at this member the thread's clause IS `K6Keeps`, up to "if and only
if": a weaker clause meets that law and starves these; a stronger one the reverse. Where the first
chain's clause is laid by the place's kind (`kpBy`, Honest/Thread/KeepsBy.lean), it is the kind's
own at this member, both ways.

Limits. The premise on the thread's clause is shown at no thread here. Modules under
lean/Johnson/Goal/ are among what this file imports, through Honest/Thread/RidersStayH.lean,
which imports RidersStay.lean: it imports no module of that folder by name and calls nothing that is
declared there: they lie beneath the thread's file that it calls. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersStayH
import Johnson.Desc.K6.Honest.Law.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps)

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **A fact on the head's own part that reads none of the three fields stays.** CONDITIONAL: hk:
the thread's clause at the member gives `K6Keeps`; hP: P does not read the three fields. -/
theorem k6_staysBy_head {b lo hi : Nat} {P : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → K6Keeps s s')
    (hP : ∀ (o : HeadOwn) (F : Fork) x q, P o → P { o with F := F, x := x, squaresP := q }) :
    StaysBy T b (riderHead lo hi P) :=
  staysBy_head_of T fun s s' hK a ha => by
    obtain ⟨o, o', ho, ho', e⟩ := (hk s s' hK).own
    obtain rfl : a = o := by
      rw [ha] at ho
      exact VerifiableInference.Desc.First.Here.head.inj ho
    exact ⟨o', ho', fun hPa => by rw [e]; exact hP a _ _ _ hPa⟩

/-- At three facts on the head's own part. CONDITIONAL: hk. -/
theorem k6_staysBy_three {b lo hi : Nat} (hk : ∀ s s', T.keeps b s s' → K6Keeps s s') :
    StaysBy T b (riderHead lo hi fun a => a.opened = true) ∧
      StaysBy T b (riderHead lo hi fun a => a.t.isSome = true) ∧
      StaysBy T b (riderHead lo hi fun a => a.claim.isSome = true) :=
  ⟨k6_staysBy_head T hk fun _ _ _ _ h => h, k6_staysBy_head T hk fun _ _ _ _ h => h,
    k6_staysBy_head T hk fun _ _ _ _ h => h⟩

/-- **"The ledger has its sizes" stays.** CONDITIONAL: hk. -/
theorem k6_staysBy_sized {b lo hi : Nat} (hk : ∀ s s', T.keeps b s s' → K6Keeps s s') :
    StaysBy T b (riderHead lo hi fun a => OnBytes.PscRun.Sized a.F) :=
  staysBy_head_of T fun s s' hK a ha => by
    obtain ⟨_, _, o, o', ho, ho', _, _, _, hL, _⟩ := hk s s' hK
    obtain rfl : a = o := by
      rw [ha] at ho
      exact VerifiableInference.Desc.First.Here.head.inj ho
    exact ⟨o', ho', fun hPa => hL.sized hPa⟩

/-- **The pile's length stays.** CONDITIONAL: hk; the count does not move. -/
theorem k6_staysBy_pile {b lo hi : Nat} {n : Nat → Nat}
    (hk : ∀ s s', T.keeps b s s' → K6Keeps s s') (hn : n (b + 1) = n b) :
    StaysBy T b (riderPile lo hi n) :=
  staysBy_pile T (fun s s' hK => by rw [(hk s s' hK).here]) hn

/-- **The counting rider stays.** CONDITIONAL: hk. -/
theorem k6_staysBy_room {b lo hi : Nat} {fvs : List Bool} {kCol : Nat}
    (hk : ∀ s s', T.keeps b s s' → K6Keeps s s') : StaysBy T b (riderRoom lo hi fvs kCol) :=
  staysBy_room T fun s s' hK =>
    ⟨by rw [(hk s s' hK).here], by rw [(hk s s' hK).here]⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_staysBy_head
#print axioms ProofFile.Honest.K6.k6_staysBy_three
#print axioms ProofFile.Honest.K6.k6_staysBy_sized
#print axioms ProofFile.Honest.K6.k6_staysBy_pile
#print axioms ProofFile.Honest.K6.k6_staysBy_room
