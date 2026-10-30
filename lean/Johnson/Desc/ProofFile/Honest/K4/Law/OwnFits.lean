-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/OwnFits.lean: CONDITIONAL on `K4Seated` (Law/Seated.lean) and
on a run that stands in front of the member.

What is here. What the honest parts of the layers' own rounds (sub-protocol K4) find of K4's own
challenges where a run stands inside the member: which they are, how many, and that each holds as
many elements as the verifier's table of rounds says for its round. Five statements with their
proofs.

  `drawsFit_at`   challenge number j of a list that rounds can sample is one that round number j
      can sample
  `k4_heard_front`   in front of the member as many challenges have been heard as the public data
      count: the frame's `Thread.heard_length` (Honest/Thread/PaysLaw.lean) with `K4Seated.front`
  `k4_own_drop`   of the challenges in front with the member's first n, K4's own are these n
  `k4_own_fits`   **they have the table's shape** (`PtsLaw.OwnFits`,
      Johnson/Desc/K4/Honest/Law/PtsSizes.lean, of these writers), at every n
  `k4_own_length`   they are n, where the member has so many rounds

Not shown here. THAT `K4Seated` HOLDS: a hypothesis here. `k4Seated_of_laid` (Law/SeatedAt.lean) has
it at a thread as a letter, from a member that is laid alone and ties on the public data;
`k4Seated_head` and `k4Seated_letters` (Law/SeatedHead.lean) at the frame's thread under the
library's hypothesis; each CONDITIONAL on three of its fields that nothing there gives (the half
found, the number of rounds in front, the fit of the public data); the two at the frame's thread
also on that the member's public data are made of the public part (`k4PubOf … = some`); this file
gives no example. PUBLIC SIZES ALONE: nothing on a sampled value. No step of the verifier is in hand
or asked: the challenges are any list that the member's rounds can sample (`drawsFit`). Nothing on
soundness, on completeness or on any other property.

Kin. `drawsFit_at` IS THE WEAKER FORM OF `SumLaw.drawsFit_at` (Honest/SumLaw/BetaMarked.lean, of
other writers), which it calls: that law finds the challenge; here it is given.
Honest/K5/Law/BetaFit.lean, of other writers, has a third text of that law, under the same short
name; the library's `roundsFit_at` (Johnson/Top/H0/MergeLaw/Beta.lean) is kin in another form, on
the verifier's test on rounds as they were sent. Sought: by statement, to the letter and up to the
bound letters, and by short name, among the theorems of the library and of files that are no part of
it yet, as they lay with the writer. Not sought: by the names that the four other proofs call.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Seated
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.K4.Honest.Law.PtsSizes
import Johnson.Desc.ProofFile.Honest.SumLaw.BetaMarked

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par rounds entries entryOf blockAtC)
open OnBytes.Desc.First.K4.Honest (K4Pub PtsLaw.OwnFits)
open VerifiableInference.Desc (Block Claim First.S)

/-- Challenge number j of a list that rounds can sample is one that round number j can sample. -/
theorem drawsFit_at : ∀ (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit zs ds = true →
    ∀ (j : Nat) (z : Fmt.DeclaredRound) (d : Fmt.Drawn), zs[j]? = some z → ds[j]? = some d →
    drawFit z d = true := by
  intro zs ds h j z d hz hd
  obtain ⟨R, hR, hf⟩ := SumLaw.drawsFit_at zs ds h j z hz
  cases hR.symm.trans hd
  exact hf

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim}

/-- **In front of the member as many challenges have been heard as the public data count.** -/
theorem k4_heard_front (Se : K4Seated T b cells weights tokens look Q p blk) {k : Coins Bk}
    {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T b k s m E) :
    m.st.heard.length = Q.r0 := by
  rw [Se.front]
  exact T.heard_length hT.2.1

/-- **K4's own challenges, where a run stands behind the member's first n rounds.** -/
theorem k4_own_drop (Se : K4Seated T b cells weights tokens look Q p blk) {k : Coins Bk}
    {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T b k s m E)
    (ds : List Fmt.Drawn) (n : Nat) : (m.st.heard ++ ds.take n).drop Q.r0 = ds.take n := by
  rw [← k4_heard_front Se hT]
  exact List.drop_left

/-- **THEY HAVE THE SHAPE OF THE VERIFIER's TABLE OF ROUNDS.** -/
theorem k4_own_fits (Se : K4Seated T b cells weights tokens look Q p blk) {k : Coins Bk}
    {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T b k s m E)
    {ds : List Fmt.Drawn} (hd : drawsFit blk.rounds ds = true) (n : Nat) :
    PtsLaw.OwnFits Q (m.st.heard ++ ds.take n) := by
  intro j d x hj hx
  rw [k4_own_drop Se hT] at hj
  have hdj : ds[j]? = some d := by
    rw [List.getElem?_take] at hj
    split at hj
    · exact hj
    · cases hj
  obtain ⟨eP, eh, eg, _, _⟩ := Se.own
  have hr : blk.rounds[j]? = some { entry := entryOf x } := by
    rw [Se.rounds]
    show (((rounds p.P p.hp p.g).map entryOf).map fun e => ({ entry := e } : Fmt.DeclaredRound))[j]? = _
    rw [eP, eh, eg, List.getElem?_map, List.getElem?_map, hx]
    rfl
  have hf := drawsFit_at _ _ hd j _ d hr hdj
  simp only [drawFit, Bool.and_eq_true] at hf
  exact of_decide_eq_true (by simpa using hf.1.1.1.1.1.1.1)

/-- **They are n**, where the member has so many rounds. -/
theorem k4_own_length (Se : K4Seated T b cells weights tokens look Q p blk) {k : Coins Bk}
    {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T b k s m E)
    {ds : List Fmt.Drawn} (hd : drawsFit blk.rounds ds = true) {n : Nat}
    (hn : n ≤ blk.rounds.length) : ((m.st.heard ++ ds.take n).drop Q.r0).length = n := by
  rw [k4_own_drop Se hT, List.length_take, drawsFit_length _ _ hd]
  exact Nat.min_eq_left hn

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.drawsFit_at
#print axioms ProofFile.Honest.K4.k4_heard_front
#print axioms ProofFile.Honest.K4.k4_own_drop
#print axioms ProofFile.Honest.K4.k4_own_fits
#print axioms ProofFile.Honest.K4.k4_own_length
