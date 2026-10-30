-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/Speaks.lean: the closing of a segment (K10): sentences that tell a closing which
speaks of its tables from one that sends the words at empty tables (the filler returns: `stAtZero_at_head`,
Wipe/AtHead.lean; the statement is at hand at every move; the data are made), at the filler at made-up columns
(`stAtZero`, Honest/K10/StAtZero.lean), under the library's head. Lemmas; no definition.

Why. The row's part is total (`foldShellT true`, Honest/K10/Sim.lean): no move of it refuses. Where the filler refuses,
and where `closeAsk` (Honest/K10/Job.lean) refuses behind the filler's return, it sends what the fold's words say at
empty tables. `closeAsk` has five such refusals: the verifier's batching refuses; the layout's k, h are not the place's;
the batched row does not fit the mask table; the job's `rows` refuses; `rowsFit` says no (two more throws stand in its
text and cannot be reached: Job.lean says so). `closeAskAt` has two of its own in front: "BAT"'s challenge has not been
heard; one of the fold's own challenges so far has not drawn just one element.

  `cut_heard`, `atHand_of_cut`   in the job's own letters: where the rounds shown are a list a and n + 1 more, the
                    challenges heard a list h₀ and n + 1 more, and `stAt` returns at a, at the value o of
                    `Seen.opened` that is handed, and at h₀: `closeAtHand` says yes at the fold's move number n
  **`atHand_at_head`**   under the head, where the description's fold over the chain's members in front of a link's
                    closing returns at a and at some columns: `closeAtHand` says yes at every move n, at the job whose
                    statement is made by `stAtZero`, at a and n + 1 rounds more
  **`ask_made_at_head`**   under the head and that premise on the fold, with the facts on the record in front
                    (`CloseBase`, Johnson/Desc/K10/Honest/Base.lean) at the record of the state that the fold reaches,
                    the job's h that of these facts, the job's `rows` returning R and `rowsFit` saying yes of R, at a
                    challenge of "BAT"'s form (one element t, no position, no matrix entry, no digest: ⟨[t], [], [],
                    none⟩): `closeAsk` at that job returns data: none of the five refusals is met
  `askZero_at_head`   the same of `askZero` (Honest/K10/SimSent.lean), of which `plays_is` writes out what the part
                   sends
  **`askOr_made_at_head`**   so at the fold's move number n, at a stand that is written out (heard: a list h₀, "BAT"'s
                    challenge of that form, the fold's own n, each of one element; shown: a list r₀ and n + 1 rounds
                    more): what the total part reads (`askOr true`, Honest/K10/Sim.lean) is data, not nothing: none of
                    the seven refusals (`closeAsk`'s five, `closeAskAt`'s two) is met: by `askOr_is` (SimSent.lean)

Limits. The premises of `ask_made_at_head` stand by name and are shown of no run: H, hh (on the record in front), hr,
hfit (on the prover's rows). That the lists of rounds and challenges have the two forms at a stand inside the closing is
the frame's matter: premises here. start, xi and J are letters, and J's own place is not tied to Q. `plays_is` asks of
"BAT"'s challenge one element alone; these lemmas want the whole form: that is the caller's to show. At a challenge of
another form nothing is said (the batching refuses there, but for the digest, which it does not look at: Job.lean).
Nothing on what the data are: Honest/K10/AskLaw.lean has that. No property of the protocol is claimed: nothing is said
on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.AtHead
import Johnson.Desc.ProofFile.Honest.K10.AskLaw
import Johnson.Desc.ProofFile.Honest.K10.SimSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K10.YesFree (CloseBase BaseData)

/-- The cut takes the last n + 1 challenges off. -/
theorem cut_heard {W X : Type} (n : Nat) (s : Seen) (t : State W X) (h₀ h₁ : List Fmt.Drawn) (ht : t.heard = h₀ ++ h₁)
    (hl : h₁.length = n + 1) : (closeCut n s t).2 = h₀ := by
  show t.heard.take (t.heard.length - (n + 1)) = h₀
  rw [ht, List.length_append, hl, Nat.add_sub_cancel, List.take_left']
  rfl

/-- **The statement is at hand at the fold's move number n**, where it is at hand at what stands in front of "BAT". -/
theorem atHand_of_cut {W X : Type} (J : CloseJob W) (n : Nat) (a b : List Fmt.RoundView)
    (o : Option (List OpenedColumn)) (t : State W X)
    (h₀ h₁ : List Fmt.Drawn) (hb : b.length = n + 1) (ht : t.heard = h₀ ++ h₁) (hl : h₁.length = n + 1)
    {z : OnBytes.Statement × Nat} (hst : J.stAt t.input ⟨a, o⟩ h₀ = .ok z) : closeAtHand J n ⟨a ++ b, o⟩ t = true := by
  unfold closeAtHand
  rw [cut_own n a b o t hb, cut_heard n ⟨a ++ b, o⟩ t h₀ h₁ ht hl, hst]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl}

/-- **Under the head the statement is at hand at every move.** -/
theorem atHand_at_head {W X Xi : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b)
    (J : CloseJob W) (start : Xi → S) (xi : W → Xi) (n : Nat) (a a' : List Fmt.RoundView)
    (o : Option (List OpenedColumn)) (t : State W X)
    (h₀ h₁ : List Fmt.Drawn) (ha : a'.length = n + 1) (ht : t.heard = h₀ ++ h₁) (hh : h₁.length = n + 1)
    {cols : List OpenedColumn} {y : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start (xi t.input)) a cols = .ok y) :
    closeAtHand { J with stAt := fun w' s f => stAtZero cF.blocksInOrder start (xi w') Q s f } n ⟨a ++ a', o⟩ t = true :=
  atHand_of_cut _ n a a' o t h₀ h₁ ha ht hh
    (stAtZero_at_head h hl T start (xi t.input) ⟨a, o⟩ h₀ hf)

/-- **Under the head, under four named premises, and at a challenge of "BAT"'s form, the data are made.** -/
theorem ask_made_at_head {W Xi : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b)
    (J : CloseJob W) (start : Xi → S) (xi : W → Xi) (w : W) (seen : Seen) (front : List Fmt.Drawn) (t : Fmt.Ext)
    (u : Fin (2 * J.pub.par.k + 1) → OnBytes.E) (ca : CsAll (closeCarries J.pub)) {cols : List OpenedColumn}
    {y : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start (xi w)) seen.rounds cols =
      .ok y)
    {B : BaseData} (H : CloseBase J.pub.par (VerifiableInference.Desc.K9.recOf y.1) B) (hh : J.pub.par.h = B.Gq.h)
    (R : GroupData) (hr : J.rows w front ca = .ok R) (hfit : rowsFit y.1.st B.G R = true) :
    ∃ A, closeAsk { J with stAt := fun w' s f => stAtZero cF.blocksInOrder start (xi w') Q s f } w seen front
      ⟨[t], [], [], none⟩ u ca = .ok (some A) := by
  rw [closeAsk_at_head h hl T J start xi w seen front ⟨[t], [], [], none⟩ u ca hf]
  obtain ⟨row, -, e⟩ := ask_of_base { J with stAt := fun _ _ _ => .ok (y.1.st, y.1.live.frame.group) } H hh w seen
    front t rfl u ca R hr hfit
  exact ⟨_, e⟩

/-- The same of `askZero`, at a challenge of that form. -/
theorem askZero_at_head {W Xi : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b)
    (J : CloseJob W) (start : Xi → S) (xi : W → Xi) (w : W) (sn : Seen) (front : List Fmt.Drawn) (t : Fmt.Ext)
    (ca : CsAll (closeCarries J.pub)) {cols : List OpenedColumn} {y : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start (xi w)) sn.rounds cols = .ok y)
    {B : BaseData} (H : CloseBase J.pub.par (VerifiableInference.Desc.K9.recOf y.1) B) (hh : J.pub.par.h = B.Gq.h)
    (R : GroupData) (hr : J.rows w front ca = .ok R) (hfit : rowsFit y.1.st B.G R = true) :
    ∃ A, askZero { J with stAt := fun w' s f => stAtZero cF.blocksInOrder start (xi w') Q s f } w sn front
      ⟨[t], [], [], none⟩ ca = some A := by
  obtain ⟨A, e⟩ := ask_made_at_head h hl T J start xi w sn front t (fun _ => OnBytes.zeroE) ca hf H hh R hr hfit
  refine ⟨A, ?_⟩
  unfold askZero
  rw [e]
  rfl

/-- **At every move the total part reads data**, under the same premises, at a stand that is written out. -/
theorem askOr_made_at_head {W X Xi : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b)
    (J : CloseJob W) (start : Xi → S) (xi : W → Xi) (n : Nat)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (s : Seen) (t : State W X)
    (h₀ : List Fmt.Drawn) (e : Fmt.Ext) (gs : List Fmt.Drawn) (r₀ rs : List Fmt.RoundView)
    (ht : t.heard = h₀ ++ ⟨[e], [], [], none⟩ :: gs) (hn : gs.length = n) (hs : s.rounds = r₀ ++ rs)
    (hr : rs.length = n + 1) (hg : ∀ g ∈ gs, g.elems.length = 1) {cols : List OpenedColumn}
    {y : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start (xi t.input)) r₀ cols = .ok y)
    {B : BaseData} (H : CloseBase J.pub.par (VerifiableInference.Desc.K9.recOf y.1) B) (hh : J.pub.par.h = B.Gq.h)
    (R : GroupData) (hR : J.rows t.input h₀ c.2.2 = .ok R) (hfit : rowsFit y.1.st B.G R = true) :
    ∃ A, askOr true { J with stAt := fun w' s' f => stAtZero cF.blocksInOrder start (xi w') Q s' f } n c s t =
      .ok (some (A, drawnE gs)) := by
  obtain ⟨A, eA⟩ := askZero_at_head h hl T J start xi t.input ⟨r₀, s.opened⟩ h₀ e c.2.2 hf H hh R hR hfit
  rw [askOr_is { J with stAt := fun w' s' f => stAtZero cF.blocksInOrder start (xi w') Q s' f } n c s t h₀
    ⟨[e], [], [], none⟩ gs r₀ rs ht hn hs hr hg, eA]
  exact ⟨_, rfl⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.cut_heard
#print axioms ProofFile.Honest.K10.atHand_of_cut
#print axioms ProofFile.Honest.K10.atHand_at_head
#print axioms ProofFile.Honest.K10.ask_made_at_head
#print axioms ProofFile.Honest.K10.askZero_at_head
#print axioms ProofFile.Honest.K10.askOr_made_at_head
