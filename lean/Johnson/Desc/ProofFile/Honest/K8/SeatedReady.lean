-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/SeatedReady.lean: THE SMALLNESS TEST AT ITS OWN MEMBER: IT IS
ACCEPTED, ASKED FROM THE PAIR OF THE THREAD AND WHAT IS SAID (`ThrS`, `AcceptedS`:
Johnson/Desc/ProofFile/Honest/Thread/Said.lean, PaysS.lean); AND "THE STATE IN FRONT IS READY" PAID
OFF THE THREAD's CLAUSE ON HOW THE STATE WAS MADE, at a member right behind a block that closes the
list of tables. Statements, each a definition of a proposition or a record of named premises, and
their proofs. General in the thread; none of the library's goals.

  `K8ReadyS T Said b p`   THE PREMISE "READY", WITH THE THREAD IN FRONT: from the pair at b:
                   `ReadyAt p s` (Honest/K8/Seated.lean). Weaker than `K8Ready`, which asks it of
                   the two letters form and formP alone: `readyS_of_ready`
  `stepped_of_ready`   at the seat, where the state is ready, the prover's side of the step is
                   followed by the block's yes
  **`small_acceptedS`**   K8Seated → K8ReadyS → AcceptedS T Said fall b, at every fall
  `K8Front T j p tl0 c start zOf`   NAMED PREMISES AT THE MEMBER NUMBER j, RIGHT IN FRONT. `prev`: c
                   is that member · `closes`: where its decision says yes the test's data behind are
                   tl0, closed, with some list of tables (`Ready.ClosesFrom`,
                   Johnson/Desc/First/K8/LawReadyText.lean) · `begun`: the chain's first state is a
                   function of a public part · `waits`: NO COUNT WAITS, BY EITHER OF TWO ROADS: the
                   letter formP behind c gives it of the state there; or it holds at every state
                   that is reached in front of c (and c keeps it) · `undrawn`, `fold0`, `nm`, `ks`,
                   `ms`, `tau`: six facts on tl0 against the place's numbers · `tabs`: AT EVERY
                   STATE THAT IS REACHED BEHIND c THE CLOSED LIST HAS THE PLACE's SHAPES · `mark`:
                   where the letter form holds behind c no mark stands
  **`ready_of_front`**   K8Front → from the thread at j + 1: `ReadyAt p s`: by the thread's clause
                   on how the state was made (`reach_of_made`, Honest/Thread/MadeLaw.lean), one step
                   back along the library's "reached", and the library's `means_of_values`
  `small_acceptedS_front`   so: K8Seated at j + 1 → K8Front → AcceptedS, whatever is said
  `tabs_of_yes`   FOR WHOEVER PAYS THE FIELD tabs, of either record: it is enough that every yes of
                   the member in front lays a list of the place's shapes (at the output head:
                   `head_tabs_under`, Johnson/Desc/K8/Honest/HeadShapes.lean)
  `K8FrontAtt`, **`ready_of_front_att`**, `small_acceptedS_front_att`   THE LIKE WHERE THE MEMBER IN
                   FRONT CLOSES THE STATE's OWN DATA (`Ready.Closes`,
                   Johnson/Desc/First/K8/LawReadyAtt.lean): one premise more: `kept`: at every state
                   that is reached in front of c five fields of the test's data are tl0's; by the
                   library's `means_of_values`
  `K8Reached T b p tl0 start zOf`, **`ready_of_reached`**, `small_acceptedS_reached`   THE COMMON
                   RECORD: ALL SENTENCES AT THE BORDER b ITSELF: at every state that is reached at
                   b: five fields of the test's data are tl0's (`keep`), the list is closed
                   (`closed`), it has the place's shapes (`tabs`); `waits`, by either of two roads,
                   both at b; the six facts; `begun`; `mark`: no member in front is named and no
                   step back is gone
  `K8Front.reached`, `K8FrontAtt.reached`   each of the two records above yields it
WHICH RECORD AT WHICH SEGMENT, by the library's own files: `Ready.ClosesFrom` is the form of the
closing step at a layers' segment and at the output head; `Ready.Closes` at an attention segment.
Limits. `kept`, `tabs` and the second road of `waits` are sentences on reached states, with content;
who pays each is not said here. Whether a chain's formP gives the first road of `waits` is not held
here. The six facts are on public numbers; none is shown at a value. That a description's member in
front has either form is not shown here. A member of `K8Front`, by the second road of `waits`:
Honest/K8/SeatedReadyToy.lean; of `K8FrontAtt` none.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SeatedLaws
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.First.K8.LawReadyAtt
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par MeansAtS firstColumns step_seats_iff tabs)
open VerifiableInference.Desc.First.K8.Ready (ClosesFrom Closes keep closedAt means_of_values)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)

variable {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}

/-- **"Ready", with the thread in front: from the pair.** -/
def K8ReadyS (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat) (p : Par) : Prop :=
  ∀ k s m E, ThrS T Said b k s m E → ReadyAt p s

/-- The premise from the two letters alone gives the premise from the pair. -/
theorem readyS_of_ready {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop} {b : Nat} {p : Par}
    (h : K8Ready T b p) : K8ReadyS T Said b p :=
  fun _ s _ _ hA => h _ s hA.1.2.2.1.1 hA.1.2.2.1.2

/-- At the seat, where the state is ready, the block says yes behind the prover's side. -/
theorem stepped_of_ready {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    (h : K8Seated T b blk cells P) {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hR : ReadyAt P.1 s)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols) :
    ∃ s', T.Stepped blk k s m E ds y cols s' := by
  obtain ⟨d, rfl, hdf, rfl, rfl, -⟩ := seated_moved h hd hM
  obtain ⟨hfail, tl, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hR
  refine ⟨s.putTl { tl with cfF := d.trits.toArray, cfFirst := firstColumns P.1 }, hM, ?_⟩
  exact (step_seats_iff P.1 blk h.seats T.ft s _ _ _ _).2
    ⟨⟨[], d⟩, rfl, fit_of_draw P.1 d hdf, ⟨tl, c1, c2, c3, c4, c5, c6, c7, c8, c9, rfl⟩, rfl, hfail⟩

/-- **It is accepted, asked from the pair.** -/
theorem small_acceptedS {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop} {b : Nat} {blk : Block S Claim}
    {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    (fall : Nat → S → List Fmt.Drawn → Option String) (h : K8Seated T b blk cells P)
    (hR : K8ReadyS T Said b P.1) : AcceptedS T Said fall b := by
  intro blk' hblk' k s m E ds y cols hA hd _ _ hM
  rw [h.here] at hblk'
  cases hblk'
  exact stepped_of_ready h (hR k s m E hA) hd hM

/-- **Named premises at the member right in front.** -/
structure K8Front (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (j : Nat)
    (p : Par) (tl0 : HTailF2) (c : Block S Claim) {Q : Type} (start : Q → S)
    (zOf : Local W₀ Rc Xi Tr → Q) : Prop where
  prev : T.bs[j]? = some c
  closes : ClosesFrom tl0 c
  begun : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = start (zOf w)
  waits : (∀ a s, T.formP (j + 1) (a, s) → s.noneWaits = true) ∨
    ∀ z s, Reach T.ft T.bs start j (z, s) → s.noneWaits = true
  undrawn : tl0.cfF.size = 0
  fold0 : tl0.foldDrawn = 0
  nm : tl0.NM = p.ks.length
  ks : tl0.mats.toList.map (·.k) = p.ks
  ms : tl0.mats.toList.map (·.m) = p.ms
  tau : tl0.tau = p.tau
  tabs : ∀ z s tl, Reach T.ft T.bs start (j + 1) (z, s) → s.tl? = some tl →
    tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p
  mark : ∀ a s, T.form (j + 1) (a, s) = true → s.failed = none

/-- What is reached at k + 1 comes of what is reached at k by a yes of the member number k. -/
theorem reach_back {σ Cl Q : Type} {ft : Nat} {bs : List (Block σ Cl)} {start : Q → σ} {k : Nat}
    {z : Q} {s' : σ} (h : Reach ft bs start (k + 1) (z, s')) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ hr hb hy => exact ⟨_, _, hr, hb, hy⟩

/-- **For whoever pays the field tabs**: it is enough that every yes of the member in front lays a
list of the place's shapes. -/
theorem tabs_of_yes {Cl Q : Type} {ft : Nat} {bs : List (Block S Cl)} {start : Q → S} {j : Nat}
    {p : Par} {c : Block S Cl} (hprev : bs[j]? = some c)
    (hy : ∀ s rs gs s', c.decide s rs gs = .ok s' → ∀ tl, s'.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p) :
    ∀ z s tl, Reach ft bs start (j + 1) (z, s) → s.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p := by
  intro z s tl hr ht
  obtain ⟨sj, c', -, hc', hs⟩ := reach_back hr
  rw [hprev] at hc'
  cases hc'
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hs
  exact hy sj rs gs s hd tl ht

/-- **"Ready", paid off how the state was made.** -/
theorem ready_of_front {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {j : Nat} {p : Par} {tl0 : HTailF2} {c : Block S Claim} {Q : Type} {start : Q → S}
    {zOf : Local W₀ Rc Xi Tr → Q} (h : K8Front T j p tl0 c start zOf) {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T (j + 1) k s m E) : ReadyAt p s := by
  have hlen : j + 1 ≤ T.bs.length := (List.getElem?_eq_some_iff.1 h.prev).1
  have hr : Reach T.ft T.bs start (j + 1) (zOf m.st.input, s) :=
    reach_of_made T start (zOf m.st.input) hlen (fun s₀ hb => h.begun _ _ _ _ hb) hT.2.2.2.2.1
  obtain ⟨sj, c', hrj, hc', hy⟩ := reach_back hr
  rw [h.prev] at hc'
  cases hc'
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hw : s.noneWaits = true :=
    h.waits.elim (fun f => f _ s hT.2.2.1.2) fun g => (h.closes sj rs gs s hd).2 (g _ _ hrj)
  obtain ⟨s'', tl, c1, c2, c3, c4, c5, c6, c7, c8, c9, -⟩ :=
    means_of_values p s tl0 (h.closes.lays.1 sj rs gs s hd) (h.closes.lays.2 sj rs gs s hd) hw
      h.undrawn h.fold0 h.nm h.ks h.ms h.tau (fun tl ht => h.tabs _ _ tl hr ht)
      ⟨[], ⟨[], [], [], none⟩⟩
  exact ⟨h.mark _ s hT.2.2.1.1, tl, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩

/-- **Named premises at the member right in front, where that member closes the state's own
data.** -/
structure K8FrontAtt (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (j : Nat)
    (p : Par) (tl0 : HTailF2) (c : Block S Claim) {Q : Type} (start : Q → S)
    (zOf : Local W₀ Rc Xi Tr → Q) : Prop where
  prev : T.bs[j]? = some c
  closes : Closes c
  begun : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = start (zOf w)
  waits : (∀ a s, T.formP (j + 1) (a, s) → s.noneWaits = true) ∨
    ∀ z s, Reach T.ft T.bs start j (z, s) → s.noneWaits = true
  kept : ∀ z s, Reach T.ft T.bs start j (z, s) →
    keep s = some (tl0.NM, tl0.mats, tl0.tau, tl0.cfF, tl0.foldDrawn)
  undrawn : tl0.cfF.size = 0
  fold0 : tl0.foldDrawn = 0
  nm : tl0.NM = p.ks.length
  ks : tl0.mats.toList.map (·.k) = p.ks
  ms : tl0.mats.toList.map (·.m) = p.ms
  tau : tl0.tau = p.tau
  tabs : ∀ z s tl, Reach T.ft T.bs start (j + 1) (z, s) → s.tl? = some tl →
    tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p
  mark : ∀ a s, T.form (j + 1) (a, s) = true → s.failed = none

/-- **"Ready", paid off how the state was made, there.** -/
theorem ready_of_front_att {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {j : Nat} {p : Par} {tl0 : HTailF2} {c : Block S Claim} {Q : Type} {start : Q → S}
    {zOf : Local W₀ Rc Xi Tr → Q} (h : K8FrontAtt T j p tl0 c start zOf) {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T (j + 1) k s m E) : ReadyAt p s := by
  have hlen : j + 1 ≤ T.bs.length := (List.getElem?_eq_some_iff.1 h.prev).1
  have hr : Reach T.ft T.bs start (j + 1) (zOf m.st.input, s) :=
    reach_of_made T start (zOf m.st.input) hlen (fun s₀ hb => h.begun _ _ _ _ hb) hT.2.2.2.2.1
  obtain ⟨sj, c', hrj, hc', hy⟩ := reach_back hr
  rw [h.prev] at hc'
  cases hc'
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hw : s.noneWaits = true :=
    h.waits.elim (fun f => f _ s hT.2.2.1.2) fun g => h.closes.2.2 sj rs gs s hd (g _ _ hrj)
  obtain ⟨s'', tl, c1, c2, c3, c4, c5, c6, c7, c8, c9, -⟩ :=
    means_of_values p s tl0 ((h.closes.1 sj rs gs s hd).trans (h.kept _ _ hrj))
      (h.closes.2.1 sj rs gs s hd) hw h.undrawn h.fold0 h.nm h.ks h.ms h.tau
      (fun tl ht => h.tabs _ _ tl hr ht) ⟨[], ⟨[], [], [], none⟩⟩
  exact ⟨h.mark _ s hT.2.2.1.1, tl, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩

/-- **Named premises at the border b itself**: what the two records above yield, and all that
"ready" wants. -/
structure K8Reached (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (p : Par) (tl0 : HTailF2) {Q : Type} (start : Q → S) (zOf : Local W₀ Rc Xi Tr → Q) : Prop where
  len : b ≤ T.bs.length
  begun : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = start (zOf w)
  keep : ∀ z s, Reach T.ft T.bs start b (z, s) →
    keep s = some (tl0.NM, tl0.mats, tl0.tau, tl0.cfF, tl0.foldDrawn)
  closed : ∀ z s, Reach T.ft T.bs start b (z, s) → closedAt s = some true
  waits : (∀ a s, T.formP b (a, s) → s.noneWaits = true) ∨
    ∀ z s, Reach T.ft T.bs start b (z, s) → s.noneWaits = true
  undrawn : tl0.cfF.size = 0
  fold0 : tl0.foldDrawn = 0
  nm : tl0.NM = p.ks.length
  ks : tl0.mats.toList.map (·.k) = p.ks
  ms : tl0.mats.toList.map (·.m) = p.ms
  tau : tl0.tau = p.tau
  tabs : ∀ z s tl, Reach T.ft T.bs start b (z, s) → s.tl? = some tl →
    tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p
  mark : ∀ a s, T.form b (a, s) = true → s.failed = none

/-- **"Ready", from sentences at the border itself.** -/
theorem ready_of_reached {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {p : Par} {tl0 : HTailF2} {Q : Type} {start : Q → S} {zOf : Local W₀ Rc Xi Tr → Q}
    (h : K8Reached T b p tl0 start zOf) {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X}
    {E : Env} (hT : Thr T b k s m E) : ReadyAt p s := by
  have hr : Reach T.ft T.bs start b (zOf m.st.input, s) :=
    reach_of_made T start (zOf m.st.input) h.len (fun s₀ hb => h.begun _ _ _ _ hb) hT.2.2.2.2.1
  have hw : s.noneWaits = true := h.waits.elim (fun f => f _ s hT.2.2.1.2) fun g => g _ _ hr
  obtain ⟨s'', tl, c1, c2, c3, c4, c5, c6, c7, c8, c9, -⟩ :=
    means_of_values p s tl0 (h.keep _ _ hr) (h.closed _ _ hr) hw h.undrawn h.fold0 h.nm h.ks h.ms
      h.tau (fun tl ht => h.tabs _ _ tl hr ht) ⟨[], ⟨[], [], [], none⟩⟩
  exact ⟨h.mark _ s hT.2.2.1.1, tl, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩

/-- The first record yields it. -/
theorem K8Front.reached {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {j : Nat} {p : Par} {tl0 : HTailF2} {c : Block S Claim} {Q : Type} {start : Q → S}
    {zOf : Local W₀ Rc Xi Tr → Q} (h : K8Front T j p tl0 c start zOf) :
    K8Reached T (j + 1) p tl0 start zOf where
  len := (List.getElem?_eq_some_iff.1 h.prev).1
  begun := h.begun
  keep := by
    intro z s hr
    obtain ⟨sj, c', -, hc', hy⟩ := reach_back hr
    rw [h.prev] at hc'
    cases hc'
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact h.closes.lays.1 sj rs gs s hd
  closed := by
    intro z s hr
    obtain ⟨sj, c', -, hc', hy⟩ := reach_back hr
    rw [h.prev] at hc'
    cases hc'
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact h.closes.lays.2 sj rs gs s hd
  waits := h.waits.imp id fun g z s hr => by
    obtain ⟨sj, c', hrj, hc', hy⟩ := reach_back hr
    rw [h.prev] at hc'
    cases hc'
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact (h.closes sj rs gs s hd).2 (g _ _ hrj)
  undrawn := h.undrawn
  fold0 := h.fold0
  nm := h.nm
  ks := h.ks
  ms := h.ms
  tau := h.tau
  tabs := h.tabs
  mark := h.mark

/-- So does the second. -/
theorem K8FrontAtt.reached {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {j : Nat} {p : Par} {tl0 : HTailF2} {c : Block S Claim} {Q : Type} {start : Q → S}
    {zOf : Local W₀ Rc Xi Tr → Q} (h : K8FrontAtt T j p tl0 c start zOf) :
    K8Reached T (j + 1) p tl0 start zOf where
  len := (List.getElem?_eq_some_iff.1 h.prev).1
  begun := h.begun
  keep := by
    intro z s hr
    obtain ⟨sj, c', hrj, hc', hy⟩ := reach_back hr
    rw [h.prev] at hc'
    cases hc'
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact (h.closes.1 sj rs gs s hd).trans (h.kept _ _ hrj)
  closed := by
    intro z s hr
    obtain ⟨sj, c', -, hc', hy⟩ := reach_back hr
    rw [h.prev] at hc'
    cases hc'
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact h.closes.2.1 sj rs gs s hd
  waits := h.waits.imp id fun g z s hr => by
    obtain ⟨sj, c', hrj, hc', hy⟩ := reach_back hr
    rw [h.prev] at hc'
    cases hc'
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact h.closes.2.2 sj rs gs s hd (g _ _ hrj)
  undrawn := h.undrawn
  fold0 := h.fold0
  nm := h.nm
  ks := h.ks
  ms := h.ms
  tau := h.tau
  tabs := h.tabs
  mark := h.mark

/-- It is accepted, under the record at the border itself, whatever is said. -/
theorem small_acceptedS_reached
    {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop} {b : Nat} {blk : Block S Claim}
    {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)} {tl0 : HTailF2} {Q : Type}
    {start : Q → S} {zOf : Local W₀ Rc Xi Tr → Q}
    (fall : Nat → S → List Fmt.Drawn → Option String) (h : K8Seated T b blk cells P)
    (hF : K8Reached T b P.1 tl0 start zOf) : AcceptedS T Said fall b :=
  small_acceptedS fall h fun _ _ _ _ hA => ready_of_reached hF hA.1

/-- So: it is accepted, whatever is said. -/
theorem small_acceptedS_front {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop} {j : Nat} {blk c : Block S Claim}
    {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)} {tl0 : HTailF2} {Q : Type}
    {start : Q → S} {zOf : Local W₀ Rc Xi Tr → Q}
    (fall : Nat → S → List Fmt.Drawn → Option String) (h : K8Seated T (j + 1) blk cells P)
    (hF : K8Front T j P.1 tl0 c start zOf) : AcceptedS T Said fall (j + 1) :=
  small_acceptedS fall h fun _ _ _ _ hA => ready_of_front hF hA.1

/-- The like where the member in front closes the state's own data. -/
theorem small_acceptedS_front_att
    {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop} {j : Nat} {blk c : Block S Claim}
    {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)} {tl0 : HTailF2} {Q : Type}
    {start : Q → S} {zOf : Local W₀ Rc Xi Tr → Q}
    (fall : Nat → S → List Fmt.Drawn → Option String) (h : K8Seated T (j + 1) blk cells P)
    (hF : K8FrontAtt T j P.1 tl0 c start zOf) : AcceptedS T Said fall (j + 1) :=
  small_acceptedS fall h fun _ _ _ _ hA => ready_of_front_att hF hA.1

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.readyS_of_ready
#print axioms ProofFile.Honest.K8.ready_of_front_att
#print axioms ProofFile.Honest.K8.small_acceptedS_front_att
#print axioms ProofFile.Honest.K8.stepped_of_ready
#print axioms ProofFile.Honest.K8.small_acceptedS
#print axioms ProofFile.Honest.K8.ready_of_reached
#print axioms ProofFile.Honest.K8.K8Front.reached
#print axioms ProofFile.Honest.K8.K8FrontAtt.reached
#print axioms ProofFile.Honest.K8.small_acceptedS_reached
#print axioms ProofFile.Honest.K8.reach_back
#print axioms ProofFile.Honest.K8.tabs_of_yes
#print axioms ProofFile.Honest.K8.ready_of_front
#print axioms ProofFile.Honest.K8.small_acceptedS_front
