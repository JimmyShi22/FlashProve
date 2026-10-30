-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindKeeps.lean: WHAT «LINK m: BEHIND THE BATCHING»
KEEPS. The thread's letter keeps goes by the member's place (Honest/Thread/FirstHead.lean: Kp). Here
the clause for this sort of place, made of the library's own two relations, and its payer from the
runs' share.

WHAT THIS IS. A definition that fills a letter of the thread and that whoever rides past this member
spends; and a conditional lemma: calls of the library's. None of the library's goals.

  `rowsAlone`, `behindLeaves`, each with `_refl` and `_trans`; `keepsBehind`, `behind_keeps`,
  `keepsBehind_out`, `keepsBehind_reads`, `keepsBehind_head`, `keepsBehind_headP`,
  `keepsBehind_mark`, `keepsBehind_left`

Limits. `LinkShare` is shown here of no link. Which readers of the state read none of what is
blanked (`ReadsRest9`, Johnson/Desc/First/Link/Law/Rest9.lean) is for each reader's authors to show.
This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindPays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.LinkJoin (Rb rest9 here9 ReadsRest9 LinkShare rest_blocks)

/-- `G` is the ledger `F` except for the virtual rows of its arrays: every other field of the
ledger, and every other field of each array, is the same. -/
def rowsAlone (F G : OnBytes.Model.Fork) : Prop :=
  ∃ ts : Array OnBytes.Model.HTree, G = { F with trees := ts } ∧
    ts.map (fun X => { X with rows := #[] }) = F.trees.map fun X => { X with rows := #[] }

theorem rowsAlone_refl (F : OnBytes.Model.Fork) : rowsAlone F F := ⟨F.trees, rfl, rfl⟩

theorem rowsAlone_trans {F G H : OnBytes.Model.Fork} (h₁ : rowsAlone F G) (h₂ : rowsAlone G H) :
    rowsAlone F H := by
  obtain ⟨t₁, rfl, e₁⟩ := h₁
  obtain ⟨t₂, rfl, e₂⟩ := h₂
  exact ⟨t₂, rfl, e₂.trans e₁⟩

/-- What the step after a segment's batching leaves of the three parts of the open segment that
`rest9` blanks. The link's context is the same. The range proof's state is the same except for its
field `lsTail`, where there is one. The ledger is the same except for the virtual rows of its
arrays, where there is one. -/
def behindLeaves (s s' : S) : Prop :=
  s'.link? = s.link? ∧
    (∀ tl, s.tl? = some tl → ∃ ls, s'.tl? = some { tl with lsTail := ls }) ∧
    ∀ F, s.fork? = some F → ∃ G, s'.fork? = some G ∧ rowsAlone F G

theorem behindLeaves_refl (s : S) : behindLeaves s s :=
  ⟨rfl, fun tl h => ⟨tl.lsTail, h⟩, fun F h => ⟨F, h, rowsAlone_refl F⟩⟩

theorem behindLeaves_trans {s t u : S} (h₁ : behindLeaves s t) (h₂ : behindLeaves t u) :
    behindLeaves s u := by
  refine ⟨h₂.1.trans h₁.1, fun tl h => ?_, fun F h => ?_⟩
  · obtain ⟨l₁, e₁⟩ := h₁.2.1 tl h
    obtain ⟨l₂, e₂⟩ := h₂.2.1 _ e₁
    exact ⟨l₂, e₂⟩
  · obtain ⟨G, e₁, r₁⟩ := h₁.2.2 F h
    obtain ⟨H, e₂, r₂⟩ := h₂.2.2 G e₁
    exact ⟨H, e₂, rowsAlone_trans r₁ r₂⟩

/-- **What the sub-protocol "link m: behind the batching" keeps**: the clause of the thread's
parameter for what is kept, at that sub-protocol's place. Four conjuncts. The library's `Rb`: the
mark, the statement, the book, the roots, the sort of place at which the chain is and the open
link's number are the same. The library's `rest9` is the same at every blank: so all of the state is
the same except the count of rows that is still to come and, in the open segment's part, the link's
context, the ledger and the range proof's state. There is no mark after it. And `behindLeaves`: what
is the same of these three. -/
def keepsBehind (s s' : S) : Prop :=
  Rb s s' ∧ (∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) ∧ s'.failed = none ∧
    behindLeaves s s'

/-- **Its payer, from the runs' share.** hl: Honest/Law/NoHouse/BehindRows.lean pays it. -/
theorem behind_keeps (Lk : Link S Claim) (pp : Where) (hs : LinkShare Lk pp) (s s' : S)
    (h0 : s.failed = none) (h : Lk.runBehind s = .ok s') (hl : behindLeaves s s') :
    keepsBehind s s' := by
  have hst := behind_step Lk h 0
  have R : Rb s s' := (hs.two.2 _ _ _ _ _ _ hst).1
  exact ⟨R, fun L₀ F₀ t₀ => (rest_blocks L₀ F₀ t₀ Lk pp hs.hb₁ hs.stand).2 _ _ _ _ _ _ hst,
    R.failed.trans h0, hl⟩

/-- What goes on to the later chains is as it was, whole. -/
theorem keepsBehind_out {s s' : S} (h : keepsBehind s s') : s'.out = s.out := by
  have e := h.2.1 { check := s.check } {} {}
  have e' : (rest9 { check := s.check } {} {} s').out = (rest9 { check := s.check } {} {} s).out :=
    congrArg (fun z : S => z.out) e
  exact e'

/-- Whatever reads none of what is blanked is as it was. -/
theorem keepsBehind_reads {β : Type} {s s' : S} (h : keepsBehind s s') (L₀ : OnBytes.Model.LinkCtx)
    (F₀ : OnBytes.Model.Fork) (t₀ : OnBytes.Model.HTailF2) (f : S → β)
    (hf : ReadsRest9 L₀ F₀ t₀ f) : f s' = f s :=
  hf.alike L₀ F₀ t₀ (h.2.1 L₀ F₀ t₀)

/-- **In the head's link**: behind the member the chain stands there still, at the same part but for
the link's context, the ledger and the approximate range proof's state. -/
theorem keepsBehind_head {s s' : S} (h : keepsBehind s s') (a : HeadOwn)
    (ha : s.here = .head a) :
    ∃ L F tl, s'.here = .head { a with L := L, F := F, tl := tl } := by
  have e := h.2.1 a.L a.F a.tl
  have e' : (rest9 a.L a.F a.tl s').here = (rest9 a.L a.F a.tl s).here :=
    congrArg (fun z : S => z.here) e
  have e'' : here9 a.L a.F a.tl s'.here =
      here9 a.L a.F a.tl s.here := e'
  rw [ha] at e''
  cases hs : s'.here with
  | head a' =>
    rw [hs] at e''
    have e3 : ({ a' with L := a.L, F := a.F, tl := a.tl } : HeadOwn) =
        { a with L := a.L, F := a.F, tl := a.tl } :=
      Here.head.inj e''
    refine ⟨a'.L, a'.F, a'.tl, ?_⟩
    cases a
    cases a'
    simp only [HeadOwn.mk.injEq] at e3
    obtain ⟨g1, g2, g3, -, -, g4, g5, -, g6, g7, g8, g9, g10, g11, g12⟩ := e3
    subst g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12
    rfl
  | between => rw [hs] at e''; cases e''
  | lay _ => rw [hs] at e''; cases e''
  | att _ => rw [hs] at e''; cases e''
  | fin _ => rw [hs] at e''; cases e''
  | mem _ => rw [hs] at e''; cases e''

/-- **So a sentence on the head's own part that reads none of these three stays.** The form that
`staysBy_head_of` (Honest/Thread/RidersStayH.lean) takes. -/
theorem keepsBehind_headP {s s' : S} (h : keepsBehind s s')
    {P : HeadOwn → Prop}
    (hP : ∀ a L F tl, P a → P { a with L := L, F := F, tl := tl })
    (a : HeadOwn) (ha : s.here = .head a) :
    ∃ a', s'.here = .head a' ∧ (P a → P a') := by
  obtain ⟨L, F, tl, e⟩ := keepsBehind_head h a ha
  exact ⟨_, e, hP a L F tl⟩

/-- No mark after it. -/
theorem keepsBehind_mark {s s' : S} (h : keepsBehind s s') : s'.failed = none := h.2.2.1

/-- The fourth conjunct. -/
theorem keepsBehind_left {s s' : S} (h : keepsBehind s s') : behindLeaves s s' := h.2.2.2

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rowsAlone_refl
#print axioms ProofFile.Honest.FirstThread.rowsAlone_trans
#print axioms ProofFile.Honest.FirstThread.behindLeaves_refl
#print axioms ProofFile.Honest.FirstThread.behindLeaves_trans
#print axioms ProofFile.Honest.FirstThread.keepsBehind_mark
#print axioms ProofFile.Honest.FirstThread.keepsBehind_left
#print axioms ProofFile.Honest.FirstThread.behind_keeps
#print axioms ProofFile.Honest.FirstThread.keepsBehind_out
#print axioms ProofFile.Honest.FirstThread.keepsBehind_reads
#print axioms ProofFile.Honest.FirstThread.keepsBehind_head
#print axioms ProofFile.Honest.FirstThread.keepsBehind_headP
