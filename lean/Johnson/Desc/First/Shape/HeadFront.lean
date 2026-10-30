-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HeadFront.lean: THE TWO HALVES OF THE PLACE THAT HEARS THE REPLY ("H:1":
the head's link's first place), EACH AS ONE STEP ON THE SHAPE OF THE STATE THAT THE FIRST CHAIN
CARRIES (Chain.lean): the head's front (First.K2.headFrontQ, Johnson/Top/H0/Tw/K2C/Head.lean: no
round) and the kind "the next token" at that state (Kinds.Reply.blockAt,
Johnson/Stored/ReplySeatAt.lean: one round). General laws; nothing is evaluated.
  `freshHead`, `headFrontB`, **`headFrontG t`**: the front's guards and its step: no mark; the chain
    stands between the links; a link's first call is due; the frame's four tests (a first message is
    due; the link is not link 0; the shape has the link; the groups' list has the link's); one new
    group (Ground.Sh.newGroupS). It lays: the chain stands in the head's link, not yet opened; the
    core with the new group; the head's own fields as the entry lays them, with the frame at the new
    group, moment 1 and no own message, nothing heard and no table laid; and, shut until the link is
    opened (HeadSh.shut : ShutSh, HeadPart.lean): t, an empty ledger, a fresh context of the link
    with the walk's state of the calls, and nothing yet of the lookup's two records and of the
    tables.
  `newGroupG_sh`: the front's routine for a new group, which reads a statement alone, against the
    routine on the core's shape.
  **`headFront_sh`**: the front's decision, seen through the shape, IS the step at t := tailSh tl,
    the shape of the plan's record of the smallness test, which the front lays: it returns just
    where the step returns, and then the shape behind is what the step returns. One equation, at
    every state; no premise; no test on values.
  `ex_bind`, `headFront_keeps`: the front leaves what goes out and returns no marked state.
    `headFront_forms`: the makes of the statement's rows behind it (Forms.lean): one new group
    without a row.
  `reply_iff`: what a yes of the kind's block is, clause by clause. **`replyG`**: its step: the
    head's link is entered and not opened; no reply was heard; then one is. **`reply_carries`**
    (strong: behind a yes the step returns the shape behind), **`reply_returns`**: where the step
    returns, the block says yes on one round that holds just one element, draws nothing, and whose
    element is a token of the vocabulary.
Limits. The bare texts: the guards of a seat are not in them. The two premises of reply_returns are
on the round: one of them is a test on a value (the element is a token). No state is shown at which
a step returns. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.First.Shape.Forms
import Johnson.Desc.Ground.Shape.Ground
import Johnson.Top.H0.Tw.K2C.Head
import Johnson.Stored.ReplySeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh)

/-- The head's link's own fields as the entry lays them, with the frame f; t: the shape of the
plan's record of the smallness test; c: the shape of the walk's state of the calls. What lies shut
until the link is opened: t, an empty ledger, and a fresh context of the link with c. -/
def freshHead (f : FrameSh) (t : TailSh) (c : CheckSh) : HeadSh :=
  { fr := f, kept := #[], ids := #[], x := none, tab := none, claim := none, wo := none
    Fm := ledSh {}, slot := none, squaresP := none
    shut := some
      { tl := t, led := ledSh {}
        link := { check := c, link := 0, arrayOf := #[], list := {}, moments := 1, handed := false
                  done := false }
        look := none, lookHeard := none, tables := none } }

/-- The guards of the head's front, on the shape. -/
def headFrontB (a : ChainSh) : Bool :=
  !a.marked && a.here == 0 && !a.check.inLink &&
    decide (a.check.frame.link < a.check.frame.shape.link.length) &&
    a.check.frame.next == .first && !(a.check.frame.link == 0) &&
    (a.check.frame.shape.link[a.check.frame.link]?).isSome &&
    (a.check.frame.groups[a.check.frame.link]?).isSome

/-- **The head's front ("H.0.front") on the chain's shape.** -/
def headFrontG (t : TailSh) (a : ChainSh) : Option ChainSh :=
  if headFrontB a then
    (Ground.Sh.newGroupS a.core a.check.frame.shape.code a.check.frame.shape.maskCode).map fun x =>
      ChainSh.mk false 4 none none none a.rowsOwed x.2 a.reply a.indexMasks a.pile none a.check
        none none none none
        (some (freshHead { a.check.frame with group := x.1, moment := 1, own := #[] } t a.check))
        none none
  else none

/-- A new group at a statement alone, against the routine on the core's shape. -/
theorem newGroupG_sh (st : Statement) (book : TreeBook) (roots c z : Nat) :
    ((_root_.Tw.K2.newGroupG st c z).toOption.map fun x =>
        (x.2, coreSh ⟨x.1, book, roots⟩)) =
      Ground.Sh.newGroupS (coreSh ⟨st, book, roots⟩) c z := by
  unfold _root_.Tw.K2.newGroupG
  by_cases hok : Ground.ok (Ground.newGroupL st c z) = true
  · have h1 : Ground.newGroupP (_root_.Tw.K2.dOf st) c z =
        some (st.groups.size, { _root_.Tw.K2.dOf st with st := Ground.withGroup st c z }) := by
      unfold Ground.newGroupP
      exact if_pos hok
    have h2 : Ground.newGroupP (⟨st, book, roots, [], ()⟩ : _root_.Desc.Plain.DState Unit) c z =
        some (st.groups.size, ⟨Ground.withGroup st c z, book, roots, [], ()⟩) := by
      unfold Ground.newGroupP
      exact if_pos hok
    rw [h1]
    exact (Ground.Sh.newGroup_carries _ _ c z _ h2).symm
  · have h1 : Ground.newGroupP (_root_.Tw.K2.dOf st) c z = none := by
      unfold Ground.newGroupP
      exact if_neg hok
    rw [h1]
    unfold Ground.Sh.newGroupS
    exact (if_neg hok).symm

/-- **The front's decision, seen through the shape, is the step**: one equation, at every state. -/
theorem headFront_sh (tl : HTailF2) (s : S) :
    ((K2.headFrontQ tl s).toOption.map chainSh) = headFrontG (tailSh tl) (chainSh s) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | between =>
    have hN := newGroupG_sh st book roots check.frame.shape.code check.frame.shape.maskCode
    unfold K2.headFrontQ headFrontG headFrontB _root_.Tw.K2.firstFront
    simp only [S.atBetween, Johnson.Desc.First.Walk.firstDue]
    show _ = if (!failed.isSome && ((0 : Nat) == 0) && !check.inLink &&
        decide (check.frame.link < check.frame.shape.link.length) &&
        check.frame.next == .first && !(check.frame.link == 0) &&
        (check.frame.shape.link[check.frame.link]?).isSome &&
        (check.frame.groups[check.frame.link]?).isSome) = true then
      Option.map (fun x : Nat × CoreSh =>
        ChainSh.mk false 4 none none none rowsOwed x.2 out.reply.isSome out.indexMasks
          (out.pending.map K13.Honest.rowSh) none (checkSh check) none none none none
          (some (freshHead { frameSh check.frame with group := x.1, moment := 1, own := #[] }
            (tailSh tl) (checkSh check)))
          none none)
        (Ground.Sh.newGroupS (coreSh ⟨st, book, roots⟩) check.frame.shape.code
          check.frame.shape.maskCode) else none
    rw [← hN]
    cases hf : failed <;> cases hi : check.inLink <;>
      cases hl : decide (check.frame.link < check.frame.shape.link.length) <;>
      cases hnx : (check.frame.next == ReqNext.first) <;>
      cases h0 : (check.frame.link == 0) <;>
      cases hL : check.frame.shape.link[check.frame.link]? <;>
      cases hG : check.frame.groups[check.frame.link]? <;>
      cases hg : _root_.Tw.K2.newGroupG st check.frame.shape.code check.frame.shape.maskCode <;>
      simp only [bne, hnx, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, if_true, if_false, Option.isSome, beq_self_eq_true] <;>
      rfl
  | lay a => simp [K2.headFrontQ, headFrontG, headFrontB, S.atBetween, chainSh, ChainSh.mk,
      ChainSh.here, hereNo, Except.toOption]
  | att a => simp [K2.headFrontQ, headFrontG, headFrontB, S.atBetween, chainSh, ChainSh.mk,
      ChainSh.here, hereNo, Except.toOption]
  | head a => cases ho : a.opened <;> simp [K2.headFrontQ, headFrontG, headFrontB, S.atBetween,
      chainSh, ChainSh.mk, ChainSh.here, hereNo, Except.toOption, ho]
  | fin a => simp [K2.headFrontQ, headFrontG, headFrontB, S.atBetween, chainSh, ChainSh.mk,
      ChainSh.here, hereNo, Except.toOption]
  | mem a => simp [K2.headFrontQ, headFrontG, headFrontB, S.atBetween, chainSh, ChainSh.mk,
      ChainSh.here, hereNo, Except.toOption]

/-- A bind that returns. -/
theorem ex_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The head's front leaves what goes out, and returns no marked state. -/
theorem headFront_keeps {tl : HTailF2} {s m : S} (h : K2.headFrontQ tl s = .ok m) :
    m.out = s.out ∧ m.failed = none := by
  unfold K2.headFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨x, -, h⟩ := ex_bind h
      obtain ⟨s₁, h1, h⟩ := ex_bind h
      obtain ⟨e1, e2⟩ := (S.unmarked_ok _ _).1 h1
      split at h
      · obtain rfl := Except.ok.inj h
        refine ⟨?_, e2⟩
        show s₁.out = s.out
        rw [← e1]
        unfold S.enterHead
        split
        · rfl
        · unfold S.mark
          split <;> rfl
      · cases h

/-- The makes of the statement's rows behind the head's front: one new group without a row. -/
theorem headFront_forms {tl : HTailF2} {s m : S} (h : K2.headFrontQ tl s = .ok m) :
    formsOf m.st = { formsOf s.st with groups := (formsOf s.st).groups ++ [[]] } := by
  unfold K2.headFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨x, hx, h⟩ := ex_bind h
      obtain ⟨s₁, -, h⟩ := ex_bind h
      have hst : m.st = x.st := by
        split at h
        · obtain rfl := Except.ok.inj h
          rfl
        · cases h
      rw [hst]
      unfold _root_.Tw.K2.firstFront at hx
      split at hx
      · cases hx
      · split at hx
        · cases hx
        · split at hx
          · rename_i L G _ _
            unfold _root_.Tw.K2.newGroupG at hx
            cases hn : Ground.newGroupP (_root_.Tw.K2.dOf s.st) s.check.frame.shape.code
                s.check.frame.shape.maskCode with
            | none =>
              rw [hn] at hx
              cases hx
            | some y =>
              rw [hn] at hx
              obtain rfl := Except.ok.inj hx
              exact newGroup_forms hn
          · cases hx
          · cases hx

/-! ## The kind "the next token" at the first chain's state -/

/-- **What a yes of the kind's block is.** -/
theorem reply_iff (l V : Nat) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (Kinds.Reply.blockAt l V).decide s rs gs = .ok t ↔
      ∃ a r h, s.here = .head a ∧ a.opened = false ∧ rs = [r] ∧ s.out.reply = none ∧
        OnBytes.Desc.Reply.readReply r = some h ∧ OnBytes.Desc.Reply.isToken V h = true ∧
        t = { s with out := { s.out with reply := some h } } := by
  unfold Kinds.Reply.blockAt Kinds.Reply.entered Kinds.Reply.kind
  dsimp only
  constructor
  · intro h
    split at h
    · rename_i o ho
      split at h
      · cases h
      · rename_i hop
        cases rs with
        | nil => cases h
        | cons r rest =>
          cases rest with
          | cons _ _ => cases h
          | nil =>
            have h' : (if (Kinds.Reply.seatAt.reply s).isSome then .error "heard once" else
                match OnBytes.Desc.Reply.readReply r with
                | none => .error "one element, nothing drawn"
                | some x => if OnBytes.Desc.Reply.isToken V x then
                    .ok (Kinds.Reply.seatAt.setReply s x) else .error "a token" :
                Except String S) = .ok t := h
            by_cases hr : (Kinds.Reply.seatAt.reply s).isSome = true
            · rw [if_pos hr] at h'
              cases h'
            · rw [if_neg hr] at h'
              cases hx : OnBytes.Desc.Reply.readReply r with
              | none =>
                rw [hx] at h'
                cases h'
              | some x =>
                rw [hx] at h'
                by_cases ht : OnBytes.Desc.Reply.isToken V x = true
                · have h2 : (Except.ok (Kinds.Reply.seatAt.setReply s x) : Except String S) =
                      .ok t := by
                    simpa [ht] using h'
                  refine ⟨o, r, x, ho, by simpa using hop, rfl, ?_, hx, ht,
                    (Except.ok.inj h2).symm⟩
                  have hr' : s.out.reply.isSome ≠ true := hr
                  simpa using hr'
                · exfalso
                  simp [ht] at h'
    · cases h
  · rintro ⟨a, r, h, e1, e2, rfl, e4, e5, e6, rfl⟩
    rw [e1]
    simp only [e2, Bool.false_eq_true, if_false]
    unfold Kinds.Reply.decideE
    have hr : (Kinds.Reply.seatAt.reply s).isSome = false := by
      show s.out.reply.isSome = false
      rw [e4]
      rfl
    simp only [hr, Bool.false_eq_true, if_false, e5, e6, if_true]
    rw [← e1]
    rfl

/-- **The kind's block on the chain's shape**: the head's link is entered and not opened; no reply
was heard; then one is. -/
def replyG (a : ChainSh) : Option ChainSh :=
  if a.here == 4 && !a.reply then some (a.setReply true) else none

/-- **"Carries", strong**: behind a yes the step returns the shape behind. -/
theorem reply_carries {l V : Nat} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (Kinds.Reply.blockAt l V).decide s rs gs = .ok t) :
    replyG (chainSh s) = some (chainSh t) := by
  obtain ⟨a, r, x, e1, e2, -, e4, -, -, rfl⟩ := (reply_iff l V s t rs gs).1 h
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .head a := e1
  have e4' : out.reply = none := e4
  unfold replyG
  have h1 : ((chainSh ⟨st, book, roots, rowsOwed, failed, check, out, .head a, req⟩).here == 4 &&
      !(chainSh ⟨st, book, roots, rowsOwed, failed, check, out, .head a, req⟩).reply) = true := by
    show ((if a.opened then 3 else 4 : Nat) == 4 && !out.reply.isSome) = true
    rw [e2, e4']
    rfl
  rw [if_pos h1]
  rfl

/-- **"Returns"**: where the step returns, the block says yes on one round that holds just one
element, draws nothing, and whose element is a token. -/
theorem reply_returns {l V : Nat} {s : S} {r : Fmt.RoundView} {x : E}
    {gs : List (List (Nat × List UInt64))} {u : ChainSh} (hg : replyG (chainSh s) = some u)
    (hr : OnBytes.Desc.Reply.readReply r = some x) (ht : OnBytes.Desc.Reply.isToken V x = true) :
    ∃ t, (Kinds.Reply.blockAt l V).decide s [r] gs = .ok t ∧ t.failed = s.failed := by
  unfold replyG at hg
  split at hg
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    obtain ⟨c1, c2⟩ := hc
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    have c2' : out.reply.isSome = false := c2
    cases here with
    | head a =>
      have c1' : (if a.opened then 3 else 4 : Nat) = 4 := c1
      have ho : a.opened = false := by
        cases hh : a.opened
        · rfl
        · rw [hh] at c1'
          cases c1'
      exact ⟨_, (reply_iff l V _ _ [r] gs).2 ⟨a, r, x, rfl, ho, rfl, by simpa using c2', hr, ht,
        rfl⟩, rfl⟩
    | between => cases c1
    | lay a => cases c1
    | att a => cases c1
    | fin a => cases c1
    | mem a => cases c1
  · cases hg

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.newGroupG_sh
#print axioms VerifiableInference.Desc.First.Shape.ex_bind
#print axioms VerifiableInference.Desc.First.Shape.headFront_sh
#print axioms VerifiableInference.Desc.First.Shape.headFront_keeps
#print axioms VerifiableInference.Desc.First.Shape.headFront_forms
#print axioms VerifiableInference.Desc.First.Shape.reply_iff
#print axioms VerifiableInference.Desc.First.Shape.reply_carries
#print axioms VerifiableInference.Desc.First.Shape.reply_returns
