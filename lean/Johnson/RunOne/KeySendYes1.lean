-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySendYes1.lean: THE KEY FILE's ROW 1.1 (msg.1.send: the lookups' own message B and the fresh mask that rides with it, in one tree; then the ranges' group is opened and B joins it): (yes): WHAT THE BLOCK's YES GIVES OF THE RECORD: from the tables' book-keeping and last letter at border 1: those at border 2. By the general form SentN (KeySentN.lean) and JoinedTo | joinP_to (Johnson/Desc/Key/Laid/RowsLaid.lean).
OBJECT: shape₁ | free₁ at border 2 · USER: row 1.1's Left-structure · LETTERS: F G at_ one R coll; N groups.
  msg_yes     PROVED: a yes of sendOwnMessage on two rounds is a yes of the seat and then of openRangesGroup
  group_yes   PROVED: a yes of openRangesGroup, written out: the first number sent is the plan's messageId · a new group · that message joins it · grp | rider laid
  Public11    PUBLIC PREMISES ON THE PLAN: the prover's message holds two notices · planOkOwn at the place · the first is sampled, the second not · masks ride · the ranges' test has a stage · the layout of the two: one tree, parts 0 and 1
  Laid1       what the block leaves, where it began at border 1's sizes: sizes 3 | 1 | 2 | 3 · grp = 0 · the group: members [1], no row, no test begun · rider = some 2 · place 0 kept, places 1 | 2 = (1, 0) | (1, 1) · message 0 the same record but for its list of groups · message 1 sampled · message 2 unsampled, unspent · InOrder · the statement behind is a later statement (Means.Extends)
  laid1_of    PROVED
  front1      PROVED: what the book-keeping at border 1 says of the state in front
  shape_send1 PROVED: the book-keeping at border 2
  open₁_send1 | pinned_send1 | pinned_behind1   PROVED by decide
  SmpOwn      A CONDITION ON THE READING: the sample of the table's message k is read off that message's own record at the statement's codes, and not off the record's list of groups
  smp_send1   PROVED: under it the elder pin's sample rides
  free_send1  PROVED: the promise's last letter at border 2, at New := ShownAt F at_ 1
  rowHolds_ext   (private) KIN, TO THE LETTER: rowHolds_extends (Johnson/Desc/Key/RowsCarry.lean): not imported here
  back_send1  PROVED: the older items ride back, among them pin 0 and its sample's row: UNDER A CONDITION ON THE LETTER R: R.same = fun a b => ρ.val a = ρ.val b
Nothing on soundness.
-/
import Johnson.RunOne.KeySentN
import Johnson.RunOne.KeySendYes
import Johnson.Desc.Key.Laid.RowsLaid
import Johnson.Desc.Key.RowHoldsSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.K1 (Par decideSend planOkOwn)
open VerifiableInference.Desc.Ground (newGroupP joinP)
open VerifiableInference.Desc.Keeps (ebind_ok named_ok)
open VerifiableInference.Desc.Key.LaidW (JoinedTo joinP_to ins)

section
variable {β Cl : Type}

/-- The place's parameters. -/
abbrev parMsg' (one : OneTime) (N : Pieces) (groups : List (List Nat)) : Par :=
  sendingPar one N.msg "the lookups' own message and what rides with it" (Wf.messageOf one.ranges) groups

theorem msg_yes (one : OneTime) (N : Pieces) (groups : List (List Nat)) (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendOwnMessage one N groups : Block (ChainState β) Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ (s₁ : ChainState β) (gs' : List (List (Nat × List UInt64))),
      (sendingSeat "K1: the own message's sending" (parMsg' one N groups) : Block (ChainState β) Cl).decide s [r₁, r₂] gs' = .ok s₁ ∧ openRangesGroup one s₁ = .ok s' := by
  obtain ⟨m, h1, h2⟩ := ebind_ok h
  exact ⟨m, _, h1, h2⟩

theorem group_yes (one : OneTime) (s₁ s' : ChainState β) (h : openRangesGroup one s₁ = .ok s') :
    s₁.sent[0]? = some one.ranges.messageId ∧
    ∃ d, joinP ({ s₁.d with st := VerifiableInference.Desc.Ground.withGroup s₁.d.st one.ranges.message.shape.code one.ranges.message.shape.maskCode }) s₁.d.st.groups.size one.ranges.messageId false = some d ∧
      s' = { s₁ with d := d, grp := s₁.d.st.groups.size, rider := if one.ranges.choice.masksRide then s₁.sent[1]? else none } := by
  unfold openRangesGroup at h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨m, hm, h⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨_, hid, h⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨g, hg, h7⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨d, hd, h8⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h7
  clear h h7
  have hm' := named_ok hm
  have hid' : m = one.ranges.messageId := beq_iff_eq.1 (need_ok hid)
  subst hid'
  have hg' := named_ok hg
  have hd' := named_ok hd
  unfold newGroupP at hg'
  split at hg'
  · obtain rfl := Option.some.inj hg'
    exact ⟨hm', d, hd', (Except.ok.inj h8).symm⟩
  · cases hg'

end

/-! ## What the yes lays, in the tables' own readers -/

/-- **Public premises on the plan, at the own message's place.** -/
structure Public11 (one : OneTime) (N : Pieces) (groups : List (List Nat)) where
  /-- the two notices that the prover's message holds: B, and the fresh mask of the ranges' test's first fold -/
  n₁ : OracleNotice
  n₂ : OracleNotice
  two : Wf.messageOf one.ranges = #[n₁, n₂]
  /-- the sending kind's own test on the plan, at the place -/
  plan : planOkOwn (parMsg' one N groups) = true
  /-- B is sampled; the mask is not -/
  sampled : n₁.shape.answers ≠ 0
  bare : n₂.shape.answers = 0
  /-- masks ride with a sending -/
  ride : one.ranges.choice.masksRide = true
  /-- the ranges' test has a stage -/
  stages : 1 ≤ one.ranges.stages.length
  /-- the layout of the two: one tree; B its first part, the mask its second -/
  lay : ∀ lay, layTrees one.codes #[n₁, n₂] = some lay →
    lay.shapes.size = 1 ∧ lay.tree.getD 0 0 = 0 ∧ lay.part.getD 0 0 = 0 ∧ lay.tree.getD 1 0 = 0 ∧ lay.part.getD 1 0 = 1

/-- What row 1.1's block leaves of the first chain's state, where it began at border 1's sizes (one message, no group, one tree). -/
structure Laid1 (s s' : FirstState) : Prop where
  codes : s'.d.st.codes = s.d.st.codes
  idx : s'.idx = s.idx
  base : s'.base = s.base
  lin : s'.lin = s.lin
  atEnd : s'.atEnd = s.atEnd
  size : s'.d.st.oracles.size = 3
  gsize : s'.d.st.groups.size = 1
  grp : s'.grp = 0
  group : ∃ G, s'.d.st.groups[0]? = some G ∧ G.members.toList = [1] ∧ G.rows = #[] ∧ G.inRun = false
  rider : s'.rider = some 2
  trees : s'.d.book.trees.size = 2
  places : s'.d.book.place.size = 3
  place0 : s'.d.book.place[0]? = s.d.book.place[0]?
  place1 : s'.d.book.place[1]? = some (1, 0)
  place2 : s'.d.book.place[2]? = some (1, 1)
  /-- the elder message is the same record but for its list of groups -/
  msg0 : ∀ x, s.d.st.oracles[0]? = some x → ∃ gs, s'.d.st.oracles[0]? = some { x with groups := gs }
  msg1 : ∃ x, s'.d.st.oracles[1]? = some x ∧ x.sampled = true ∧ x.sampleRows.size ≠ 0
  msg2 : ∃ x, s'.d.st.oracles[2]? = some x ∧ x.sampled = false ∧ x.spentAsMask = false
  order : Means.InOrder s'.d.st
  /-- the statement behind is a later statement -/
  ext : Means.Extends s.d.st s'.d.st
  /-- the book stays in order -/
  step : VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots = true → VerifiableInference.Desc.Sound.bookStepB 0 s'.d.book s'.d.roots = true

theorem laid1_of (one : OneTime) (N : Pieces) (groups : List (List Nat)) (Pb : Public11 one N groups) (s s' : FirstState) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (K1.rounds (parMsg' one N groups)) [r₁, r₂] = true)
    (h : (sendOwnMessage one N groups : Block FirstState Claim).decide s [r₁, r₂] gs = .ok s')
    (h0 : s.d.st.oracles.size = 1) (hg : s.d.st.groups.size = 0) (ht : s.d.book.trees.size = 1) (hp : s.d.book.place.size = 1)
    (hid : one.ranges.messageId = 1) (hI : Means.InOrder s.d.st) : Laid1 s s' := by
  obtain ⟨s₁, gs', hs₁, hgr⟩ := msg_yes one N groups s s' r₁ r₂ gs h
  have T := sentN_of _ _ s s₁ r₁ r₂ gs' hs₁
  have O₁ := sentN_order _ _ s s₁ r₁ r₂ gs' Pb.plan hfit hs₁ hI
  obtain ⟨-, d, hj, rfl⟩ := group_yes one s₁ s' hgr
  have J := joinP_to _ d _ _ _ hj
  have hs : (parMsg' one N groups).sent = #[Pb.n₁, Pb.n₂] := by
    have e : (parMsg' one N groups).sent = ((Wf.messageOf one.ranges).toList ++ []).toArray := rfl
    rw [e, Pb.two]
    rfl
  have hn : (parMsg' one N groups).sent.size = 2 := by rw [hs]; rfl
  have hc : s.d.st.codes = one.codes := T.plan
  obtain ⟨lay, hlay, hseat⟩ := T.book
  have hlay' : layTrees one.codes #[Pb.n₁, Pb.n₂] = some lay := by rw [← hc, ← hs]; exact hlay
  obtain ⟨l1, l2, l3, l4, l5⟩ := Pb.lay lay hlay'
  have g₁ : s₁.d.st.groups.size = 0 := by rw [T.groups]; exact hg
  have z₁ : s₁.d.st.oracles.size = 3 := by rw [T.size, hn, h0]
  rw [hid, g₁] at hj J
  obtain ⟨x1, hx1, -, -, -, -, hx1s⟩ := T.new 0 Pb.n₁ (by rw [hs]; rfl)
  obtain ⟨x2, hx2, -, -, hx2m, hx2s, -⟩ := T.new 1 Pb.n₂ (by rw [hs]; rfl)
  rw [h0] at hx1 hx2
  obtain ⟨q1, hq1⟩ := J.msg 1 x1 hx1
  obtain ⟨q2, hq2⟩ := J.msg 2 x2 hx2
  have hG0 : (VerifiableInference.Desc.Ground.withGroup s₁.d.st one.ranges.message.shape.code one.ranges.message.shape.maskCode).groups[0]? =
      some { code := one.ranges.message.shape.code, maskCode := one.ranges.message.shape.maskCode } := by
    show (s₁.d.st.groups.push _)[0]? = _
    rw [← g₁]
    exact Array.getElem?_push_size
  obtain ⟨G', hG', m', r', i'⟩ := J.at_ _ hG0
  have p0 := hseat.places 0 (by rw [hp]; exact Nat.zero_lt_one)
  have p1 := hseat.new 0 (by rw [hn]; decide)
  have p2 := hseat.new 1 (by rw [hn]; decide)
  rw [h0, ht, l2, l3] at p1
  rw [h0, ht, l4, l5] at p2
  exact
    { codes := (J.codes.trans T.codes : d.st.codes = s.d.st.codes)
      idx := T.idx, base := T.base, lin := T.lin, atEnd := T.atEnd
      size := (J.msgs.trans z₁ : d.st.oracles.size = 3)
      gsize := by
        have e := J.size
        show d.st.groups.size = 1
        rw [e]
        show (s₁.d.st.groups.push _).size = 1
        rw [Array.size_push, g₁]
      grp := g₁
      group := ⟨G', hG', by rw [m']; simp [ins], r', i'⟩
      rider := by
        show (if one.ranges.choice.masksRide = true then s₁.sent[1]? else none) = some 2
        rw [if_pos Pb.ride, T.sent, hn, h0]
        simp
      trees := by
        show d.book.trees.size = 2
        rw [J.book]
        show s₁.d.book.trees.size = 2
        rw [hseat.size, ht, l1]
      places := by
        show d.book.place.size = 3
        rw [J.book]
        show s₁.d.book.place.size = 3
        rw [hseat.count, hp, hn]
      place0 := by
        show d.book.place[0]? = _
        rw [J.book]
        exact p0
      place1 := by
        show d.book.place[1]? = _
        rw [J.book]
        exact p1
      place2 := by
        show d.book.place[2]? = _
        rw [J.book]
        exact p2
      msg0 := fun x hx => J.msg 0 x ((T.older 0 (by rw [h0]; exact Nat.zero_lt_one)).trans hx)
      msg1 := ⟨_, hq1, (hx1s Pb.sampled).1, by
        show x1.sampleRows.size ≠ 0
        rw [(hx1s Pb.sampled).2]
        exact Pb.sampled⟩
      msg2 := ⟨_, hq2, (hx2s Pb.bare).1, hx2m⟩
      order := Means.joinP_keeps hj (O₁.withGroup _ _)
      ext := ⟨(J.codes.trans T.codes : d.st.codes = s.d.st.codes), fun o x hx => by
        have ho : o < s.d.st.oracles.size := by
          by_contra c
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
          cases hx
        obtain ⟨q, hq⟩ := J.msg o x ((T.older o ho).trans hx)
        exact ⟨_, hq, rfl⟩⟩
      step := fun hb => by
        show VerifiableInference.Desc.Sound.bookStepB 0 d.book d.roots = true
        rw [J.book, J.roots]
        exact (VerifiableInference.Desc.Sound.bookStep_iff 0 s₁.d.book s₁.d.roots).2
          (bookStep_of_seated 0 s.d.book s₁.d.book _ _ lay _ s.d.roots s₁.d.roots ((VerifiableInference.Desc.Sound.bookStep_iff 0 s.d.book s.d.roots).1 hb) hseat (T.roots lay hlay)) }

/-- What the tables' book-keeping at border 1 says of the state in front. -/
theorem front1 (one : OneTime) (s : FirstState) (h : shape₁' one 1 s = true) :
    s.d.st.oracles.size = 1 ∧ s.d.st.groups.size = 0 ∧ s.d.book.trees.size = 1 ∧ s.d.book.place.size = 1 ∧ one.ranges.messageId = 1 ∧ s.idx = 0 := by
  have ht : ties₁ one 1 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ tiesA sizesB at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, counts₁] at ht
  obtain ⟨⟨⟨⟨⟨⟨-, e⟩, -⟩, i⟩, -⟩, -⟩, ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, -⟩, -⟩, -⟩, -⟩⟩ := ht
  have a' : s.d.st.oracles.size = 1 := a
  exact ⟨a', b, c, by rw [d]; exact a', e, i.resolve_left (by decide)⟩

/-- **The book-keeping at border 2.** -/
theorem shape_send1 (one : OneTime) (hst : 1 ≤ one.ranges.stages.length) (s s' : FirstState) (H : Laid1 s s') (h : shape₁' one 1 s = true) : shape₁' one 2 s' = true := by
  have ht : ties₁ one 1 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  have hc : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 1 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).2
  obtain ⟨G, hG, hGm, hGr, hGi⟩ := H.group
  obtain ⟨x1, hx1, hx1a, hx1b⟩ := H.msg1
  obtain ⟨x2, hx2, hx2a, hx2b⟩ := H.msg2
  -- message 0 was sent in front
  have s0 : sentB (plan₁ one) (readers₁ one) s 0 = true := by
    have hc' := hc
    simp [core₁] at hc'
    exact hc'.1.1
  have e0 : sentB (plan₁ one) (readers₁ one) s' 0 = true := by
    have s0' : (match s.d.st.oracles[0]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = true := s0
    cases hx : s.d.st.oracles[0]? with
    | none => rw [hx] at s0'; cases s0'
    | some x =>
      rw [hx] at s0'
      obtain ⟨q, hq⟩ := H.msg0 x hx
      show (match s'.d.st.oracles[0]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = true
      rw [hq]
      exact s0'
  have e1 : sentB (plan₁ one) (readers₁ one) s' 1 = true := by
    show (match s'.d.st.oracles[1]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = true
    rw [hx1]
    simp [hx1a, hx1b]
  have e2 : sentB (plan₁ one) (readers₁ one) s' 2 = false := by
    show (match s'.d.st.oracles[1 + 2 * one.ranges.stages.length]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = false
    rw [Array.getElem?_eq_none (by rw [H.size]; omega)]
  have e3 : groupB (readers₁ one) s' false 0 = true := by
    show (match (if s'.grp == noId then none else some s'.grp).bind fun g => s'.d.st.groups[g]? with | some G => G.inRun == false && G.rows.size == 0 | none => false) = true
    rw [H.grp]
    have e : ((if (0 : Nat) == noId then none else some 0).bind fun g => s'.d.st.groups[g]?) = some G := hG
    rw [e]
    simp [hGi, hGr]
  have hstep := H.step
  refine (shape₁_iff _ _ _ _ _ _ _).2 ⟨?_, ?_⟩
  · show ties₁ one 2 s' = true
    unfold ties₁ tiesA moreB sizesB at ht ⊢
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, counts₁, done₁, H.codes, H.idx, H.base, H.lin, H.atEnd, H.size, H.gsize, H.trees, H.places, H.grp, H.rider, hG, hx2] at ht ⊢
    simp_all
  · show core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 2 s' = true
    unfold ties₁ sizesB at ht
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
    obtain ⟨-, ⟨⟨⟨⟨-, hemp⟩, -⟩, -⟩, -⟩⟩ := ht
    obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩ := hemp.resolve_left (by decide)
    have d0 : doneB (plan₁ one) (readers₁ one) 2 0 s' = true := by
      unfold doneB
      have r0 : ∀ l, (readers₁ one).rowsAt s' l = none := fun l => by
        show s'.base.rows[l]? = none
        rw [H.base, List.isEmpty_iff.1 b1]
        rfl
      have k0 : ∀ l, (readers₁ one).keysAt s' l = none := fun l => by
        show (s'.base.keys[l]?).bind _ = none
        rw [H.base, List.isEmpty_iff.1 b2]
        rfl
      simp [r0, k0]
    have p0 : ((readers₁ one).pile s').isNone = true := by
      show (s'.lin.map _).isNone = true
      rw [H.lin, Option.isNone_iff_eq_none.1 b5]
      rfl
    have l0 : ((book₁ one).ledger s').isNone = true := by
      show (s'.base.fork.map _).isNone = true
      rw [H.base, Option.isNone_iff_eq_none.1 b3]
      rfl
    have h0 : (book₁ one).heard s' = false := by
      show s'.base.heard.isSome = false
      rw [H.base, Option.isNone_iff_eq_none.1 b4]
      rfl
    unfold core₁
    simp [e0, e1, e2, e3, d0, p0, l0, h0]

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

theorem open₁_send1 : open₁ 2 2 = open₁ 2 1 ++ [.pin 1, .srow 1] := by decide
theorem pinned_send1 : pinned (open₁ 2 1 ++ [.pin 1, .srow 1]) = pinned (open₁ 2 1) ++ [1] := by decide
theorem pinned_behind1 : pinned (open₁ 2 2) = [0, 1] := by decide

/-- **A condition on the reading**: the sample that it holds of the table's message k is read off that message's own record in the statement, at the statement's codes, and not off the record's list of groups. -/
def SmpOwn : Prop :=
  ∀ (p : Xi) (s s' : FirstState) (k o : Nat) (x : OnBytes.Oracle) (gs : List Nat), (plan₁ one).orc k = some o → s'.d.st.codes = s.d.st.codes →
    s.d.st.oracles[o]? = some x → s'.d.st.oracles[o]? = some { x with groups := gs } → G.smp (p, s') (at_ k).1 (at_ k).2 = G.smp (p, s) (at_ k).1 (at_ k).2

/-- The elder pin's sample rides. -/
theorem smp_send1 (hG : SmpOwn G at_ one) (p : Xi) (s s' : FirstState) (H : Laid1 s s') (h : shape₁' one 1 s = true) :
    G.smp (p, s') (at_ 0).1 (at_ 0).2 = G.smp (p, s) (at_ 0).1 (at_ 0).2 := by
  have z := (front1 one s h).1
  have hx : s.d.st.oracles[0]? = some (s.d.st.oracles[0]'(by rw [z]; exact Nat.zero_lt_one)) := Array.getElem?_eq_getElem _
  obtain ⟨q, hq⟩ := H.msg0 _ hx
  exact hG p s s' 0 0 _ q rfl H.codes hx hq

/-- **The promise's last letter at border 2.** -/
theorem free_send1 (hR : RecStays G) (hcoll : CollCell coll) (hat : at_ 1 = (1, 0)) (p : Xi) (s s' : FirstState) (y y' : Strs) (H : Laid1 s s')
    (Hy : StrsStay F at_ (open₁ 2 1) y y') (hN : ShownAt F at_ 1 y') (h : free₁ F G at_ one R coll 1 (p, s) y) : free₁ F G at_ one R coll 2 (p, s') y' := by
  obtain ⟨⟨r, hr, hn⟩, h2, h3, -, -, -, -, h8, h9, -, -⟩ := h
  refine ⟨⟨r, (hR p s s').trans hr, fun hc => hn (hcoll y y' r Hy.cell hc)⟩, h2, ?_, fun h18 => absurd h18 (by decide), ?_, fun h18 => absurd h18 (by decide), H.order, ?_, h9,
    fun _ => ⟨1, 0, H.place1, H.place2⟩, fun h18 => absurd h18 (by decide)⟩
  · intro k hk
    rw [pinned_behind1] at hk
    rcases (by simpa using hk : k = 0 ∨ k = 1) with rfl | rfl
    · obtain ⟨o, t, ho, ht, e⟩ := h3 0 (by rw [pinned_behind0]; exact List.mem_singleton.2 rfl)
      obtain rfl : 0 = o := Option.some.inj ho
      exact ⟨0, t, rfl, H.place0.trans ht, e⟩
    · exact ⟨1, (1, 0), rfl, H.place1, hat⟩
  · intro j _ o _ x hx r' hr'
    exact H.order.samples o x hx r' hr'
  · intro j hj
    rw [pinned_behind1] at hj
    rcases (by simpa using hj : j = 0 ∨ j = 1) with rfl | rfl
    · exact shownAt_ride F at_ 0 y y' (Hy.word 0 (by rw [pinned_behind0]; exact List.mem_singleton.2 rfl)) (h8 0 (by rw [pinned_behind0]; exact List.mem_singleton.2 rfl))
    · exact hN

/-- A row that has passed the tests at a statement holds at a later statement just where it holds there. KIN: rowHolds_extends (Johnson/Desc/Key/RowsCarry.lean): to the letter; not imported here. -/
private theorem rowHolds_ext {K : Type} [CommRing K] (ρ : Model.Reading K) {S S' : Statement} {Gp : OnBytes.Group} {row : OnBytes.Row} (hE : Means.Extends S S')
    (hr : Means.RowIn S Gp row) (val : Nat → Part → Nat → E) :
    RowHolds (fun a b => ρ.val a = ρ.val b) S' val row ↔ RowHolds (fun a b => ρ.val a = ρ.val b) S val row := by
  rw [rowHolds_iff_says_of_rowIn ρ S' Gp val row (Means.RowIn.extends hE (fun _ h => h) hr), rowHolds_iff_says_of_rowIn ρ S Gp val row hr]
  exact Means.says_extends ρ hE hr _

/-- **The older items ride back**: among them now a pin and its sample's row. -/
theorem back_send1 {K : Type} [CommRing K] (ρ : Model.Reading K) (hs : R.same = fun a b => ρ.val a = ρ.val b) (hR : RecStays G) (p : Xi) (s s' : FirstState) (y y' : Strs)
    (w : Wit Cells Unit M) (H : Laid1 s s') (z : s.d.st.oracles.size = 1) (hI : Means.InOrder s.d.st) (e : G.smp (p, s') (at_ 0).1 (at_ 0).2 = G.smp (p, s) (at_ 0).1 (at_ 0).2)
    (Hy : StrsStay F at_ (open₁ 2 1) y y')
    (h : relAt F G at_ (meaning₁At one R) (open₁ 2 1 ++ [.pin 1, .srow 1]) (p, s') y' w) : relAt F G at_ (meaning₁At one R) (open₁ 2 1) (p, s) y w := by
  intro i hi
  have Hi := h i (List.mem_append_left _ hi)
  have hi' : i = .unmarked ∨ i = .pinT ∨ i = .inRange 0 ∨ i = .inRange 1 ∨ i = .pin 0 ∨ i = .srow 0 := by
    have e : open₁ 2 1 = [.unmarked, .pinT, .inRange 0, .inRange 1, .pin 0, .srow 0] := by decide
    rw [e] at hi
    simpa using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rfl
  · obtain ⟨r, h1, h2⟩ := Hi
    exact ⟨r, (hR p s s') ▸ h1, Hy.cell ▸ h2⟩
  · exact Hi
  · exact Hi
  · exact rides_pin2_at F G _ _ (p, s) (p, s') y y' w e (Hy.word 0 (by rw [pinned_behind0]; exact List.mem_singleton.2 rfl)) Hi
  · obtain ⟨o, x', ho, hx', h1, h2, h3⟩ := Hi
    obtain rfl : 0 = o := Option.some.inj ho
    have hx'' : s'.d.st.oracles[0]? = some x' := hx'
    have hx : s.d.st.oracles[0]? = some (s.d.st.oracles[0]'(by rw [z]; exact Nat.zero_lt_one)) := Array.getElem?_eq_getElem _
    obtain ⟨q, hq⟩ := H.msg0 _ hx
    obtain rfl := Option.some.inj (hq.symm.trans hx'')
    refine ⟨0, _, rfl, hx, h1, h2, fun r hr => ?_⟩
    have hh := h3 r hr
    rw [hs] at hh ⊢
    exact (rowHolds_ext ρ H.ext (hI.samples 0 _ hx r hr) _).1 hh

end

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.msg_yes
#print axioms Johnson.RunOne.KeyRows1.group_yes
#print axioms Johnson.RunOne.KeyRows1.laid1_of
#print axioms Johnson.RunOne.KeyRows1.front1
#print axioms Johnson.RunOne.KeyRows1.shape_send1
#print axioms Johnson.RunOne.KeyRows1.smp_send1
#print axioms Johnson.RunOne.KeyRows1.free_send1
#print axioms Johnson.RunOne.KeyRows1.back_send1
