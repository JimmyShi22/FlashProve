-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyWLaid.lean (over the key file's tables, with their clause on the book: Laid17's last field is «step»; laid17_of pays it as laid1_of (KeySendYes1.lean) does: bookStep_of_seated at W's sending, then book and roots unturned through K13's rows): THE KEY FILE's ROW 1.17 (w.1.send): WHAT THE BLOCK's YES LAYS ON THE FIRST CHAIN's STATE, where it began at border 17's sizes. By row 1.1's pattern (Public11 | Laid1 | laid1_of, KeySendYes1.lean).
OBJECT: the state behind the yes of sendW (Johnson/Desc/Key/One.lean) · USER: shape | free | back at border 18 · LETTERS: one N sent groups.
  wAt one       the number under which W is sent: 1 + 2 · (the stages of the ranges' test)
  Public117     PUBLIC PREMISES ON THE PLAN: the message with W holds two notices (W; the fresh mask) · the sending kind's own test on the plan · W is sampled, with as many answers as the plan's samples; the mask is not · the shape asks no split's message · masks ride ahead · the layout of the two: one tree, parts 0 and 1
  Laid17        what the block leaves
  laid17_of     PROVED: by w_yes · sentN_of | sentN_order · rows_laid | ins_two · rows_mask
Nothing on soundness.
-/
import Johnson.RunOne.KeyWYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim)
open VerifiableInference.Desc.K1 (Par planOkOwn)
open VerifiableInference.Desc.Key.LaidW (rows_laid ins_two)

/-- The number under which W is sent. -/
abbrev wAt (one : OneTime) : Nat := 1 + 2 * one.ranges.stages.length

/-- **Public premises on the plan, at W's place.** -/
structure Public117 (one : OneTime) (N : Pieces) (groups : List (List Nat)) where
  n₁ : OracleNotice
  n₂ : OracleNotice
  two : linMessageW one.lin = some #[n₁, n₂]
  plan : planOkOwn (parW' one N groups #[n₁, n₂]) = true
  answers : n₁.shape.answers = one.given.plan.samples
  sampled : n₁.shape.answers ≠ 0
  bare : n₂.shape.answers = 0
  noSplit : one.lin.ownSplitNeeded = false
  ahead : one.lin.masksAhead = true
  lay : ∀ lay, layTrees one.codes #[n₁, n₂] = some lay →
    lay.shapes.size = 1 ∧ lay.tree.getD 0 0 = 0 ∧ lay.part.getD 0 0 = 0 ∧ lay.tree.getD 1 0 = 0 ∧ lay.part.getD 1 0 = 1

/-- What row 1.17's block leaves of the first chain's state, where it began at border 17's sizes. -/
structure Laid17 (one : OneTime) (s s' : FirstState) : Prop where
  codes : s'.d.st.codes = s.d.st.codes
  idx : s'.idx = s.idx
  base : s'.base = s.base
  atEnd : s'.atEnd = s.atEnd
  grp : s'.grp = s.grp
  size : s'.d.st.oracles.size = wAt one + 2
  gsize : s'.d.st.groups.size = one.ranges.stages.length + 1
  trees : s'.d.book.trees.size = one.ranges.stages.length + 2
  places : s'.d.book.place.size = wAt one + 2
  /-- the claim is kept; W's number, the own group's, the mask's are laid; the own group is the last: its members the claim's masks' message 0 and W; ONE open row, plain, WHICH IS THE CLAIM's (Eval); no test begun -/
  lin : ∃ (l L : LinFirst) (G : OnBytes.Group) (row : OnBytes.Row), s.lin = some l ∧ s'.lin = some L ∧ L.claim = l.claim ∧ L.w = wAt one ∧ L.own = one.ranges.stages.length ∧
    L.mask = some (wAt one + 1) ∧ s'.d.st.groups[one.ranges.stages.length]? = some G ∧ G.members = #[0, wAt one] ∧ G.rows = #[row] ∧ G.inRun = false ∧ row.kind = .plain ∧
    linEvalRow one.lin l.claim (wAt one) (linLayW s.d.st.codes one.lin) = some row
  placeOld : ∀ o, o < wAt one → s'.d.book.place[o]? = s.d.book.place[o]?
  placeW : s'.d.book.place[wAt one]? = some (one.ranges.stages.length + 1, 0)
  placeM : s'.d.book.place[wAt one + 1]? = some (one.ranges.stages.length + 1, 1)
  /-- every elder message is the same record but for its list of groups -/
  msgOld : ∀ (o : Nat) (x : OnBytes.Oracle), s.d.st.oracles[o]? = some x → ∃ gs, s'.d.st.oracles[o]? = some { x with groups := gs }
  msgW : ∃ x, s'.d.st.oracles[wAt one]? = some x ∧ x.sampled = true ∧ x.sampleRows.size = one.given.plan.samples ∧ x.sampleRows.size ≠ 0 ∧ x.spentAsMask = false
  msgM : ∃ x, s'.d.st.oracles[wAt one + 1]? = some x ∧ x.sampled = false ∧ x.sampleRows = #[] ∧ x.spentAsMask = false
  grpOld : ∀ i, i < one.ranges.stages.length → s'.d.st.groups[i]? = s.d.st.groups[i]?
  order : Means.InOrder s'.d.st
  ext : Means.Extends s.d.st s'.d.st
  /-- the book stays in order: the last field, as in Sent0 | Laid1 -/
  step : VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots = true → VerifiableInference.Desc.Sound.bookStepB 0 s'.d.book s'.d.roots = true

theorem laid17_of (one : OneTime) (N : Pieces) (sent : Nat) (groups : List (List Nat)) (Pb : Public117 one N groups) (bw : Block FirstState Claim)
    (hb : sendW one N sent groups = some bw) (s s' : FirstState) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (K1.rounds (parW' one N groups #[Pb.n₁, Pb.n₂])) [r₁, r₂] = true)
    (h : bw.decide s [r₁, r₂] gs = .ok s')
    (h0 : s.d.st.oracles.size = wAt one) (hg : s.d.st.groups.size = one.ranges.stages.length) (ht : s.d.book.trees.size = one.ranges.stages.length + 1)
    (hp : s.d.book.place.size = wAt one) (hm : ∀ l, s.lin = some l → listOfT (l.claim.masks.toList.map (·.oracle)) = [0]) (hI : Means.InOrder s.d.st) : Laid17 one s s' := by
  obtain ⟨msg, s₁, gs', l, o, hmsg, -, hs₁, -, hl, hrows, rfl⟩ := w_yes one N sent groups bw hb s s' r₁ r₂ gs h
  obtain rfl : #[Pb.n₁, Pb.n₂] = msg := Option.some.inj (Pb.two.symm.trans hmsg)
  have T := sentN_of _ _ s s₁ r₁ r₂ gs' hs₁
  have O₁ := sentN_order _ _ s s₁ r₁ r₂ gs' Pb.plan hfit hs₁ hI
  obtain ⟨L, d'⟩ := o
  have RL := rows_laid one.lin l.claim s₁.sent s₁.d d' L Pb.noSplit hrows
  have hmk := rows_mask one.lin l.claim s₁.sent s₁.d d' L hrows
  have hs : (parW' one N groups #[Pb.n₁, Pb.n₂]).sent = #[Pb.n₁, Pb.n₂] := rfl
  have hn : (parW' one N groups #[Pb.n₁, Pb.n₂]).sent.size = 2 := rfl
  have hc : s.d.st.codes = one.codes := T.plan
  obtain ⟨lay, hlay, hseat⟩ := T.book
  have hlay' : layTrees one.codes #[Pb.n₁, Pb.n₂] = some lay := by rw [← hc, ← hs]; exact hlay
  obtain ⟨l1, l2, l3, l4, l5⟩ := Pb.lay lay hlay'
  have g₁ : s₁.d.st.groups.size = one.ranges.stages.length := by rw [T.groups]; exact hg
  have z₁ : s₁.d.st.oracles.size = wAt one + 2 := by rw [T.size, hn, h0]
  have hsl : s.lin = some l := T.lin.symm.trans hl
  have hsent0 : s₁.sent[0]? = some (wAt one) := by
    rw [T.sent, hn, h0]
    simp
  have hsentB : s₁.sent.back? = some (wAt one + 1) := by
    rw [T.sent, hn, h0]
    simp [Array.back?, Nat.add_comm]
  have hw : L.w = wAt one := Option.some.inj (RL.w.symm.trans hsent0)
  obtain ⟨x1, hx1, -, -, hx1m, -, hx1s⟩ := T.new 0 Pb.n₁ (by rw [hs]; rfl)
  obtain ⟨x2, hx2, -, -, hx2m, hx2s, -⟩ := T.new 1 Pb.n₂ (by rw [hs]; rfl)
  rw [h0] at hx1 hx2
  obtain ⟨q1, hq1⟩ := RL.msg _ x1 hx1
  obtain ⟨q2, hq2⟩ := RL.msg _ x2 hx2
  obtain ⟨G, row, hG, hGm, hGr, hGi, hk, hrow⟩ := RL.last
  rw [g₁] at hG
  rw [hm l hsl, hw, ins_two 0 (wAt one) (by unfold wAt; omega)] at hGm
  rw [hw, T.codes] at hrow
  have p1 := hseat.new 0 (by rw [hn]; decide)
  have p2 := hseat.new 1 (by rw [hn]; decide)
  rw [h0, ht, l2, l3] at p1
  rw [h0, ht, l4, l5] at p2
  exact
    { codes := (RL.codes.trans T.codes : d'.st.codes = s.d.st.codes)
      idx := T.idx, base := T.base, atEnd := T.atEnd, grp := T.grp
      size := (RL.msgs.trans z₁ : d'.st.oracles.size = wAt one + 2)
      gsize := by
        show d'.st.groups.size = _
        rw [RL.size, g₁]
      trees := by
        show d'.book.trees.size = _
        rw [RL.book, hseat.size, ht, l1]
      places := by
        show d'.book.place.size = _
        rw [RL.book, hseat.count, hp, hn]
      lin := ⟨l, L, G, row, hsl, rfl, RL.claimIs, hw, RL.own.trans g₁, by
        rw [hmk, Pb.ahead, if_pos rfl, hsentB], hG, hGm, hGr, hGi, hk, hrow⟩
      placeOld := fun o ho => by
        show d'.book.place[o]? = _
        rw [RL.book]
        exact hseat.places o (by rw [hp]; exact ho)
      placeW := by
        show d'.book.place[wAt one]? = _
        rw [RL.book]
        exact p1
      placeM := by
        show d'.book.place[wAt one + 1]? = _
        rw [RL.book]
        exact p2
      msgOld := fun o x hx => by
        have ho : o < s.d.st.oracles.size := by
          by_contra c
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
          cases hx
        exact RL.msg o x ((T.older o ho).trans hx)
      msgW := ⟨_, hq1, (hx1s Pb.sampled).1, by
        show x1.sampleRows.size = _
        rw [(hx1s Pb.sampled).2, Pb.answers], by
        show x1.sampleRows.size ≠ 0
        rw [(hx1s Pb.sampled).2]
        exact Pb.sampled, hx1m⟩
      msgM := ⟨_, hq2, (hx2s Pb.bare).1, (hx2s Pb.bare).2, hx2m⟩
      grpOld := fun i hi => by
        show d'.st.groups[i]? = _
        rw [RL.older i (by rw [g₁]; exact hi), T.groups]
      order := RL.order O₁
      ext := ⟨(RL.codes.trans T.codes : d'.st.codes = s.d.st.codes), fun o x hx => by
        have ho : o < s.d.st.oracles.size := by
          by_contra c
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
          cases hx
        obtain ⟨q, hq⟩ := RL.msg o x ((T.older o ho).trans hx)
        exact ⟨_, hq, rfl⟩⟩
      step := fun hbk => by
        show VerifiableInference.Desc.Sound.bookStepB 0 d'.book d'.roots = true
        rw [RL.book, RL.roots]
        exact (VerifiableInference.Desc.Sound.bookStep_iff 0 s₁.d.book s₁.d.roots).2
          (bookStep_of_seated 0 s.d.book s₁.d.book _ _ lay _ s.d.roots s₁.d.roots ((VerifiableInference.Desc.Sound.bookStep_iff 0 s.d.book s.d.roots).1 hbk) hseat (T.roots lay hlay)) }

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.laid17_of
