-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FrontSteps.lean: THE
PROMISE IN FRONT OF THE FIRST LINK, STEP BY STEP: what stands in the record of a key file's first
chain at its start, behind the sending of the index-mask message, and behind the sending of the
lookups' own message; each step from ONE block's yes, so that the facts can ride in the rows at the
chain's first three borders. Behind the second step PromL 0 holds (PromKeyD.lean), at the index-mask
message's number 0 and at the two ledgers as the sendings open them.

Main names:
  seat_sent: the yes of a sending's seat is a yes of the kind's own decision; what the seat leaves.
  sent_old, sent_new, sent_codes, sent_first: what that decision leaves, writes and returns.
  joinP_msg, open_facts: what the making of the ranges' group leaves.
  Half one s: behind the first sending. Front one t: behind the second.
  idx_step: from the chain's start, the first block's yes gives Half.
  msg_step: from Half, the second block's yes gives Front.
  ledOf: a message's ledger as its sending opens it.
  front_promL: FROM Front AND PUBLIC NUMBERS, PromL 0.

Object: Key.sendIndexMasks and Key.sendOwnMessage (Johnson/Desc/Key/One.lean) at Key.pieces, which
are the blocks 0 and 1 of (FK X N P).first.blocksInOrder up to their tests on the plan (fk_idx_at, fk_msg_at:
Johnson/RunOne/Sound/KeyMapAtFK.lean), and Key.chainStart, which is the description's start₁.
User: FrontAtFK.lean. Whoever fills the seats 0 and 1 lays Half and Front into the conditions of the
rows 1 and 2.
Letters: one, N, groups, the rounds and groups of columns that the block is shown; Ex.

Limits. The steps ask that the block is shown two rounds. Both messages count an answer: a premise
of the steps. Nothing on what a table of masks holds. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.Writes3
import Johnson.RunOne.Law.TakesSum
import Johnson.RunOne.Law.LinkAtCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FrontSteps
open OnBytes OnBytes.Params OnBytes.Slice
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc (Block named need)
open VerifiableInference.Desc.Ground (newGroupP joinP)
open VerifiableInference.Desc.K1 (Par decideSend decideSend_iff shapesOf outs wr seedsOf answersIn)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim ChainState Source sendingSeat sendingPar withLoc
  sendIndexMasks sendOwnMessage openRangesGroup chainStart Pieces sourceClauses)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.TakesSum

variable {β Cl L : Type}

/-! ## The kind's own decision -/

/-- **The yes of a sending's seat is a yes of the kind's own decision.** -/
theorem seat_sent {name : String} {P : Par} {s t : ChainState β} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (sendingSeat (Cl := Cl) name P).decide s rs gs = .ok t) :
    ∃ ids d', decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs = .ok (ids, d') ∧
      t.d.st = d'.st ∧ t.sent = ids ∧ t.idx = s.idx ∧ t.base = s.base := by
  have h' : ((decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs).map fun x =>
      ({ s with d := withLoc ({ x.2 with loc := x.1 } : DState (Array ℕ)) (), owed := none,
                sent := x.1 } : ChainState β)) = .ok t := by
    rw [← h]
    show _ = ((decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs).map _).map _
    cases decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs <;> rfl
  cases hd : decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs with
  | error e =>
    rw [hd] at h'
    cases h'
  | ok x =>
    rw [hd] at h'
    cases h'
    exact ⟨x.1, x.2, rfl, rfl, rfl, rfl, rfl⟩

/-- It leaves the messages that stood. -/
theorem sent_old {P : Par} {owed : Option ℕ} {d d' : DState L} {r₁ r₂ : Fmt.RoundView} {ids : Array ℕ}
    (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) {j : ℕ} {x : Oracle}
    (hx : d.st.oracles[j]? = some x) : d'.st.oracles[j]? = some x := by
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
    (answersIn r₂)).toArray[j]? = _
  rw [List.getElem?_toArray,
    List.getElem?_append_left (by simpa using (Array.getElem?_eq_some_iff.1 hx).1)]
  simpa using hx

/-- The first new message, if it counts an answer, stands with its shape and the fresh ledger of its
shape. -/
theorem sent_new {P : Par} {owed : Option ℕ} {d d' : DState L} {r₁ r₂ : Fmt.RoundView} {ids : Array ℕ}
    (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) {sh : OracleShape} {l : List OracleShape}
    (hs : shapesOf P = sh :: l) (ha : sh.answers ≠ 0) :
    ∃ x, d'.st.oracles[d.st.oracles.size]? = some x ∧ x.shape = sh ∧
      x.ledger = freshLedger P.codes sh := by
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  refine ⟨wr P.codes (seedsOf P r₁) d.st.oracles.size sh (answersIn r₂), ?_, ?_, ?_⟩
  · show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size]? = _
    rw [hs, List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simp [outs]
  · unfold wr
    rw [if_neg ha]
  · unfold wr
    rw [if_neg ha]

/-- The codes in front are the sending's, and they stay. -/
theorem sent_codes {P : Par} {owed : Option ℕ} {d d' : DState L} {r₁ r₂ : Fmt.RoundView} {ids : Array ℕ}
    (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    d.st.codes = P.codes ∧ d'.st.codes = P.codes := by
  obtain ⟨⟨_, hc, _⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  exact ⟨hc, hc⟩

/-- The first new message's number is the number of messages in front. -/
theorem sent_first {P : Par} {owed : Option ℕ} {d d' : DState L} {r₁ r₂ : Fmt.RoundView} {ids : Array ℕ}
    (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (h0 : 0 < P.sent.size) :
    ids[0]? = some d.st.oracles.size := by
  have := ((decideSend_iff P owed d d' r₁ r₂ ids).1 h).2.1
  rw [this]
  simp [h0]

theorem sent_par (one : OneTime) (piece : ℕ) (what : String) (msg : Array OracleNotice)
    (groups : List (List ℕ)) : (sendingPar one piece what msg groups).sent = msg := by
  simp [sendingPar, VerifiableInference.Desc.K1.Par.sent]

theorem shapes_par (one : OneTime) (piece : ℕ) (what : String) (msg : Array OracleNotice)
    (groups : List (List ℕ)) :
    shapesOf (sendingPar one piece what msg groups) = msg.toList.map (·.shape) := by
  unfold shapesOf
  rw [sent_par]

/-! ## The making of the ranges' group -/

/-- A joining leaves the codes, and every message's shape and ledger. -/
theorem joinP_msg {d d' : DState L} {g o : ℕ} {kept : Bool} (h : joinP d g o kept = some d') :
    d'.st.codes = d.st.codes ∧ ∀ (j : ℕ) (x : Oracle), d.st.oracles[j]? = some x →
      ∃ x', d'.st.oracles[j]? = some x' ∧ x'.shape = x.shape ∧ x'.ledger = x.ledger := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨rfl, fun j x hx => ?_⟩
    show ∃ x', (d.st.oracles.modify o fun y => { y with groups := y.groups ++ [g] })[j]? =
      some x' ∧ _
    rw [Array.getElem?_modify, hx]
    split
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl⟩
  · cases h

/-- **What the making of the ranges' group says where it returns.** -/
theorem open_facts {one : OneTime} {m t : ChainState β} (h : openRangesGroup one m = .ok t) :
    t.idx = m.idx ∧ t.base = m.base ∧ m.sent[0]? = some one.ranges.messageId ∧
      t.d.st.codes = m.d.st.codes ∧ ∀ (j : ℕ) (x : Oracle), m.d.st.oracles[j]? = some x →
        ∃ x', t.d.st.oracles[j]? = some x' ∧ x'.shape = x.shape ∧ x'.ledger = x.ledger := by
  unfold openRangesGroup at h
  obtain ⟨_, _, h⟩ := bindX h
  obtain ⟨_, _, h⟩ := bindX h
  obtain ⟨_, _, h⟩ := bindX h
  obtain ⟨_, _, h⟩ := bindX h
  obtain ⟨mm, hm, h⟩ := bindX h
  obtain ⟨_, hq, h⟩ := bindX h
  obtain ⟨g, hg, h⟩ := bindX h
  obtain ⟨d, hd, h⟩ := bindX h
  cases h
  obtain ⟨n, d₀⟩ := g
  have h0 : d₀.st.oracles = m.d.st.oracles ∧ d₀.st.codes = m.d.st.codes := by
    have hg' := namedX hg
    unfold newGroupP at hg'
    split at hg'
    · have e := Option.some.inj hg'
      simp only [Prod.mk.injEq] at e
      rw [← e.2]
      exact ⟨rfl, rfl⟩
    · cases hg'
  obtain ⟨j1, j2⟩ := joinP_msg (namedX hd)
  have hmm : mm = one.ranges.messageId := by simpa using needX hq
  refine ⟨rfl, rfl, hmm ▸ namedX hm, j1.trans h0.2, fun j x hx => j2 j x ?_⟩
  show d₀.st.oracles[j]? = some x
  rw [h0.1]
  exact hx

/-! ## The two steps -/

/-- **Behind the sending of the index-mask message.** -/
structure Half (one : OneTime) (s : FirstState) : Prop where
  idx : s.idx = 0
  idxMsg : ∃ x, s.d.st.oracles[0]? = some x ∧ x.shape = one.indexMasks.shape ∧
    x.ledger = freshLedger one.codes one.indexMasks.shape
  base : s.base = {}

/-- **Behind the sending of the lookups' own message: in front of the first link.** -/
structure Front (one : OneTime) (t : FirstState) : Prop where
  idx : t.idx = 0
  codes : t.d.st.codes = one.codes
  idxMsg : ∃ x, t.d.st.oracles[0]? = some x ∧ x.shape = one.indexMasks.shape ∧
    x.ledger = freshLedger one.codes one.indexMasks.shape
  own : ∃ x, t.d.st.oracles[one.ranges.messageId]? = some x ∧
    x.shape = one.ranges.message.shape ∧
    x.ledger = freshLedger one.codes one.ranges.message.shape
  base : t.base = {}

/-- **The first step**: from the chain's start. -/
theorem idx_step {one : OneTime} {N : Pieces} {groups : List (List ℕ)} {t : FirstState}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (ha : one.indexMasks.shape.answers ≠ 0)
    (h : (sendIndexMasks (Cl := Claim) one N groups).decide (chainStart one.codes {}) [r₁, r₂] gs =
      .ok t) : Half one t := by
  obtain ⟨m, hk, hq⟩ := bindX h
  obtain ⟨ids, d', hd, e1, e2, e3, e4⟩ := seat_sent hk
  obtain ⟨i, hi, hq⟩ := bindX hq
  cases hq
  have hd' : decideSend (sendingPar one N.idx "the index masks" #[one.indexMasks] groups)
      (chainStart one.codes ({} : VerifiableInference.Desc.Key.LookupRecord)).debt
      (withLoc (chainStart one.codes ({} : VerifiableInference.Desc.Key.LookupRecord)).d
        (#[] : Array ℕ)) [r₁, r₂] = .ok (ids, d') := hd
  have hi0 : i = 0 := by
    have h0 := sent_first hd' (by rw [sent_par]; exact Nat.one_pos)
    rw [← e2, namedX hi] at h0
    exact Option.some.inj h0
  obtain ⟨x, hx, hs, hl⟩ := sent_new hd' (sh := one.indexMasks.shape) (l := [])
    (by rw [shapes_par]; rfl) ha
  refine ⟨hi0, ⟨x, ?_, hs, hl⟩, e4⟩
  show m.d.st.oracles[0]? = some x
  rw [e1]
  exact hx

theorem messageOf_first (x : WfPublic) : ∃ l, (Wf.messageOf x).toList = x.message :: l := by
  unfold Wf.messageOf
  split
  · split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **The second step.** -/
theorem msg_step {one : OneTime} {N : Pieces} {groups : List (List ℕ)} {s t : FirstState}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hs : Half one s)
    (ha : one.ranges.message.shape.answers ≠ 0)
    (h : (sendOwnMessage (Cl := Claim) one N groups).decide s [r₁, r₂] gs = .ok t) :
    Front one t := by
  obtain ⟨m, hk, hw⟩ := bindX h
  obtain ⟨ids, d', hd, e1, e2, e3, e4⟩ := seat_sent hk
  have hd' : decideSend (sendingPar one N.msg "the lookups' own message and what rides with it"
      (Wf.messageOf one.ranges) groups) s.debt (withLoc s.d (#[] : Array ℕ)) [r₁, r₂] =
      .ok (ids, d') := hd
  obtain ⟨w1, w2, w3, w4, w5⟩ := open_facts (show openRangesGroup one m = .ok t from hw)
  obtain ⟨lm, hlm⟩ := messageOf_first one.ranges
  have hpos : 0 < (Wf.messageOf one.ranges).size := by
    rw [← Array.length_toList, hlm]
    exact Nat.succ_pos _
  have hsz : one.ranges.messageId = s.d.st.oracles.size := by
    have h0 := sent_first hd' (by rw [sent_par]; exact hpos)
    rw [← e2, w3] at h0
    exact Option.some.inj h0
  obtain ⟨x0, hx0, a0, b0⟩ := hs.idxMsg
  have hx0' : m.d.st.oracles[0]? = some x0 := by
    rw [e1]
    exact sent_old hd' hx0
  obtain ⟨y0, hy0, c0, d0⟩ := w5 0 x0 hx0'
  obtain ⟨x1, hx1, a1, b1⟩ := sent_new hd' (sh := one.ranges.message.shape)
    (l := lm.map (·.shape)) (by rw [shapes_par, hlm]; rfl) ha
  have hx1' : m.d.st.oracles[one.ranges.messageId]? = some x1 := by
    rw [e1, hsz]
    exact hx1
  obtain ⟨y1, hy1, c1, d1⟩ := w5 _ x1 hx1'
  refine ⟨by rw [w1, e3]; exact hs.idx, ?_, ⟨y0, hy0, c0.trans a0, d0.trans b0⟩,
    ⟨y1, hy1, c1.trans a1, d1.trans b1⟩, by rw [w2, e4]; exact hs.base⟩
  rw [w4, e1]
  exact (sent_codes hd').2

/-! ## The promise -/

/-- A message's ledger as its sending opens it. -/
def ledOf (codes : Codes) (s : OracleShape) : Ledger :=
  { next := 0
    left := Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers
    rows := max s.maskRows 1, logRows := ceilLog2 s.maskRows }

theorem fresh_some (codes : Codes) (s : OracleShape) (h : 0 < s.maskRows) :
    freshLedger codes s = some (ledOf codes s) := by
  unfold freshLedger
  rw [if_pos h]
  rfl

theorem tableSize_main {S : Statement} {o : ℕ} {x : Oracle} (hx : S.oracles[o]? = some x)
    (hm : 0 < x.shape.mainRows) : Means.tableSize S o .main =
      2 ^ ((S.codes.base.getD x.shape.code default).logEll + ceilLog2 x.shape.mainRows) := by
  have hne : (x.shape.mainRows == 0) = false := by simpa using Nat.pos_iff_ne_zero.1 hm
  simp only [Means.tableSize, Statement.has, Statement.tableBits, Statement.rowBits,
    Statement.placeBits, hx, OracleShape.rows, hm, decide_true, if_true, hne, Bool.false_eq_true,
    if_false]
  rw [Nat.add_comm]

theorem tableSize_mask {S : Statement} {o : ℕ} {x : Oracle} (hx : S.oracles[o]? = some x)
    (hm : 0 < x.shape.maskRows) : Means.tableSize S o .mask =
      2 ^ ((S.codes.mask.getD x.shape.maskCode default).logEll + ceilLog2 x.shape.maskRows) := by
  have hne : (x.shape.maskRows == 0) = false := by simpa using Nat.pos_iff_ne_zero.1 hm
  simp only [Means.tableSize, Statement.has, Statement.tableBits, Statement.rowBits,
    Statement.placeBits, hx, OracleShape.rows, hm, decide_true, if_true, hne, Bool.false_eq_true,
    if_false]
  rw [Nat.add_comm]

/-- The lookups' own message has a main row. -/
theorem mainRows_pos {codes : Codes} {x : WfPublic} {m : Wf.Matrix}
    (h : Wf.admitted codes x m = true) : 0 < x.message.shape.mainRows := by
  unfold Wf.admitted at h
  simp only [Bool.and_eq_true] at h
  have hl := h.1.1.1.2.2
  cases hb : (Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell).getLast? with
  | none =>
    rw [hb] at hl
    cases hl
  | some b =>
    rw [hb] at hl
    simp only [Option.any_some, beq_iff_eq] at hl
    omega

/-- **FROM Front AND PUBLIC NUMBERS, THE PROMISE IN FRONT OF THE FIRST LINK.** -/
theorem front_promL {one : OneTime} {Ex : FirstState → Prop} {t : FirstState} (h : Front one t)
    (hw : Wf.admitted one.codes one.ranges (Wf.matrixOf one.lin) = true)
    (hR : RoomFor one.ranges (Wf.matrixOf one.lin) one.codes one.indexMasks.shape) (hE : Ex t) :
    PromL one one.ranges.messageId (Wf.matrixOf one.lin) (Lof one) 0
      one.ranges.lookups.length (ledOf one.codes one.ranges.message.shape)
      (ledOf one.codes one.indexMasks.shape) Ex 0 t := by
  obtain ⟨x0, hx0, a0, b0⟩ := h.idxMsg
  obtain ⟨x1, hx1, a1, b1⟩ := h.own
  refine promL_room hR h.idx ?_ ?_ ⟨(Array.getElem?_eq_some_iff.1 hx1).1, ?_⟩
    (Array.getElem?_eq_some_iff.1 hx0).1 rfl rfl rfl rfl rfl rfl ?_ ?_ hE
  · show (t.d.st.oracles[one.ranges.messageId]?).bind (·.ledger) = _
    rw [hx1]
    exact b1.trans (fresh_some _ _ hR.1)
  · show (t.d.st.oracles[0]?).bind (·.ledger) = _
    rw [hx0]
    exact b0.trans (fresh_some _ _ hR.2.1)
  · rw [tableSize_main hx1 (a1 ▸ mainRows_pos hw), a1, h.codes]
    rfl
  · rw [tableSize_mask hx1 (a1 ▸ hR.1), a1, h.codes]
  · rw [tableSize_mask hx0 (a0 ▸ hR.2.1), a0, h.codes]

end Johnson.RunOne.Law.FrontSteps

#print axioms Johnson.RunOne.Law.FrontSteps.seat_sent
#print axioms Johnson.RunOne.Law.FrontSteps.sent_old
#print axioms Johnson.RunOne.Law.FrontSteps.sent_new
#print axioms Johnson.RunOne.Law.FrontSteps.sent_codes
#print axioms Johnson.RunOne.Law.FrontSteps.sent_first
#print axioms Johnson.RunOne.Law.FrontSteps.joinP_msg
#print axioms Johnson.RunOne.Law.FrontSteps.open_facts
#print axioms Johnson.RunOne.Law.FrontSteps.idx_step
#print axioms Johnson.RunOne.Law.FrontSteps.msg_step
#print axioms Johnson.RunOne.Law.FrontSteps.front_promL
