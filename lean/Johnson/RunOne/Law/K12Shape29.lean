-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Shape29.lean: ROW 2.9 OF THE KEY FILE's TABLES (the shared chain's block 9: the proximity test on G_u): THE BOOK-KEEPING's STEP: shape₂ at border 9 in front gives shape₂ at border 10 behind, at a yes of the seated test. Statements with proofs.
OBJECT. LKFU.Shape23.shape₂ (Johnson/RunOne/BorderShapes/LKFU/Shape23.lean, at the tables' files, which ask «the book is in order»: eighteen named clauses) and Seat.onGu (proximityTestKind guardedProximityTestParts p) (Johnson/Desc/K12/Seat.lean). USER. Johnson/RunOne/Law/K12Fwd29.lean.
LETTERS. S a p d d' rs gs: free. Premises: early · answers = 1 · the yes · hst: the test's own number of stages is the shape's (S.testU.length) · hft: the place's first tree's number is 0 · ha1: the answers to a sample are 1 (the tables' letter a; the kind's law says «one sample row») · h9: the book-keeping in front.
CLAUSE BY CLAUSE: the form: no state · the counts of messages and groups: OutK2 · of trees and roots: Johnson/RunOne/Law/K12Trees.lean with oneTree_all · statement and book in step: OutK3 · seven clauses on the chain's local state (loc): the seat's door out does not write it · the elder messages' marks, the first mask's «spent», the later stages' messages and groups: Johnson/RunOne/Law/K12Tower.lean · G_u begun, G_omega untouched: OutK2.begunG | others · the split's ledger shut with «left» unturned: closeLedgers_get here · the book in order: onGu_bookStep (Johnson/Desc/K12/Coin/BookThrough.lean).
  shut · closeLedgers_get: what the closing of ledgers does to each message, to the letter. msgIs_congr · msgIs_tgt · msgIs_rdr · grpIs_grp · tower_of: the tables' Bools from the kind's law's words.
  seat_yes: a yes of a test seated by Seat.enter | Seat.leave, written out. shape₂_9_10.
Limits. A block that says no to all meets every statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Tower
import Johnson.RunOne.Law.K12Trees
import Johnson.RunOne.Law.K12OneTree
import Johnson.RunOne.BorderShapes.LKFU.Shape23
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.Coin.BookThrough
import Johnson.Desc.Sound.BookInOrder
import Johnson.RunOne.KeyBookAtSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Shape29
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Out
open LKFU.Shape23
open VerifiableInference.Desc.Sound (bookStepB BookStep bookStep_iff)
open Johnson.RunOne.Law.K12Tower (mk Tgt Rdr Grp Tower k12_tower begun_mk spent)
open Johnson.RunOne.Law.K12Trees (k12_trees k12_roots)
open Johnson.RunOne.Law.K12OneTree (oneTree_all)

/-- A message with its ledger, if it has one, shut. -/
abbrev shut (x : OnBytes.Oracle) : OnBytes.Oracle := { x with ledger := x.ledger.map fun l => { l with closed := true } }

theorem shut_shut (x : OnBytes.Oracle) : shut (shut x) = shut x := by
  cases x with
  | mk sh sa sr pa gr le sp =>
    cases le with
    | none => rfl
    | some l => rfl

/-- **What the closing of ledgers does to each message, to the letter.** -/
theorem closeLedgers_get : ∀ (l : List ℕ) (S : Statement) (o : ℕ),
    (closeLedgers S l).oracles[o]? = if o ∈ l then (S.oracles[o]?).map shut else S.oracles[o]?
  | [], _, _ => by simp [closeLedgers]
  | a :: l, S, o => by
    show (closeLedgers { S with oracles := S.oracles.modify a shut } l).oracles[o]? = _
    rw [closeLedgers_get l]
    show (if o ∈ l then ((S.oracles.modify a shut)[o]?).map shut else (S.oracles.modify a shut)[o]?) = _
    rw [Array.getElem?_modify]
    by_cases hao : a = o
    · subst hao
      rw [if_pos rfl, if_pos List.mem_cons_self]
      split
      · cases S.oracles[a]? with
        | none => rfl
        | some x => exact congrArg some (shut_shut x)
      · rfl
    · rw [if_neg hao]
      have e : (o ∈ a :: l) ↔ o ∈ l := by
        rw [List.mem_cons]
        exact ⟨fun h => h.elim (fun e => absurd e.symm hao) id, Or.inr⟩
      simp only [e]

/-- The tables' test on a message reads its three marks alone. -/
theorem msgIs_congr (st st' : Statement) (o : ℕ) (s : Option ℕ) (sp : Bool) (h : (st'.oracles[o]?).map mk = (st.oracles[o]?).map mk) :
    msgIs st' o s sp = msgIs st o s sp := by
  unfold msgIs
  cases hx : st.oracles[o]? with
  | none =>
    rw [hx] at h
    cases hx' : st'.oracles[o]? with
    | none => rfl
    | some x' =>
      rw [hx'] at h
      cases h
  | some x =>
    rw [hx] at h
    cases hx' : st'.oracles[o]? with
    | none =>
      rw [hx'] at h
      cases h
    | some x' =>
      rw [hx'] at h
      have e : mk x' = mk x := Option.some.inj h
      have e1 : x'.sampled = x.sampled := congrArg (·.1) e
      have e2 : x'.sampleRows = x.sampleRows := congrArg (·.2.1) e
      have e3 : x'.spentAsMask = x.spentAsMask := congrArg (·.2.2) e
      cases s with
      | none => simp only [e1, e2, e3]
      | some a => simp only [e1, e2, e3]

theorem msgIs_tgt (st : Statement) (o : ℕ) (h : Tgt st o) : msgIs st o (some 1) false = true := by
  obtain ⟨x, hx, x1, x2, x3⟩ := h
  unfold msgIs
  rw [hx]
  simp [x1, x2, x3]

theorem msgIs_rdr (st : Statement) (o : ℕ) (sp : Bool) (h : Rdr st o sp) : msgIs st o none sp = true := by
  obtain ⟨x, hx, x1, x2, x3⟩ := h
  unfold msgIs
  rw [hx]
  simp [x1, x2, x3]

theorem rdr_of_msgIs (st : Statement) (o : ℕ) (sp : Bool) (h : msgIs st o none sp = true) : Rdr st o sp := by
  unfold msgIs at h
  cases hx : st.oracles[o]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    exact ⟨x, hx, h.1.1, by simpa using h.1.2, h.2⟩

theorem grpIs_grp (st : Statement) (g o : ℕ) (h : Grp st g o) : grpIs st g [o] 0 0 true = true := by
  obtain ⟨G, hG, g1, g2, g3⟩ := h
  unfold grpIs
  rw [hG]
  simp [g1, g2, g3, plainRows, genRows]

/-- **The tables' tower from the kind's law's words.** -/
theorem tower_of (st : Statement) (m₀ g₀ s : ℕ)
    (h : ∀ i, i < s - 1 → Tgt st (m₀ + 2 * i) ∧ Rdr st (m₀ + 2 * i + 1) true ∧ Grp st (g₀ + i) (m₀ + 2 * i)) : towerIs st m₀ g₀ s 1 = true := by
  unfold towerIs
  rw [List.all_eq_true]
  intro j hj
  obtain ⟨a, b, c⟩ := h j (List.mem_range.1 hj)
  rw [msgIs_tgt _ _ a, msgIs_rdr _ _ _ b, grpIs_grp _ _ _ c]
  rfl

/-- **A yes of a test seated by Seat.enter and Seat.leave, written out.** -/
theorem seat_yes (g : _root_.Desc.K14.Lin → ℕ) (mask : _root_.Desc.K14.Lin → Option ℕ) (p : P12) (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs = .ok d') :
    ∃ tE, (proximityTestKind guardedProximityTestParts p : Blk').decide { st := d.st, book := d.book, roots := d.roots, g := g d.loc, pass := .nothing, mask := mask d.loc } rs gs = .ok tE ∧
      d' = { d with st := tE.st, book := tE.book, roots := tE.roots } := by
  have h' : ((Seat.enter g mask d).bind fun t => ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  exact ⟨t', ht', rfl⟩

theorem grpIs_members (st : Statement) (g : ℕ) (ms : List ℕ) (p q : ℕ) (r : Bool) (h : grpIs st g ms p q r = true) :
    ∃ G, st.groups[g]? = some G ∧ G.members.toList = ms := by
  unfold grpIs at h
  cases hG : st.groups[g]? with
  | none =>
    rw [hG] at h
    cases h
  | some G =>
    rw [hG] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨G, rfl, h.1.1.1.1⟩

theorem grpIs_begun (st : Statement) (g : ℕ) (ms : List ℕ) (G : Group) (hG : st.groups[g]? = some { G with inRun := true, rows := #[] })
    (hm : G.members.toList = ms) : grpIs st g ms 0 0 true = true := by
  unfold grpIs
  rw [hG]
  simp [hm, plainRows, genRows]

theorem grpIs_congr (st st' : Statement) (g : ℕ) (ms : List ℕ) (p q : ℕ) (r : Bool) (h : st'.groups[g]? = st.groups[g]?) :
    grpIs st' g ms p q r = grpIs st g ms p q r := by
  unfold grpIs
  rw [h]

/-- The state that a seat hands the test. -/
abbrev recS (d : _root_.Desc.K14.St) (g : ℕ) (m : Option ℕ) : T12 := { st := d.st, book := d.book, roots := d.roots, g := g, pass := .nothing, mask := m }

/-- **The book-keeping's step across the test on G_u.** -/
theorem shape₂_9_10 (S : LinShape) (a : ℕ) (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') (hst : p.nums.stages.length = S.testU.length) (hft : p.nums.firstTree = 0)
    (ha1 : a = 1) (h9 : ok (shape₂ S a 9 d) = true) : ok (shape₂ S a 10 d') = true := by
  subst ha1
  have bk := (VerifiableInference.Desc.K12.Coin.onGu_bookStep p he ha d d' rs gs h (by
    rw [hft]
    exact Johnson.RunOne.KeyRows23.bookStep_of_shape₂ S 1 9 d h9)).1
  rw [hft] at bk
  simp [ok, shape₂] at h9
  obtain ⟨c1, c2, c3, ⟨c4, c4'⟩, c5, c6, ⟨c7, c7'⟩, ⟨c8, c8'⟩, ⟨c9, c9'⟩, c10, ⟨c11, c11'⟩, c12, c13, c14, c15, _⟩ := h9
  obtain ⟨tE, hy, rfl⟩ := seat_yes (·.gU) (·.firstMask) p d d' rs gs h
  have hy' : (proximityTestKind guardedProximityTestParts p : Blk').decide (recS d 0 (some 1)) rs gs = .ok tE := by
    have e : (recS d 0 (some 1)) = { st := d.st, book := d.book, roots := d.roots, g := d.loc.gU, pass := .nothing, mask := d.loc.firstMask } := by
      rw [c7, c8']
    rw [e]
    exact hy
  obtain ⟨G, T⟩ := k12_tower p he ha (recS d 0 (some 1)) tE rs gs hy' 1 rfl
  obtain ⟨G2, K2⟩ := k12_out2 p he ha (recS d 0 (some 1)) tE rs gs hy'
  obtain rfl : G = G2 := Option.some.inj (T.was.symm.trans K2.was)
  have K1 := k12_out p he ha (recS d 0 (some 1)) tE rs gs hy'
  have K3 := k12_out3 p he ha (recS d 0 (some 1)) tE rs gs hy'
  have tr : tE.book.trees.size = d.book.trees.size + (p.nums.stages.length - 1) :=
    k12_trees p he ha (recS d 0 (some 1)) tE rs gs hy' (fun nx last lay h => oneTree_all _ nx last lay h) 1 rfl
  have ro : tE.roots = d.roots + (p.nums.stages.length - 1) :=
    k12_roots p he ha (recS d 0 (some 1)) tE rs gs hy' (fun nx last lay h => oneTree_all _ nx last lay h) 1 rfl
  have o1 : tE.st.oracles.size = d.st.oracles.size + 0 + 2 * (p.nums.stages.length - 1) := K2.oraclesN
  have g1 : tE.st.groups.size = d.st.groups.size + (p.nums.stages.length - 1) := K2.groupsN
  have hwas : d.st.groups[0]? = some G := T.was
  obtain ⟨G0, hG0, hmem⟩ := grpIs_members _ _ _ _ _ _ c13
  obtain rfl : G0 = G := Option.some.inj (hG0.symm.trans hwas)
  have old : ∀ o, o < 4 → o ≠ 1 → tE.st.oracles[o]? = (begun d.st 0 G0).oracles[o]? := fun o ho hne => T.old o (by
    show o < d.st.oracles.size
    rw [c2]
    exact ho) hne
  have oldmk : ∀ o, o < 4 → o ≠ 1 → (tE.st.oracles[o]?).map mk = (d.st.oracles[o]?).map mk := fun o ho hne => by
    rw [old o ho hne]
    exact begun_mk _ _ _ _
  have later : ∀ i, i < S.testU.length - 1 → Tgt tE.st (4 + 2 * i) ∧ Rdr tE.st (4 + 2 * i + 1) true ∧ Grp tE.st (2 + i) (4 + 2 * i) := by
    intro i hi
    have k := T.later i (by rw [hst]; exact hi)
    have e1 : (recS d 0 (some 1)).st.oracles.size = 4 := c2
    have e2 : (recS d 0 (some 1)).st.groups.size = 2 := c3
    rw [e1, e2] at k
    exact k
  simp [ok, shape₂]
  refine ⟨c1, by omega, by omega, ⟨by omega, by omega⟩, K3.step, c6, ⟨c7, c7'⟩, ⟨c8, c8'⟩, ⟨?_, ?_⟩, c10, ⟨?_, ?_⟩, c12, ?_, ?_, ?_, ?_, ?_⟩
  · rw [msgIs_congr d.st tE.st 0 _ _ (oldmk 0 (by omega) (by omega))]
    exact c9
  · obtain ⟨x, hx, x1, x2, x3⟩ := rdr_of_msgIs _ _ _ c9'
    have e : ((begun d.st 0 G0).oracles[1]?).map mk = some (false, #[], false) := by
      rw [begun_mk, hx]
      show some (x.sampled, x.sampleRows, x.spentAsMask) = _
      rw [x1, x2, x3]
    obtain ⟨x', hx', y1, y2, _⟩ := Johnson.RunOne.Law.K12Tower.of_mk e
    refine msgIs_rdr _ _ _ ⟨spent x', ?_, y1, y2, rfl⟩
    have k : tE.st.oracles[1]? = ((begun d.st 0 G0).oracles[1]?).map spent := T.mask
    rw [k, hx']
    rfl
  · rw [msgIs_congr d.st tE.st 2 _ _ (oldmk 2 (by omega) (by omega))]
    exact c11
  · rw [msgIs_congr d.st tE.st 3 _ _ (oldmk 3 (by omega) (by omega))]
    exact c11'
  · exact grpIs_begun _ _ _ G0 K2.begunG hmem
  · rw [grpIs_congr d.st tE.st 1 _ _ _ _ (K2.others 1 (by
      show 1 < d.st.groups.size
      omega) Nat.one_ne_zero)]
    exact c14
  · have e3 : tE.st.oracles[3]? = (d.st.oracles[3]?).map shut := by
      rw [old 3 (by omega) (by omega)]
      show (closeLedgers d.st G0.members.toList).oracles[3]? = _
      rw [closeLedgers_get, hmem, if_pos (by simp)]
    have ec : tE.st.codes = d.st.codes := K1.codes
    rw [e3, ec]
    cases hx : d.st.oracles[3]? with
    | none =>
      rw [hx] at c15
      simp at c15
    | some x =>
      rw [hx] at c15
      cases hL : x.ledger with
      | none => simp [hL] at c15
      | some L =>
        simp [hL] at c15 ⊢
        exact c15.2
  · exact tower_of _ _ _ _ later
  · exact (bookStep_iff 0 _ _).2 bk

end Johnson.RunOne.Law.K12Shape29

#print axioms Johnson.RunOne.Law.K12Shape29.shape₂_9_10
#print axioms Johnson.RunOne.Law.K12Shape29.closeLedgers_get
#print axioms Johnson.RunOne.Law.K12Shape29.msgIs_congr
#print axioms Johnson.RunOne.Law.K12Shape29.tower_of
#print axioms Johnson.RunOne.Law.K12Shape29.seat_yes
