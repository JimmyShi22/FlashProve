-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PileKeptK2.lean: `PileKept` (FHeadH.lean) after the code
switch's accepting step from a state at which the first chain's invariant holds, at the full size:
the hypothesis `hk2` of `head_hbook` (PileKeptPaid.lean). So `relsBook` holds after every
sub-protocol's step with no hypothesis left on a kind (`head_hbook_paid`). No definition.

  1  `k2Where_full`, `k2Where_control`, `k2_number_of`   a closed test by Lean's kernel on the
     written list: a place of the kind K2 stands at the first number of one of the segments 1 to 23,
     at number 339 or at number 353. The negative test: with 352 for 353 it fails
  2  `pileKept_of_left`   the library's `Left` (Johnson/Top/H0/K2Ties/Left.lean: what an accept of
     the code switch leaves of the verifier's state) gives `PileKept`, if the message of the index
     masks is there, has a place in the book, and a tree stands at that place
  3  `pileKept_then_same`   `PileKept`, then a step that leaves the rows, the statement and the book
  4  `k2_left_link`, `k2_left_head`, `k2_left_finish`   an accepting step at the three sorts of
     place gives `Left`; at a segment's first place up to the state before the frame's "opened"
  5  `head_pileKept_k2`, `head_hbook_paid`

Where this comes from. The three lemmas under 4 are `k2_link_head`, `k2_finish_head` (K2AtHead.lean)
and `k2_head_head` (K2AtHeadH.lean) with one call changed: `k2Left_link`, `k2Left_finish`,
`k2Left_head` (Johnson/Desc/K2/Honest/LeftAt.lean, of other authors) in the place of `k2Keeps_link`,
`k2Keeps_finish`, `k2Keeps_head`. The lines before that call stand a second time here. The library's
`seat_left` and `shape_left` (Johnson/Top/H0/K2Ties/Pile.lean) give the last two clauses of
`PileKept`.

Limits.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PileKeptPaid
import Johnson.Desc.ProofFile.Honest.Thread.K2AtHead
import Johnson.Desc.ProofFile.Honest.Thread.K2AtHeadH
import Johnson.Desc.ProofFile.Honest.Thread.OpenedKeepsR
import Johnson.Desc.K2.Honest.LeftAt
import Johnson.Top.H0.K2Ties.Pile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K2Ties (Left seat_left shape_left)
open VerifiableInference.Desc.K2.Honest (k2Left_link k2Left_head k2Left_finish)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (StepYes)
open Johnson.Desc.First.Walk.Seat (framesOf)

set_option maxRecDepth 1000000 in
/-- Where the places of the kind K2 stand. -/
theorem k2Where_full :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K2) || b == 339 || b == 353 ||
        (List.range 24).any fun l => decide (1 ≤ l) && b == 14 * l + 0 + 2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with 352 in the place of 353 the same test fails. -/
theorem k2Where_control :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K2) || b == 339 || b == 352 ||
        (List.range 24).any fun l => decide (1 ≤ l) && b == 14 * l + 0 + 2) = false := by
  decide +kernel

/-- The test at a place. -/
theorem k2_number_of {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K2) :
    b = 339 ∨ b = 353 ∨ ∃ l, 1 ≤ l ∧ l < 24 ∧ b = 14 * l + 0 + 2 := by
  have t := List.all_eq_true.1 k2Where_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  have t' : (b == 339 || b == 353 ||
      (List.range 24).any fun l => decide (1 ≤ l) && b == 14 * l + 0 + 2) = true := t
  rcases Bool.or_eq_true_iff.1 t' with e | e
  · rcases Bool.or_eq_true_iff.1 e with e | e
    · exact Or.inl (eq_of_beq e)
    · exact Or.inr (Or.inl (eq_of_beq e))
  · obtain ⟨l, hl, e⟩ := List.any_eq_true.1 e
    obtain ⟨e1, e2⟩ := Bool.and_eq_true_iff.1 e
    exact Or.inr (Or.inr ⟨l, of_decide_eq_true e1, List.mem_range.1 hl, eq_of_beq e2⟩)

/-- The library's `Left` gives `PileKept`. -/
theorem pileKept_of_left {s s' : S} (hL : Left s s')
    (hi : s.out.indexMasks < s.st.oracles.size) {q : Nat × Nat}
    (hq : s.book.place[s.out.indexMasks]? = some q) (hz : q.1 < s.book.trees.size) :
    PileKept s s' :=
  ⟨hL.rows, hL.grows.1, shape_left hL _ hi, seat_left hL _ q hq hz⟩

/-- `PileKept`, then a step that leaves the rows, the statement and the book. -/
theorem pileKept_then_same {s m s' : S} (h1 : PileKept s m) (hr : s'.rows = m.rows)
    (hst : s'.st = m.st) (hbk : s'.book = m.book) : PileKept s s' := by
  refine ⟨hr.trans h1.1, ?_, ?_, ?_⟩
  · rw [hst]
    exact h1.2.1
  · rw [hst]
    exact h1.2.2.1
  · rw [hbk]
    exact h1.2.2.2

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- At the first place of segment `l`, for `l` from 1 to 23. -/
theorem k2_left_link {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∀ blk, cF.blocksInOrder[14 * l + 0 + 2]? = some blk → ∀ s s', StepYes 0 blk s s' →
      ∃ m : TS, Left s m ∧ keepsOpenedR l m s' := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Z', Bs', base', c', A', B', O', H⟩ :=
    P1K2.k02_sits_pAt h.scope h.reads h.laid.value
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := O.unique O'
  obtain ⟨a1, -, -⟩ := H (H2K12.spots_atAll h (OnBytes.Road.K4.cut_of_head h.toAtMg))
    (P1K2.links25_atAll h)
  obtain ⟨b, hb', hX⟩ := a1 l h1 h24
  obtain rfl : b = blk := Option.some.inj (hb'.symm.trans hb)
  obtain ⟨hst, fs, f, hfs, hf, hS⟩ :=
    hX (P1K2.flat_planOk O h.laid.planOk b (List.mem_of_getElem? hb))
  obtain ⟨R, c, hlen, e⟩ := hy
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step 0 s s' R c c.length e
  obtain rfl : s = t := Except.ok.inj e1
  exact ⟨t', k2Left_link hst ⟨R, c, by rw [← hS.rounds]; exact hlen, e2⟩,
    keepsOpenedR_of hfs hf (P1K2.leaveOpened_is e3) (P1K2.leaveOpened_unmarked e3)⟩

include h in
/-- At number 353, after the last segment. -/
theorem k2_left_finish :
    ∀ blk, cF.blocksInOrder[353]? = some blk → ∀ s s', StepYes 0 blk s s' → Left s s' := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, q, e0, hq, hU⟩ := IM.k2_finish_under O
  obtain ⟨b₂, y, e0', -, -, hla, -⟩ := IM.k2_finish_of O
  obtain rfl : b₂ = b := Option.some.inj (e0'.symm.trans e0)
  obtain ⟨hfr, h352⟩ := IM.links_flat_352 h.scope h.reads O
  have hf := IM.back_at_flat e0
  rw [hfr, h352] at hf
  have hf' : cF.blocksInOrder[353]? = some { b₂ with planOk := b₂.planOk && b₂.hasNoClaimsAndNothingAfter } := hf
  obtain rfl := Option.some.inj (hf'.symm.trans hb)
  exact k2Left_finish hq
    (fun s rs gs t d => ⟨hU s rs gs t d, (IM.alone_noMark hla d).2⟩) hy

include h in
/-- At number 339, in the output head's segment. -/
theorem k2_left_head :
    ∀ blk, cF.blocksInOrder[339]? = some blk → ∀ s s', StepYes 0 blk s s' → Left s s' := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, hx, hla, his⟩ := IM.k2_head_of h.scope h.reads O
  have hb1 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by decide) 1] at hb1
  have hb2 : cF.blocksInOrder[339]? = some b := hb1
  obtain rfl : b = blk := Option.some.inj (hb2.symm.trans hb)
  have hp := P1K2.flat_planOk O h.laid.planOk b (List.mem_of_getElem? hb)
  rw [IM.alone_planOk hla] at hp
  have hyp : y.planOk = true := (IM.retype_planOk y hp).1
  have hpl := P1K2.place_of_is his hyp
  obtain ⟨Q, n, -, -, e, arms⟩ := VerifiableInference.Desc.First.K2Caller.seated_is_pAt O.blank
    (H2K12.spots_atAll h (OnBytes.Road.K4.cut_of_head h.toAtMg)) hx hyp
  have hst : (ProofFile.pAtK2 Zp (n.grp - 1)).stands = .head := by
    rw [e, hpl, P1K2.links25_atAll h]
    rfl
  rcases arms with ⟨h0, -⟩ | ⟨-, l', HP, -, -, hy'⟩ | ⟨h0, -⟩
  · rw [hst] at h0
    cases h0
  · refine k2Left_head hst y.name y.place HP (fun s rs gs t d => ?_) hy
    obtain ⟨d1, hm⟩ := IM.alone_noMark hla d
    have d2 : y.decide s rs gs = .ok t := d1
    rw [hy'] at d2
    exact ⟨d2, hm⟩
  · rw [hst] at h0
    cases h0

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **`PileKept` after the step at a place of the kind K2.** -/
theorem head_pileKept_k2 :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      blk.place.kind = KindName.K2 → PileKept s s' := by
  intro b hb blk hblk k s m E ds y cols s' hA hd hS hk
  have hb' : b < 358 := by
    have e : b < cF.blocksInOrder.length := hb
    rw [head_len h] at e
    exact e
  have hlen : b ≤ cF.blocksInOrder.length := Nat.le_of_lt hb
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk
  have hy :=
    stepYes_of_stepped (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread hd hS
  have hn := k2_number_of hb' hp hk
  have h3 : 3 ≤ b := by
    rcases hn with e | e | ⟨l, h1, -, e⟩ <;> omega
  have hi := (head_seat_some h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w h3 (by omega) hA.1).1
  have hpl : s.out.indexMasks < s.book.place.size := by
    rw [(head_book h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA.1).2]
    exact hi
  have hq := Array.getElem?_eq_getElem hpl
  have hz := head_hold h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hA.1 _ _ hq
  rcases hn with rfl | rfl | ⟨l, h1, h24, rfl⟩
  · exact pileKept_of_left (k2_left_head h blk hblk s s' hy) hi hq hz
  · exact pileKept_of_left (k2_left_finish h blk hblk s s' hy) hi hq hz
  · obtain ⟨m', hL, ho⟩ := k2_left_link h h1 h24 blk hblk s s' hy
    exact pileKept_then_same (pileKept_of_left hL hi hq hz) ho.2 (keepsOpened_st ho.1)
      (keepsOpened_book ho.1)

/-- **`relsBook` after every sub-protocol's step.** -/
theorem head_hbook_paid {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      relsBook blk.place.kind s s' :=
  head_hbook h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB
    (head_pileKept_k2 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k2Where_full
#print axioms ProofFile.Honest.FirstThread.k2Where_control
#print axioms ProofFile.Honest.FirstThread.k2_number_of
#print axioms ProofFile.Honest.FirstThread.pileKept_of_left
#print axioms ProofFile.Honest.FirstThread.pileKept_then_same
#print axioms ProofFile.Honest.FirstThread.k2_left_link
#print axioms ProofFile.Honest.FirstThread.k2_left_finish
#print axioms ProofFile.Honest.FirstThread.k2_left_head
#print axioms ProofFile.Honest.FirstThread.head_pileKept_k2
#print axioms ProofFile.Honest.FirstThread.head_hbook_paid
