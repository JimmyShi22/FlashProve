-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PileKeptPaid.lean: the relation `relsBook` (FHeadH.lean) after
a sub-protocol's accepting step from a state at which the first chain's invariant holds, at the full
size. It is what `fHeadH` asks of `keeps` beyond `fHeadG`: `PileKept` at the kinds K2, K7 and K12.
At K7 and K12 it is proved here from lemmas of the kinds' authors; at K2 it is left as a hypothesis.
No definition.

  1  `k12Where_full`, `k12Where_control`, `k12_number_of`   a closed test by Lean's kernel on the
     written list: a place of the kind K12 stands at number 354. The negative test: with 353 it
     fails
  2  `head_seat_some`   where the invariant holds, from border 3 on, the message of the index masks
     has a seat by the book
  3  `pileKept_of_extends`   `PileKept` where the rows and the book stay and the statement after the
     step extends the one before
  4  `head_pileKept_k7`, `head_pileKept_k12`   after the step at the kinds K7 and K12
  5  `head_hbook`   `relsBook` after every sub-protocol's step, from `PileKept` at K2

Called, of other authors: `k7_rows_at` (Johnson/Desc/Kinds/Honest/Law/K7Rows.lean): the step at
number 338 leaves the rows. `four_at_354` (Johnson/Desc/K12/Honest/Shape/TestKeepsPile.lean): the
step at number 354 gives the four clauses of `PileKept`, if the message of the index masks is there
and has a seat. Of ours: `fHead_hK_whole` (FHeadKeepsWhole.lean), `k7KeepsAt_pile`
(PileCellsEqK7.lean), `head_index` (HeadFences.lean), `head_book`, `head_hold`
(RowPileForwardKinds.lean), `stepYes_of_stepped` (SteppedYes.lean).

Limits.
  * `hk2`: `PileKept` after the step at the 25 places of the kind K2 is a hypothesis.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadH
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsWhole
import Johnson.Desc.ProofFile.Honest.Thread.PileCellsEqK7
import Johnson.Desc.Kinds.Honest.Law.K7Rows
import Johnson.Desc.K12.Honest.Shape.TestKeepsPile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT seatBy noFirst seatBy_some)
open OnBytes.Means (Extends)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

set_option maxRecDepth 1000000 in
/-- A place of the kind K12 stands at number 354. -/
theorem k12Where_full :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K12) || b == 354) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with 353 in the place of 354 the same test fails. -/
theorem k12Where_control :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K12) || b == 353) = false := by
  decide +kernel

/-- The test at a place. -/
theorem k12_number_of {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K12) : b = 354 := by
  have t := List.all_eq_true.1 k12Where_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  exact eq_of_beq (show (b == 354) = true from t)

/-- `PileKept` where the rows and the book stay and the statement extends. -/
theorem pileKept_of_extends {s s' : S} (hr : s'.rows = s.rows) (hE : Extends s.st s'.st)
    (hlt : s.out.indexMasks < s.st.oracles.size) (hb : s'.book = s.book) : PileKept s s' :=
  ⟨hr, hE.codes, shape_of_extends hE hlt, by rw [hb]⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- Where the invariant holds, from border 3 on, the message of the index masks has a seat. -/
theorem head_seat_some {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (h3 : 3 ≤ b) (h358 : b ≤ 358)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    s.out.indexMasks < s.st.oracles.size ∧
      (seatBy noFirst s.book s.out.indexMasks).isSome = true := by
  have hi := head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT (open_pinI h3 h358)
  have hlen : b ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    exact h358
  have hp : s.out.indexMasks < s.book.place.size := by
    rw [(head_book h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT).2]
    exact hi
  have hq := Array.getElem?_eq_getElem hp
  have ht := head_hold h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT _ _ hq
  refine ⟨hi, ?_⟩
  rw [seatBy_some noFirst s.book _ _ _ hq (Array.getElem?_eq_getElem ht)]
  rfl

variable (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **`PileKept` after the step at the place of the kind K7.** -/
theorem head_pileKept_k7 {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      blk.place.kind = KindName.K7 → PileKept s s' := by
  intro b hb blk hblk k s m E ds y cols s' hA hd hS hk
  have hb' : b < 358 := by
    have e : b < cF.blocksInOrder.length := hb
    rw [head_len h] at e
    exact e
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk
  obtain rfl := k7_number_of hb' hp hk
  have a := fHead_hK_whole h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB 338 hb blk hblk k s
    m E ds y cols s' hA hd hS
  rw [hk] at a
  obtain ⟨e2, e3⟩ := k7KeepsAt_pile (G := Bs.G₀) (p := blk.place) a
  exact pileKept_of_extends
    (H2K7.k7_rows_at h blk hblk s s'
      (stepYes_of_stepped (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread hd hS))
    e2 (head_seat_some h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) (by omega) hA.1).1 e3

/-- **`PileKept` after the step at the place of the kind K12.** -/
theorem head_pileKept_k12 :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      blk.place.kind = KindName.K12 → PileKept s s' := by
  intro b hb blk hblk k s m E ds y cols s' hA hd hS hk
  have hb' : b < 358 := by
    have e : b < cF.blocksInOrder.length := hb
    rw [head_len h] at e
    exact e
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk
  obtain rfl := k12_number_of hb' hp hk
  obtain ⟨hi, hs⟩ := head_seat_some h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (b := 354) (by omega)
    (by omega) hA.1
  exact ProofFile.Honest.Sh.four_at_354 h.toAtMg hblk 0 s s'
    (stepYes_of_stepped (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread hd hS) hi hs

/-- **`relsBook` after every sub-protocol's step**, from `PileKept` at K2. -/
theorem head_hbook {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hk2 : ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
        ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
        ∀ k s m E ds y cols s',
        ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
        drawsFit blk.rounds ds = true →
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
          cols s' →
        blk.place.kind = KindName.K2 → PileKept s s') :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      relsBook blk.place.kind s s' := by
  intro b hb blk hblk k s m E ds y cols s' hA hd hS
  cases hκ : blk.place.kind with
  | K2 => exact hk2 b hb blk hblk k s m E ds y cols s' hA hd hS hκ
  | K7 =>
    exact head_pileKept_k7 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB b hb blk hblk k s m
      E ds y cols s' hA hd hS hκ
  | K12 =>
    exact head_pileKept_k12 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said b hb blk hblk k s m E
      ds y cols s' hA hd hS hκ
  | _ => trivial

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k12Where_full
#print axioms ProofFile.Honest.FirstThread.k12Where_control
#print axioms ProofFile.Honest.FirstThread.k12_number_of
#print axioms ProofFile.Honest.FirstThread.pileKept_of_extends
#print axioms ProofFile.Honest.FirstThread.head_seat_some
#print axioms ProofFile.Honest.FirstThread.head_pileKept_k7
#print axioms ProofFile.Honest.FirstThread.head_pileKept_k12
#print axioms ProofFile.Honest.FirstThread.head_hbook
