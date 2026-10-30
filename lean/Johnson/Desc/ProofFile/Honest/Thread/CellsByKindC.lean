-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CellsByKindC.lean: the hypothesis `RidesPastAtS`
(Honest/Thread/SharesS.lean) for the open items `pile` and `row m c` of the first chain's invariant
at the places of the kinds K1, K10 and K11, and for `pinW` and `constr m q` at every place, stated
by the kind of the place as in CellsByKind.lean and CellsByKindB.lean. The invariant's `keeps` is
`kpBy fHeadG` (FHeadG.lean). No definition.

  1  `k1Where_full`, `k1Where_control`   a closed test by Lean's kernel on the written list: a place
     of the kind K1 in the first case of `fHead`'s clause stands at number 2, one in the second case
     at number 356, every other at a number from 3 on. The negative test: with 3 for 2 it fails
  2  `k1Ends_full`, `k1Ends_control`   a closed test: no item `row` is open before number 2, and
     neither `pile` nor an item `row` before number 356. The negative test: with `unmarked` barred
     too it fails
  3  `head_arm`   what `keeps` says at a place, where `keeps` is `fHead`
  4  `cell_pinW`, `cell_constr4`, `cell_constr_digits`   at every place
  5  `cell_pile_k11`, `cell_row_k11`, `cell_pile_k10`   at K11 and K10
  6  `cell_pile_k1`, `cell_row_k1`   at K1

The cells are calls: `ridesPastAt_pinW` (HeadPinW.lean), `ridesPastAt_constr4`
(Law/NoHouse/FrameCells.lean), `ridesPastAt_constr_lookDigits` (ConstrDigitsRides.lean),
`rides_of_quiet` (CellsQuiet.lean) with `k11Keeps_st`, `k11Keeps_book`, `k11Keeps_rows`,
`ridesPastAt_pile_k10_at`, `ridesPastAt_pile_k1_at`, `ridesPastAt_row_k1_at`
(RowPileForwardKinds.lean), `ridesPastAt_pile_two` (PileFirst.lean).

Limits.
  * Not treated: `pile` at K2, K7 and K12.
  * Nothing here shows that an item's statement holds at any state of a run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CellsQuiet
import Johnson.Desc.ProofFile.Honest.Thread.CellsByKind
import Johnson.Desc.ProofFile.Honest.Thread.K11RowPile
import Johnson.Desc.ProofFile.Honest.Thread.PileFirst
import Johnson.Desc.ProofFile.Honest.Thread.ConstrDigitsRides
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item RowClass)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

set_option maxRecDepth 1000000 in
/-- Where the places of the kind K1 stand, by the three cases of `fHead`'s clause. -/
theorem k1Where_full :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K1) ||
        (if p.link == some 0 && p.piece == 1 then b == 2
          else if p.link == none && p.piece == 4 then b == 356 else decide (3 ≤ b))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with 3 in the place of 2 the same test fails. -/
theorem k1Where_control :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K1) ||
        (if p.link == some 0 && p.piece == 1 then b == 3
          else if p.link == none && p.piece == 4 then b == 356 else decide (3 ≤ b))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- What is not open before the numbers 2 and 356. -/
theorem k1Ends_full :
    (((IM.openAt P5J.At.links P5J.At.ps 2).all fun i =>
        match i with
        | .row _ _ => false
        | _ => true) &&
      (IM.openAt P5J.At.links P5J.At.ps 356).all fun i =>
        match i with
        | .row _ _ => false
        | .pile => false
        | _ => true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with `unmarked` barred too the same test fails. -/
theorem k1Ends_control :
    (((IM.openAt P5J.At.links P5J.At.ps 2).all fun i =>
        match i with
        | .row _ _ => false
        | .unmarked => false
        | _ => true) &&
      (IM.openAt P5J.At.links P5J.At.ps 356).all fun i =>
        match i with
        | .row _ _ => false
        | .pile => false
        | _ => true) = false := by
  decide +kernel

/-- The first test at a place. -/
theorem k1_where {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K1) :
    (p.link = some 0 ∧ p.piece = 1 → b = 2) ∧
      (¬ (p.link = some 0 ∧ p.piece = 1) → p.link = none ∧ p.piece = 4 → b = 356) ∧
      (¬ (p.link = some 0 ∧ p.piece = 1) → ¬ (p.link = none ∧ p.piece = 4) → 3 ≤ b) := by
  have t := List.all_eq_true.1 k1Where_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  have t' : (if p.link == some 0 && p.piece == 1 then b == 2
      else if p.link == none && p.piece == 4 then b == 356 else decide (3 ≤ b)) = true := t
  by_cases c1 : p.link = some 0 ∧ p.piece = 1
  · have e1 : (p.link == some 0 && p.piece == 1) = true := by
      rw [c1.1, c1.2]
      rfl
    rw [if_pos e1] at t'
    exact ⟨fun _ => eq_of_beq t', fun n => absurd c1 n, fun n => absurd c1 n⟩
  · have e1 : ¬ (p.link == some 0 && p.piece == 1) = true := fun e =>
      c1 ⟨eq_of_beq (Bool.and_eq_true_iff.1 e).1, eq_of_beq (Bool.and_eq_true_iff.1 e).2⟩
    rw [if_neg e1] at t'
    by_cases c2 : p.link = none ∧ p.piece = 4
    · have e2 : (p.link == none && p.piece == 4) = true := by
        rw [c2.1, c2.2]
        rfl
      rw [if_pos e2] at t'
      exact ⟨fun c => absurd c c1, fun _ _ => eq_of_beq t', fun _ n => absurd c2 n⟩
    · have e2 : ¬ (p.link == none && p.piece == 4) = true := fun e =>
        c2 ⟨eq_of_beq (Bool.and_eq_true_iff.1 e).1, eq_of_beq (Bool.and_eq_true_iff.1 e).2⟩
      rw [if_neg e2] at t'
      exact ⟨fun c => absurd c c1, fun _ c => absurd c c2, fun _ _ => of_decide_eq_true t'⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- What `keeps` says at a place of a given kind, where `keeps` is `fHead`. -/
theorem head_arm {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) {κ : KindName}
    (hk : p.kind = κ) {s s' : TS}
    (hK : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps b s s') :
    fHead Zp cF G take P11 p12 P13 κ p s s' := by
  have a : fHead Zp cF G take P11 p12 P13 p.kind p s s' :=
    (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w hp s s').1 hK
  rw [hk] at a
  exact a

/-- The item `pinW` at every number. -/
theorem cell_pinW (b : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.pinW :=
  ridesPastAtS_of _ _ (ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w b)

/-- The item `constr m q` at every number, for the four parts of the library's `P5J.parts4`. -/
theorem cell_constr4 (b m : Nat) {q : P5J.TPart} (hq : q ∈ parts4) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.constr m q) :=
  ridesPastAtS_of _ _ (ridesPastAt_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w b m hq)

/-- The item `constr m lookDigits` at every number. -/
theorem cell_constr_digits (b m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.constr m .lookDigits) :=
  ridesPastAtS_of _ _ (ridesPastAt_constr_lookDigits h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w b m)

/-- At K11 the clause leaves the statement, the book of trees and the rows on the table. -/
theorem head_quiet_k11 {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K11) (s s' : TS)
    (hK : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps b s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  have a : Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAt P11 p s s' :=
    head_arm h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 hp hk hK
  exact ⟨k11Keeps_st a.2.1, k11Keeps_book a.2.1, k11Keeps_rows a.2.1⟩

/-- The item `pile` at a place of the kind K11. -/
theorem cell_pile_k11 {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K11) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.pile :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _ (rides_of_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (head_quiet_k11 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 hp hk)).1)

/-- The item `row m c` at a place of the kind K11. -/
theorem cell_row_k11 {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K11) (m : Nat) (c : RowClass) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.row m c) :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _ ((rides_of_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (head_quiet_k11 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 hp hk)).2.2.2 m c))

/-- The item `pile` at a place of the kind K10. -/
theorem cell_pile_k10 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K10) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.pile := by
  obtain ⟨l, -, e⟩ := k10_number hb hp hk
  have hlen : b ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    omega
  exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ (ridesPastAt_pile_k10_at h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        hlen (by omega) (by omega) fun s s' hK =>
          head_arm h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 hp hk hK))

/-- The item `pile` at a place of the kind K1, where it is open and is not closed. -/
theorem cell_pile_k1 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K1)
    (hi : Item.pile ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.pile ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.pile := by
  obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨w1, w2, w3⟩ := k1_where hb hp hk
  have hlen : b ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    omega
  by_cases c1 : p.link = some 0 ∧ p.piece = 1
  · obtain rfl := w1 c1
    exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ (ridesPastAt_pile_two h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        hlen fun s s' hK =>
          (fHead_K1_first Zp cF G take P11 p12 P13 c1.1 c1.2 s s').1
            (head_arm h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 hp hk hK)))
  · by_cases c2 : p.link = none ∧ p.piece = 4
    · obtain rfl := w2 c1 c2
      have t := List.all_eq_true.1 (Bool.and_eq_true_iff.1 k1Ends_full).2 _ ho
      exact absurd (show false = true from t) (by decide)
    · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w
          (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
          (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
        (ridesPastAtS_of _ _ (ridesPastAt_pile_k1_at h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w
          hlen (w3 c1 c2) (by omega) fun s s' hK => by
            have a := head_arm h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 hp hk hK
            change (if p.link = some 0 ∧ p.piece = 1 then _
              else if p.link = none ∧ p.piece = 4 then _ else _) at a
            rw [if_neg c1, if_neg c2] at a
            exact ⟨k1KeepsAt_rest a.1, a.2⟩))

/-- The item `row m c` at a place of the kind K1, where it is open and is not closed. -/
theorem cell_row_k1 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K1) {m : Nat} {c : RowClass}
    (hi : Item.row m c ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.row m c ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.row m c) := by
  obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨w1, w2, w3⟩ := k1_where hb hp hk
  have hlen : b ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    omega
  by_cases c1 : p.link = some 0 ∧ p.piece = 1
  · obtain rfl := w1 c1
    have t := List.all_eq_true.1 (Bool.and_eq_true_iff.1 k1Ends_full).1 _ ho
    exact absurd (show false = true from t) (by decide)
  · by_cases c2 : p.link = none ∧ p.piece = 4
    · obtain rfl := w2 c1 c2
      have t := List.all_eq_true.1 (Bool.and_eq_true_iff.1 k1Ends_full).2 _ ho
      exact absurd (show false = true from t) (by decide)
    · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w
          (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
          (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
        (ridesPastAtS_of _ _ (ridesPastAt_row_k1_at h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w
          hlen (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp).1) m c ho fun s s' hK => by
            have a := head_arm h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 hp hk hK
            change (if p.link = some 0 ∧ p.piece = 1 then _
              else if p.link = none ∧ p.piece = 4 then _ else _) at a
            rw [if_neg c1, if_neg c2] at a
            exact ⟨k1KeepsAt_rest a.1, a.2⟩))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k1Where_full
#print axioms ProofFile.Honest.FirstThread.k1Where_control
#print axioms ProofFile.Honest.FirstThread.k1Ends_full
#print axioms ProofFile.Honest.FirstThread.k1Ends_control
#print axioms ProofFile.Honest.FirstThread.k1_where
#print axioms ProofFile.Honest.FirstThread.head_arm
#print axioms ProofFile.Honest.FirstThread.cell_pinW
#print axioms ProofFile.Honest.FirstThread.cell_constr4
#print axioms ProofFile.Honest.FirstThread.cell_constr_digits
#print axioms ProofFile.Honest.FirstThread.head_quiet_k11
#print axioms ProofFile.Honest.FirstThread.cell_pile_k11
#print axioms ProofFile.Honest.FirstThread.cell_row_k11
#print axioms ProofFile.Honest.FirstThread.cell_pile_k10
#print axioms ProofFile.Honest.FirstThread.cell_pile_k1
#print axioms ProofFile.Honest.FirstThread.cell_row_k1
