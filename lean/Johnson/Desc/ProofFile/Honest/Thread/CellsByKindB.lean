-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CellsByKindB.lean: the hypothesis `RidesPastAtS`
(Honest/Thread/SharesS.lean) for the open items `unmarked`, `pinI`, `pin m t`, `pile` and `row m c`
of the first chain's invariant, stated by the kind of the place, as CellsByKind.lean states it for
`forms` and `wo`. The invariant's `keeps` is `kpBy fHeadG` (FHeadG.lean). This is the form in which
the gathering takes a cell of its column `hR`. No definition.

  1  `cell_unmarked`, `cell_pinI`, `cell_pin`   at every place that is not of the kind `frame`
  2  `cell_pile_quiet`, `cell_row_quiet`   at a place of the kind K3, K4, K6 or K8
  3  `cell_pile_k9`, `cell_row_k9`   at a place of the kind K9

The lemmas are calls. CellsMark.lean, CellsPin.lean, CellsQuiet.lean and CellsK9.lean prove the
statements at `keeps` := `fHead`; at K9's "one equation" PileCellsEqK7.lean and RowCellEq.lean do.
`head_ridesPastAtS_mono` (KeepsMono.lean) carries them to `fHeadG`. `k9_number_of`
(PinKeptCells.lean) says at which three numbers of a segment a place of the kind K9 stands.

Limits.
  * Not treated: `pile` and `row` at the other kinds.
  * Nothing here shows that an item's statement holds at any state of a run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CellsPin
import Johnson.Desc.ProofFile.Honest.Thread.CellsK9
import Johnson.Desc.ProofFile.Honest.Thread.PileCellsEqK7
import Johnson.Desc.ProofFile.Honest.Thread.RowCellEq
import Johnson.Desc.ProofFile.Honest.Thread.OpenNext
import Johnson.Desc.ProofFile.Honest.Thread.KeepsMono
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item RowClass)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

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

/-- The item `unmarked` at a place that is not of the kind `frame`. -/
theorem cell_unmarked {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind ≠ KindName.frame) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.unmarked :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _ (head_rides_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w G take P11 p12 P13 (fun _ _ _ hk => hk) hp hk))

/-- The item `pinI` at a place that is not of the kind `frame`. -/
theorem cell_pinI {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind ≠ KindName.frame) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.pinI :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _
      (head_rides_pins h H Q test carryX item n₁ n₂ b₀ Vd Rd G take P11 p12 P13 w hb hp hk).1)

/-- The item `pin m t` at a place that is not of the kind `frame`. -/
theorem cell_pin {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind ≠ KindName.frame) (m t : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.pin m t) :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _
      ((head_rides_pins h H Q test carryX item n₁ n₂ b₀ Vd Rd G take P11 p12 P13 w hb hp hk).2 m t))

/-- The item `pile` at a place of the kind K3, K4, K6 or K8. -/
theorem cell_pile_quiet {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3 ∨ p.kind = KindName.K4 ∨ p.kind = KindName.K6 ∨
      p.kind = KindName.K8) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.pile :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _ (head_rides_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w G take P11 p12 P13 (fun _ _ _ hk => hk) hp hk).1)

/-- The item `row m c` at a place of the kind K3, K4, K6 or K8. -/
theorem cell_row_quiet {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3 ∨ p.kind = KindName.K4 ∨ p.kind = KindName.K6 ∨
      p.kind = KindName.K8) (m : Nat) (c : RowClass) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.row m c) :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _ ((head_rides_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w G take P11 p12 P13 (fun _ _ _ hk => hk) hp
      hk).2.2.2 m c))

/-- The item `pile` at a place of the kind K9. -/
theorem cell_pile_k9 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K9) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.pile := by
  obtain ⟨l, hl, rfl | rfl | rfl⟩ := k9_number_of hb hp hk
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ (head_rides_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (fHead Zp cF G take P11 p12 P13) w rfl hl).1)
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ (pile_cell_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (fHead Zp cF G take P11 p12 P13) w rfl hl))
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ (head_rides_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (fHead Zp cF G take P11 p12 P13) w rfl hl).1)

/-- The item `row m c` at a place of the kind K9, where it is open and is not closed. -/
theorem cell_row_k9 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K9) {m : Nat} {c : RowClass}
    (hi : Item.row m c ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.row m c ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.row m c) := by
  obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨l, hl, rfl | rfl | rfl⟩ := k9_number_of hb hp hk
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ ((head_rides_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (fHead Zp cF G take P11 p12 P13) w rfl hl).2.2.2 m c))
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ (row_cell_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (fHead Zp cF G take P11 p12 P13) w rfl hl m c ho))
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w
        (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ ((head_rides_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (fHead Zp cF G take P11 p12 P13) w rfl hl).2.2.2 m c))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.cell_unmarked
#print axioms ProofFile.Honest.FirstThread.cell_pinI
#print axioms ProofFile.Honest.FirstThread.cell_pin
#print axioms ProofFile.Honest.FirstThread.cell_pile_quiet
#print axioms ProofFile.Honest.FirstThread.cell_row_quiet
#print axioms ProofFile.Honest.FirstThread.cell_pile_k9
#print axioms ProofFile.Honest.FirstThread.cell_row_k9
