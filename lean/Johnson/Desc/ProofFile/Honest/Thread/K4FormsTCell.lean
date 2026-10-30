-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K4FormsTCell.lean: the hypothesis `RidesPastAtS`
(Honest/Thread/SharesS.lean) for an open item `formsT m k r` of the first chain's invariant at a
place of the kind K4 (a feed-forward segment's own rounds), for an item that is open at the border
and is not closed there. The invariant's `keeps` is `kpBy fHeadG` (FHeadG.lean). No definition.

The authors of kind K4 show that the item `formsT m 2 "objects"` passes over their sub-protocol of
segment `m` (`K4.k4_ridesPastAtS_objects_head`, Honest/K4/Law/ObjectsRidesHead.lean), if `keeps`
there gives their clause `K4KeepsM`. A closed test by Lean's kernel on the written lists ties the
kind to that statement.

  1  `k4At_full`, `k4At_control`   a place of the kind K4 is piece 3 of a segment `2 g` with `g`
     below 12; that segment is a feed-forward segment; and the only item `formsT` that is open
     before it is `formsT (2 g) 2 "objects"`. The negative test: with 3 in the place of 2 the test
     fails
  2  `k4_place`   the test at a place
  3  `cell_formsT_k4`   the cell

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG
import Johnson.Desc.ProofFile.Honest.Thread.OpenNext
import Johnson.Desc.ProofFile.Honest.K4.Law.ObjectsRidesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 and 2 The closed test -/

set_option maxRecDepth 1000000 in
/-- What a place of the kind K4 is, and which item `formsT` is open before it. -/
theorem k4At_full : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K4) || (List.range 12).any fun g =>
      p == ⟨1, some (2 * g), 3, KindName.K4⟩ && linksFull[2 * g]? == some .layers &&
        (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
          match i with
          | .formsT m k ρ => m == 2 * g && k == 2 && ρ == "objects"
          | _ => true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with 3 in the place of 2 the same test fails. -/
theorem k4At_control : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K4) || (List.range 12).any fun g =>
      p == ⟨1, some (2 * g), 3, KindName.K4⟩ && linksFull[2 * g]? == some .layers &&
        (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
          match i with
          | .formsT m k ρ => m == 2 * g && k == 3 && ρ == "objects"
          | _ => true) = false := by
  decide +kernel

/-- The test at a place. -/
theorem k4_place {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K4) :
    ∃ g, p = ⟨1, some (2 * g), 3, KindName.K4⟩ ∧ linksFull[2 * g]? = some .layers ∧
      ∀ m k ρ, Item.formsT m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps b →
        m = 2 * g ∧ k = 2 ∧ ρ = "objects" := by
  have t := List.all_eq_true.1 k4At_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · rw [hk] at t0
    exact absurd t0 (by decide)
  · obtain ⟨g, -, e⟩ := List.any_eq_true.1 t1
    simp only [Bool.and_eq_true] at e
    refine ⟨g, eq_of_beq e.1.1, eq_of_beq e.1.2, fun m k ρ ho => ?_⟩
    have t2 : (m == 2 * g && k == 2 && ρ == "objects") = true := List.all_eq_true.1 e.2 _ ho
    simp only [Bool.and_eq_true] at t2
    exact ⟨eq_of_beq t2.1.1, eq_of_beq t2.1.2, eq_of_beq t2.2⟩

/-! ## 3 The cell -/

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

/-- The item `formsT m k r` at a place of the kind K4. -/
theorem cell_formsT_k4 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K4) {m k : Nat} {ρ : String}
    (hi : Item.formsT m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.formsT m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.formsT m k ρ) := by
  obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨g, ep, hs, hf⟩ := k4_place hb hp hk
  obtain ⟨rfl, rfl, rfl⟩ := hf m k ρ ho
  exact ProofFile.Honest.K4.k4_ridesPastAtS_objects_head h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w Said b (2 * g) hp ep hs
    fun s s' a => ((kpBy_at _ hk s s').1 a).1.1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k4At_full
#print axioms ProofFile.Honest.FirstThread.k4At_control
#print axioms ProofFile.Honest.FirstThread.k4_place
#print axioms ProofFile.Honest.FirstThread.cell_formsT_k4
