-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K5CellsAll.lean: every open item of the first chain's invariant
that is neither closed nor owed again at an attention segment's own rounds (kind K5) passes over
them, at `lettersHead`, where `keeps` gives the clause that the authors of kind K5 supply by the
place (`K5KeepsAt`, Johnson/Desc/K5/Honest/Law/KeepsM.lean). No definition.

K5Rides.lean calls these authors' lemma over their older clause `K5Keeps`. The clause in `fHead`
(FHead.lean) is `K5KeepsAt`, which gives `K5KeepsM`. The same authors state the whole condition
`RidesPast` (Honest/Thread/Pays.lean) over `K5KeepsM`: `K5.k5_ridesPast_M_T`, with the structure
`K5RidersM` shown for the first chain's invariant (`K5.k5RidersM_thrAt`; both in
Honest/K5/Law/KeepsMT.lean). This file calls them.

  1  `ridesPast_k5M`   `RidesPast` at group `g` below 12, if `keeps` there gives `K5KeepsM`
  2  `ridesPast_k5_at`   the same, if the letter `Kp` at the kind's place gives `K5KeepsAt`. The
     place and the plan: `K5.k5_member` (Honest/K5/Law/Member.lean)
  3  `k5_numbers`, `k5_numbers_control`, `k5_number`   a closed test by Lean's kernel: a place of
     the kind K5 in the written list stands at the number of a group below 12. The negative test:
     with 11 groups the test fails
  4  `cell_k5`   the hypothesis `RidesPastAtS` (Honest/Thread/SharesS.lean) at `kpBy fHeadG`
     (FHeadG.lean), at every place of the kind K5 and every item that is open there and is neither
     closed nor owed again

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Nothing here shows that an item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K5Rides
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.K5.Law.KeepsMT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 3 The places of the kind K5 -/

set_option maxRecDepth 1000000 in
/-- A place of the kind K5 stands at the number of a group below 12. -/
theorem k5_numbers : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K5) || (List.range 12).any fun g => b == K5.borderOf g) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with 11 groups the same test fails. -/
theorem k5_numbers_control : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K5) || (List.range 11).any fun g => b == K5.borderOf g) = false := by
  decide +kernel

/-- The test at a place. -/
theorem k5_number {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K5) : ∃ g, g < 12 ∧ b = K5.borderOf g := by
  have t := List.all_eq_true.1 k5_numbers b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · exact absurd t0 (by decide)
  · obtain ⟨g, hg, e⟩ := List.any_eq_true.1 t1
    exact ⟨g, List.mem_range.1 hg, eq_of_beq e⟩

/-! ## 1, 2 and 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- Every item that is open, not closed and not owed again passes over the own rounds of attention
segment `2 g + 1`, if `keeps` there gives `K5KeepsM`. -/
theorem ridesPast_k5M {g : Nat} (hg : g < 12) {o}
    (hk : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps (K5.borderOf g) s s' →
      H2K5.Honest.K5KeepsM o s s') :
    RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (K5.borderOf g) :=
  K5.k5_ridesPast_M_T h
    (K5.k5AtT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)) test carryX
      item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ Rd b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → Kp p s s') hg)
    (K5.k5RidersM_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)) test carryX
      item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ Rd b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → Kp p s s') hg hk)
    hg (ansOn_head Zp Z.lay _ _)

/-- The same, if `Kp` at the kind's place gives the clause by the place. -/
theorem ridesPast_k5_at {g : Nat} (hg : g < 12)
    (hK : ∀ s s',
      Kp { chain := 1, link := some (2 * g + 1), piece := 3, kind := KindName.K5 } s s' →
      H2K5.Honest.K5KeepsAt (P5J.At.X Zp)
        { chain := 1, link := some (2 * g + 1), piece := 3, kind := KindName.K5 } s s') :
    RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (K5.borderOf g) := by
  obtain ⟨blk, a, hb, Pl, Dc⟩ := K5.k5_member h hg
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb
  rw [Dc.place] at hp
  exact ridesPast_k5M h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg (o := a.own)
    fun s s' hk => (H2K5.Honest.k5KeepsAt_iff Pl.plan s s').1
      (hK s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').1 hk))

variable (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- At a place of the kind K5: every item that is open, not closed and not owed again. -/
theorem cell_k5 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K5) {i : Item}
    (hi : i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts)
    (h2 : i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).owes) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b i := by
  obtain ⟨g, hg, rfl⟩ := k5_number hb hp hk
  exact fun k s m E s' ps v hA hK h0 =>
    ridesPast_k5_at h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hg
      (fun _ _ a => a.1.1) k s m E s' ps i v hA.1 hK hi h1 h2 h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k5_numbers
#print axioms ProofFile.Honest.FirstThread.k5_numbers_control
#print axioms ProofFile.Honest.FirstThread.k5_number
#print axioms ProofFile.Honest.FirstThread.ridesPast_k5M
#print axioms ProofFile.Honest.FirstThread.ridesPast_k5_at
#print axioms ProofFile.Honest.FirstThread.cell_k5
