-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/BudAtHead.lean: the kind "the code switch" (K2): in the goals'
scope, under the opening and the library's test on the public files, at each written place of the kind:
at every list of challenges that the description can draw, the positions that the description's own
rounds read of the trees of the switch's sending are within the bound of the kind (switchBud). It is
the field bud₁ of BudDebts (Honest/Law/OwedRule.lean) at the kind's rows.

  reads_at_switch       the test at the description, at every way to split the chain at the place
  bud_at_switch         the end

By: readsWithinOf (Johnson/SendSim/Seat/ReadsCountProof.lean), budAt_of_reads (BudProof.lean),
plan_of_live, D_in_scope (ReadsAtLive.lean), tabW, treesAt (ReadsAtWritten.lean), switchBud_iff_bud
(CoreSenderLaw.lean), places_at_head (PlacesWritten.lean).

Limits. It counts positions of the description's declared rounds: no input, no coin. The test counts
a position once for each opening. That a run reads no position beyond what treeAsks lists is the
frame's. One request: nothing on a batch.
-/
import Johnson.SendSim.Seat.ReadsAtLive
import Johnson.SendSim.Seat.ReadsCountProof
import Johnson.Desc.ProofFile.Honest.K2.Law.CoreSenderLaw
import Johnson.Desc.ProofFile.Honest.K2.Law.ReadsWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Chain Place Block)
open OnBytes.SendSim.Seat (readsWithinB treesOf treesOf_cut readsWithinB_tab takeWhile_split
  plan_of_live D_in_scope budAt_of_reads readsWithinOf)
open P5J (TS)

variable {P : VerifierAndGoals.PublicFiles} {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Zp : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {c : Chain TS ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {p : SwitchPlace}

/-- **The test at the description, at every way to split the first chain at a written place.** -/
theorem reads_at_switch (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Zp Bs base c A B) (hpW : p ∈ placesW) :
    ∀ pre b t, F.first.blocksInOrder = pre ++ b :: t → b.place = p.place →
      readsWithinB F (sendingPar p.sizes.codes (switchSent p.sizes p.others))
        (treesOf F.first.blocksInOrder pre) = true := by
  obtain ⟨h2, h4⟩ := plan_of_live hL O
  have PO := (F.planOk_ok).1 h2
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure hS O.pub
  obtain ⟨hm, hc⟩ := LPFD.asks_pins h4 O.pub (decide_eq_true hk)
  have hcut := (VerifiableInference.PlanWritten.cutIs_eq hc).1
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row (Z := Zp) (by rw [hm, Bool.or_true])
  have hD : Zp.D = Johnson.AtFull.Pub.DW := D_in_scope hS O.pub hy
  have hpl : F.plans = Zp.D := by
    rw [O.desc]
    rfl
  have hd : F.roundsDeclaredByBlocks = Johnson.AtFull.Pub.DW := by
    rw [← hD, ← hpl]
    exact Prod.ext PO.decl₁ (Prod.ext PO.decl₂ PO.decl₃)
  have hs : ∀ b ∈ F.first.blocksInOrder, b.oracles.length = b.rounds.length := fun b hb => by
    have e := (PO.blocks₁ b hb).2
    unfold Block.shaped at e
    rw [Bool.and_eq_true] at e
    exact beq_iff_eq.1 e.1
  have hn := (places_nodup PO.places).1
  intro pre b t hF hb
  have e : F.first.blocksInOrder.takeWhile (·.place != p.place) = pre := by
    rw [hF] at hn ⊢
    rw [← hb]
    exact OnBytes.SendSim.Seat.takeWhile_split (fun x : Block _ _ => x.place) pre b t hn
  rw [← e, readsWithinB_tab, treesOf_cut _ hs, hd, hcut]
  exact List.all_eq_true.1 switchReadsW p hpW

/-- The bound at a place, from the test, at any description. -/
theorem bud_of_reads {Xi : Type} {F : VerifiableInference.Desc.FileDescription Xi}
    (pre : List (Block F.S₁ F.Cl)) (p : SwitchPlace)
    (hr : readsWithinB F (sendingPar p.sizes.codes (switchSent p.sizes p.others))
      (treesOf F.first.blocksInOrder pre) = true)
    (n : Nat) (ds : List Fmt.Drawn) (ρ : Draws) (hρ : ρ.due F = true) (rs : List Nat) :
    switchBud p n ds (asksFrom (treeAsks F ρ 0) rs (OnBytes.SendSim.Seat.treesTo F pre)) := by
  rw [switchBud_iff_bud]
  exact budAt_of_reads (readsWithinOf Xi F _ _ hr) ρ hρ rs

/-- **The bound at a written place of the kind**, at every due list of challenges, at the number of
trees stated in front of the place. -/
theorem bud_at_switch (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Zp Bs base c A B) (hpW : p ∈ placesW)
    {pre : List (Block F.S₁ F.Cl)} {b : Block F.S₁ F.Cl} {t : List (Block F.S₁ F.Cl)}
    (hF : F.first.blocksInOrder = pre ++ b :: t) (hb : b.place = p.place)
    (n : Nat) (ds : List Fmt.Drawn) (ρ : Draws) (hρ : ρ.due F = true) (rs : List Nat) :
    switchBud p n ds (asksFrom (treeAsks F ρ 0) rs (OnBytes.SendSim.Seat.treesTo F pre)) :=
  bud_of_reads pre p (reads_at_switch hS hL O hpW pre b t hF hb) n ds ρ hρ rs

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.reads_at_switch
#print axioms ProofFile.Honest.K2.Law.bud_at_switch
