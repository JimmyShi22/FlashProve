-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/MaskAtMgAll.lean (kind K10): AT A STATE THAT IS REACHED IN FRONT OF K10's OWN SUB-PROTOCOL OF LINK l, AT ALL 25 LINKS: THE FRAME THAT THE CLOSING READS HAS, AS ITS FRESH MASK, THE PLAN's OWN NUMBER OF THAT MESSAGE's SEAT. Theorems: MaskAtMg.lean (beside this file; the links 1 … 23) with the head's link and link 0 laid
beside, and the three joined.

BY: `mask_head_named` (Johnson/IMR/MaskHeadNamed.lean) and `mask_zero_named` (Johnson/IMR/MaskZeroNamed.lean) · `size_at_table` · `mask_at_cut` (Johnson/Desc/First/Close/Law/MaskAtFull.lean: by the kernel at the written values, all 25 links).

What is said.
  `mask_reached_head`: at a state reached at 350: the open link of number 24 has frame.mask = some (maskNo seatsPlanW P5T.psFull 24). `mask_reached_zero`: at 12: link 0.
  `AtMg.mask_at_head`, `AtMg.mask_at_zero`: at the constant's own «reached» and letters.
  `AtMg.mask_all`: **l < 25 · a reached at batchAt fullLinks At.ps l + 3 ⊢ (rdK a.1.2).2.1.mask = some (maskNo (At.seats Zp) (At.pseats Zp) l): ALL 25 LINKS IN ONE STATEMENT.**
ITS PREMISES: AtMg at OnBytes.secondHashFunction (in scope · the files are read · the value is laid: WITH THE FOURTEEN ENTRY TESTS: the proof spends the pins on the plan's seats and on the first chain's cut) and «reached».

Limits. AtMg is a premise. o := OnBytes.secondHashFunction alone. Nothing on soundness.

-/
import Johnson.P5J.MaskAtMg
import Johnson.IMR.MaskHeadNamed
import Johnson.IMR.MaskZeroNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE HEAD's LINK.** -/
theorem mask_reached_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hsh : Z.first.shape = shapeFull)
    (hc : VerifiableInference.PlanWritten.cutOf c.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 350 (z, s)) :
    ∃ L : LinkCtx, s.link? = some L ∧ L.link = 24 ∧
      L.check.frame.mask = some (maskNo seatsPlanW P5T.psFull 24) := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  obtain ⟨t₀, R₀, C₀, L, f₀, hL, e2, em⟩ :=
    Meaning.K2.mask_head_named hS hR O (n := 10) (Nat.le_refl 10) f
  have hlen := Meaning.K2.flat_358 hS O
  have s0 := Meaning.K2.size_at_table hS hR O hF P5T.N0Full (k := 339) (by omega) f₀
  have e : maskPub (P5T.N0Full.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) Z.first.shape 24 =
      t₀.st.oracles.size + (1 + (K2.targetAt Z.first.shape 24).kept.size) +
        Meaning.K2.msgsAt Z.first.shape 24 0 := by
    unfold maskPub
    rw [if_neg (by omega : ¬ (24 : ℕ) = 0), if_pos rfl, ← s0]
  rw [← e, hsh] at em
  exact ⟨L, hL, e2, em.trans (congrArg some (mask_at_cut hc P5T.N0Full 24 (by omega)))⟩

/-- **AT LINK 0.** -/
theorem mask_reached_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = shapeFull)
    (hc : VerifiableInference.PlanWritten.cutOf c.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 12 (z, s)) :
    ∃ L : LinkCtx, s.link? = some L ∧ L.link = 0 ∧
      L.check.frame.mask = some (maskNo seatsPlanW P5T.psFull 0) := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  obtain ⟨L, hL, e2, em⟩ := Meaning.K2.mask_zero_named hS hR O (n := 9) (Nat.le_refl 9) f
  have e : maskPub (P5T.N0Full.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) Z.first.shape 0 =
      Meaning.K2.msgsAt Z.first.shape 0 0 := by
    unfold maskPub
    rw [if_pos rfl]
  rw [← e, hsh] at em
  exact ⟨L, hL, e2, em.trans (congrArg some (mask_at_cut hc P5T.N0Full 0 (by omega)))⟩

end VerifiableInference.Desc.First.Close

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Chain)
open VerifiableInference.Desc.First.Close (rdK maskNo seatsPlanW mask_reached_head
  mask_reached_zero hc_at_laid)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

theorem AtMg.mask_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch 350 a) :
    (rdK a.1.2).2.1.mask = some (maskNo (At.seats Zp) (At.pseats Zp) 24) := by
  have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
  have e2 : At.seats Zp = seatsPlanW := by
    unfold At.seats
    rw [e1]
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, hL, -, em⟩ := mask_reached_head h.scope h.reads O h.laid.planOk h.shape_full
    (hc_at_laid h.scope h.laid) (z := a.1.1) (s := a.1.2) (h.rch_is_reach _ a hr)
  rw [e1, e2, ← em]
  show a.1.2.live.frame.mask = _
  unfold VerifiableInference.Desc.First.S.live
  rw [hL]

theorem AtMg.mask_at_zero (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch 12 a) :
    (rdK a.1.2).2.1.mask = some (maskNo (At.seats Zp) (At.pseats Zp) 0) := by
  have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
  have e2 : At.seats Zp = seatsPlanW := by
    unfold At.seats
    rw [e1]
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, hL, -, em⟩ := mask_reached_zero h.scope h.reads O h.shape_full
    (hc_at_laid h.scope h.laid) (z := a.1.1) (s := a.1.2) (h.rch_is_reach _ a hr)
  rw [e1, e2, ← em]
  show a.1.2.live.frame.mask = _
  unfold VerifiableInference.Desc.First.S.live
  rw [hL]

/-- **ALL 25 LINKS IN ONE STATEMENT, AT THE NUMBER OF THE CONSTANT's OWN LIST OF PLACES.** -/
theorem AtMg.mask_all (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : ℕ} (hl : l < 25)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (hr : h.rch (batchAt fullLinks At.ps l + 3) a) :
    (rdK a.1.2).2.1.mask = some (maskNo (At.seats Zp) (At.pseats Zp) l) := by
  by_cases h24 : l = 24
  · subst h24
    rw [LPFK9.k10_border_head] at hr
    exact h.mask_at_head a hr
  · by_cases h0 : l = 0
    · subst h0
      rw [LPFK9.k10_border 0 (by omega)] at hr
      exact h.mask_at_zero a hr
    · exact h.mask_at_border (by omega) (by omega) a hr

end P5J

#print axioms VerifiableInference.Desc.First.Close.mask_reached_head
#print axioms VerifiableInference.Desc.First.Close.mask_reached_zero
#print axioms P5J.AtMg.mask_at_head
#print axioms P5J.AtMg.mask_at_zero
#print axioms P5J.AtMg.mask_all
