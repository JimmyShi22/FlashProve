-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/MaskAtMg.lean (kind K10): AT A STATE THAT IS REACHED IN FRONT OF K10's OWN SUB-PROTOCOL OF LINK l, 1 ≤ l < 24: THE FRAME THAT THE CLOSING READS HAS, AS ITS FRESH MASK, THE PLAN's OWN NUMBER OF THAT MESSAGE's SEAT. Theorems: a join of two halves.

Why. K10's hCar asks five things of «rows.fresh» behind the closing (`hCar_end`, Johnson/Desc/First/Link/Law/HCarEnd.lean). By `closeFrame_reads` (Johnson/Desc/First/Link/Law/CloseReads.lean) rows.fresh is the frame's mask in front. THE TWO HALVES: `mask_named` (Johnson/IMR/MaskNamed.lean): along the fold the open link's frame's mask is some (the count of
oracle messages in front of the link's first sub-protocol + (1 + the switch's kept) + the link's own messages of moment 0) · `mask_at_laid` (Johnson/Desc/First/Close/Law/MaskAtFull.lean): in the table's counts, at the written values, that number is `maskNo`: by the kernel.

What is said.
  `mask_public`: in scope, under the opening at OnBytes.secondHashFunction and F.planOk, at the cuts 14 l + 3 + n, n ≤ 9: the open link L of number l has L.check.frame.mask = some (maskPub N sh l), N the table's counts.
  `mask_reached`: so at a state reached at 14 l + 12, where the shape is the written one and the first chain's cut the written one: = some (maskNo seatsPlanW P5T.psFull l).
  `AtMg.mask_at`: **at the constant's own «reached» and letters: (rdK a.1.2).2.1.mask = some (maskNo (At.seats Zp) (At.pseats Zp) l).** `AtMg.mask_at_border`: the same at batchAt fullLinks At.ps l + 3.
NO FoldFacts, NO PROMISE, NO «NO MARK» IS ASKED: AtMg and «reached» alone.

Limits. THE LINKS 1 … 23: the head's link and link 0 wait for two other statements; the closed half stands at all 25. AtMg is a premise. o := OnBytes.secondHashFunction alone. Nothing on soundness.

-/
import Johnson.IMR.MaskNamed
import Johnson.Desc.First.Close.Law.MaskAtFull
import Johnson.P5J.HingeAtMg

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

/-- **THE FRESH MASK's NUMBER IS PUBLIC.** -/
theorem mask_public (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List Col} {n : Nat} (hn : n ≤ 9) {t : S} {r : List Fmt.RoundView} {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ L : LinkCtx, t.link? = some L ∧ L.link = l ∧ L.check.frame.mask =
      some (maskPub (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) Z.first.shape l) := by
  obtain ⟨t₀, R₀, C₀, L, f₀, hL, e2, em⟩ := Meaning.K2.mask_named hS hR O h1 h24 hn g
  have hlen := Meaning.K2.flat_358 hS O
  have s0 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 14 * l + 2) (by omega) f₀
  refine ⟨L, hL, e2, ?_⟩
  unfold maskPub
  rw [if_neg (by omega : ¬ l = 0), if_neg (by omega : ¬ l = 24), ← s0]
  exact em

/-- **AT A REACHED STATE IN FRONT OF K10's OWN SUB-PROTOCOL.** -/
theorem mask_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hsh : Z.first.shape = shapeFull)
    (hc : VerifiableInference.PlanWritten.cutOf c.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull)
    {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 12) (z, s)) :
    ∃ L : LinkCtx, s.link? = some L ∧ L.link = l ∧
      L.check.frame.mask = some (maskNo seatsPlanW P5T.psFull l) := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  obtain ⟨L, hL, e2, em⟩ := mask_public hS hR O hF P5T.N0Full h1 h24 (n := 9) (Nat.le_refl 9)
    (by rw [show 14 * l + 3 + 9 = 14 * l + 12 by omega]; exact f)
  rw [hsh] at em
  exact ⟨L, hL, e2, em.trans (congrArg some (mask_at_cut hc P5T.N0Full l (by omega)))⟩

end VerifiableInference.Desc.First.Close

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Chain)
open VerifiableInference.Desc.First.Close (rdK maskNo seatsPlanW mask_reached hc_at_laid)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE FRAME's FRESH MASK IN FRONT OF THE CLOSING IS THE PLAN's OWN NUMBER.** -/
theorem AtMg.mask_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch (14 * l + 12) a) :
    (rdK a.1.2).2.1.mask = some (maskNo (At.seats Zp) (At.pseats Zp) l) := by
  have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
  have e2 : At.seats Zp = seatsPlanW := by
    unfold At.seats
    rw [e1]
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, hL, -, em⟩ := mask_reached h.scope h.reads O h.laid.planOk h.shape_full
    (hc_at_laid h.scope h.laid) h1 h24 (z := a.1.1) (s := a.1.2) (h.rch_is_reach _ a hr)
  rw [e1, e2, ← em]
  show a.1.2.live.frame.mask = _
  unfold VerifiableInference.Desc.First.S.live
  rw [hL]

/-- **THE SAME AT THE NUMBER OF THE CONSTANT's OWN LIST OF PLACES.** -/
theorem AtMg.mask_at_border (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : ℕ} (h1 : 1 ≤ l)
    (h24 : l < 24)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (hr : h.rch (batchAt fullLinks At.ps l + 3) a) :
    (rdK a.1.2).2.1.mask = some (maskNo (At.seats Zp) (At.pseats Zp) l) := by
  rw [LPFK9.k10_border l h24] at hr
  exact h.mask_at h1 h24 a hr

end P5J

#print axioms VerifiableInference.Desc.First.Close.mask_public
#print axioms VerifiableInference.Desc.First.Close.mask_reached
#print axioms P5J.AtMg.mask_at
#print axioms P5J.AtMg.mask_at_border
