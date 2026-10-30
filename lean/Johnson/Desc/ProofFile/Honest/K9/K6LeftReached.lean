-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/K6LeftReached.lean: AT EVERY STATE THAT THE FIRST CHAIN's OWN STEPS REACH AT BORDER 341
(in front of the output head's own rounds) THE THREE CLAUSES `K6Left` (Johnson/Desc/Kinds/Law/SeatedSays.lean) HOLD; and
one small tool. Joinings of sealed lemmas; statements and proofs; no definition; no goal is stated.
  `cEndFilled_341` every slot that the form in which the calls' lookup's key side ended names is filled in the ledger:
      the lines of the sealed `P4.leavesFilled_341` (Johnson/P4R/LeavesFilledAt341.lean) and of `k3_calls_leavesFilled`
      (Johnson/Top/H/Keep/K3LeftWindow.lean) a second time, at `decide_lkPad` (Johnson/Top/H/K3KeySizes.lean) and
      `Fo.Tp.lkPadCEnd` (K3CEnd.lean there)
  **`k6Left_341`** under the head: `P4.wellLaid_341` · `tokSmall_pays` at `IM.tokSmallAt_reach` · `cEndFilled_341`
  `canonical_of_rounds` the library's test on rounds' words gives the output head's laws' sentence on rounds
WHAT IS NOT CLAIMED. That any state is reached. Nothing on any run. NO MEMBER. The head h is a premise: the full size
and the format's second hash function alone. IT STANDS OVER THE SEALED LIBRARY ALONE. `k6Left_341` and `canonical_of_rounds` are
called by Honest/K9/K6GoodHanded.lean alone. Nothing on any property.
-/
import Johnson.P4R.LeavesFilledAt341
import Johnson.Top.H.Keep.K3LeftAnyWords
import Johnson.IMR.TokAtReach
import Johnson.Top.H.K3LawKind
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.OnPublicFiles (okRoundsE)
open VerifiableInference.Desc.Kinds.Head.Law (K6Left CEndFilled Canonical)

section
variable {P₀ : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Fd : FileDescription ProofFile.Inst} {Z₀ : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **Made by the accept right in front of border 341**: every slot that the form left for the join names is filled in
the state's ledger. The start of "reached" is free. -/
theorem cEndFilled_341 (hS : VerifierAndGoals.InScope P₀ = true) (hR : VerifierAndGoals.readFiles P₀ = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P₀.pol lay P₀.KL Fd Z₀ Bs base c A₀ B₀) (hOk : Fd.planOk = true)
    {XP : Type} {start : XP → S} {z : XP} {s0 : S} (h : Reach 0 c.blocksInOrder start 341 (z, s0))
    (hh : OnBytes.Model.Head.Shape) (iU3 : ℕ) :
    ∀ gk, s0.lookHeard? = some gk → CEndFilled gk ((Kinds.Head.seatAt hh iU3).ledger s0) := by
  obtain ⟨_, _, s340, -, -, ⟨p, n, HP, rs, gs, a2⟩, b3, Q, sent, laid, rs3, gs3, f3, hv, hp⟩ :=
    P4.back_341 hS hR O h
  obtain ⟨G, hG, hs, -, -⟩ := Kinds.Head.Law.placeH2_free a2
  have hd := Desc.K3.Law.blockVia_decide (hp (P4.plan_at O hOk 340 b3 f3)) hv
  obtain ⟨F1, F', g, t, hF1, hn, hl, e⟩ :=
    OnPublicFiles.decide_lkPad (Desc.K3.seatCalls K3Lot.ofForm) 3 laid sent Q [] s340 s0 rs3 gs3 hd
  obtain rfl : G = F1 := Option.some.inj (hG.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls K3Lot.ofForm).fork s340).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : s0.lookHeard? = some g := by
    rw [e]
    exact Desc.K3.seatCalls_reads K3Lot.ofForm _ _ _ hsome hn
  have hf1 : s0.fork? = some F' := by
    rw [e]
    exact OnPublicFiles.seatCalls_keeps K3Lot.ofForm _ _ _ hsome hn
  obtain ⟨-, c2⟩ := _root_.Fo.Tp.lkPadCEnd _ _ _ _ _ _ _ _ hl hs
  intro gk hgk y hy
  obtain rfl : g = gk := Option.some.inj (hg1.symm.trans hgk)
  show OnBytes.PscRun.Filled (s0.fork?.getD {}) y.1
  rw [hf1]
  exact (c2 y hy).2

end

/-- The library's test on rounds' words gives the output head's laws' sentence on rounds. -/
theorem canonical_of_rounds {R : List Fmt.RoundView} (h : okRoundsE R = true) : Canonical R := by
  intro r hr
  unfold okRoundsE at h
  have k := List.all_eq_true.1 h r hr
  rw [Bool.and_eq_true] at k
  exact ⟨fun y hy => List.all_eq_true.1 k.1 (Fmt.ItemValue.e y) hy, fun y hy => List.all_eq_true.1 k.2 y hy⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **WHAT IS LEFT OF THE OUTPUT HEAD's LAW's CONDITION IN FRONT, AT EVERY STATE REACHED AT BORDER 341**, under the
head. -/
theorem k6Left_341 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {zp : ProofFile.InstPub} {sk : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (zp, sk)) : K6Left (P5J.At.X Zp) sk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ⟨P4.wellLaid_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hr _ _,
    Kinds.Head.Law.tokSmall_pays (P5J.At.X Zp) sk (IM.tokSmallAt_reach h.scope h.reads O (by omega) hr),
    cEndFilled_341 h.scope h.reads O h.laid.planOk hr _ _⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.cEndFilled_341
#print axioms ProofFile.Honest.K9.canonical_of_rounds
#print axioms ProofFile.Honest.K9.k6Left_341
