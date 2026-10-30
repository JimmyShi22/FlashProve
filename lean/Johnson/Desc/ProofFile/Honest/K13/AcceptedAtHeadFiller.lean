-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/AcceptedAtHeadFiller.lean: AT THE THREAD OF THE FIRST CHAIN UNDER
THE LIBRARY's ONE HYPOTHESIS AT THE FULL SIZE (`lettersHead`, Honest/Thread/FirstHead.lean): THE TIE
OF THE FILLER's PILE TO THE STATE's (`RowsTie`), AND THAT K13's SUB-PROTOCOL AT 355 IS ACCEPTED, AT
THE FILLER OVER THE CHAIN's OWN SITES. Conditional statements with their proofs: calls.

`k13_accepted_at_head` (GuardsAtHead.lean of this folder) takes a filler `pile` as a variable, with
two premises on it: hW (`RowsTie`) and hfill. Here pile := `fillerAt cF Zp claims`
(FillFitsAtHead.lean). hfill: `hfill_at_head`: under h alone. hW: `rowsTie_of_pileIs` (PileIs.lean)
at `pileIs_at_chain` (SitesClaims.lean), whose scope, opening and premise on the plan are had of h
(h.scope, h.reads, h.laid.opened; the library's `P5J.flat_ok`, Johnson/P5J/FoldJ1.lean); of its five
premises two are shown: hreach (`hreach_at_flat`, ReachAtFlat.lean) and hfive (`hfive_at_head`,
BatchStays.lean). That the thread's list of sub-protocols, its first state and its public part of an
instance are cF.blocksInOrder, `ProofFile.startS Zp` and the instance's `pub`: by unfolding.
Main names:
  `rowsTie_at_head`: **`RowsTie` at `lettersHead`, the border 355, that filler**, from THREE
    premises: hfront (`LayersFront` at each 28 g + 4: three sentences on the fold's state in front
    of the layers' own sub-protocol) · hlaw (`ClaimsFromHearing` at each group: the law on the
    parameter's claims, from the hearing's own return) · hhead (`HeadClaimIs` at 346: the like at
    the head).
  `k13_accepted_at_head_filler`: **`AcceptedS` at 355**, from these three; b₀ ≤ 355; and hH: the
    honest part found at the place of number 355 is `proverSideOfClaimCombination` at that filler.

What is not claimed. Any of these premises; that they can be met together; that h holds at any
public files; claims: the parameter: free. It is none of the library's goals. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.GuardsAtHead
import Johnson.Desc.ProofFile.Honest.K13.PileIs
import Johnson.Desc.ProofFile.Honest.K13.FillFitsAtHead
import Johnson.Desc.ProofFile.Honest.K13.ReachAtFlat
import Johnson.Desc.ProofFile.Honest.K13.BatchStays

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.K13.Honest (SiteClaims LayersFront ClaimsFromHearing HeadClaimIs
  roundsAhead)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`RowsTie` AT THE HEAD's THREAD, AT THE FILLER OVER THE CHAIN's OWN SITES.** -/
theorem rowsTie_at_head (claims : SiteClaims ProofFile.Inst) {Szd : Nat → Fork → Prop}
    {Tie : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard → Prop}
    {tokOf : Nat → ProofFile.Inst → Array Nat}
    (hfront : ∀ g < 12, LayersFront cF.blocksInOrder (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) (28 * g + 4)
      (Szd g) (Tie g) (tokOf g))
    (hlaw : ∀ g < 12, ∀ p : OnBytes.Desc.First.K4.Par, p.P = Zp.p.X.layers →
      Zp.p.X.G[g]? = some p.hp → p.g = g →
      ClaimsFromHearing p (2 * g) (roundsAhead cF.blocksInOrder (28 * g + 4)) claims (Szd g) (Tie g)
        (tokOf g))
    (hhead : HeadClaimIs cF.blocksInOrder (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) 346 24 claims
      ProofFile.Inst.asked) :
    RowsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 (fillerAt cF Zp claims)
      ProofFile.Inst.asked := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact rowsTie_of_pileIs _ 355 _ _
    (pileIs_at_chain h.scope h.reads O (P5J.flat_ok h.toAtMg) (fun x : ProofFile.Inst => x.pub) _ claims
      ProofFile.Inst.asked hfront hlaw hhead (hreach_at_flat h.scope h.reads O) (hfive_at_head h _))

/-- **K13's SUB-PROTOCOL AT 355 IS ACCEPTED, at every `fall`, from the thread and what is said, AT
THE FILLER OVER THE CHAIN's OWN SITES**: `k13_accepted_at_head` (GuardsAtHead.lean) with its
premises hW and hfill had by calls. -/
theorem k13_accepted_at_head_filler
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {weights : W₀ → Weights} (hb : b₀ ≤ 355) (claims : SiteClaims ProofFile.Inst)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination weights (fillerAt cF Zp claims) h.𝔇.P13))
    {Szd : Nat → Fork → Prop} {Tie : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard → Prop}
    {tokOf : Nat → ProofFile.Inst → Array Nat}
    (hfront : ∀ g < 12, LayersFront cF.blocksInOrder (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) (28 * g + 4)
      (Szd g) (Tie g) (tokOf g))
    (hlaw : ∀ g < 12, ∀ p : OnBytes.Desc.First.K4.Par, p.P = Zp.p.X.layers →
      Zp.p.X.G[g]? = some p.hp → p.g = g →
      ClaimsFromHearing p (2 * g) (roundsAhead cF.blocksInOrder (28 * g + 4)) claims (Szd g) (Tie g)
        (tokOf g))
    (hhead : HeadClaimIs cF.blocksInOrder (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) 346 24 claims
      ProofFile.Inst.asked)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 :=
  k13_accepted_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb hH
    (rowsTie_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w claims hfront hlaw hhead)
    (hfill_at_head h claims) fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.rowsTie_at_head
#print axioms ProofFile.Honest.K13.k13_accepted_at_head_filler
