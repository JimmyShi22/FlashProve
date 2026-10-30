-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/AcceptedAtHeadK4.lean: `AcceptedS` AT NUMBER 355 OF THE FIRST
CHAIN's THREAD, AT THE FILLER OVER THE CHAIN's OWN SITES, WITH THE LAW ON THE LAYERS' CLAIMS HAD
FROM THE LIST OF CLAIMS THAT THE HONEST PARTS' FUNCTION MAKES: CONDITIONAL ON THE LIBRARY's ONE
HYPOTHESIS AT THE FULL SIZE, h, AND ON SIX NAMED PREMISES BESIDE IT. One conditional statement with
its proof: a call.

`k13_accepted_at_head_filler` (AcceptedAtHeadFiller.lean of this folder) has three premises on the
filler's parameter. One, hlaw, follows from two others by `hlaw_of_k4` (SitesClaimsK4.lean):
`K4PubsAt` (four public equations a group on the public data of K4's honest parts) and the arms (the
parameter at segment 2 g is `layersClaims`).
  `k13_accepted_at_head_k4`: **`AcceptedS` at 355**, from: h · b₀ ≤ 355 · hH · `K4PubsAt cF Zp Qs` ·
    the arms · hfront (`LayersFront` at each 28 g + 4, at `OnBytes.PscRun.Sized`, the lookup's zk
    and the tokens of wOf g) · hhead (`HeadClaimIs` at 346).

What is not claimed. Any of these premises; that they can be met together. That the thread holds at
any run: `AcceptedS` (Honest/Thread/PaysS.lean) is itself a premise's form: IF the thread and Said
stand in front, the challenges fit, nothing stops, `fall` is silent and the member has moved, THEN
the sub-protocol's step returns. Qs, wOf, claims: free parameters. That this is the list which the
seated halves of kind K4's lot merge is not shown (K4PubsTerm.lean's head). Called by
`k13_accepted_at_head_k4_term` (K4PubsTerm.lean) alone. It is none of the library's goals. Nothing
on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.AcceptedAtHeadFiller
import Johnson.Desc.ProofFile.Honest.K13.SitesClaimsK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.K13.Honest (SiteClaims LayersFront HeadClaimIs)
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

/-- **`AcceptedS` AT 355**, the law on the layers' claims had from the list of claims that the
honest parts' function makes: from h and six premises: hb, hH, hQ, hcl, hfront, hhead. -/
theorem k13_accepted_at_head_k4
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {weights : W₀ → Weights} (hb : b₀ ≤ 355) (claims : SiteClaims ProofFile.Inst)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination weights (fillerAt cF Zp claims) h.𝔇.P13))
    (Qs : Nat → K4Pub) (wOf : Nat → ProofFile.Inst → K4In) (hQ : K4PubsAt cF Zp Qs)
    (hcl : ∀ g < 12, ∀ x hd, claims (2 * g) x hd = layersClaims (Qs g) (wOf g) x hd)
    (hfront : ∀ g < 12, LayersFront cF.blocksInOrder (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) (28 * g + 4)
      OnBytes.PscRun.Sized (fun x h fo => ((wOf g x).look h).zk = fo.zk)
      (fun x => (wOf g x).tokv))
    (hhead : HeadClaimIs cF.blocksInOrder (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) 346 24 claims
      ProofFile.Inst.asked)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 :=
  k13_accepted_at_head_filler h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb claims hH
    (Szd := fun _ => OnBytes.PscRun.Sized) (Tie := fun g x h fo => ((wOf g x).look h).zk = fo.zk)
    (tokOf := fun g x => (wOf g x).tokv) hfront (hlaw_of_k4 claims Qs wOf hQ hcl) hhead fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_accepted_at_head_k4
