-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/K4PubsTerm.lean: THE PREMISE `K4PubsAt` (SitesClaimsK4.lean of
this folder: four public equations a group on the public data of K4's honest parts) IS MET BY A
TERM; AND `k13_accepted_at_head_k4` (AcceptedAtHeadK4.lean) WITHOUT THAT PREMISE. Two definitions
with code, and statements with their proofs.

Main names:
  `blankPlan`: a plan of a layers' sub-proof with every field empty or 0: laid where the public data
    have no plan of that group.
  `k4PubsOf c Z Q₀ g`: **the term**: Q₀ g with four fields laid: P := Z's public data for the
    layers; hp := the plan of group g in Z's public data (`blankPlan` where there is none); g := g;
    r0 := `roundsAhead c.blocksInOrder (28 g + 4)`. The three other fields of `K4Pub` (link, piece, seg) stay
    as Q₀ has them: `K4PubsAt` does not ask them. Q₀: a free parameter.
  `k4PubsAt_term`: **In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening
    of the proof file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's
    holder, the first chain): `K4PubsAt c Z (k4PubsOf c Z Q₀)`.** Three of the four equations hold
    by the term's text; that the public data have a plan of group g for g < 12: the fourth conjunct
    of `layersSite_at_flat` (SitesAtFlat.lean).
  `k13_accepted_at_head_k4_term`: **`AcceptedS` at 355** under the library's one hypothesis at the
    full size, from: b₀ ≤ 355 · hH · the arms at that term · hfront · hhead.

What is not claimed. Any of these premises; that they can be met together. That link, piece and seg
of any Q₀ are the chain's. A KIN, UNTIED: kind K4's lot seats its halves at `k4PubOf Z p`
(Honest/K4/Part.lean), which counts r0 off `Z.roundsBefore?`, lays link, piece and seg, and has the
tokens by `k4Tokens`; `k4PubsOf` here counts r0 as `roundsAhead c.blocksInOrder (28 g + 4)`, takes the plan
with a default, and `smallIn` (ClaimsText.lean) takes the tokens off the first state. NO LAW SAYS
THAT THE TWO AGREE: what this folder shows ties the parts' FUNCTION `mergeClaimsAt`, at K13's own
data, to the verifier's hearing; that it is the list which K4's seated halves merge is not shown.
`AcceptedS` (Honest/Thread/PaysS.lean) is itself a premise's form: IF the thread and Said stand in
front, the challenges fit, nothing stops, `fall` is silent and the member has moved, THEN the
sub-protocol's step returns: where the thread stands nowhere it speaks of nothing. Q₀, wOf, claims:
free parameters. It is none of the library's goals. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.AcceptedAtHeadK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open VerifiableInference.Desc (Block Chain FileDescription Strs Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (SiteClaims LayersFront HeadClaimIs roundsAhead)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

/-- A plan of a layers' sub-proof with every field empty or 0. -/
def blankPlan : Layer.HPlan2 :=
  { tl := {}, Fp := {}, Tp := {}, nU := #[], ns := 0, used := 0, NCL := 0, nLin := 0, nBatched := 0
    lamS := 0 }

/-- **The public data of K4's honest parts, group by group, off the chain and what is public.** Q₀:
whence the fields link, piece and seg are taken. -/
def k4PubsOf (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub) (Q₀ : Nat → K4Pub) (g : Nat) : K4Pub :=
  { Q₀ g with
    P := Z.p.X.layers, hp := (Z.p.X.G[g]?).getD blankPlan, g := g
    r0 := roundsAhead c.blocksInOrder (28 * g + 4) }

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`K4PubsAt` AT THE TERM.** -/
theorem k4PubsAt_term (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (Q₀ : Nat → K4Pub) :
    K4PubsAt c Z (k4PubsOf c Z Q₀) := by
  intro g hg
  obtain ⟨x, _, _, _, h4, _⟩ := layersSite_at_flat hS hR O g hg
  refine ⟨rfl, ?_, rfl, rfl⟩
  show Z.p.X.G[g]? = some ((Z.p.X.G[g]?).getD blankPlan)
  rw [h4]
  rfl

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **K13's SUB-PROTOCOL AT 355 IS ACCEPTED**, the public data of K4's honest parts laid by the
term. -/
theorem k13_accepted_at_head_k4_term
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {weights : W₀ → Weights} (hb : b₀ ≤ 355) (claims : SiteClaims ProofFile.Inst)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination weights (fillerAt cF Zp claims) h.𝔇.P13))
    (Q₀ : Nat → K4Pub) (wOf : Nat → ProofFile.Inst → K4In)
    (hcl : ∀ g < 12, ∀ x hd,
      claims (2 * g) x hd = layersClaims (k4PubsOf cF Zp Q₀ g) (wOf g) x hd)
    (hfront : ∀ g < 12, LayersFront cF.blocksInOrder (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) (28 * g + 4)
      OnBytes.PscRun.Sized (fun x h fo => ((wOf g x).look h).zk = fo.zk)
      (fun x => (wOf g x).tokv))
    (hhead : HeadClaimIs cF.blocksInOrder (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) 346 24 claims
      ProofFile.Inst.asked)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact k13_accepted_at_head_k4 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb claims hH
    (k4PubsOf cF Zp Q₀) wOf (k4PubsAt_term h.scope h.reads O Q₀) hcl hfront hhead fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k4PubsAt_term
#print axioms ProofFile.Honest.K13.k13_accepted_at_head_k4_term
#print axioms ProofFile.Honest.K13.blankPlan
#print axioms ProofFile.Honest.K13.k4PubsOf
