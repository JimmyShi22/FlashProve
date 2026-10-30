-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ClaimsText.lean: A TEXT FOR THE PARAMETER OF THE PILE's FILLER
(`SiteClaims`, Johnson/Desc/K13/Honest/PileDefs.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS
WRITTEN IN LEAN; AND THAT K13's SUB-PROTOCOL AT 355 IS ACCEPTED AT THE FILLER OVER THAT TEXT. Two
definitions with code, and statements with their proofs.

WHAT IT IS. WITH `fillerAt` (FillFitsAtHead.lean of this folder): A TEXT THAT MAKES THE ROW WEIGHTS
AND THE COLUMN POINTS OF THE PILE's ROWS OF PUBLIC DATA, THE INSTANCE's PUBLIC PART AND THE
CHALLENGES, UP TO TWO NAMED PARAMETERS: lookOf AND headArm.
WHAT IT IS NOT. NOT THE ROWS' MASK FORMS. NOT THEIR TARGETS. NO TEXT FOR lookOf (what the lookup in
front of the layers' own rounds has sampled, of the challenges in front). NO TEXT FOR headArm (the
head's claim on the weights). NOT THAT IT YIELDS A ROW ANYWHERE.
WHY THE CELLS AND THE WEIGHTS' DIGITS MAY BE LAID 0 IN `smallIn`: BY `layersClaims_reads`: of the
small input of K4's honest parts the layers' arm reads the tokens and `look` alone; a claim on the
weights (`WsClaim`, OnBytes/Model/Weights.lean) holds a unit's number and factors, no claimed value.
Main names:
  `layersClaims_reads`: **two makers of the small input that agree in tokv and look at x give the
    same `layersClaims` at x** (ClaimsIsLayers.lean). By unfolding `ptsOf`, `mergeClaimsAt`,
    `embClaim` (Johnson/Desc/K4/Honest/Front.lean, Merge.lean). A SECOND TEXT: kind K4's
    `ptsOf_look` and `claimsAt_input` (Honest/K4/Law/ClaimsAre.lean, which lies beneath this file)
    are the same two equations, and `layersClaims_reads_zk` (ClaimsReadZk.lean) gives it. Called by
    no file: it stands as the reason why `smallIn` may lay zeros.
  `smallIn Z look x`: the small input as far as the claims read it: tokv := the tokens of the IOP's
    own first state at x's public part; look := look x; cell, w := 0.
  `claimsText c Z lookOf headArm Q₀`: **the text**: at segment 24: headArm; at every other segment
    l: `layersClaims` at `k4PubsOf c Z Q₀ (l / 2)` (K4PubsTerm.lean) and `smallIn Z (lookOf (l /
    2))`. At an odd l, and at an even l from 26 on, the term has a value and no meaning: no site of
    `sitesAt` has such a segment.
    `claimsText_arm`, `claimsText_head`: its two arms, by its text.
  `k13_accepted_at_head_text`: **`AcceptedS` at 355 at the thread under the library's one hypothesis
    at the full size**, from: h · b₀ ≤ 355 · hH (the honest part found at the place of number 355 is
    `proverSideOfClaimCombination` at the filler over this text) · htie (in lookOf) · hhead (`HeadClaimIs` at 346, in
    headArm). By `k13_accepted_at_head_k4_term` (K4PubsTerm.lean) and `layersFront_of_tie`
    (FrontAtHead.lean).

What is not claimed. hH, htie, hhead; that they can be met together; that h holds at any public
files. `AcceptedS` (Honest/Thread/PaysS.lean) is itself a premise's form: IF the thread and Said
stand in front, the challenges fit, nothing stops, `fall` is silent and the member has moved, THEN
the sub-protocol's step returns: where the thread stands nowhere it speaks of nothing. That this is
the list which the seated halves of kind K4's lot merge is not shown (K4PubsTerm.lean's head). Q₀: a
free parameter: three fields that no line here reads. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.K4PubsTerm
import Johnson.Desc.ProofFile.Honest.K13.FrontAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub K4In mergeClaimsAt embClaim ptsOf)
open VerifiableInference.Desc (Chain Strs Place foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (SiteClaims HeadClaimIs roundsAhead)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

/-- **OF THE SMALL INPUT OF K4's PARTS THE LAYERS' ARM READS THE TOKENS AND `look` ALONE**: two
makers of that input that agree in these two fields at x give the same claims at x. -/
theorem layersClaims_reads {Xi : Type} (Q : K4Pub) (wOf wOf' : Xi → K4In) (x : Xi)
    (hd : List Fmt.Drawn) (h1 : (wOf x).tokv = (wOf' x).tokv)
    (h2 : (wOf x).look = (wOf' x).look) :
    layersClaims Q wOf x hd = layersClaims Q wOf' x hd := by
  have e : ptsOf Q (wOf x) hd = ptsOf Q (wOf' x) hd := by
    unfold ptsOf
    rw [h2]
  unfold layersClaims
  rw [e]
  unfold mergeClaimsAt embClaim
  rw [h1]

/-- **The small input, as far as the claims read it**: the tokens of the IOP's own first state at
the instance's public part; look: a parameter. The cells and the weights' digits are laid 0: by
`layersClaims_reads` no claim reads them. -/
def smallIn (Z : ProofFile.Pub) (look : ProofFile.Inst → List Fmt.Drawn → Forest.Heard) (x : ProofFile.Inst) : K4In :=
  { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := (ProofFile.startS Z x.pub).tokv, look := look x }

/-- **THE PARAMETER's TEXT.** At segment 24: headArm. At every other segment l: the list of claims
that the honest parts' function makes at `k4PubsOf` of group l / 2. lookOf, headArm, Q₀:
parameters. -/
def claimsText (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub)
    (lookOf : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub) :
    SiteClaims ProofFile.Inst := fun l x hd =>
  if l = 24 then headArm x hd
  else layersClaims (k4PubsOf c Z Q₀ (l / 2)) (smallIn Z (lookOf (l / 2))) x hd

/-- The arm at a layers' segment. -/
theorem claimsText_arm (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub)
    (lookOf : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub) (g : Nat)
    (hg : g < 12) (x : ProofFile.Inst) (hd : List Fmt.Drawn) :
    claimsText c Z lookOf headArm Q₀ (2 * g) x hd =
      layersClaims (k4PubsOf c Z Q₀ g) (smallIn Z (lookOf g)) x hd := by
  unfold claimsText
  rw [if_neg (by omega), show 2 * g / 2 = g by omega]

/-- The arm at the head's segment. -/
theorem claimsText_head (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub)
    (lookOf : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub)
    (x : ProofFile.Inst) (hd : List Fmt.Drawn) :
    claimsText c Z lookOf headArm Q₀ 24 x hd = headArm x hd :=
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **K13's SUB-PROTOCOL AT 355 IS ACCEPTED, AT THE FILLER OVER THE PARAMETER's TEXT.** htie: what
the lookup returned, as the fold's state in front of number 28 g + 4 holds it, has the zk of
lookOf g at the instance and the challenges in front. hhead: the head's claim, as the fold's state
in front of number 346 holds it, is headArm's. -/
theorem k13_accepted_at_head_text
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {weights : W₀ → Weights} (hb : b₀ ≤ 355)
    (lookOf : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination weights (fillerAt cF Zp (claimsText cF Zp lookOf headArm Q₀)) h.𝔇.P13))
    (htie : ∀ g < 12, ∀ (ξ : ProofFile.Inst) rs cols sj c y fo,
      foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) (ProofFile.startS Zp ξ.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead cF.blocksInOrder (28 * g + 4)), c) →
      sj.failed = none → sj.here = .lay y → y.fo = some fo →
      (lookOf g ξ ((rs.take (roundsAhead cF.blocksInOrder (28 * g + 4))).map (·.drawn))).zk = fo.zk)
    (hhead : HeadClaimIs cF.blocksInOrder (fun ξ : ProofFile.Inst => ProofFile.startS Zp ξ.pub) 346 24
      (fun _ => headArm) ProofFile.Inst.asked)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 :=
  k13_accepted_at_head_k4_term h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb
    (claimsText cF Zp lookOf headArm Q₀) hH Q₀ (fun g => smallIn Zp (lookOf g))
    (fun g hg ξ hd => claimsText_arm cF Zp lookOf headArm Q₀ g hg ξ hd)
    (fun g hg => layersFront_of_tie h (fun ξ : ProofFile.Inst => ProofFile.startS Zp ξ.pub) g hg
      (fun ξ hd fo => (lookOf g ξ hd).zk = fo.zk) (htie g hg))
    hhead fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.layersClaims_reads
#print axioms ProofFile.Honest.K13.claimsText_arm
#print axioms ProofFile.Honest.K13.claimsText_head
#print axioms ProofFile.Honest.K13.k13_accepted_at_head_text
#print axioms ProofFile.Honest.K13.smallIn
#print axioms ProofFile.Honest.K13.claimsText
