-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileIsAtHead.lean: kind K13, the members' batching: UNDER THE
LIBRARY's ONE HYPOTHESIS AT THE FULL SIZE, h (`P5J.AtMgA`; the format's second hash function) AND A BASE
(hB: under h there is one: `base_at_head`, AcceptedByTies.lean of this folder; under h alone it is
no term: so it is a letter, with hB): THE LIBRARY's SENTENCE `PileIs`
(Johnson/Desc/K13/Honest/PileDefs.lean: a definition: a premise's form) HOLDS, AT THE FIRST CHAIN's
OWN LIST, ITS OWN FIRST STATE AND THE BORDER 355, OF THE PILE's FILLER OVER THE TEXT OF THE CLAIMS
WITH ALL ITS ARMS LAID. One statement with its proof: one call; no definition; nothing is evaluated
in this file. PUBLIC DATA ALONE: the verifier's fold, the instance, the challenges.

Main name: `k13_pileIs_at_head`.

What it says. For every instance, rounds and columns: WHERE the verifier's own fold over the first
355 sub-protocols returns a state without a mark that holds the asked reply: the filler's rows, at
the challenges of the rounds in front and any tail, have the weights and column points of the rows
on that state's pile.

Why. The laws of this kind that end in `AcceptedS` at 355 (`k13_accepted_at_head_filler`,
AcceptedAtHeadFiller.lean of this folder, and the files over it) go through `RowsTie`, which is said
from the thread. `k13_g_at_356` (AtFullSide/K13/GAt356.lean) wants `PileIs` itself, which is said of
the fold: the same payers, one statement.

How. The library's `pileIs_at_chain` (SitesClaims.lean of this folder) asks the scope, the files'
reading and the opening (the head's fields), the chain's own test on the plan (`P5J.flat_ok`,
Johnson/P5J/FoldJ1.lean), and five premises. hreach, hfive: `hreach_at_flat` (ReachAtFlat.lean),
`hfive_at_head` (BatchStays.lean). hlaw (`ClaimsFromHearing` at each group): `hlaw_of_k4`
(SitesClaimsK4.lean) at `k4PubsAt_term` (K4PubsTerm.lean) and `claimsText_arm` (ClaimsText.lean).
hfront (`LayersFront` at each 28 g + 4): `layersFront_of_tie` (FrontAtHead.lean) at kind K3's
`htie_head` (Honest/K3/Law/Thread/LayersTieHead.lean). hhead (`HeadClaimIs` at 346): kind K11's
`headClaimIsOfKeysBare` (Honest/K11/ThreeTiesBare.lean) at K3's `head_keys_tie`
(Honest/K3/Law/Thread/HeadCallsTie.lean).

Limits. CONDITIONAL ON h AND hB. AN IMPLICATION FROM THE FOLD's RETURN: that a fold returns anywhere
is not said. THAT THE FILLER's TEXT YIELDS A ROW AT ANY DATA IS NOT SAID BESIDE THAT: it has been
evaluated at none. Of a row's mask form and target nothing is said: weights and column points alone.
The row weights hold one value that was sent, the reply as heard: hence the clause on the reply in
`PileIs`. Q₀: a free parameter: three fields that no line here reads; that the text of the claims is
the same at every Q₀ is not shown here (near it: `claimsTextOf_any_q0`, DefaultsIdle.lean of this
folder: of `claimsTextOf`, the text at any number of segments). No statement names a thread, a
Script, a book or a coin. This file's imports reach Johnson/Goal/, Honest/Thread/ and
Honest/K3/Law/Thread/. `k13_pileIs_pileAnyK3` (AtFullSide/K13/GAt356AnyK3.lean) calls it, and so do
AtFullSide/K12/LettersReadyW.lean and FiveAt355.lean of this folder.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.AcceptedAtHeadFiller
import Johnson.Desc.ProofFile.Honest.K13.AcceptedByTies
import Johnson.Desc.ProofFile.Honest.K11.ThreeTiesBare
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LayersTieHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadCallsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Chain Strs Place foldBlocks)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Honest (roundsAhead PileIs)
open ProofFile.Honest.K11 (headFourOfK6 headClaimIsOfKeysBare)
open ProofFile.Honest.K3.Law.AtThr (lookOfK3 headKeysOfK3 head_keys_tie htie_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`PileIs` AT THE FIRST CHAIN's OWN LIST, THE BORDER 355, OF THE FILLER OVER THE TEXT OF THE
CLAIMS WITH ALL ITS ARMS LAID**: under h and a base. An implication from the fold's return. -/
theorem k13_pileIs_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (Q₀ : Nat → K4Pub) :
    PileIs cF.blocksInOrder (fun ξ : ProofFile.Inst => ProofFile.startS Zp ξ.pub) 355 (roundsAhead cF.blocksInOrder 355)
      (fillerAt cF Zp (claimsText cF Zp (lookOfK3 Zp cF)
        (headArmOf (headFourOfK6 (headKeysOfK3 cF) (roundsAhead cF.blocksInOrder 341)) Zp Bs) Q₀))
      ProofFile.Inst.asked := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  exact pileIs_at_chain h.scope h.reads O (P5J.flat_ok h.toAtMg) (fun ξ : ProofFile.Inst => ξ.pub) _
    (claimsText cF Zp (lookOfK3 Zp cF)
      (headArmOf (headFourOfK6 (headKeysOfK3 cF) (roundsAhead cF.blocksInOrder 341)) Zp Bs) Q₀)
    ProofFile.Inst.asked
    (Szd := fun _ => OnBytes.PscRun.Sized)
    (Tie := fun g ξ hd fo => ((smallIn Zp (lookOfK3 Zp cF g) ξ).look hd).zk = fo.zk)
    (tokOf := fun g ξ => (smallIn Zp (lookOfK3 Zp cF g) ξ).tokv)
    (fun g hg => layersFront_of_tie h (fun ξ : ProofFile.Inst => ProofFile.startS Zp ξ.pub) g hg
      (fun ξ hd fo => (lookOfK3 Zp cF g ξ hd).zk = fo.zk) (htie_head h g hg))
    (hlaw_of_k4 _ (k4PubsOf cF Zp Q₀) (fun g => smallIn Zp (lookOfK3 Zp cF g))
      (k4PubsAt_term h.scope h.reads O Q₀)
      (fun g hg ξ hd => claimsText_arm cF Zp _ _ Q₀ g hg ξ hd))
    (headClaimIsOfKeysBare (headKeysOfK3 cF) Z D r Zp Np cF x Bs 24
      (fun _ => headArmOf (headFourOfK6 (headKeysOfK3 cF) (roundsAhead cF.blocksInOrder 341)) Zp Bs) h hB
      (fun _ _ => rfl) (head_keys_tie h Bs.G₀))
    (hreach_at_flat h.scope h.reads O) (hfive_at_head h _)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_pileIs_at_head
