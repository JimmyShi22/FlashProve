-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/OmegaWindowAtTerm.lean: THE WINDOW ON o_omega's TREE AT THE SEATED IOP's OWN TERM F0T o Zp Np
cF AND AT THE PIECES THAT THE MAKER CUTS OUT OF IT: the second and third premise of omegaForward |
omegaBack (Johnson/Desc/Sound/OmegaCrosses.lean) IN THE LETTERS AT WHICH THE TOWER ASKS TablesFitR's
fields POf | POb (Johnson/P5J/TowerEnd.lean: T := piecesAt (ckP .two) F₀ ‹the data› c₁ k₁ c₂ k₂ c₃ k₃
‹three rests› dW wEnd). One theorem: a call of Johnson/Desc/K14/Law/OmegaWindowAtDesc.lean.

  omega_window_at_term   from hp : F₀.planOk = true · hD : F₀.data "proof file" = .ok DP (THE TOWER's OWN TWO
      BINDERS; DP is whatever data stand there, D.at frS.P.T.a among them) · the three chains' sub-protocols
      by name (q₁ q₂ q₃) · the two sendings' layouts at the seat's own parameters p14Of Zp.p.chains
      (beforePointOf Np) · hN · hNlo.
PAID HERE: the row's first base, its written rounds and "tiled": paidAtDesc · hG (the shared
chain tells what chainOf tells): the term's shared chain IS that chain behind Chain.retype: oracles_retype.
IT SPEAKS OF ANY NUMBERS Ns WHOSE FIRST TREE IS THE NUMBER OF TREES THAT THE FIRST CHAIN TELLS (hNlo) AND WHOSE
TENANTS ARE tenantSh THERE (hN). Whether the tower's own letter for the shared table's numbers is laid so is
not shown here: at another first tree hN | hNlo are false and this theorem serves nobody.
What is not claimed. ReadsTree. That the premises are met anywhere. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.OmegaWindowAtDesc
import Johnson.P5J.AtTerm
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Flat.Dec.PlanOkForFree
import Johnson.Desc.Sound.OmegaCrosses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block FileDescription Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (Numbers)
open _root_.Run _root_.Run.PQ
open Desc.K14 (St p14Of beforePointOf withU withOmega)
open Desc.K14.Law.Fence (tenantSh oracles_retype)

/-- **The window on o_omega's tree, at the seated IOP's own term and the maker's own pieces.** -/
theorem omega_window_at_term (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (DP : WholeD) {W : Type}
    (hp : (F0T o Zp Np cF).planOk = true) (hD : (F0T o Zp Np cF).data "proof file" = .ok DP)
    (c₁ : Block (F0T o Zp Np cF).S₁ (F0T o Zp Np cF).Cl)
    (k₁ : List (Block (F0T o Zp Np cF).S₁ (F0T o Zp Np cF).Cl))
    (c₂ : Block (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).Cl)
    (k₂ : List (Block (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).Cl))
    (c₃ : Block (F0T o Zp Np cF).S₃ (F0T o Zp Np cF).Cl)
    (k₃ : List (Block (F0T o Zp Np cF).S₃ (F0T o Zp Np cF).Cl))
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = c₁ :: k₁) (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = c₂ :: k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = c₃ :: k₃)
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt DP (allOf DP) DP.key₁ 0)
      ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt DP (allOf DP) DP.key₂ 0)
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt DP (allOf DP) DP.key₃ (F0T o Zp Np cF).lastChainFirstTreeNumber)
        (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) ×
          (F0T o Zp Np cF).S₃) W ds)
    (dW wEnd : W) (sU : Array OracleNotice)
    (hU : withU (p14Of Zp.p.chains (beforePointOf Np)).S = some sU) (layU layO : TreeLay)
    (hlU : layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes sU = some layU)
    (hlO : layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes
      (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S) = some layO)
    (N₁ : Numbers) (Ns : NumbersS)
    (hN : Ns.tenant =
      tenantSh (VerifiableInference.Desc.oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length layU layO)
    (hNlo : Ns.lo = (VerifiableInference.Desc.oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length) :
    (tiedNumbers N₁ Ns).lo ≤ ((tiedNumbers N₁ Ns).tenant .oOmega).1 ∧
      ((tiedNumbers N₁ Ns).tenant .oOmega).1 <
        hiAt (1 + (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
            wEnd).l₂.length)
          (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).p₂
          (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).l₂ :=
  have hF := (paidAtDesc _ W (F0T o Zp Np cF) "proof file" DP hD
    (sealLast_of_planOk (F0T o Zp Np cF) hp) (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ rest₁ rest₂ rest₃
    dW wEnd).2.1
  Desc.K14.Law.omega_window_at_desc (F0T o Zp Np cF) "proof file" DP hp hD
    (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)
    hF.base₂ hF.data₂ hF.tiled₂ Zp.p.chains (p14Of Zp.p.chains (beforePointOf Np))
    (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last
    (oracles_retype _ rfl) sU hU layU layO hlU hlO N₁ Ns hN hNlo

/-- The two comparisons are handed to `omegaForward` and `omegaBack` at these pieces and numbers: that
this elaborates is the fit. (An example: no declaration; it is to be counted by nobody. ReadsTree stays a
premise.) -/
example (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (DP : WholeD) {W : Type}
    (hp : (F0T o Zp Np cF).planOk = true) (hD : (F0T o Zp Np cF).data "proof file" = .ok DP)
    (c₁ : Block (F0T o Zp Np cF).S₁ (F0T o Zp Np cF).Cl)
    (k₁ : List (Block (F0T o Zp Np cF).S₁ (F0T o Zp Np cF).Cl))
    (c₂ : Block (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).Cl)
    (k₂ : List (Block (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).Cl))
    (c₃ : Block (F0T o Zp Np cF).S₃ (F0T o Zp Np cF).Cl)
    (k₃ : List (Block (F0T o Zp Np cF).S₃ (F0T o Zp Np cF).Cl))
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = c₁ :: k₁) (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = c₂ :: k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = c₃ :: k₃)
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt DP (allOf DP) DP.key₁ 0)
      ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt DP (allOf DP) DP.key₂ 0)
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt DP (allOf DP) DP.key₃ (F0T o Zp Np cF).lastChainFirstTreeNumber)
        (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) ×
          (F0T o Zp Np cF).S₃) W ds)
    (dW wEnd : W) (sU : Array OracleNotice)
    (hU : withU (p14Of Zp.p.chains (beforePointOf Np)).S = some sU) (layU layO : TreeLay)
    (hlU : layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes sU = some layU)
    (hlO : layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes
      (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S) = some layO)
    (N₁ : Numbers) (Ns : NumbersS)
    (hN : Ns.tenant =
      tenantSh (VerifiableInference.Desc.oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length layU layO)
    (hNlo : Ns.lo = (VerifiableInference.Desc.oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length)
    (Mg : MeaningS (F0T o Zp Np cF).S₂ ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) W)
    (Pm : PromMeaning (F0T o Zp Np cF).S₂) (hR : ReadsTree Mg Pm) : True :=
  have h := omega_window_at_term o Zp Np cF DP hp hD c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ rest₁ rest₂ rest₃ dW wEnd sU hU
      layU layO hlU hlO N₁ Ns hN hNlo
  have _f := omegaForward _ _ _ _ _ _ _ _ _ _ _ _ (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)
    (tiedNumbers N₁ Ns) Mg Pm hR h.1 h.2
  have _b := omegaBack _ _ _ _ _ _ _ _ _ _ _ _ (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)
    (tiedNumbers N₁ Ns) Mg Pm hR h.1 h.2
  trivial

end P5J

#print axioms P5J.omega_window_at_term
