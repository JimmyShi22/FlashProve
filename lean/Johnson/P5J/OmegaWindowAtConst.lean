-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/OmegaWindowAtConst.lean: THE WINDOW ON o_omega's TREE AT THE SHARED TABLE's CONSTANT's OWN NUMBERS
(Sh.nums A O = tiedNumbers O.N₁ (numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) (0, 0) (0, 0)), at A := Sh.planAt Zp
Np (F0T o Zp Np cF)) AND AT THE PIECES THAT THE MAKER CUTS OUT OF THE SEATED IOP's OWN TERM: the premise «hw» of
Sh.POf_of_window | Sh.POb_of_window (Johnson/Desc/K14/Law/SharedConstPo.lean), to the letter. Two theorems: calls
of omega_window_at_desc (Johnson/Desc/K14/Law/OmegaWindowAtDesc.lean): its two premises on the numbers (hN · hNlo)
are rfl at the constant's numbers; its three on the two sendings are Sh.tests_hUw | _hlU | _hlO.

  window_at_plan    GENERAL IN THE PLAN A (a letter): so that the two rfl are taken at a letter, not at the seated
                    term (there Lean's unifier ran out of its heartbeats).
  window_at_const   that, at A := Sh.planAt Zp Np (F0T o Zp Np cF): from hp · hD · q₁ q₂ q₃ (the tower's own
                    binders) and Sh.Tests A.
  an example (no declaration): the window is handed to Sh.POf_of_window and Sh.POb_of_window at these pieces.
What is not claimed. That the tower's own letter for the shared table's numbers is laid at these numbers: that is
the laying's. That Sh.Tests accepts anywhere. Nothing on soundness.

-/
import Johnson.P5J.OmegaWindowAtTerm
import Johnson.Desc.K14.Law.SharedConstTests
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.Desc.K14.Law.SharedConstPo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block FileDescription Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (Numbers)
open _root_.Run _root_.Run.PQ
open Desc.K14.Law (ShOpen ShPlan)
open Desc.K14 (St chainOf p14Of beforePointOf)
open Desc.K14.Law.Fence (oracles_retype)
open Desc.K14.Law.Sh (planAt Tests sentU layU layO t₁ tests_hUw tests_hlU tests_hlO POf_of_window
  POb_of_window)
open Desc.K14.Law.Fence (numbersSh)

/-- **The window at the constant's own numbers, general in the plan.** -/
theorem window_at_plan {Xi : Type} (A : ShPlan Xi) (hT : Tests A) (file : String) (D : WholeD)
    (hp : A.G.planOk = true) (hD : A.G.data file = .ok D)
    {C : CK} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type}
    (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (hb : T.p₂.base = D.t₁)
    (hd : rowData T.p₂ T.l₂ = D.ds₂) (ht : Tiled T.p₂ T.l₂)
    (c : Model.Verify.Chains) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hG : VerifiableInference.Desc.oraclesOf A.G.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf c A.Q tests last).blocksInOrder) (N₁ : Numbers) :
    (tiedNumbers N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).lo ≤
        ((tiedNumbers N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).tenant .oOmega).1 ∧
      ((tiedNumbers N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).tenant .oOmega).1 <
        hiAt (1 + T.l₂.length) T.p₂ T.l₂ :=
  Desc.K14.Law.omega_window_at_desc A.G file D hp hD T hb hd ht c A.Q tests last hG (sentU A)
    (tests_hUw A hT) (layU A) (layO A) (tests_hlU A hT) (tests_hlO A hT) N₁ _ rfl rfl

/-- **The window at the constant's own numbers and the maker's own pieces.** -/
theorem window_at_const (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (DP : WholeD) {Cells Tok : Type}
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
      ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) (Wit Cells Tok MsgT) ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt DP (allOf DP) DP.key₂ 0)
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) (Wit Cells Tok MsgT) ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt DP (allOf DP) DP.key₃ (F0T o Zp Np cF).lastChainFirstTreeNumber)
        (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) ×
          (F0T o Zp Np cF).S₃) (Wit Cells Tok MsgT) ds)
    (dW wEnd : (Wit Cells Tok MsgT))
    (hT : Tests (planAt Zp Np (F0T o Zp Np cF))) (N₁ : Numbers) :
    (tiedNumbers N₁ (numbersSh (t₁ (planAt Zp Np (F0T o Zp Np cF))) (layU (planAt Zp Np (F0T o Zp Np cF)))
        (layO (planAt Zp Np (F0T o Zp Np cF))) (0, 0) (0, 0))).lo ≤
        ((tiedNumbers N₁ (numbersSh (t₁ (planAt Zp Np (F0T o Zp Np cF))) (layU (planAt Zp Np (F0T o Zp Np cF)))
        (layO (planAt Zp Np (F0T o Zp Np cF))) (0, 0) (0, 0))).tenant .oOmega).1 ∧
      ((tiedNumbers N₁ (numbersSh (t₁ (planAt Zp Np (F0T o Zp Np cF))) (layU (planAt Zp Np (F0T o Zp Np cF)))
        (layO (planAt Zp Np (F0T o Zp Np cF))) (0, 0) (0, 0))).tenant .oOmega).1 <
        hiAt (1 + (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).l₂.length)
          (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).p₂
          (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).l₂ :=
  have hF := (paidAtDesc _ (Wit Cells Tok MsgT) (F0T o Zp Np cF) "proof file" DP hD
    (sealLast_of_planOk (F0T o Zp Np cF) hp) (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ rest₁ rest₂ rest₃
    dW wEnd).2.1
  have hG : VerifiableInference.Desc.oraclesOf (F0T o Zp Np cF).shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf Zp.p.chains
        (p14Of Zp.p.chains (beforePointOf Np)) (VerifiableInference.Desc.K12.Seat.tests Np)
        VerifiableInference.Desc.K12.Seat.last).blocksInOrder := oracles_retype _ rfl
  window_at_plan (planAt Zp Np (F0T o Zp Np cF)) hT "proof file" DP hp hD
    (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)
    hF.base₂ hF.data₂ hF.tiled₂ Zp.p.chains (VerifiableInference.Desc.K12.Seat.tests Np)
    VerifiableInference.Desc.K12.Seat.last hG N₁

/-- The window is handed to the two fields' lemmas at the constant: that this elaborates is the fit. (An example:
no declaration; it is to be counted by nobody.) -/
example (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (DP : WholeD) {Cells Tok : Type}
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
      ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) (Wit Cells Tok MsgT) ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt DP (allOf DP) DP.key₂ 0)
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) (Wit Cells Tok MsgT) ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt DP (allOf DP) DP.key₃ (F0T o Zp Np cF).lastChainFirstTreeNumber)
        (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) ×
          (F0T o Zp Np cF).S₃) (Wit Cells Tok MsgT) ds)
    (dW wEnd : (Wit Cells Tok MsgT))
    (hT : Tests (planAt Zp Np (F0T o Zp Np cF)))
    (O : ShOpen (F0T o Zp Np cF).XiPub ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) Cells Tok
      (planAt Zp Np (F0T o Zp Np cF)).Q) : True :=
  have h := window_at_const o Zp Np cF DP hp hD c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ rest₁ rest₂ rest₃ dW wEnd hT
    O.N₁
  have _f := POf_of_window (planAt Zp Np (F0T o Zp Np cF)) O DP (allOf DP) (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd) h
  have _b := POb_of_window (planAt Zp Np (F0T o Zp Np cF)) O DP (allOf DP) (piecesAt (ckP .two) (F0T o Zp Np cF) DP c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd) h
  trivial

end P5J

#print axioms P5J.window_at_plan
#print axioms P5J.window_at_const
