-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FreeAt.lean: **THE TOWER'S FREE LETTERS AT ONE CLOSED VALUE**: `AtMg.free h 𝔇₀` : Free …
(TowerFree.lean's 21 fields), every field a named term of its files; and the tower's joining theorem
CALLED at it.
  `AtMg.free`      `AtMg.freeOf` (FreeShared.lean: the shared table's, the lists' and the top's
                   letters) at the last table's and the pieces' letters of L0/Last.lean.
  `free_q₁ q₂ q₃`  the three lists' heads: theorems at the value.
  `free_sh`        tables_fit's field SH at the value, under the shared table's files' test on the
                   sizes (hA).
  **`rows_at_free`** `rows_at_mg` at the value: AtMg → (∀ K, h.KindR 𝔇₀ (h.free 𝔇₀) K) →
                   h.Five 𝔇₀ (h.free 𝔇₀) depthReq → h.Seven …: no letter 𝔏 and no premise on one.
WHICH FIELDS ARE IDLE (a value is laid because the structure wants one; nothing is read of it):
Q₀ (`placesM_any`) · e₁ e₂ · dW wEnd (L0/Last.lean's head says why, by reading). 𝔇₀ is still a
letter (the composed meaning's).
Limits. A VALUE AND CALLS: no law is paid: no member of h.Kind or h.Five at the value is known.
Whether AtMg can be met at the release's own files is not shown here. The full size alone. No
soundness follows. Nothing on hiding. It holds no coding theory.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FreeShared
import Johnson.P5J.KeyFitsAtMg
import Johnson.P5J.L0.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open Desc.K14.Law.Fence (numbersSh)
open Desc.K14.Law (ShPlan ShOpen Sh.planAt Sh.openAt Sh.Open₁ Sh.nums Sh.mg Sh.pm Sh.own Sh.ex)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE VALUE.** -/
def AtMg.free (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp)) :
    Free numsFull D (F0T o Zp Np cF) At.Tok :=
  h.freeOf 𝔇₀ (L0.mlAt o D Zp Np cF) (L0.plmAt o Zp Np cF (Desc.K14.Law.Sh.X h.shPlan 12))
    (L0.e1At o D Zp Np cF) (L0.e2At o D Zp Np cF)
    (L0.e3At o Z D Zp Np cF (Desc.K14.Law.Sh.oNo h.shPlan) (Desc.K14.Law.Sh.ms h.shPlan)
      (numbersSh (Desc.K14.Law.Sh.t₁ h.shPlan) (Desc.K14.Law.Sh.layU h.shPlan)
        (Desc.K14.Law.Sh.layO h.shPlan) (0, 0) (0, 0)))
    L0.dWAt L0.dWAt

/-- **The default statement** (the plain form's last letter): nothing is asked of it. The empty request
    at the empty key, the first chain's start there, no oracle's string. -/
def AtMg.dIdle (_ : AtMg o Z D r Zp Np cF) :
    ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str :=
  (((⟨ByteArray.empty, {}⟩ : ProofFile.InstPub), (F0T o Zp Np cF).start₁ ⟨ByteArray.empty, {}⟩),
    (fun _ => (0, []), fun _ => []))

variable (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
  (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))

theorem free_q₁ : (F0T o Zp Np cF).first.blocksInOrder = (h.free 𝔇₀).c₁ :: (h.free 𝔇₀).k₁ :=
  freeOf_q₁ h 𝔇₀ _ _ _ _ _ _ _
theorem free_q₂ : (F0T o Zp Np cF).shared.blocksInOrder = (h.free 𝔇₀).c₂ :: (h.free 𝔇₀).k₂ :=
  freeOf_q₂ h 𝔇₀ _ _ _ _ _ _ _
theorem free_q₃ : (F0T o Zp Np cF).second.blocksInOrder = (h.free 𝔇₀).c₃ :: (h.free 𝔇₀).k₃ :=
  freeOf_q₃ h 𝔇₀ _ _ _ _ _ _ _

/-- The top's own sample. -/
theorem free_rP : (h.free 𝔇₀).rP = VerifierAndGoals.AtTheName.recZ Z := rfl

/-- **The tower's Rc is the shared table's constant's R.** -/
theorem rc_is_R : h.rc = (h.shOpen 𝔇₀).R := rfl

/-- The two later tables' own condition, as the tower spells it, is the constant's. -/
theorem free_own : ocR (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
      ((a.1, a.2) : (F0T o Zp Np cF).XiPub × TS)) (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps h.rc =
    Sh.own h.shPlan (h.shOpen 𝔇₀) := rfl

/-- **tables_fit's field SH at the value.** -/
theorem free_sh (hA : H2K.Sizes.AtFull Zp.p.chains.made)
    (p : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) (hp : h.rc p) :
    (h.free 𝔇₀).Pm.shape 0 ((F0T o Zp Np cF).start₂ p.1) = true :=
  h.sh_of_start (h.free 𝔇₀) (freeOf_hk h 𝔇₀ _ _ _ _ _ _ _ hA) p hp

set_option maxHeartbeats 4000000 in
/-- **THE TOWER's JOINING THEOREM, CALLED AT THE VALUE.** -/
theorem rows_at_free (depthReq : ℕ)
    (kinds : ∀ K, h.KindR 𝔇₀ (h.free 𝔇₀) K) (V : h.Five 𝔇₀ (h.free 𝔇₀) depthReq)
    (d : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (EAll (D.at frS.P.T.a)
        (VerifiableInference.Desc.Sound.allOf (D.at frS.P.T.a))).Str)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {b : Bool} (hb : b = true)
    {runP : (kcReq numsFull (ppAtFiles Z.pol Z.KL) (At.EAt Z)).conf.X × RecFull → PQ.View → PQ.View
        → PQ.View → Bool}
    (er : runP = gatedFileDecision b ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord).run)
    {P : (threeProtocolsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL))
      (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL)) (At.EAt Z))
          DK D runK runP ds xs dec rK (h.free 𝔇₀).rP
      depthReq reqWithoutReply salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL))
        (At.EAt Z) DK D runK runP ds xs
      dec rK (h.free 𝔇₀).rP depthReq reqWithoutReply salt K P) :
    h.Seven 𝔇₀ (h.free 𝔇₀) depthReq d Tl :=
  rows_at_mg h 𝔇₀ (h.free 𝔇₀) depthReq (free_q₁ h 𝔇₀) (free_q₂ h 𝔇₀) (free_q₃ h 𝔇₀) kinds V d hb er
    Tl

end P5J

#print axioms P5J.free_q₁
#print axioms P5J.free_q₂
#print axioms P5J.free_q₃
#print axioms P5J.free_rP
#print axioms P5J.rc_is_R
#print axioms P5J.free_own
#print axioms P5J.free_sh
#print axioms P5J.rows_at_free
