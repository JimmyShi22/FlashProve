-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPByBase.lean: the field yes of YesDebts at the public files, from ThreadsC at the base
prover: the prover that the family reads through. So a house assembles at the base, and the road
crosses once. It states no goal.

  BaseThreadsAt   at every tied input and coin: at the base prover ready returns, the plan serves, and
                  a value of ThreadsC stands, with the rows' own falls
  yesZ_of_base_threads   YesZ at TiedOut at the prover read through
  BaseThreadsJAt, yesZ_of_base_threadsJ   the same with ThreadsCJ

Limits. As E2E/RoadHonDebts.lean: hypotheses; BaseThreadsAt is shown of no prover.
-/
import E2E.CompleteAsIOPByYes
import E2E.CompleteAsIOPBaseThreads

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides ready PlanServes ThreadsC ThreadsCJ CommittedColumns)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

local instance (priority := high) nonemptyPadZ_byBase : Nonempty PadZ := pads_nonempty frS 402653181

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (Z : PublicFiles)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh W₀ Rc : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (g : FullSizeMatrix → W₀) (rd : (protocolAtFiles Z).EncodingRandomness → Rc) (d : FullSizeMatrix) (H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Xh)

/-- **At the base prover: ready, the plan, and the invariants with the rows' falls.** -/
def BaseThreadsAt (TiedX : ℕ → WZ Z → ProofFile.Inst → Prop) : Prop :=
  ∀ n w x (c : CoinG B R₂ R₃), TiedX n w x →
    ∃ R, ready (descZ Zp Np cF) B H (g w.1) (rd w.2.1) x (pursesOf c) = .ok R ∧
      PlanServes H (g w.1) (rd w.2.1) R ∧
      ∃ T : ThreadsC (descZ Zp Np cF) B H (g w.1) (rd w.2.1) x (pursesOf c) R,
        T.f₁ = G.falls₁ ∧ T.f₂ = G.falls₂ ∧ T.f₃ = G.falls₃

/-- **The same with ThreadsCJ.** -/
def BaseThreadsJAt (TiedX : ℕ → WZ Z → ProofFile.Inst → Prop) : Prop :=
  ∀ n w x (c : CoinG B R₂ R₃), TiedX n w x →
    ∃ R, ready (descZ Zp Np cF) B H (g w.1) (rd w.2.1) x (pursesOf c) = .ok R ∧
      PlanServes H (g w.1) (rd w.2.1) R ∧
      ∃ T : ThreadsCJ (descZ Zp Np cF) B H (g w.1) (rd w.2.1) x (pursesOf c) R,
        T.f₁ = G.falls₁ ∧ T.f₂ = G.falls₂ ∧ T.f₃ = G.falls₃

variable {Yes : FullSizeMatrix → XF → Prop}

/-- **The verdict at the run at the public files, from the invariants at the base prover.** -/
theorem yesZ_of_base_threads (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (Zs) (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true)
    (Q : PlainAt Z Zp Np cF B G (H.thru g rd d))
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d)
    (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = H.key)
    (hcols : ∀ n w x, TiedOut Z Zp Np cF run₂ run₃ B G (H.thru g rd d) Yes Zs n w x →
      CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 H g rd w.1 w.2.1)
    (htr : ∀ n w x, TiedOut Z Zp Np cF run₂ run₃ B G (H.thru g rd d) Yes Zs n w x →
      (H.trace (g w.1) x).isSome = true)
    (hbase : BaseThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G g rd H
      (TiedOut Z Zp Np cF run₂ run₃ B G (H.thru g rd d) Yes Zs)) :
    YesZ c₀ m₀ Z Zp Np cF run₂ run₃ B G (H.thru g rd d)
      (TiedOut Z Zp Np cF run₂ run₃ B G (H.thru g rd d) Yes Zs) := by
  refine yesAt_of_base_threads (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B G g rd d
    (cmAlong (AZ Z) PadZ (holdZ Z)) 0 H (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z) L.planOk
    Q.plainSeal (dataFits_atFiles Z Zp Np cF scope live L) Q.halved
    (due_atFiles Z Zp Np cF scope live L Q.nonZero) hd hrows hk _ _ (fun _ _ _ h => h.2.2) hcols htr
    (fun n w x c hx => ?_)
  exact ⟨firstAt_of_one Z Zp Np cF run₂ run₃ B G (H.thru g rd d) scope L h₀ Zs n w x hx,
    hbase n w x c hx⟩

/-- **The verdict at the run at the public files, from ThreadsCJ at the base prover.** -/
theorem yesZ_of_base_threadsJ (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (Zs) (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true)
    (Q : PlainAt Z Zp Np cF B G (H.thru g rd d))
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d)
    (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = H.key)
    (hcols : ∀ n w x, TiedOut Z Zp Np cF run₂ run₃ B G (H.thru g rd d) Yes Zs n w x →
      CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 H g rd w.1 w.2.1)
    (htr : ∀ n w x, TiedOut Z Zp Np cF run₂ run₃ B G (H.thru g rd d) Yes Zs n w x →
      (H.trace (g w.1) x).isSome = true)
    (hbase : BaseThreadsJAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G g rd H
      (TiedOut Z Zp Np cF run₂ run₃ B G (H.thru g rd d) Yes Zs)) :
    YesZ c₀ m₀ Z Zp Np cF run₂ run₃ B G (H.thru g rd d)
      (TiedOut Z Zp Np cF run₂ run₃ B G (H.thru g rd d) Yes Zs) := by
  refine yesAt_of_base_threadsJ (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B G g rd d
    (cmAlong (AZ Z) PadZ (holdZ Z)) 0 H (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z) L.planOk
    Q.plainSeal (dataFits_atFiles Z Zp Np cF scope live L) Q.halved
    (due_atFiles Z Zp Np cF scope live L Q.nonZero) hd hrows hk _ _ (fun _ _ _ h => h.2.2) hcols htr
    (fun n w x c hx => ?_)
  exact ⟨firstAt_of_one Z Zp Np cF run₂ run₃ B G (H.thru g rd d) scope L h₀ Zs n w x hx,
    hbase n w x c hx⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.yesZ_of_base_threads
#print axioms AtPublicFiles.AtFiles.yesZ_of_base_threadsJ
