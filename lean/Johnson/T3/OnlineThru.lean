-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OnlineThru.lean: the online clause of the zero-knowledge statement (ZeroKnowledgeOnServedRequests) at the prover read through, from the kinds and the invariants at the base filling.
Owed at the base's own prover, read through once (owed_thru), at the committer's columns (owed_atCommitter), at the description. Conditional
lemmas on this library's definitions: no value of any premise is given here.
-/
import Johnson.T3.OwedOfKinds
import Johnson.T3.OwedThru

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed
open ProofFile.Honest (Prover Sides Owed relAt AtHonest OnlineProverWithDescription OnlineProverParts ready Committer)
open VerifiableInference.Desc (Chain)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) onlineThruInstance1 : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) onlineThruInstance2 {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

section Base
variable {W₀ Rc Tr X₀ X : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {P : OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {G : Sides A.F A.B W₀ Rc TableKey Tr X₀ X}
  {more : List (String × Bool)} {Rel : W₀ → Rc → ProofFile.Inst → Prop}

/-- **Owed at the base's own prover, from the kinds.** -/
theorem owed_of_kinds_atBase (hd : AtHonest o Z D r Zp Np cF x P A G more)
    (debts : RowDebtsP A G A.H Rel) : Owed A.F A.B A.H G.mute Rel :=
  have hand₁ := fun L hL σ hσ => (debts.kinds L.place.kind).1 L hL rfl σ hσ
  have hand₂ := fun L hL σ hσ => (debts.kinds L.place.kind).2.1 L hL rfl σ hσ
  have hand₃ := fun L hL σ hσ => (debts.kinds L.place.kind).2.2 L hL rfl σ hσ
  have hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready A.F A.B (G.prover A.H) w₀ rc x k = .ok R := by
    obtain ⟨w₁, rc₁, ξ₁, k₁, R₁, h₁⟩ := hd.one
    have h₂ : ready A.F A.B (G.prover A.H) w₁ rc₁ ξ₁ k₁ = .ok R₁ := by rw [hd.ring]; exact h₁
    exact fun w₀ rc x hrel k =>
      ProofFile.Honest.ready_any h₂ (debts.input w₀ rc x hrel).1 (debts.input w₀ rc x hrel).2 k
  ProofFile.Honest.owed_mute_of_threads_at_run hd.plan hd.book hd.seats hd.seal hd.rooted hand₁ hand₂ hand₃
    debts.input debts.hst hready
    (fun w₀ rc x h k R hR => Classical.choose (debts.threads w₀ rc x h k R hR))
    (fun _ _ _ _ _ _ hR => ProofFile.Honest.partsStand_of_hand hd.plan hd.book hd.seats hand₁ hand₂ hand₃ hR)
    debts.hbud
    (fun w₀ rc x h k R hR => Classical.choose_spec (debts.threads w₀ rc x h k R hR))

end Base

section AtFiles
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {W₀ Rc Tr X₀ Xh : Type} {D : WholeD} {r : LPFD.Full.RunPF}
  {x : VerifiableInference.Desc.First.Look.Place} {P : OnlineProverParts W₀ Rc Tr X₀ Xh}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ Xh} {G : Sides A.F A.B W₀ Rc TableKey Tr X₀ Xh}
  {more : List (String × Bool)} {Rel₀ : W₀ → Rc → ProofFile.Inst → Prop}
  (g : FullSizeMatrix → W₀) (rd : (protocolAtFiles Z).EncodingRandomness → Rc) (d : FullSizeMatrix)

/-- The family at the rows read through is onlineProversOfCommitter at the prover read through. -/
theorem famG_thru (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more) :
    famG Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 (G.thru g rd)) (A.H.thru g rd d) =
      onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B (dataAtFiles flashProveData Z).P (A.H.thru g rd d) :=
  (famG_eq Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 (G.thru g rd)) (A.H.thru g rd d)).trans
    (by rw [sidesAt_prover, ProofFile.Honest.prover_thru, hd.ring])

/-- **Owed at the description, at the committer's prover over the prover read through**, from the kinds and the invariants at the base. -/
theorem owed_of_base {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (debts : RowDebtsP A G A.H Rel₀)
    (hrange : A.H.inRange (g d) = A.H.inRange A.H.dummy)
    (hRel : ∀ w rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord w rc x →
      Rel₀ (g w) (rd rc) x)
    (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = A.H.key)
    (hcols : ∀ w rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord w rc x →
      ProofFile.Honest.CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H g rd w rc) :
    Owed (descZ Zp Np cF) A.B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 (A.H.thru g rd d))
      (sidesAt hd.isTerm.2 (G.thru g rd)).mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord) :=
  owed_sidesAt hd.isTerm.2
    (ProofFile.Honest.owed_atCommitter (cmAlong (AZ Z) PadZ (holdZ Z)) 0 hk
      (fun w rc x h => funext fun it => funext fun p => hcols w rc x h it p)
      (ProofFile.Honest.owed_thru g rd d (owed_of_kinds_atBase hd debts) hrange hRel))

/-- **The online clause at the prover read through, from the base.** -/
theorem online_exact_of_base (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (debts : RowDebtsP A G A.H Rel₀)
    (hrange : A.H.inRange (g d) = A.H.inRange A.H.dummy)
    (hRel : ∀ w rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord w rc x →
      Rel₀ (g w) (rd rc) x)
    (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = A.H.key)
    (hcols : ∀ w rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord w rc x →
      ProofFile.Honest.CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H g rd w rc)
    (owns : G.owns = true)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    ExactOutsideStops
      ((HonestProvers.ofThreeProvers (proversOf hT hL (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B
                (dataAtFiles flashProveData Z).P (A.H.thru g rd d)))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online.cleared
      (onlineSimulator Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 (G.thru g rd)) (A.H.thru g rd d) n) := by
  rw [← famG_thru Z Zp Np cF run₂ run₃ g rd d hd]
  exact online_exact_of_owed_atServed Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 (G.thru g rd))
    (A.H.thru g rd d) scope live hr hd.laid (owed_of_base Z Zp Np cF g rd d hr hd debts hrange hRel hk hcols)
    ((sidesAt_owns hd.isTerm.2 (G.thru g rd)).trans ((ProofFile.Honest.owns_thru g rd G).trans owns)) hT hL n

/-- **The statement at the protocol, for the online prover onlineProversOfCommitter at the prover read through**, from the base. -/
theorem zeroKnowledgeOnServedRequests_of_base {zHid a : ℝ≥0∞}
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (debts : RowDebtsP A G A.H Rel₀)
    (hrange : A.H.inRange (g d) = A.H.inRange A.H.dummy)
    (hRel : ∀ w rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord w rc x →
      Rel₀ (g w) (rd rc) x)
    (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = A.H.key)
    (hcols : ∀ w rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord w rc x →
      ProofFile.Honest.CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H g rd w rc)
    (owns : G.owns = true)
    (hid : HidSmall (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B (dataAtFiles flashProveData Z).P (A.H.thru g rd d))
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a) zHid)
    (faithful : (workAtFiles Z).Faithful) (two : TwoIndicesServeOneRequest Z hr)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (offlineSimulator : Compile.Lifetime.SimOf (protocolAtFiles Z).offline)
    (offlineTable : ∀ i r e, hT.ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r)
    (offline : ExactOutsideStops hT (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y)
      (workAtFiles Z).offline.cleared offlineSimulator)
    (offlineStops : PrivateStopsAtMost hT (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y)
      (workAtFiles Z).offline a) :
    ZeroKnowledgeOnServedRequests Z hr
      (HonestProvers.ofThreeProvers (proversOf hT (linkProverAtFiles committerCoinCountLessOne Z) (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B
                                            (dataAtFiles flashProveData Z).P (A.H.thru g rd d)))) a 0 zHid := by
  rw [← famG_thru Z Zp Np cF run₂ run₃ g rd d hd] at hid ⊢
  exact zeroKnowledgeOnServedRequests_of_owed Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 (G.thru g rd))
    (A.H.thru g rd d) scope live hr hd.laid (owed_of_base Z Zp Np cF g rd d hr hd debts hrange hRel hk hcols)
    ((sidesAt_owns hd.isTerm.2 (G.thru g rd)).trans ((ProofFile.Honest.owns_thru g rd G).trans owns)) hid
    faithful two hT offlineSimulator offlineTable offline offlineStops

end AtFiles

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.owed_of_kinds_atBase
#print axioms VerifiableInference.Compilation.famG_thru
#print axioms VerifiableInference.Compilation.owed_of_base
#print axioms VerifiableInference.Compilation.online_exact_of_base
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_of_base
