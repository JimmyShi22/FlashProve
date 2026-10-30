-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineAcceptedInSoundnessWords.lean: THE OFFLINE CLAUSE OF COMPLETENESS, SAID IN THE WORDS OF SOUNDNESS. From the list of named statements on the key file's
prover (`OfflineDebts`, E2E/CompleteAsIOPOffline.lean) at no fall and at measures 0: the honest offline prover's own run, at
challenges cleared BY SOUNDNESS's OWN CLEARING (`offlineClearing`, E2E/SoundAsIOPProbabilityAtFiles.lean), laid as the offline part of a whole run
of soundness (`WholeRun`, Hiop/SoundAsIOP.lean) with the honest table as its first table and that table's own out-of-domain sample as
its first sample, meets the first clause of `WholeRun.Accepted`.

  `null_is_empty`              a set of measure 0 under the uniform law on a finite type is empty
  `nothing_is_withheld`        at measures 0 the prover's abort set is empty
  `offline_accepts_own_run`    `(protocolAtFiles Z).offline.accept (recOf i r e) (encodeIndex i r) ‹the run at cleared challenges› = true`, at every coin
  `offline_part_of_whole_run`  **the same as the first clause of `WholeRun.Accepted`**, whatever the run's other parts

Why. That completeness and soundness name one protocol is seen in their definitions. This is a CALL: its proof feeds what completeness's
list gives into the very terms of soundness's conclusion: it type-checks only if the verifier, the instance, the table and the
clearing of the two are the same terms.

Limits. AN IMPLICATION from `OfflineDebts`: no value of it is shown here. The offline part alone: nothing on the link or the online part, so
`WholeRun.Accepted` whole is not concluded. It spends no theorem of soundness. Nothing on any property.
-/
import E2E.CompleteAsIOPOffline
import E2E.CompleteAsIOPWorkBits
import E2E.SoundAsIOPProbabilityAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.OneProtocol
open Iop Prob
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open TypedOracleCompiler.Iop (RoundsQueryLayout.cleared_clearing)
open TypedOracleCompiler.Compile.Batch.Cms (wTC)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts)
open LPFD.Full (XF)
open AtPublicFiles.AtFiles AtPublicFiles.Committed
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

local instance (priority := high) acceptedWordsPads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) acceptedWordsNonempty {α : Type} [Inhabited α] : Nonempty α :=
  ⟨default⟩

/-- A set of measure 0 under the uniform law on a finite type is empty. -/
theorem null_is_empty {C : Type} [Fintype C] [Nonempty C] (S : Set C) (h : pr (unif C) S ≤ 0) :
    S = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun a ha => ?_
  have h1 : pr (unif C) {a} ≤ pr (unif C) S := pr_mono _ (Set.singleton_subset_iff.2 ha)
  rw [pr_singleton] at h1
  exact (PMF.mem_support_iff _ _).1 (PMF.mem_support_uniformOfFintype a)
    (le_antisymm (h1.trans h) (zero_le _))

variable {Z : PublicFiles} {Fx : FileDescription KeyInst} {TrT X₀T XT Q₂ Q₃ : Type} {BT : ProverCoinCounts} [Fintype Q₂]
  [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃]
  {HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT}
  {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray} {shT : TableKey → Fx.S₂}
  {Relation : FullSizeMatrix → XF → Prop} {Tied TiedM : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)}

/-- **At measures 0 the prover's abort set is empty.** -/
theorem nothing_is_withheld
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation (fun _ _ _ => ∅) Tied TiedM 0 0 0) (i : FullSizeMatrix)
    (x : XF) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (hy : Relation i x) :
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).withheld (i, r, e) ((protocolAtFiles Z).recOf i r e) = ∅ := by
  have hb : (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Bad = ∅ := null_is_empty _ d.bad
  have hh : (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e) = ∅ :=
    null_is_empty _ (d.hid (i, r, e) ((protocolAtFiles Z).recOf i r e) (d.tiedM i x r e hy))
  unfold Iop.Honest.withheld
  rw [hb, hh, Set.union_empty]

/-- **The offline verifier accepts the honest prover's own run, at challenges cleared by soundness's own clearing.** -/
theorem offline_accepts_own_run
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation (fun _ _ _ => ∅) Tied TiedM 0 0 0) (i : FullSizeMatrix)
    (x : XF) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (hy : Relation i x)
    (c : (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Coin) (ρ : Rho (protocolAtFiles Z).offline.shape) :
    (protocolAtFiles Z).offline.accept ((protocolAtFiles Z).recOf i r e) ((protocolAtFiles Z).encodeIndex i r)
      (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
        ((offlineClearing Z).cleared ρ)).1 = true := by
  have hf := (workFaithful_atFiles Z).offline
  have hcl : (offlineClearing Z).cleared ρ = (workAtFiles Z).offline.cleared ρ :=
    RoundsQueryLayout.cleared_clearing (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh ρ
  rw [hcl]
  have hρ := Strat.rho_run ((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c)
    ((workAtFiles Z).offline.cleared ρ)
  have hp : (workAtFiles Z).offline.passes
      (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
        ((workAtFiles Z).offline.cleared ρ)).1.rho = true := by
    rw [hρ]
    exact hf.clearedPasses ρ
  have hs : (workAtFiles Z).offline.sameButForNonces
      (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
        (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
          ((workAtFiles Z).offline.cleared ρ)).1.rho).1
      (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
        ((workAtFiles Z).offline.cleared ρ)).1 := by
    rw [hρ]
    exact hf.ownNonces _
  have hn : (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
        ((workAtFiles Z).offline.cleared ρ)).1.rho ∉
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).withheld (i, r, e) ((protocolAtFiles Z).recOf i r e) ∪
        (∅ : Set (Rho (protocolAtFiles Z).offline.shape)) := by
    rw [nothing_is_withheld d i x r e hy, Set.union_empty]
    exact Set.notMem_empty _
  have ha := d.accepted (i, r, e) ((protocolAtFiles Z).recOf i r e) c (d.tied i x r e hy)
    (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
      ((workAtFiles Z).offline.cleared ρ)).1 hp hs hn
  rw [extIsEnc_obj Z Fx BT (dataAtFiles flashProveData Z).P HT _ shT i r e] at ha
  exact ha

/-- **THE SAME AS THE FIRST CLAUSE OF `WholeRun.Accepted`**: the whole run of soundness whose first table is the honest table, whose first sample
is that table's own, and whose offline part is the honest run; its other parts are whatever. -/
theorem offline_part_of_whole_run
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation (fun _ _ _ => ∅) Tied TiedM 0 0 0) (i : FullSizeMatrix)
    (x : XF) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (hy : Relation i x)
    (c : (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Coin) (ρ : Rho (protocolAtFiles Z).offline.shape) (run : (protocolAtFiles Z).WholeRun)
    (hT : run.firstTable = (protocolAtFiles Z).encodeIndex i r) (hS : run.firstSample = (protocolAtFiles Z).recOf i r e)
    (hO : run.offline = (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
      ((offlineClearing Z).cleared ρ)).1) :
    (protocolAtFiles Z).offline.accept run.firstSample run.firstTable run.offline = true := by
  rw [hT, hS, hO]
  exact offline_accepts_own_run d i x r e hy c ρ

end AtPublicFiles.OneProtocol

#print axioms AtPublicFiles.OneProtocol.null_is_empty
#print axioms AtPublicFiles.OneProtocol.nothing_is_withheld
#print axioms AtPublicFiles.OneProtocol.offline_accepts_own_run
#print axioms AtPublicFiles.OneProtocol.offline_part_of_whole_run
