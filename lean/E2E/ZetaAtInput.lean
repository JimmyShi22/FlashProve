-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaAtInput.lean: twelve numbers of the verifier's parameters at Z, for every Z in scope.

Summary. These twelve bounds are all that the bound on `zetaW` (E2E/ZetaAtCaps.lean) uses of the
parameters and the wiring.

Main results.
  `twelve_description`: `Twelve` holds at the verifier's parameters at Z, for every Z in scope,
    whether or not the description is live.
  `Twelve r` states: both lengths of salts are at least 256 bits · the tree over an encoded index is
    32 deep · the three protocols' trees have at most 2 ^ 37, 2 ^ 25 and 2 ^ 39 leaves · each
    protocol has at most 2 ^ 20 rounds · each request tree is at most 2 ^ 20 deep.

Terms: E2E/HidingTerms.lean.

Limits.
- That the parameters' first two numbers are the lengths of the salts that the programs use is the
  library's reading of its own files (Johnson/Top/Fire/Code/Vals/DvFull.lean). No theorem states it.
- Bounds, not the numbers themselves. No security property is stated.

Definitions and helper lemmas.
  `twelve_atFiles`: at the structure of parameters from which the verifier is compiled.
  `twelve_built`: at the parameters of the value that the library builds.


-/
import E2E.ZetaNumbers
import Johnson.Goal.Description.Description
import Johnson.Top.Fire.Code.TieAtValues

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.ZetaAt
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput innerCompilerInputAtFullSize)
open OnBytes.Slice (frS frZ)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open LPFD.Full (sBG sTG saltG)

/-- **Twelve numbers of the parameters and the wiring**: the two lengths of salts; the depth of
the tree over an encoded index; the leaves of the three wirings' trees; the three protocols' rounds;
the depths of the three request trees. -/
structure Twelve (r : InnerCompilerInput) : Prop where
  sMT : 256 ≤ r.compilerParameters.sMT
  sFS : 256 ≤ r.compilerParameters.sFS
  depth : r.queryLayout.depth = 32
  lvT : lv r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh ≤ 2 ^ 37
  lvL : lv r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh ≤ 2 ^ 25
  lvB : lv r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh ≤ 2 ^ 39
  rT : r.protocol.offline.shape.length ≤ 2 ^ 20
  rL : r.protocol.link.shape.length ≤ 2 ^ 20
  rB : r.protocol.onlineBatch.loc.shape.length ≤ 2 ^ 20
  qT : r.queryLayout.depthReqT ≤ 2 ^ 20
  qL : r.queryLayout.depthReqL ≤ 2 ^ 20
  qB : r.queryLayout.depthReq ≤ 2 ^ 20

/-- **At the structure of parameters from which the verifier is compiled**, for every Z in scope,
whether or not the description is live. -/
theorem twelve_atFiles (Z : PublicFiles) (scope : InScope Z = true)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) :
    Twelve (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) := by
  have hr := rounds_atFiles Z
  obtain ⟨hk, hp⟩ := leaves_atFiles Z scope
  have lv3 := lv_fullD (dataAtFiles flashProveData Z).A
    (OnBytes.Flat.relationsAndEncodingOfClaims (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E)
    (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
    PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀
    (dataAtFiles flashProveData Z).G.z₀.2 (sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).P
    (LPFD.Full.KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) (sTG (dataAtFiles flashProveData Z).G).logLeaves
  have rd3 := rounds_fullD (dataAtFiles flashProveData Z).A
    (OnBytes.Flat.relationsAndEncodingOfClaims (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E)
    (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
    PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀
    (dataAtFiles flashProveData Z).G.z₀.2 (sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).P
  exact
    { sMT := Nat.le_add_right 256 (8 * saltG (dataAtFiles flashProveData Z).G)
      sFS := Nat.le_refl 256
      depth := Johnson.G.fr_a
      lvT := le_of_eq_of_le lv3.1 (Nat.le_of_lt hk)
      lvL := le_of_eq_of_le (lv3.2.1.trans leaves_link) (by norm_num)
      lvB := le_of_eq_of_le lv3.2.2 (Nat.le_of_lt hp)
      rT := le_of_eq_of_le rd3.1 (by omega)
      rL := le_of_eq_of_le (rd3.2.1.trans (by rw [rounds_link])) (by norm_num)
      rB := le_of_eq_of_le rd3.2.2 (by omega)
      qT := show (sTG (dataAtFiles flashProveData Z).G).logLeaves ≤ _ by omega
      qL := Nat.zero_le _
      qB := show (sBG (dataAtFiles flashProveData Z).G).logLeaves ≤ _ by omega }

/-- At the parameters of the value that the library builds. -/
theorem twelve_built (Z : PublicFiles) (scope : InScope Z = true) (c : VerifiableInference.Digest)
    (m : (FlashProve.descriptionOfDataOnBytes flashProveData).More) :
    Twelve ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m) := twelve_atFiles Z scope c m

/-- **At the verifier's parameters at Z**, for every Z in scope. -/
theorem twelve_description (Z : PublicFiles) (scope : InScope Z = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      Twelve ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), Twelve (D.input Z c m))
    fun c m => twelve_built Z scope c m

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.twelve_atFiles
#print axioms AtPublicFiles.ZetaAt.twelve_built
#print axioms AtPublicFiles.ZetaAt.twelve_description
