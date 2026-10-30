-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaSalt.lean: the length of a leaf's salt at the verifier's parameters at Z: 256 + 320 bits,
for Z in scope with a live description.

Main results.
  `salt_atFiles`: for Z in scope with a live description, the plan's salt has 40 bytes: `saltG
    (dataAtFiles flashProveData Z).G = 40`.
  `sMT_description`: so `r.compilerParameters.sMT = 576` = 256 + 8 · 40 at the verifier's parameters at Z.

Terms: E2E/HidingTerms.lean.

Limits.
- Where the description is not live, nothing is proved about the salt's length.
- That a compiled run of the protocol publishes the first 256 of these bits, and that the other
  8 · 40 are the free ones, is not proved in Lean: it is by inspection of Johnson/WholeKey/Defs.lean
  and Johnson/Top/Fire/Code/Vals/DvFull.lean.
- No security property is stated.

Definitions and helper lemmas.
  `chainsOf_key_salt`: in what the planner's `chainsOf` returns, for any digest, the salt in the
    plan of the key's one-time chain, as read back, is that of the parameter file's lines, as a word
    of 64 bits. The library has the same for `planned` (`planned_key_salt`, OnBytes/K/KeySalt.lean),
    and the proof follows its steps.
  `sMT_built`: `sMT_description` at the parameters of the value that the library builds.


-/
import E2E.ZetaAtInput
import OnBytes.K.KeySalt
import Johnson.Goal.Scope.ScopeLines
import Johnson.Goal.Description.PlanKey
import Johnson.Goal.Conditions.LiveAtThe
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.ZetaAt
open OnBytes
open OnBytes.Model (polScan_frame)
open OnBytes.Model.Verify (chainsOf Public Chains chainsOf_made publicOf_scan)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open LPFD.Full (saltG)

/-- The salt in the plan of the key's one-time chain, as read back, is the lines'. -/
theorem chainsOf_key_salt {X : Public} {layout : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : chainsOf X layout c = .ok ch) :
    ch.key.oneTime.given.plan.salt = (UInt64.ofNat X.P.frame.salt).toNat := by
  obtain ⟨r1, -, -⟩ := OnBytes.TieK.G.chainsOf_read h
  obtain ⟨shapes, hm⟩ := chainsOf_made h
  obtain ⟨P, I, e, es⟩ := Params.configure_oneTime_salt hm
  obtain ⟨k1, -, -⟩ := Params.KeyChains.read_parts r1
  have hg := Params.OneTime.read_given k1
  have e' : ch.bytes .keyOneTime = Fmt.paramsBytes P c I := e
  rw [e'] at hg
  rw [Params.Given.read_salt hg, es]

/-- **For Z in scope with a live description, the plan's salt has 40 bytes.** -/
theorem salt_atFiles (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    saltG (dataAtFiles flashProveData Z).G = 40 := by
  obtain ⟨X₀, m, hX, -, hG, hc, -⟩ := FlashProve.thePlan_key Z live
  rw [VerifiableInference.PlanWritten.publicOfO_older] at hX
  obtain ⟨rest, hr⟩ := polScan_frame (publicOf_scan hX)
  have hl := Johnson.G.ScopeLines.inScope_says scope
  unfold OnBytes.Tie.EntryGround.SaysLines at hl
  rw [hr] at hl
  have e : X₀.P.frame = OnBytes.Tie.recordGround.lines := Option.some.inj hl
  rw [FlashProve.g_built_live Z live, hG]
  show m.p.chains.key.oneTime.given.plan.salt = 40
  rw [chainsOf_key_salt hc, e]
  decide

/-- At the parameters of the value that the library builds. -/
theorem sMT_built (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (c : VerifiableInference.Digest) (m : (FlashProve.descriptionOfDataOnBytes flashProveData).More) :
    ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).compilerParameters.sMT = 576 := by
  show 256 + 8 * saltG (dataAtFiles flashProveData Z).G = 576
  rw [salt_atFiles Z scope live]

/-- **At the verifier's parameters at Z.** -/
theorem sMT_description (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).compilerParameters.sMT = 576 :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), (D.input Z c m).compilerParameters.sMT = 576)
    fun c m => sMT_built Z scope live c m

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.chainsOf_key_salt
#print axioms AtPublicFiles.ZetaAt.salt_atFiles
#print axioms AtPublicFiles.ZetaAt.sMT_description
#print axioms AtPublicFiles.ZetaAt.sMT_built
