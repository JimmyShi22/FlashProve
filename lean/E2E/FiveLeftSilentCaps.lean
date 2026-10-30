-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/FiveLeftSilentCaps.lean: the placeholder provers with arbitrary search limits meet the five
premises of index privacy that read provers, coins and simulators.

Summary. `FiveLeft` (E2E/PrivacyAtDescription.lean) collects the five fields of
`OnBytes.WholeKey.PremW` that read provers, coins and simulators. E2E/FiveLeftSilent.lean proves
that three placeholder provers meet it, with the three search limits equal to 0. Here the search
limits are parameters: three functions. The result is meant as a warning: these premises are met by
provers that send no message of the protocol. The main limit is the same: each of the three sends
every round's fixed message, and no verifier is stated to accept them.

Main results.
  `fiveLeft_fixed`: `FiveLeft` holds for the placeholder provers, for every b and every number ℓ ≤
    r.compilerParameters.sMT of free bits in a leaf's salt, with the three simulators `fixedSims` and all six errors
    of simulators and aborts equal to 0: for arbitrary parameters r, with no "there is".
  `fiveLeft_silentC`: the same with "there are simulators", by the proof of `fiveLeft_silent`.
  `hasSilentMemberC_description` (`HasSilentMemberC r`): at the verifier's parameters at Z, for all
    public files Z, each fixed c and m and all search limits.

Terms: E2E/HidingTerms.lean. This file defines the placeholder provers, `silentAtC`.

Limits.
- In the words of Johnson/WholeKey/Statement.lean, which E2E/FiveLeftSilent.lean quotes: "Nothing of
  a protocol unless completeness of the same honest sides, at a small error, stands beside it"
  (capitals dropped). That the placeholder provers fail completeness is proved nowhere.
- The error of index privacy, `zetaW`, is none of the six errors above, and it reads ℓ. For these
  provers it is not computed here, for any ℓ or any search limits. E2E/ZetaAtCaps.lean has the
  conclusion of `wholeKeyPrivacy` for them with a bound on `zetaW`: for public files Z in scope, 256
  ≤ ℓ ≤ r.compilerParameters.sMT, at most 710,324 copies, at most 688,127 sessions per copy, bounded search limits
  and n ≤ s1 requests. Below ℓ = 256 no bound on the error for these provers is stated in this
  folder: the general bound of E2E/ZetaCaps.lean has the denominator 2 ^ k for every k ≤ ℓ with k ≤
  p.sFS and k ≤ 256, and it is applied for k = 256 only.
- For ℓ = 0 the error is 1 or more and the conclusion says nothing. This is not proved in Lean: it
  is by inspection of `zetaW`'s definition (E2E/FiveLeftSilent.lean).
- For ℓ = 0 the conditions on salts hold for a poor reason: the salts are constant.
- b is any value of the parameters' type LeafBody. That the type has a member is proved at the verifier's
  parameters (`bd_nonempty_description`), not for every r; where it has none, there are no such
  provers and `FiveLeft` is met by nothing.
- The other remarks of E2E/FiveLeftSilent.lean on these provers hold: among them, their external
  strings are the index's true encodings.
- What a search limit does in the scheme's provers is not stated here. The clauses of `PremW` that
  read search limits are among the fifteen of `NoProverSide` (E2E/PremisesAtFiles.lean), which are
  proved there for all search limits.

Definitions and helper lemmas.
  `silentAtC r b M ℓ ℓr capT capL capB`: `silentAt r b M ℓ ℓr` with these three search limits in
    place of its own; all other parameters are its own. `silentAtC_zero`: with search limits 0 it is
    `silentAt`, by unfolding.
  `coinsFit_silentC`: `CoinsFit` holds for it. Each clause is the clause of `coinsFit_silent`, taken
    field by field: so no clause of `CoinsFit` reads a search limit for these parameters.
  `hasSilentMemberC_of`: `HasSilentMemberC r` wherever the type LeafBody has a member.
    `hasSilentMember_of_C`: `HasSilentMember` is its case with search limits 0.
  `fixedSims`, `fixedSims_good`: the three simulators by name; they meet the premise `good` for the
    placeholder provers with errors 0.


-/
import E2E.FiveLeftSilent

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Premises
open OnBytes.WholeKey OnBytes.Prover
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles)
open FlashProve (flashProveData)

/-- **The placeholder provers' parameters, with any three search limits.** -/
def silentAtC (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ) :
    AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits :=
  { silentAt r b M ℓ ℓr with capT := capT, capL := capL, capB := capB }

/-- With search limits 0 it is `silentAt`. -/
theorem silentAtC_zero (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr : ℕ) :
    silentAtC r b M ℓ ℓr (fun _ => 0) (fun _ => 0) (fun _ => 0) = silentAt r b M ℓ ℓr := rfl

/-- The conditions on all coins hold for these parameters: each clause is that of `coinsFit_silent`.
-/
theorem coinsFit_silentC (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (hℓ : ℓ ≤ r.compilerParameters.sMT) :
    CoinsFit r.queryLayout r.compilerParameters (silentAtC r b M ℓ ℓr capT capL capB) (coinNums r b ℓ ℓr) where
  ri := (coinsFit_silent r b M ℓ ℓr hℓ).ri
  kT := (coinsFit_silent r b M ℓ ℓr hℓ).kT
  kL := (coinsFit_silent r b M ℓ ℓr hℓ).kL
  kB := (coinsFit_silent r b M ℓ ℓr hℓ).kB
  sl := (coinsFit_silent r b M ℓ ℓr hℓ).sl
  len₀ := (coinsFit_silent r b M ℓ ℓr hℓ).len₀
  okT := (coinsFit_silent r b M ℓ ℓr hℓ).okT
  okL := (coinsFit_silent r b M ℓ ℓr hℓ).okL
  okB := (coinsFit_silent r b M ℓ ℓr hℓ).okB
  lenT := (coinsFit_silent r b M ℓ ℓr hℓ).lenT
  lenL := (coinsFit_silent r b M ℓ ℓr hℓ).lenL
  lenB := (coinsFit_silent r b M ℓ ℓr hℓ).lenB
  coT := (coinsFit_silent r b M ℓ ℓr hℓ).coT
  coL := (coinsFit_silent r b M ℓ ℓr hℓ).coL
  coB := (coinsFit_silent r b M ℓ ℓr hℓ).coB
  rounds := (coinsFit_silent r b M ℓ ℓr hℓ).rounds
  winT := (coinsFit_silent r b M ℓ ℓr hℓ).winT
  winL := (coinsFit_silent r b M ℓ ℓr hℓ).winL
  winB := (coinsFit_silent r b M ℓ ℓr hℓ).winB

/-- **A warning: the placeholder provers meet `FiveLeft`, with any search limits.** They are no
provers of the protocol: they send none of its messages. The error `zetaW` for them is not computed
here (a bound for 256 ≤ ℓ: E2E/ZetaAtCaps.lean). -/
theorem fiveLeft_silentC (r : InnerCompilerInput) (b : r.LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (hℓ : ℓ ≤ r.compilerParameters.sMT) (Gs : r.protocol.OutOfDomainSeed → Prop) (Ryes : r.Index → r.Instance → Prop) :
    ∃ Sm : Sims r.protocol, FiveLeft r (silentAtC r b M ℓ ℓr capT capL capB) Sm (fun _ => True) Gs Ryes
      (coinNums r b ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) := by
  obtain ⟨⟨Sm, hg⟩, hs⟩ := silent_good r.Index r.Instance 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits r.queryLayout Gs Ryes
  exact ⟨Sm, extEnc_silent r.protocol, ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl,
           fun _ _ _ _ _ _ _ _ _ => rfl⟩, hg, hs, coinsFit_silentC r b M ℓ ℓr capT capL capB hℓ⟩

/-- The placeholder provers meet the five fields at the parameters r, with all search limits. -/
def HasSilentMemberC (r : InnerCompilerInput) : Prop :=
  ∀ (M s1 ℓ ℓr : ℕ), ℓ ≤ r.compilerParameters.sMT → ∀ (capT capL capB : ℕ → ℕ) (Gs : r.protocol.OutOfDomainSeed → Prop)
    (Ryes : r.Index → r.Instance → Prop),
    ∃ (b : r.LeafBody) (Sm : Sims r.protocol), FiveLeft r (silentAtC r b M ℓ ℓr capT capL capB) Sm
      (fun _ => True) Gs Ryes (coinNums r b ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0)

/-- They do wherever the parameters' type LeafBody, of what a query's body may hold besides, has a member.
-/
theorem hasSilentMemberC_of (r : InnerCompilerInput) (h : Nonempty r.LeafBody) : HasSilentMemberC r :=
  fun M s1 ℓ ℓr hℓ capT capL capB Gs Ryes => h.elim fun b =>
    ⟨b, fiveLeft_silentC r b M s1 ℓ ℓr capT capL capB hℓ Gs Ryes⟩

/-- `HasSilentMember` is its case with search limits 0. -/
theorem hasSilentMember_of_C (r : InnerCompilerInput) (h : HasSilentMemberC r) : HasSilentMember r :=
  fun M s1 ℓ ℓr hℓ Gs Ryes => h M s1 ℓ ℓr hℓ (fun _ => 0) (fun _ => 0) (fun _ => 0) Gs Ryes

/-- **A warning, at the verifier's parameters at Z**, for all public files Z, each fixed c and m and
all search limits. -/
theorem hasSilentMemberC_description (Z : PublicFiles) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      HasSilentMemberC ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More),
      HasSilentMemberC (D.input Z c m))
    fun c m => hasSilentMemberC_of _ (bd_nonempty_built Z c m)

/-! ## With the simulators named, for every b -/

/-- **The three simulators, by name**: each returns the run of the fixed messages, with the symbols
that it is given (`fixedSim`, Johnson/WholeKey/Foes.lean). Of the parameters they read only `r.protocol`.
-/
def fixedSims {I X : Type} (L : HolographicProtocol I X) : Sims L :=
  ⟨fixedSim L.offline, fixedSim L.link, fun _ => fixedSim L.onlineBatch.loc⟩

/-- They meet the premise `good` for the placeholder provers with errors 0. The proof is that of
`silent_good` (Johnson/WholeKey/Foes.lean), which says "there are simulators" and gives these. -/
theorem fixedSims_good {I X : Type} {lam : ℕ} (L : HolographicProtocol I X) {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (Gs : L.OutOfDomainSeed → Prop)
    (Ryes : I → X → Prop) : (fixedSims L).Good (silent L) W (fun _ => True) Gs Ryes 0 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun i r e _ _ => le_of_eq (Prob.pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (output_fixed L.offline (silent L).T rfl (fun _ _ => rfl) (fun _ _ _ => rfl) _ _ _))
  · exact fun i r e r' e' _ _ _ => le_of_eq (Prob.pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (output_fixed L.link (silent L).Lk rfl (fun _ _ => rfl) (fun _ _ _ => rfl) _ _ _))
  · exact fun n i r e x _ _ _ => le_of_eq (Prob.pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (output_fixed L.onlineBatch.loc (sessionAt (silent L) n) rfl (fun _ _ => rfl)
        (fun _ _ _ => rfl) _ _ _))

/-- **A warning: for every b, with the simulators named**: no "there is" is left. -/
theorem fiveLeft_fixed (r : InnerCompilerInput) (b : r.LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (hℓ : ℓ ≤ r.compilerParameters.sMT) (Gs : r.protocol.OutOfDomainSeed → Prop) (Ryes : r.Index → r.Instance → Prop) :
    FiveLeft r (silentAtC r b M ℓ ℓr capT capL capB) (fixedSims r.protocol) (fun _ => True) Gs Ryes
      (coinNums r b ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) :=
  ⟨extEnc_silent r.protocol, ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl,
           fun _ _ _ _ _ _ _ _ _ => rfl⟩, fixedSims_good r.protocol r.queryLayout Gs Ryes,
    (silent_good r.Index r.Instance 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits r.queryLayout Gs Ryes).2,
    coinsFit_silentC r b M ℓ ℓr capT capL capB hℓ⟩

/-- At the verifier's parameters the type of b has a member, so the statement above is not vacuous
there. -/
theorem bd_nonempty_description (Z : PublicFiles) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      Nonempty ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).LeafBody :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), Nonempty (D.input Z c m).LeafBody)
    fun c m => bd_nonempty_built Z c m

end AtPublicFiles.Premises

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Premises.silentAtC_zero
#print axioms AtPublicFiles.Premises.coinsFit_silentC
#print axioms AtPublicFiles.Premises.fiveLeft_silentC
#print axioms AtPublicFiles.Premises.hasSilentMemberC_of
#print axioms AtPublicFiles.Premises.hasSilentMember_of_C
#print axioms AtPublicFiles.Premises.hasSilentMemberC_description
#print axioms AtPublicFiles.Premises.fixedSims_good
#print axioms AtPublicFiles.Premises.fiveLeft_fixed
#print axioms AtPublicFiles.Premises.bd_nonempty_description
