-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsHoldAtInput.lean: at the verifier's parameters at Z, a produced proof for the first table
or for a session opens at least one column of the encoder's table of the index if Z is in scope with
a live description, and none if the description is not live.

Summary. E2E/StringsHold.lean proves that a produced proof opens exactly what the verifier reads.
This file proves when the verifier reads something. The results on proofs hold for any three
provers, all oracle functions and all coins. No probability occurs.

Main results.
  `readsSome_description`: for Z in scope with a live description, the verifier of the first table's
    proof and the verifier of a session each read at least one column, for every instance and all
    verifier messages (`ReadsSome`; by E2E/ReadsNotEmptyAtObject.lean).
  `readsNone_description`: for every Z at which the description is not live they read none
    (`ReadsNone`): the two files' rounds' data are three empty lists each.
  `key_column`, `session_column`: under `ReadsSome r`, a produced proof for the first table (for a
    session) has a position p at which it holds `r.protocol.encodeIndex i c.r p` (`r.protocol.encodeIndex i e.r p`, e the copy at
    the sampled place), with a salt and a path.
  `key_nothing`, `session_nothing`: under `ReadsNone r` it opens nothing of the table, at any
    position.

Terms: E2E/HidingTerms.lean.

Limits. This file does not prove:
- how many columns are opened: the lower bound is one (upper bounds: E2E/StringsHoldClosed.lean,
  from the field on reads of `noProverSide_description`, E2E/PremisesAtFiles.lean); or which
  positions: they depend on the verifier messages;
- anything about the openings of the strategies' own oracle messages, or about the plain parts;
- that a column tells anything about the index, or nothing;
- that a proof is produced (E2E/StringsAtInput.lean), or that the verifier accepts it;
- that the description is live at any Z (for the library's two named sets of public files:
  AtFullSide/E2E/AtWrittenFiles.lean);
- anything about the link (E2E/StringsHoldLink.lean);
- anything on completeness, on soundness or on what is hidden.

Definitions and helper lemmas.
  `ReadsSome r`, `ReadsNone r`: the two properties of the parameters r.
  `readsSome_atFiles`, `reads_none_fullD`, `readsNone_atFiles`: the two results on reads at the
    structure of parameters from which the verifier is compiled.


-/
import E2E.StringsHold
import E2E.ReadsNotEmptyAtObject
import E2E.ZetaAtInput

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (RecFull)
open OnBytes.Slice (frS frZ)
open OnBytes.Maker (WholeD)
open _root_.Run.PQ (View XO)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInput innerCompilerInputAtFullSize)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open LPFD.Full (sBG sTG saltG)

/-! ## 1. What the two verifiers read -/

/-- The verifier of the first table's proof and the verifier of a session each read at least one
column, for every instance and all verifier messages. -/
structure ReadsSome (r : InnerCompilerInput) : Prop where
  T : ∀ x ρ, (r.protocol.offline.extReads x ρ).Nonempty
  B : ∀ x ρ, (r.protocol.onlineBatch.loc.extReads x ρ).Nonempty

theorem readsSome_atFiles (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) :
    ReadsSome (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) :=
  ⟨AtPublicFiles.Reads.test_reads_some _ _ (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK
      (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec
      (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2 (sBG (dataAtFiles flashProveData Z).G).logLeaves
      (dataAtFiles flashProveData Z).G.early (saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).P
      (by rw [AtPublicFiles.Reads.key_data Z scope live]; exact AtPublicFiles.Reads.opens_atWritten.1),
    AtPublicFiles.Reads.bat_reads_some _ _ (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK
      (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec
      (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2 (sBG (dataAtFiles flashProveData Z).G).logLeaves
      (dataAtFiles flashProveData Z).G.early (saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).P
      (by rw [AtPublicFiles.Reads.proof_data Z scope live]; exact AtPublicFiles.Reads.opens_atWritten.2)⟩

/-- **At the verifier's parameters at Z**, for Z in scope with a live description. -/
theorem readsSome_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      ReadsSome ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), ReadsSome (D.input Z c m))
    fun c m => readsSome_atFiles Z scope live c m

/-- The two verifiers read no column. -/
structure ReadsNone (r : InnerCompilerInput) : Prop where
  T : ∀ x ρ, r.protocol.offline.extReads x ρ = ∅
  B : ∀ x ρ, r.protocol.onlineBatch.loc.extReads x ρ = ∅

theorem reads_none_fullD {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD) (hK : DK = FlashProve.emptyRoundsData)
    (hP : DP = FlashProve.emptyRoundsData) (runK : RecFull → View → View → View → Bool)
    (runP : X × RecFull → View → View → View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD)
    (xs : List XO) (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull) (depthReq : ℕ)
    (early : X → X) (salt : ℕ)
    (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers) :
    (∀ x ρ, ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
        P).offline.extReads x ρ = ∅) ∧
      ∀ x ρ, ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
        P).onlineBatch.loc.extReads x ρ = ∅ := by
  subst hK
  subst hP
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem readsNone_atFiles (Z : PublicFiles) (shut : protocolDataWellFormed (asDescriptionFiles Z) = false)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) :
    ReadsNone (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) :=
  have h := reads_none_fullD (dataAtFiles flashProveData Z).A
    (OnBytes.Flat.relationsAndEncodingOfClaims (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (AtPublicFiles.Reads.data_shut Z shut).1 (AtPublicFiles.Reads.data_shut Z shut).2
    (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early (saltG (dataAtFiles flashProveData Z).G)
    (dataAtFiles flashProveData Z).P
  ⟨h.1, h.2⟩

/-- **At the verifier's parameters at Z**, for every Z at which the description is not live. -/
theorem readsNone_description (Z : PublicFiles) (shut : protocolDataWellFormed (asDescriptionFiles Z) = false) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      ReadsNone ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), ReadsNone (D.input Z c m))
    fun c m => readsNone_atFiles Z shut c m

/-! ## 2. What the first table's proof and a session's proof open, for any three provers -/

section
variable (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
  (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)))

/-- **Under `ReadsSome r`, a produced proof for the first table holds a column of the encoder's
table of the index i**, with a salt and a path. -/
theorem key_column (hR : ReadsSome r) (i : r.Index) (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL)
    (π : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits))
    (hπ : ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).1.piT = some π) :
    ∃ p sa pa, π.ext p = some ⟨r.protocol.encodeIndex i c.r p, sa, pa⟩ := by
  obtain ⟨ρ, ho, -⟩ := key_opens r.queryLayout r.seedQueries r.answerCode h g i c π hπ
  obtain ⟨p, hp⟩ := hR.T (r.protocol.recOf i c.r (tabG r.queryLayout r.seedQueries h g i c.r c.s).seed) ρ
  exact ⟨p, _, _, ho p hp⟩

/-- **Under `ReadsSome r`, a produced proof of a session holds a column of the encoder's table of
the index i for the copy at the sampled place.** -/
theorem session_column (hR : ReadsSome r) (i : r.Index) (x : r.Instance)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (e : DrawCopy 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KL)
    (dP : DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB) (hj : c.copies[dP.j]? = some e)
    (π : OneProtocolProof 256 r.protocol.onlineBatch)
    (hπ : ((proveAt r.queryLayout r.answerCode r.fixedSample h ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).2 x dP).det g).piB =
      some π) :
    ∃ p sa pa, π.ext p = some ⟨r.protocol.encodeIndex i e.r p, sa, pa⟩ := by
  obtain ⟨ρ, ho, -⟩ := session_opens r.queryLayout r.seedQueries r.answerCode r.fixedSample h g i x c e dP hj π hπ
  obtain ⟨p, hp⟩ := hR.B (x, r.protocol.recOf i e.r (tabG r.queryLayout r.seedQueries h g i e.r e.s).seed) ρ
  exact ⟨p, _, _, ho p hp⟩

/-- Where the two verifiers read nothing, the first table's proof opens nothing of the table. -/
theorem key_nothing (hR : ReadsNone r) (i : r.Index) (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL)
    (π : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits))
    (hπ : ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).1.piT = some π) : ∀ p, π.ext p = none := by
  obtain ⟨ρ, -, hn⟩ := key_opens r.queryLayout r.seedQueries r.answerCode h g i c π hπ
  intro p
  refine hn p fun hp => ?_
  have e := hR.T (r.protocol.recOf i c.r (tabG r.queryLayout r.seedQueries h g i c.r c.s).seed) ρ
  have hp' : p ∈ r.protocol.offline.extReads (r.protocol.recOf i c.r (tabG r.queryLayout r.seedQueries h g i c.r c.s).seed) ρ := hp
  rw [e] at hp'
  exact absurd hp' (Finset.notMem_empty p)

/-- Nor does a session's proof. -/
theorem session_nothing (hR : ReadsNone r) (i : r.Index) (x : r.Instance)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (e : DrawCopy 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KL)
    (dP : DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB) (hj : c.copies[dP.j]? = some e)
    (π : OneProtocolProof 256 r.protocol.onlineBatch)
    (hπ : ((proveAt r.queryLayout r.answerCode r.fixedSample h ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).2 x dP).det g).piB =
      some π) : ∀ p, π.ext p = none := by
  obtain ⟨ρ, -, hn⟩ := session_opens r.queryLayout r.seedQueries r.answerCode r.fixedSample h g i x c e dP hj π hπ
  intro p
  refine hn p fun hp => ?_
  have e' := hR.B (x, r.protocol.recOf i e.r (tabG r.queryLayout r.seedQueries h g i e.r e.s).seed) ρ
  have hp' : p ∈ r.protocol.onlineBatch.loc.extReads (x, r.protocol.recOf i e.r (tabG r.queryLayout r.seedQueries h g i e.r e.s).seed) ρ :=
    hp
  rw [e'] at hp'
  exact absurd hp' (Finset.notMem_empty p)

end

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.reads_none_fullD
#print axioms AtPublicFiles.Shown.readsNone_atFiles
#print axioms AtPublicFiles.Shown.readsNone_description
#print axioms AtPublicFiles.Shown.key_column
#print axioms AtPublicFiles.Shown.session_column
#print axioms AtPublicFiles.Shown.key_nothing
#print axioms AtPublicFiles.Shown.session_nothing
#print axioms AtPublicFiles.Shown.readsSome_atFiles
#print axioms AtPublicFiles.Shown.readsSome_description
