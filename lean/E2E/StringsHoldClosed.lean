-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsHoldClosed.lean: what each kind of produced proof opens of the committed tables at the
verifier's parameters at Z, and how many positions at most.

Summary. The results of E2E/StringsHoldAtInput.lean and E2E/StringsHoldLink.lean assume a property
of the parameters r (`ReadsSome r`, `ReadsNone r`, `ReadsLink r`), which separate theorems prove at
the verifier's parameters. Here the two are joined, and the upper counts are stated as theorems.
Each result holds for any three provers, all oracle functions and all coins. No probability occurs.

Main results, at the verifier's parameters at Z.
  `keyHolds_description`: for Z in scope with a live description, a produced proof for the first
    table holds `r.protocol.encodeIndex i c.r p` at some position p, with a salt and a path, and opens at most 62
    positions (`KeyHolds`). Here c.r is the committer's own encoding randomness of that run, not
    some randomness.
  `sessionHolds_description`: under the same premises, the same for a session's proof with `r.protocol.encodeIndex
    i e.r`, e the copy at the sampled place, and at most 64 positions (`SessionHolds`).
  `linkHolds_description`: for every Z, a produced link proof holds a column of the first table (at
    c.r) and a column of the copy's (at e.r) (`LinkHolds`).
  `linkFew_description`: for Z in scope it opens at most 62 positions of the first table and 62 of
    the copy's (`LinkFew`).
  `holdNothing_description`: for every Z at which the description is not live, the first table's
    proof and a session's proof open nothing, at any position (`HoldNothing`).

Terms: E2E/HidingTerms.lean.

Limits. This file does not prove:
- anything between one column and 62, 62 and 62, or 64: equal positions are read once; or which
  positions are opened: they depend on the verifier messages;
- anything about the openings of the strategies' own oracle messages, or about the plain parts;
- that a column tells anything about the index, or nothing;
- that a proof is produced, or that the verifier accepts it;
- that the description is live at any Z (for the library's two named sets of public files:
  AtFullSide/E2E/AtWrittenFiles.lean);
- anything on completeness, on soundness or on what is hidden.

Definitions and helper lemmas.
  `KeyHolds r`, `SessionHolds r`, `LinkHolds r`, `LinkFew r`, `HoldNothing r`: the five statements
    for arbitrary parameters r.
  `ReadsFew r`: the four counts of reads.
  `opened_sub`: the positions at which a proof opens something are among those that the verifier
    reads.
  `readsFew_description`: for Z in scope (the field on reads of `noProverSide_description`,
    E2E/PremisesAtFiles.lean).
  `index_nonempty_description`: the type of indices has a member, for every Z.
  `keyHolds_of`, `sessionHolds_of`, `linkHolds_of`, `linkFew_of`, `holdNothing_of`: for arbitrary r.


-/
import E2E.StringsHoldLink
import E2E.PremisesAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput innerCompilerInputAtFullSize)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)

/-! ## 1. No more is opened than is read -/

/-- The positions at which a proof opens something are among those that the verifier reads. -/
theorem opened_sub {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q} {x : Y} {y : E.Str} {xt : ℕ → TreeK lam L}
    {π : OneProtocolProof lam Q} {ρ : Rho Q.loc.shape} (h : OpensOf Q wq x y xt π ρ) (s : Finset E.Pos)
    (hs : ∀ p ∈ s, (π.ext p).isSome = true) : s ⊆ Q.loc.extReads x ρ := by
  intro p hp
  by_contra hn
  have e := hs p hp
  rw [h.2 p hn] at e
  cases e

/-! ## 2. The counts at the verifier's parameters -/

/-- The verifier of the first table's proof reads at most 62 columns, a link's 62 of the first table
and 62 of the copy, a session's 64. -/
structure ReadsFew (r : InnerCompilerInput) : Prop where
  T : ∀ x ρ, (r.protocol.offline.extReads x ρ).card ≤ 62
  Lp : ∀ x ρ, ((r.protocol.link.extReads x ρ).filter fun p => p.isLeft).card ≤ 62
  Lc : ∀ x ρ, ((r.protocol.link.extReads x ρ).filter fun p => p.isRight).card ≤ 62
  B : ∀ x ρ, (r.protocol.onlineBatch.loc.extReads x ρ).card ≤ 64

/-- **At the verifier's parameters at Z**, for every Z in scope. -/
theorem readsFew_description (Z : PublicFiles) (scope : InScope Z = true)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    ReadsFew ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  have h := (AtPublicFiles.Premises.noProverSide_description Z scope 0 0 (by norm_num) (by norm_num) 0 0 0 0
    0 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) c m).reads
  ⟨h.cntT, h.cntLp, h.cntLc, h.cntO⟩

/-- The type of indices is not empty there. -/
theorem index_nonempty_description (Z : PublicFiles) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      Nonempty ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).Index :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), Nonempty (D.input Z c m).Index)
    fun _ _ => ⟨fun _ _ => 0⟩

/-! ## 3. What each kind of produced proof opens, for arbitrary parameters -/

/-- **The first table's proof**, for any three provers, all oracle functions and all coins: if it is
produced, it holds at least one column of the encoder's table of the index i at the committer's own
randomness c.r, and opens at most 62 positions. -/
def KeyHolds (r : InnerCompilerInput) : Prop :=
  ∀ (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (i : r.Index)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (π : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits)),
    ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).1.piT = some π →
    (∃ p sa pa, π.ext p = some ⟨r.protocol.encodeIndex i c.r p, sa, pa⟩) ∧
      ∀ s : Finset _, (∀ p ∈ s, (π.ext p).isSome = true) → s.card ≤ 62

/-- **A session's proof**: at least one column of the table of the copy at the sampled place, at
that copy's own randomness e.r; at most 64 positions. -/
def SessionHolds (r : InnerCompilerInput) : Prop :=
  ∀ (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (i : r.Index) (x : r.Instance)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (e : DrawCopy 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KL)
    (dP : DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB), c.copies[dP.j]? = some e →
    ∀ π : OneProtocolProof 256 r.protocol.onlineBatch,
    ((proveAt r.queryLayout r.answerCode r.fixedSample h ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).2 x dP).det g).piB = some π →
    (∃ p sa pa, π.ext p = some ⟨r.protocol.encodeIndex i e.r p, sa, pa⟩) ∧
      ∀ s : Finset _, (∀ p ∈ s, (π.ext p).isSome = true) → s.card ≤ 64

/-- **A link proof**: a column of the first table and a column of the copy's. -/
def LinkHolds (r : InnerCompilerInput) : Prop :=
  ∀ (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (i : r.Index)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (j : ℕ)
    (e : DrawCopy 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KL), c.copies[j]? = some e →
    ∀ l : Dig 256 × r.protocol.Rec × Option (OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)),
    ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).1.links[j]? = some l →
    ∀ π : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits), l.2.2 = some π →
    (∃ p sa pa, π.ext (.inl p) = some ⟨r.protocol.encodeIndex i c.r p, sa, pa⟩) ∧
      ∃ p sa pa, π.ext (.inr p) = some ⟨r.protocol.encodeIndex i e.r p, sa, pa⟩

/-- **A link proof opens at most 62 positions of the first table and 62 of the copy's.** -/
def LinkFew (r : InnerCompilerInput) : Prop :=
  ∀ (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (i : r.Index)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (j : ℕ)
    (e : DrawCopy 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KL), c.copies[j]? = some e →
    ∀ l : Dig 256 × r.protocol.Rec × Option (OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)),
    ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).1.links[j]? = some l →
    ∀ π : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits), l.2.2 = some π →
    ∀ s : Finset _, (∀ p ∈ s, (π.ext p).isSome = true) →
      (s.filter fun p => p.isLeft).card ≤ 62 ∧ (s.filter fun p => p.isRight).card ≤ 62

/-- **The first table's proof and a session's proof open nothing of a table.** -/
def HoldNothing (r : InnerCompilerInput) : Prop :=
  ∀ (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (i : r.Index)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL),
    (∀ π : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits),
      ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).1.piT = some π → ∀ p, π.ext p = none) ∧
    ∀ (x : r.Instance) (e : DrawCopy 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KL)
      (dP : DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB), c.copies[dP.j]? = some e →
      ∀ π : OneProtocolProof 256 r.protocol.onlineBatch,
      ((proveAt r.queryLayout r.answerCode r.fixedSample h ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).2 x dP).det g).piB =
        some π → ∀ p, π.ext p = none

theorem keyHolds_of (r : InnerCompilerInput) (hS : ReadsSome r) (hF : ReadsFew r) : KeyHolds r := by
  intro h g i c π hπ
  refine ⟨key_column r h g hS i c π hπ, fun s hs => ?_⟩
  obtain ⟨ρ, ho⟩ := key_opens r.queryLayout r.seedQueries r.answerCode h g i c π hπ
  exact (Finset.card_le_card (opened_sub ho s hs)).trans (hF.T _ ρ)

theorem sessionHolds_of (r : InnerCompilerInput) (hS : ReadsSome r) (hF : ReadsFew r) :
    SessionHolds r := by
  intro h g i x c e dP hj π hπ
  refine ⟨session_column r h g hS i x c e dP hj π hπ, fun s hs => ?_⟩
  obtain ⟨ρ, ho⟩ := session_opens r.queryLayout r.seedQueries r.answerCode r.fixedSample h g i x c e dP hj π hπ
  exact (Finset.card_le_card (opened_sub ho s hs)).trans (hF.B _ ρ)

theorem linkHolds_of (r : InnerCompilerInput) (hR : ReadsLink r) : LinkHolds r :=
  fun h g i c j e hj l hl π hπ => link_columns r h g hR i c j e hj l hl π hπ

theorem linkFew_of (r : InnerCompilerInput) (hF : ReadsFew r) : LinkFew r := by
  intro h g i c j e hj l hl π hπ s hs
  obtain ⟨ρ, ho⟩ := link_opens r.queryLayout r.seedQueries r.answerCode h g i c j e hj l hl π hπ
  have hsub := opened_sub ho s hs
  exact ⟨(Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans (hF.Lp _ ρ),
    (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans (hF.Lc _ ρ)⟩

theorem holdNothing_of (r : InnerCompilerInput) (hR : ReadsNone r) : HoldNothing r :=
  fun h g i c => ⟨fun π hπ => key_nothing r h g hR i c π hπ,
    fun x e dP hj π hπ => session_nothing r h g hR i x c e dP hj π hπ⟩

/-! ## 4. At the verifier's parameters at Z -/

/-- **For Z in scope with a live description.** -/
theorem keyHolds_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    KeyHolds ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  keyHolds_of _ (readsSome_description Z scope live c m) (readsFew_description Z scope c m)

/-- **For Z in scope with a live description.** -/
theorem sessionHolds_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    SessionHolds ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  sessionHolds_of _ (readsSome_description Z scope live c m) (readsFew_description Z scope c m)

/-- **For every Z.** -/
theorem linkHolds_description (Z : PublicFiles) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    LinkHolds ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  linkHolds_of _ (readsLink_description Z c m)

/-- **For Z in scope.** -/
theorem linkFew_description (Z : PublicFiles) (scope : InScope Z = true)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    LinkFew ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  linkFew_of _ (readsFew_description Z scope c m)

/-- **For every Z at which the description is not live.** -/
theorem holdNothing_description (Z : PublicFiles) (shut : protocolDataWellFormed (asDescriptionFiles Z) = false)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    HoldNothing ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  holdNothing_of _ (readsNone_description Z shut c m)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.opened_sub
#print axioms AtPublicFiles.Shown.readsFew_description
#print axioms AtPublicFiles.Shown.index_nonempty_description
#print axioms AtPublicFiles.Shown.keyHolds_of
#print axioms AtPublicFiles.Shown.sessionHolds_of
#print axioms AtPublicFiles.Shown.linkHolds_of
#print axioms AtPublicFiles.Shown.linkFew_of
#print axioms AtPublicFiles.Shown.holdNothing_of
#print axioms AtPublicFiles.Shown.keyHolds_description
#print axioms AtPublicFiles.Shown.sessionHolds_description
#print axioms AtPublicFiles.Shown.linkHolds_description
#print axioms AtPublicFiles.Shown.linkFew_description
#print axioms AtPublicFiles.Shown.holdNothing_description
