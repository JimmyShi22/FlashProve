-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaAtCaps.lean

Summary. privacyWithNumber_description proves index privacy of the hashed scheme with three
placeholder provers, in the random-oracle model, with an explicit simulator (simWholeKey).
Placeholder provers send fixed messages. For these placeholder provers the error is at most 2 ^ -135
(one request, 2 ^ 64 oracle queries), and other files prove that proofs are produced under the same
search limits (E2E/StringsInGame.lean, E2E/SessionsInGame.lean). What that is worth: after hashing,
what this key and these placeholder provers' proofs disclose of the committed tables (roots, OOD
samples, opened columns) can be simulated without the index. The heaviest limit: it covers no
message that a prover computes from the index.

What this group of files has of index privacy of the protocol. The step from the interactive
protocols through hashing is proved for any three provers that meet twenty premises
(wholeKeyPrivacy, Johnson/WholeKey/Main.lean; stated in Johnson/WholeKey/Statement.lean). Its error
has a bound where the premises' seven error terms are 0: the three simulators', the three provers'
aborts', and the OOD seeds'. Of the three provers one, the link's, is explicit
(E2E/LinkLaidPrivacy.lean); the two that carry the first table's proof and the requests' proofs, so
the inference, are placeholders. Also left: completeness of the same provers, the link's result at
the digest that VerifierAndGoals.verify computes, and the step to the system that VerifierAndGoals.verify belongs to.

The index: in the release's use, the model's weights (Terms: E2E/HidingTerms.lean).

The statement. It holds at the verifier's parameters at Z, for each digest c and second public
reading m fixed before the oracles are sampled, if Z is in scope with a live description. The key
holds one copy, each leaf's salt has 320 free bits, and every proof-of-work search has 2 ^ 40 + 1
tries. It is for every index, every valid environment and every adversary within these bounds
(Terms: E2E/HidingTerms.lean).

What is simulated. In the real experiment the committer encodes the true index; the simulator runs
on a fixed index i₀, a parameter of the statement. A produced proof opens at most 62 positions for
the first table's proof, 62 and 62 for a link proof, and 64 for a session
(E2E/StringsHoldClosed.lean).

The general bound: privacyWithBound_description, under Theorems.

Theorems.
  `privacyWithNumber_description`: `PrivacyWithNumber` at the verifier's parameters at Z, for Z in
    scope with a live description.
  `privacyWithBound_description`: `PrivacyWithBound` at the verifier's parameters at Z, for Z in
    scope: at most 710,324 copies (M + 1), at most 688,127 sessions per copy (s1), a number ℓ of
    free bits with 256 ≤ ℓ ≤ the salt's length, search limits of at most CT, CL and CB in the three
    protocols. For t oracle queries and n ≤ s1 requests the error is at most `boundZ
    (9 + CT + CL + CB) M t n`.
  `zetaSmallC_description`: that bound on the error term `OnBytes.WholeKey.zetaW` alone, for Z in
    scope and every ℓ ≥ 256.
  `hasIndexPrivacy_of`: `PrivacyWithNumber` under the name `ZKCP.Gen.HasIndexPrivacyWith`.

Limits, the weightiest first.
- The three provers are placeholders. Each sends every round's fixed message, whatever it is given,
  so nothing here bears on the messages of the protocol's own provers.
- Index privacy says little about a protocol unless completeness of the same provers holds beside it
  (Johnson/WholeKey/Statement.lean). That the placeholder provers fail completeness is not proved at
  these parameters.
- The scheme is wholeKeySchemeOverTypedOracles r at fixed parameters, not the system that VerifierAndGoals.verify belongs to, with
  one request per proof.
- That the type of indices has more than one member is not proved here; with one index the statement
  would be trivial. At homeR b Z it has two (two_plains_valid,
  Johnson/LinkSim/AtHome/TwoPlains.lean).
- The number is for one copy and one request. The general bound grows with the copies, the requests
  and the search limits, and allows at most 688,127 requests in all. It is an upper bound and is not
  proved to be tight.
- No bound on the error says that the proof-of-work searches succeed; where a search runs out, no
  proof is produced. That proofs are produced at 2 ^ 40 tries is proved elsewhere, with bounds of
  their own (E2E/StringsAtInput.lean; in the real experiment E2E/StringsInGame.lean and
  E2E/SessionsInGame.lean, whose bound includes the error of index privacy).
- That any public files have a live description is not proved here; for the library's two named sets
  of public files see AtFullSide/E2E/AtWrittenFiles.lean.
- Where the description is not live, privacyWithBound_description still holds, but the first table's
  proof and a session's proof open nothing, and the salt's length is not proved.
- The form is ZKCP.Gen.PrivacyOn at all indices, which is ZKCP.Gen.HasIndexPrivacyWith
  (hasIndexPrivacy_of): not verbatim ZKCP.HasStrongIndexPrivacyWith.
- Each use of the hash is an independent random oracle on structured inputs, and randomness is
  uniform. (usual for a proof in the random-oracle model)
- The provers, the committer and the simulator are Lean terms, tied to no program, and the
  simulator's running time is not modelled. (usual for a proof in the random-oracle model)
- All other limits of E2E/FiveLeftSilentCaps.lean, E2E/PrivacyAtDescription.lean and
  Johnson/WholeKey/Statement.lean hold.

Tests and notes.
- Why the search limits matter. With one try per search a proof is produced with probability
  2 ^ -608, 2 ^ -192 or 2 ^ -1000 (a hand count, not proved in Lean), far below the bound itself.
  Within the stated error what is seen is then the key alone: roots, OOD samples, places and
  numbers: no proof string and no opened column.
- Why 320 free bits. A compiled run of the protocol publishes the first 256 bits of a leaf's salt
  (by inspection, not proved here). With the placeholder provers these bits are zeros. A salt has
  576 bits, so more than 320 free bits would include bits that the protocol publishes.
- In scope at most 19, 6 and 46 rounds of the three protocols have a proof-of-work test, each of at
  most 32 bits (E2E/ZetaTriesAtInput.lean; where the description is not live, the first and the last
  protocol have none). Where it is live these tests have 608, 192 and 1,000 bits together (a hand
  count, not proved in Lean).
- That a proof is produced does not say that it opens a column. That the first table's proof and a
  session's proof read at least one column is proved for Z in scope with a live description
  (`reads_some_filesAt`, E2E/ReadsNotEmptyAtObject.lean); for the link see E2E/StringsHoldLink.lean.
- Wherever `VerifierAndGoals.verify` accepts anything, Z is in scope with a live description
  (`FlashProve.scope_and_live_of_accept`, Johnson/Goal/Description/AcceptGivesLive.lean).

Terms: E2E/HidingTerms.lean.

Definitions and helper lemmas (see their docstrings): `boundZ`, `ZetaSmallC`, `PrivacyWithBound`,
`PrivacyWithNumber`, `zetaSmallC_of`, `zeta_number_caps`, `privacyWithBound_of`, `salt_within`.
Helper lemma without a docstring: `privacyWithNumber_of`: the case with the number.


-/
import E2E.FiveLeftSilentCaps
import E2E.ZetaCaps
import E2E.ZetaSalt

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.ZetaAt
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- The bound: (t A + k A (2 (M + 2) + A)) / 2 ^ 256 with A := `boundA M n` (E2E/ZetaArith.lean). k:
the number of oracle names that are counted; M + 1 copies; t oracle queries; n requests. -/
def boundZ (k M t n : ℕ) : ℝ≥0∞ :=
  ((t * boundA M n + k * (boundA M n * (2 * (M + 2) + boundA M n)) : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- **With the placeholder provers the error is at most the bound**, for arbitrary r: for every
number of copies, no more requests than one copy's sessions, at least 256 free bits in a leaf's
salt, and bounded search limits. -/
def ZetaSmallC (r : InnerCompilerInput) : Prop :=
  ∀ (b : r.LeafBody) (M s1 ℓ ℓr t n CT CL CB : ℕ) (capT capL capB : ℕ → ℕ), 256 ≤ ℓ → n ≤ s1 →
    (∀ i, capT i ≤ CT) → (∀ i, capL i ≤ CL) → (∀ i, capB i ≤ CB) →
    zetaW r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b M ℓ ℓr capT capL capB) (coinNums r b ℓ ℓr)
        (indexPrivacyNumbers s1 0 0 0 0 0 0) t n ≤ boundZ (9 + CT + CL + CB) M t n

/-- For arbitrary r, from twelve numbers of its parameters and its wiring. -/
theorem zetaSmallC_of (r : InnerCompilerInput) (h : Twelve r) : ZetaSmallC r :=
  fun b M s1 ℓ ℓr t n CT CL CB capT capL capB hℓ hn hT hL hB =>
    zetaW_le_caps r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b M ℓ ℓr capT capL capB) (coinNums r b ℓ ℓr)
      (indexPrivacyNumbers s1 0 0 0 0 0 0) t n 256 CT CL CB hT hL hB ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      hn hℓ h.sFS (Nat.le_refl 256) h.depth
      (le_of_eq_of_le (runLeaves_eq _ _ _) h.lvT) (le_of_eq_of_le (runLeaves_eq _ _ _) h.lvL)
      (le_of_eq_of_le (runLeaves_eq _ _ _) h.lvB) h.rT h.rL h.rB h.qT h.qL h.qB

/-- **At the verifier's parameters at Z**, for every Z in scope. -/
theorem zetaSmallC_description (Z : PublicFiles) (scope : InScope Z = true)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    ZetaSmallC ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  zetaSmallC_of _ (twelve_description Z scope c m)

/-- **The number**: one copy, one request, at most 2 ^ 64 queries, search limits of at most 2 ^ 40.
-/
theorem zeta_number_caps (t CT CL CB : ℕ) (ht : t ≤ 2 ^ 64) (hT : CT ≤ 2 ^ 40)
    (hL : CL ≤ 2 ^ 40) (hB : CB ≤ 2 ^ 40) :
    boundZ (9 + CT + CL + CB) 0 t 1 ≤ (2⁻¹ : ℝ≥0∞) ^ 135 := by
  unfold boundZ
  have e : (256 : ℕ) = 121 + 135 := by norm_num
  rw [e]
  exact div_pow_le _ 121 135 (numerator_caps t CT CL CB ht hT hL hB)

/-- **Index privacy with the bound on its error**, for arbitrary r and b, with the simulators named.
-/
def PrivacyWithBound (r : InnerCompilerInput) : Prop :=
  ∀ (b : r.LeafBody) (M s1 ℓ ℓr CT CL CB : ℕ) (capT capL capB : ℕ → ℕ) (Ryes : r.Index → r.Instance → Prop)
    (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index),
    M + 1 ≤ 710324 → s1 ≤ 688127 → 256 ≤ ℓ → ℓ ≤ r.compilerParameters.sMT →
    (∀ i, capT i ≤ CT) → (∀ i, capL i ≤ CL) → (∀ i, capB i ≤ CB) →
    (∀ i x w, R.yes i x w → Ryes i x) →
    ZKCP.Gen.PrivacyOn R (wholeKeySchemeOverTypedOracles r (silentAtC r b M ℓ ℓr capT capL capB).side) 1
        (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample (silentAtC r b M ℓ ℓr capT capL capB).side
          (fixedSims r.protocol) i₀ s1 (fun _ => True) Unit)
        (zetaW r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b M ℓ ℓr capT capL capB) (coinNums r b ℓ ℓr)
          (indexPrivacyNumbers s1 0 0 0 0 0 0)) (fun _ => True) ∧
      ∀ t n, n ≤ s1 →
        zetaW r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b M ℓ ℓr capT capL capB) (coinNums r b ℓ ℓr)
          (indexPrivacyNumbers s1 0 0 0 0 0 0) t n ≤ boundZ (9 + CT + CL + CB) M t n

/-- The conditional theorem, its premises and the bound, joined, for arbitrary r. -/
theorem privacyWithBound_of (r : InnerCompilerInput) (hP : PrivacyFromFive r) (hZ : ZetaSmallC r) :
    PrivacyWithBound r := by
  intro b M s1 ℓ ℓr CT CL CB capT capL capB Ryes R i₀ h1 h2 hℓ hℓ' hT hL hB hR
  exact ⟨hP _ (fixedSims r.protocol) _ Ryes _ s1 0 0 0 0 0 0 R i₀ h1 h2 hR
      (fiveLeft_fixed r b M s1 ℓ ℓr capT capL capB hℓ' (fun _ => True) Ryes),
    fun t n hn => hZ b M s1 ℓ ℓr t n CT CL CB capT capL capB hℓ hn hT hL hB⟩

/-- **At the verifier's parameters at Z**, for every Z in scope. -/
theorem privacyWithBound_description (Z : PublicFiles) (scope : InScope Z = true)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    PrivacyWithBound ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  privacyWithBound_of _ (privacyFromFive_description Z scope c m)
    (zetaSmallC_description Z scope c m)

/-- **For Z in scope with a live description, ℓ := 8 · 40 meets the two premises on ℓ.**
-/
theorem salt_within (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    256 ≤ 320 ∧ 320 ≤ ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).compilerParameters.sMT ∧
      ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).compilerParameters.sMT = 256 + 320 := by
  rw [sMT_description Z scope live c m]
  exact ⟨by norm_num, by norm_num, rfl⟩

/-- **Index privacy with a number**, for arbitrary r and the placeholder provers: one copy,
ℓ := 320, every search limit 2 ^ 40: error at most 2 ^ -135 (one request, 2 ^ 64 queries); that
proofs are produced at these limits: E2E/StringsInGame.lean, E2E/SessionsInGame.lean. -/
def PrivacyWithNumber (r : InnerCompilerInput) : Prop :=
  ∀ (b : r.LeafBody) (s1 ℓr : ℕ) (Ryes : r.Index → r.Instance → Prop) (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit)
    (i₀ : r.Index), 1 ≤ s1 → s1 ≤ 688127 → (∀ i x w, R.yes i x w → Ryes i x) →
    ZKCP.Gen.PrivacyOn R
        (wholeKeySchemeOverTypedOracles r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                fun _ => 2 ^ 40).side) 1
        (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40)
                                              (fun _ => 2 ^ 40) fun _ => 2 ^ 40).side (fixedSims r.protocol) i₀ s1 (fun _ => True) Unit)
        (zetaW r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                              fun _ => 2 ^ 40) (coinNums r b 320 ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0)) (fun _ => True) ∧
      ∀ t, t ≤ 2 ^ 64 →
        zetaW r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                              fun _ => 2 ^ 40) (coinNums r b 320 ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) t 1 ≤
          (2⁻¹ : ℝ≥0∞) ^ 135

theorem privacyWithNumber_of (r : InnerCompilerInput) (h : PrivacyWithBound r) (hs : 320 ≤ r.compilerParameters.sMT) :
    PrivacyWithNumber r := by
  intro b s1 ℓr Ryes R i₀ h1 h2 hR
  obtain ⟨p, z⟩ := h b 0 s1 320 ℓr (2 ^ 40) (2 ^ 40) (2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
    (fun _ => 2 ^ 40) Ryes R i₀ (by norm_num) h2 (by norm_num) hs (fun _ => le_rfl)
    (fun _ => le_rfl) (fun _ => le_rfl) hR
  exact ⟨p, fun t ht => (z t 1 h1).trans
    (zeta_number_caps t (2 ^ 40) (2 ^ 40) (2 ^ 40) ht le_rfl le_rfl le_rfl)⟩

/-- **At the verifier's parameters at Z**, for every Z in scope with a live description.
-/
theorem privacyWithNumber_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    PrivacyWithNumber ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  privacyWithNumber_of _ (privacyWithBound_description Z scope c m)
    (salt_within Z scope live c m).2.1

/-- **The same under the form's own name**: at the range of all indices `ZKCP.Gen.PrivacyOn` is
`ZKCP.Gen.HasIndexPrivacyWith` (`privacyOn_all`, ZKCP/OnRange.lean). -/
theorem hasIndexPrivacy_of (r : InnerCompilerInput) (h : PrivacyWithNumber r) (b : r.LeafBody) (s1 ℓr : ℕ)
    (Ryes : r.Index → r.Instance → Prop) (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index) (h1 : 1 ≤ s1)
    (h2 : s1 ≤ 688127) (hR : ∀ i x w, R.yes i x w → Ryes i x) :
    ZKCP.Gen.HasIndexPrivacyWith R
      (wholeKeySchemeOverTypedOracles r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                              fun _ => 2 ^ 40).side) 1
      (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40)
                                            (fun _ => 2 ^ 40) fun _ => 2 ^ 40).side (fixedSims r.protocol) i₀ s1 (fun _ => True) Unit)
      (zetaW r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                            fun _ => 2 ^ 40) (coinNums r b 320 ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0)) :=
  (ZKCP.Gen.privacyOn_all _ _ _ _ _).1 (h b s1 ℓr Ryes R i₀ h1 h2 hR).1

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.hasIndexPrivacy_of
#print axioms AtPublicFiles.ZetaAt.privacyWithNumber_description
#print axioms AtPublicFiles.ZetaAt.salt_within
#print axioms AtPublicFiles.ZetaAt.zetaSmallC_of
#print axioms AtPublicFiles.ZetaAt.zetaSmallC_description
#print axioms AtPublicFiles.ZetaAt.zeta_number_caps
#print axioms AtPublicFiles.ZetaAt.privacyWithBound_of
#print axioms AtPublicFiles.ZetaAt.privacyWithBound_description
#print axioms AtPublicFiles.ZetaAt.privacyWithNumber_of
