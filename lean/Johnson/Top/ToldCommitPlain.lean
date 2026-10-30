-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/ToldCommitPlain.lean: THE TOLD SYSTEM'S COMMITTER WITH ITS COINS FIXED, WRITTEN OUT.
Definitions, statements and proofs: general in the input R and the told record T.

Why. "The committer with the coins (r, σ) fixed" stood as the told system's committer at two
enumerations with one member each, at the number 0 (`commit_systemOn_reach`,
Johnson/Top/ToldCommitAt.lean): a term that names two enumerations, a number of coins and a prover.
The pieces lay (`commitE_of_key`,
Johnson/Top/ToldCommitSalts.lean; `commitBehind_reach`, Johnson/Top/ToldReach.lean). Here they are
joined.

Main names (namespace `VerifiableInference.OnPublicFiles`).
  `T.keyAtCoins b₀ i r σ`: THE KEY AT GIVEN COINS: the public reading gives d; `committerAtFixedCoins`
    (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean: the tree over the encoded index at r and the salts σ;
    the seed's two queries at the root; the root with the honest record) runs over the one hash
    function through the coding at d; the told part of d is laid beside.
  `T.commitAtCoins b₀ i r σ`: THE COMMITMENT AT GIVEN COINS: `keyDigest` (ZKCP/DigestKey.lean) of
    that key at the told code: one query more.
  **`commit_systemOn_plain`**: the system's committer at `enumOne r`, `enumOne σ` and the number 0
    IS `T.commitAtCoins b₀ (back j) r σ`: one algorithm. Premise: the public reading draws no coin.
  `evaluate_commitAtCoins`: its value at a hash function: that function's answer at the told code of
    the key's value there.
  `committerTreeRoot_filling`, `committerAtFixedCoins_filling`, `keyAtCoins_filling`, `commitAtCoins_filling`: where the
    word has a symbol for each of the tree's 2^depth leaves, none of the four hangs on the filling
    b₀.

Limits. Equations between terms of this library: nothing on any program. `committerAtFixedCoins` is not unfolded
further here. OF THE COMMITMENT ALONE: what the committer keeps for its prover is dropped. Nothing
on opening-form binding, no two openings, correctness of extraction, whatever else a key or a
commitment fixes, or hiding: Johnson/Goal/Conditions/BindsPlain.lean uses these.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ToldCommitSalts
import Johnson.Top.ParsedReader
import Run.RunIsVProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **The tree reads the filling beyond the word's length alone**: where the word has a symbol for
each leaf, the filling is not read. -/
theorem committerTreeRoot_filling {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (b₀ b₁ : Bd)
    (y : Fin L.wordLength → L.Symbol) (σ : ℕ → Bits) (h : 2 ^ W.depth ≤ L.wordLength) :
    committerTreeRoot W b₀ y σ = committerTreeRoot W b₁ y σ := by
  have e : (List.range (2 ^ W.depth)).map (committerLeafInput W b₀ y σ) =
      (List.range (2 ^ W.depth)).map (committerLeafInput W b₁ y σ) :=
    List.map_congr_left fun j hj => by
      have hj' : j < L.wordLength := lt_of_lt_of_le (List.mem_range.1 hj) h
      unfold committerLeafInput
      rw [dif_pos hj', dif_pos hj']
  unfold committerTreeRoot
  rw [e]

/-- So the committer behind its coins. -/
theorem committerAtFixedCoins_filling {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type}
    {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (b₀ b₁ : Bd) (i : I) (r : L.EncodingRandomness) (σ : ℕ → Bits)
    (h : 2 ^ W.depth ≤ L.wordLength) : committerAtFixedCoins W S b₀ i r σ = committerAtFixedCoins W S b₁ i r σ := by
  unfold committerAtFixedCoins
  rw [committerTreeRoot_filling W b₀ b₁ (L.encodeIndex i r) σ h]

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b₀ : R.LeafBody)

/-- **The key at given coins**: the public reading gives d; `committerAtFixedCoins` at the index i, the
randomness r and the salts σ, over the one hash function through the coding at d, gives the root
with the honest record; the told part of d is laid beside. -/
def LayoutsByPublicReading.keyAtCoins (i : R.Index) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) :
    Rom.OComp (rom 256) (Dig 256 × KeyRoot 256 R.protocol) :=
  T.Pub.bind fun d =>
    ((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ i r σ).overOne (T.m d)).bind fun o => .pure (T.part d, o.1)

/-- **The commitment at given coins**: the hash function's answer at the told code of that key. -/
def LayoutsByPublicReading.commitAtCoins (i : R.Index) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) :
    DeterministicAlgorithm Commitment :=
  deterministicOf ((ofRom (T.keyAtCoins b₀ i r σ)).bind (ZKCP.keyDigest T.encT))

/-- The committer behind the public reading at enumerations with one member each, the key alone
kept. -/
theorem commitBehind_key (noCoin : T.Pub.NoCoin) (i : R.Index) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) :
    (((T.commitBehind (enumOne r) (enumOne σ) b₀ i).withCoins 0).bind
      fun keys => Rom.OComp.pure keys.1) = T.keyAtCoins b₀ i r σ := by
  have e : (T.commitBehind (enumOne r) (enumOne σ) b₀ i).withCoins 0 =
      T.Pub.bind fun d => ((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ i r σ).overOne (T.m d)).bind
        fun o => Rom.OComp.pure ((T.part d, o.1), o.2) :=
    commitBehind_reach T (enumOne r) (enumOne σ) b₀ noCoin i 0 0
  rw [e, Rom.OComp.bind_assoc]
  unfold LayoutsByPublicReading.keyAtCoins
  congr 1
  funext d
  rw [Rom.OComp.bind_assoc]
  rfl

variable (prove : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → (l : List (R.Instance × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) l))

/-- **THE SYSTEM'S COMMITTER WITH THE COINS FIXED, WRITTEN OUT.** The right side names no
enumeration, no number of coins, no prover. -/
theorem commit_systemOn_plain {J : Type} (back : J → R.Index) (nt : J → List Token → Option Token)
    (noCoin : T.Pub.NoCoin) (j : J) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) :
    ((T.withCommit (enumOne r) (enumOne σ) b₀ prove).systemOn back nt).commit j
        (⟨0, Nat.succ_pos _⟩ : Fin (R.coinBound + 1)) = T.commitAtCoins b₀ (back j) r σ := by
  show deterministicOf (Rec.commitE ((T.withCommit (enumOne r) (enumOne σ) b₀ prove).schemeOn back)
    T.encT R.coinBound j _) = _
  rw [Rec.commitE_of_key]
  exact congrArg (fun A => deterministicOf ((ofRom A).bind (ZKCP.keyDigest T.encT)))
    (commitBehind_key T b₀ noCoin (back j) r σ)

/-- Where the word has a symbol for each leaf of the tree, the key does not hang on the filling. -/
theorem keyAtCoins_filling (b₁ : R.LeafBody) (h : 2 ^ R.queryLayout.depth ≤ R.protocol.wordLength) (i : R.Index) (r : R.protocol.EncodingRandomness)
    (σ : ℕ → Bits) : T.keyAtCoins b₀ i r σ = T.keyAtCoins b₁ i r σ := by
  unfold LayoutsByPublicReading.keyAtCoins
  congr 1
  funext d
  rw [committerAtFixedCoins_filling R.queryLayout (T.Sd d) b₀ b₁ i r σ h]

/-- Nor does the commitment. -/
theorem commitAtCoins_filling (b₁ : R.LeafBody) (h : 2 ^ R.queryLayout.depth ≤ R.protocol.wordLength) (i : R.Index) (r : R.protocol.EncodingRandomness)
    (σ : ℕ → Bits) : T.commitAtCoins b₀ i r σ = T.commitAtCoins b₁ i r σ := by
  unfold LayoutsByPublicReading.commitAtCoins
  rw [keyAtCoins_filling T b₀ b₁ h i r σ]

/-- **Its value at a hash function**: that function's answer at the told code of the key's value (a
key without a code: the digest of zeros). -/
theorem evaluate_commitAtCoins (hash : Hash) (i : R.Index) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) :
    (T.commitAtCoins b₀ i r σ).evaluate hash =
      ZKCP.digestUnder hash T.encT ((T.keyAtCoins b₀ i r σ).det (_root_.Run.famOne hash)) := by
  unfold LayoutsByPublicReading.commitAtCoins
  rw [OnBytes.Maker.ParsedRead.evaluate_deterministicOf_det, ZKCP.OComp.det_bind,
    _root_.Run.det_ofRom]
  unfold ZKCP.keyDigest ZKCP.digestUnder
  cases T.encT ((T.keyAtCoins b₀ i r σ).det (_root_.Run.famOne hash)) <;> rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.evaluate_commitAtCoins
#print axioms VerifiableInference.OnPublicFiles.committerTreeRoot_filling
#print axioms VerifiableInference.OnPublicFiles.committerAtFixedCoins_filling
#print axioms VerifiableInference.OnPublicFiles.commitBehind_key
#print axioms VerifiableInference.OnPublicFiles.commit_systemOn_plain
#print axioms VerifiableInference.OnPublicFiles.keyAtCoins_filling
#print axioms VerifiableInference.OnPublicFiles.commitAtCoins_filling
