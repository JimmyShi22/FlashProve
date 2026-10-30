-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsLaw.lean: THE LAW OF BINDING FOR A TOLD RECORD, THE COINS IN THE
OPENER'S HAND: general in the compiler's input R, the told record T and the argument system.
Statements and proofs. It reads no description: so that it can be applied over any.

Why. Whoever wants binding at a description would else walk a long road (terms laid in, a re-bound
description, a coins' algorithm, enumerations by digits). Here the law is typed at its user's own
letters. FOURTEEN PREMISES: two on the system (its committer has the values of the written committer
(written in Lean beside the IOP: a placeholder that corresponds to no program of the release)
of a told record; the salts' fence), eleven laws on the record with back and φ, one test on numbers.

Main names (namespace `VerifiableInference.OnPublicFiles`).
  `commit_systemOn_written`: the told system's committer at the number of a pair of entries that
    covers given coins (r, σ) IS `T.commitAtCoins b (back j) r σ`
    (Johnson/Top/ToldCommitPlain.lean). From `commit_systemOn_reach`, `commit_systemOn_salts`,
    `commit_systemOn_plain`.
  `told_binds_written_of`: the law from any two enumerations that cover the opener's coins and any
    prover: TOOLS OF THE PROOF: the conclusion names none.
  **`told_binds_written`**: let `new` be ANY argument system whose committer at (w, x) has, at every
    hash function, the value of `T.commitAtCoins b (back w) (rOf x) (σOf x)` (written), the salts of
    one length at the tree's 2^depth places (fence). Let the wire be in order (hW), φ give back w
    from `back w` (hφ), the decoder give back the index of every w (hdec); let the public reading
    draw no coin, ask at public strings alone, ask none twice (noCoin, asks, once); let these
    strings be spare in every coding (spare), the word's extractor hang on the told part alone
    (word), the told code be one to one and total (code, total); let the reading ask at most tP
    queries, and tP + 2 · 2^depth + 2 (K + 1) ≤ tMax. THEN `BindsWith new (T.extractorOn φ) (epsBind
    tMax)`: 3 (t + 2 tMax + 2)² / 2^256 (Ladder/FitBinds.lean). By `told_bindsWith_on`
    (Johnson/Top/OpensTold.lean) over the record re-bound to as many coins as there are pairs, and
    `BindsWith.ofCommit` (Ladder/FitBinds.lean) at an algorithm that asks nothing.

Every "there is", walked. In the conclusions: none. In premises: onto and covers of
`told_binds_written_of` (for each randomness x of the new system an entry of each enumeration): paid
in `told_binds_written` by `enumAll_onto` and `saltsAll_covers` (Johnson/Top/ToldReachAll.lean:
enumerations picked by choice: parts of the adversary that the proof builds, of no term that runs).
Limits. (1) THE FENCE: salts of another length at a place of the tree are not in the experiment (no
finite enumeration covers all lengths). (2) THE VERIFIER IS IDLE: binding reads the committer alone;
to open is to name weights and coins at which the written committer, run again, gives the
commitment. (3) VALUES, NOT ALGORITHMS: `written` ties values: nothing follows on the count or the
log of `new`'s own committer. rOf AND σOf DO NOT SEE THE HASH FUNCTION: a committer that derives its
coins from answers goes through `BindsWith.ofCommit` (Ladder/FitBinds.lean) behind this law. (4) The
eleven laws are premises. That the fourteen can be met together is shown where the law is applied
(Johnson/Goal/Conditions/BindsTold.lean; BindsAtSecondHashFunction.lean). Nothing on soundness, completeness or
hiding; no program's commitment is spoken of.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.ReBound
import Johnson.Top.ToldCommitPlain
import Johnson.Top.ToldReachAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP VerifierAndGoals.Fit
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R)

/-- **The told system's committer at the number of a pair that covers given coins is the written
committer at these coins.** -/
theorem commit_systemOn_written (ri : Enum R.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b : R.LeafBody)
    (prove : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → (l : List (R.Instance × Unit)) →
      Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) l))
    {J : Type} (back : J → R.Index) (nt : J → List Token → Option Token) (noCoin : T.Pub.NoCoin)
    (j : J) (a : Fin (ri.n + 1)) (c : Fin (sl.n + 1))
    (hn : a.val + (ri.n + 1) * c.val < R.coinBound + 1) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) (ha : ri.e a = r)
    (hc : ∀ k, k < 2 ^ R.queryLayout.depth → sl.e c k = σ k) :
    ((T.withCommit ri sl b prove).systemOn back nt).commit j ⟨a.val + (ri.n + 1) * c.val, hn⟩ =
      T.commitAtCoins b (back j) r σ := by
  rw [commit_systemOn_reach T ri sl b prove back nt noCoin j a c hn, ha,
    commit_systemOn_salts T b prove back nt noCoin j r (sl.e c) σ hc]
  exact commit_systemOn_plain T b prove back nt noCoin j r σ

/-- The law below, from any two enumerations that cover the opener's coins, and any prover: tools of
the proof: the conclusion names none of the three. -/
theorem told_binds_written_of (new : ArgumentSystem) (back : new.Weights → R.Index)
    (φ : R.Index → Option new.Weights) (b : R.LeafBody) (rOf : new.CommitmentRandomness → R.protocol.EncodingRandomness)
    (σOf : new.CommitmentRandomness → ℕ → Bits)
    (written : ∀ w x hash, (new.commit w x).evaluate hash =
      (T.commitAtCoins b (back w) (rOf x) (σOf x)).evaluate hash)
    (ri : Enum R.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (onto : ∀ x, ∃ a, ri.e a = rOf x)
    (covers : ∀ x, ∃ c, ∀ k, k < 2 ^ R.queryLayout.depth → sl.e c k = σOf x k)
    (prove : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → (l : List (R.Instance × Unit)) →
      Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) l))
    (hW : R.queryLayout.OKG) (hφ : ∀ w, φ (back w) = some w)
    (hdec : ∀ w r s, R.protocol.decodeIndex (R.protocol.encodeIndex (back w) r) (R.protocol.recOf (back w) r s) = some (back w))
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT) (total : ∀ key, T.encT key ≠ none)
    (tP : ℕ) (reading : T.Pub.QueryBound tP) (tMax : ℕ)
    (count : tP + (2 * 2 ^ R.queryLayout.depth + 2 * (R.queryLayout.K + 1)) ≤ tMax) :
    BindsWith new (T.extractorOn φ) (epsBind tMax) := by
  have hn1 : (ri.n + 1) * (sl.n + 1) - 1 + 1 = (ri.n + 1) * (sl.n + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))
  have hn : ∀ x, (Classical.choose (onto x)).val + (ri.n + 1) * (Classical.choose (covers x)).val <
      (R.reBound ((ri.n + 1) * (sl.n + 1) - 1)).coinBound + 1 := fun x =>
    lt_of_lt_of_eq (reach_pair ri.n sl.n _ _ (Classical.choose (onto x)).isLt
      (Classical.choose (covers x)).isLt).2.2 hn1.symm
  have h1 := told_bindsWith_on
    (T := (T.reBound ((ri.n + 1) * (sl.n + 1) - 1)).withCommit ri sl b prove) hW back φ hφ hdec
    (commitsBehind_withCommit (T.reBound ((ri.n + 1) * (sl.n + 1) - 1)) ri sl b prove) noCoin asks
    once spare word code ((ZKCP.SpecialAny.oneOf _).keysHaveCodes_of_total total)
    (tP + (2 * 2 ^ R.queryLayout.depth + 2 * (R.queryLayout.K + 1)))
    (fun w => queryBound_commitBehind (T.reBound ((ri.n + 1) * (sl.n + 1) - 1)) ri sl b tP reading
      (back w))
    (fun w => Rom.queryBound_oneOf_C _ w (queryBound_commitBehind
      (T.reBound ((ri.n + 1) * (sl.n + 1) - 1)) ri sl b tP reading (back w)))
    new.nextToken (epsBind tMax) (epsOpensTold_le _ tMax count)
  have h2 := BindsWith.ofCommit _ new _ (epsBind tMax) h1 some id
    (fun x => .done ⟨_, hn x⟩) 0 (fun _ => trivial) (fun _ => rfl) (fun w x hash => by
      rw [written w x hash]
      exact congrArg (fun A : DeterministicAlgorithm Commitment => A.evaluate hash)
        (commit_systemOn_written (T.reBound ((ri.n + 1) * (sl.n + 1) - 1)) ri sl b prove back
          new.nextToken noCoin w (Classical.choose (onto x)) (Classical.choose (covers x)) (hn x)
          (rOf x) (σOf x) (Classical.choose_spec (onto x)) (Classical.choose_spec (covers x))).symm)
  have e : (fun commitment queryLog =>
      ((T.extractor commitment queryLog).bind φ).bind some) = T.extractorOn φ := by
    rw [LayoutsByPublicReading.extractorOn_eq]
    funext commitment queryLog
    cases (T.extractor commitment queryLog).bind φ <;> rfl
  exact e ▸ h2

/-- **THE LAW OF BINDING FOR A TOLD RECORD, THE COINS IN THE OPENER's HAND.** Let `new` be any
argument system whose committer has, AT EVERY HASH FUNCTION, the value of the written committer of T
(`T.commitAtCoins`, Johnson/Top/ToldCommitPlain.lean) at the index `back w` and at the coins that
rOf and σOf read off its randomness, the salts of one length len at the tree's places. Then its
commitment binds to what φ makes of T's extractor's index, at the error `epsBind tMax`, tMax a bound
on the told committer's queries. -/
theorem told_binds_written (new : ArgumentSystem) (back : new.Weights → R.Index)
    (φ : R.Index → Option new.Weights) (b : R.LeafBody) (rOf : new.CommitmentRandomness → R.protocol.EncodingRandomness)
    (σOf : new.CommitmentRandomness → ℕ → Bits)
    (written : ∀ w x hash, (new.commit w x).evaluate hash =
      (T.commitAtCoins b (back w) (rOf x) (σOf x)).evaluate hash)
    (len : ℕ) (fence : ∀ x k, k < 2 ^ R.queryLayout.depth → (σOf x k).length = len)
    (hW : R.queryLayout.OKG) (hφ : ∀ w, φ (back w) = some w)
    (hdec : ∀ w r s, R.protocol.decodeIndex (R.protocol.encodeIndex (back w) r) (R.protocol.recOf (back w) r s) = some (back w))
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT) (total : ∀ key, T.encT key ≠ none)
    (tP : ℕ) (reading : T.Pub.QueryBound tP) (tMax : ℕ)
    (count : tP + (2 * 2 ^ R.queryLayout.depth + 2 * (R.queryLayout.K + 1)) ≤ tMax) :
    BindsWith new (T.extractorOn φ) (epsBind tMax) :=
  told_binds_written_of T new back φ b rOf σOf written (enumAll R.protocol.EncodingRandomness)
    (saltsAll R.queryLayout.depth len) (fun x => enumAll_onto R.protocol.EncodingRandomness (rOf x))
    (fun x => saltsAll_covers R.queryLayout.depth len (σOf x) (fence x))
    (fun _ l => .pure ⟨l.map fun _ => T.π₀.2, List.length_map ..⟩) hW hφ hdec noCoin asks once
    spare word code total tP reading tMax count

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.commit_systemOn_written
#print axioms VerifiableInference.OnPublicFiles.told_binds_written_of
#print axioms VerifiableInference.OnPublicFiles.told_binds_written
