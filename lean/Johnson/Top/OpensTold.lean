-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OpensTold.lean: THE COMMITTER BEHIND A PUBLIC READING. At a told record T
(Johnson/Top/InnerCompiledVerifierByPublicReading.lean) whose committer reads the public value d through the hash
function, runs `committerOverTypedOracles` (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean) at the wire of the record and the
coding that hang on d, and lays `T.part d` beside the key: whoever opens a key opens it to the index
that `T.ext` gives; and so for the commitment, at `T.extractor`. Theorems with proofs.

What this file states.
  `CommitsBehind T ri sl b₀ isk`: the law on T's committer, an equation of algorithms.
  `good_told`: said of logs: outside the Merkle hash event on three logs, where the word off the
    key's maker's log is the word off all three, `T.ext` gives at that log the index that the run
    again commits to.
  **`told_opens_key`**: index binding of `T.scheme` with openings in place of proofs
    (Rom/WithOpenings.lean), at `T.ext`, with the bound 2 (tC + (tO + tS) + 1)² / 2^256.
  **`told_opens`**: `ZKCP.OpensToExtracted` of the told scheme under the digest of its key's code,
    at `T.extractor`: the hypothesis `opens` of Ladder/FitBinds.lean.
  **`told_bindsWith`**: `BindsWith T.system T.extractor`.
  THE SAME AT A CUT TYPE OF INDICES, WHERE hdec IS ASKED ONLY OF THE INDICES THAT ARE OPENED TO: J
  any type, back : J → R.Index, φ : R.Index → Option J with φ (back j) = some j: `T.schemeOn back` (the
  committer at back j), `T.extOn φ` (`T.ext`, then φ, by bind), `T.systemOn back nt`,
  `good_committerOverTypedOracles_at`,
  `good_told_on`, **`told_opens_key_on`**, **`told_opens_on`**, **`told_bindsWith_on`**; and
  `extractorOn_eq`: the named extractor there is `T.extractor`, then φ, by bind.

Under. The wire's laws (hW); hdec (the decoder gives every index back from its honest encoding and
record); the law on the committer (hC); five of the told law's six (noCoin, asks, once, spare,
word) and, for the last two, the sixth (code); every key that the committer can put out has a code
(hcode); tS bounds the whole committer's queries, the public reading's among them (hS).

How. `binding_of_badW` (Johnson/TypedOracleCompiler/RecCompile/OpensTwoStage.lean) carries a public algorithm and a
family of codings already, and counts the committer's run again to the second stage: so that run may
ask the public strings. What is special to a scheme is its hypothesis hgood, on logs: here a run of
the committer in a log that holds one function's answers falls into a run of the reading, whose
value is the reading's value at that function (`det_of_runsIn`), and a run of `committerOverTypedOracles` at that
value: `good_committerOverTypedOracles`. `word` carries the extractor from the value that `T.ext` picks to that one.

Limits. Those of Johnson/TypedOracleCompiler/RecCompile/OpensCommitOverTypedOracles.lean but for "one coding": hdec IS A PREMISE
and is false at an index type with a member that the decoder never gives: READ OFF THAT FILE, NOT
PROVED: IT IS FALSE AT THE ONLY INPUTS THAT THIS LIBRARY WRITES AT THE TWO SIZES; the like at `C.D`
holds where `ConfigurationWithOutOfDomainSample.Props` does (`ConfigurationWithOutOfDomainSample.Props.D_enc`, Hiop/RecMainProof.lean). The bound is a term in
tS; the verifier is idle; no program's committer is spoken of. OF d THE KEY FIXES `T.part d` ALONE.
The public files are fixed before the hash function is drawn. No T is built here.

-/
import Johnson.Top.InnerCompiledVerifierByPublicReading
import Johnson.Top.BindsAtInnerSystem
import OnBytes.TypedOracleCompiler.Joined.YesByCutsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R)

/-- **The law on the committer**: it reads the public value d, runs `committerOverTypedOracles` at the wire of the
record and the coding at d, and lays the told part beside the key. isk: what it keeps for the
prover. -/
def CommitsBehind (ri : Enum R.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : R.LeafBody)
    (isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK) : Prop :=
  ∀ i, T.commit i = T.Pub.bind fun d =>
    ((committerOverTypedOracles R.queryLayout (T.Sd d) ri sl b₀ i).overOne (T.m d)).bind fun o =>
      .pure ((T.part d, o.1), isk d o.2)

variable {T}

/-- **Said of logs.** g: a hash function; trC the log of the key's maker, trP the opener's, trV that
of the committer's run again, all with g's answers. -/
theorem good_told (hW : R.queryLayout.OKG)
    (hdec : ∀ i r s, R.protocol.decodeIndex (R.protocol.encodeIndex i r) (R.protocol.recOf i r s) = some i)
    {ri : Enum R.protocol.EncodingRandomness} {sl : Enum (ℕ → Bits)} {b₀ : R.LeafBody}
    {isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK} (hC : CommitsBehind T ri sl b₀ isk)
    (noCoin : T.Pub.NoCoin)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (g : Fam (rom 256)) (key : Dig 256 × KeyRoot 256 R.protocol) (i : R.Index) (n : ℕ)
    (trC trP trV : Trace (rom 256))
    (hans : ∀ e ∈ trC ++ (trP ++ trV), e.2.2 = g e.1 e.2.1)
    (hrun : RunsIn trV (T.scheme.commitAt i n) key)
    (hM : ¬ EM (singleTr (T.m (T.Pub.det g)) (trC ++ (trP ++ trV))))
    (he : extEnc R.queryLayout (singleTr (T.m (T.Pub.det g)) trC) key.2.cm =
      extEnc R.queryLayout (singleTr (T.m (T.Pub.det g)) (trC ++ (trP ++ trV))) key.2.cm) :
    T.ext.Ei key trC = some i := by
  classical
  have hrun : RunsIn trV (((T.commit i).withCoins n).bind fun keys => OComp.pure keys.1) key :=
    hrun
  rw [hC i, OComp.withCoins_bind_of_noCoin _ _ _ noCoin] at hrun
  obtain ⟨keys, h1, h2⟩ := (runsIn_bind_iff _ _ _).1 hrun
  obtain rfl := runsIn_pure_iff.1 h2
  obtain ⟨d, hd, h3⟩ := (runsIn_bind_iff _ _ _).1 h1
  rw [OComp.withCoins_bind_pure (fun o : KeyRoot 256 R.protocol × (R.Index × R.protocol.EncodingRandomness × (ℕ → Bits)) =>
    ((T.part d, o.1), isk d o.2))] at h3
  obtain ⟨o, ho, h4⟩ := (runsIn_bind_iff _ _ _).1 h3
  obtain rfl := runsIn_pure_iff.1 h4
  have hdg : T.Pub.det g = d :=
    TypedOracleCompiler.Joined.det_of_runsIn (fun e he' => (hans e
              (List.mem_append_right _ (List.mem_append_right _ he'))).symm) hd
  rw [hdg] at hM he
  have key := good_committerOverTypedOracles R.queryLayout (T.Sd d) (by norm_num) hW hdec (T.m d) ri sl b₀ i n ho hM he
  have hex : ∃ d', T.part d' = T.part d := ⟨d, rfl⟩
  show (if h : ∃ d', T.part d' = T.part d then
    (extractorOverOneHashFunction (T.m h.choose) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei o.1 trC else none) = some i
  rw [dif_pos hex, word hex.choose d hex.choose_spec]
  exact key

/-- **Whoever opens a key of the told scheme, by running its committer again, opens it to what
`T.ext` gives at that key and its maker's log**, but for 2 (tC + (tO + tS) + 1)² / 2^256. -/
theorem told_opens_key (hW : R.queryLayout.OKG)
    (hdec : ∀ i r s, R.protocol.decodeIndex (R.protocol.encodeIndex i r) (R.protocol.recOf i r s) = some i)
    {ri : Enum R.protocol.EncodingRandomness} {sl : Enum (ℕ → Bits)} {b₀ : R.LeafBody}
    {isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK} (hC : CommitsBehind T ri sl b₀ isk)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (tS : ℕ) (hS : ∀ i, (T.commit i).QueryBound tS) :
    HasIndexBindingWith (openingRelation R.Index) (SpecialAny.oneOf T.scheme).withOpenings
      (Special.extOf T.ext).withOpenings
      fun tC tO => 2 * ((tC + (tO + tS) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  Rom.binding_withOpenings_rom _ _ _
    (binding_of_badW (W := R.queryLayout) (by norm_num) T.m T.Pt spare T.Pub noCoin asks once T.scheme T.ext
      (fun k => k.2.cm) tS hS
      (fun g key i n trC trP trV hans hrun hM he =>
        good_told hW hdec hC noCoin word g key i n trC trP trV hans hrun hM he))

/-- The bound of `told_opens`: that of `told_opens_key` behind the hash of the key's code. -/
def epsOpensTold (tS : ℕ) : ℕ → ℕ → ℝ≥0∞ :=
  epsOpens (fun tC tO => 2 * ((tC + (tO + tS) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256) tS

/-- **Whoever opens a commitment of the told scheme opens it to what `T.extractor` gives.** code: no
two pairs (told part, key) have one code; hcode: every key that the committer can put out has a
code; hS': the bound tS in the syntax of ZKCP/Defs.lean. -/
theorem told_opens (hW : R.queryLayout.OKG)
    (hdec : ∀ i r s, R.protocol.decodeIndex (R.protocol.encodeIndex i r) (R.protocol.recOf i r s) = some i)
    {ri : Enum R.protocol.EncodingRandomness} {sl : Enum (ℕ → Bits)} {b₀ : R.LeafBody}
    {isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK} (hC : CommitsBehind T ri sl b₀ isk)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    (hcode : (ZKCP.SpecialAny.oneOf T.scheme).KeysHaveCodes T.encT)
    (tS : ℕ) (hS : ∀ i, (T.commit i).QueryBound tS)
    (hS' : ∀ i, ((ZKCP.SpecialAny.oneOf T.scheme).C i).QueryBound tS) :
    ZKCP.OpensToExtracted (Rec.digestKeyScheme T.scheme T.encT) T.extractor (epsOpensTold tS) :=
  Rec.opens_digestSchemeE T.scheme T.ext T.encT code hcode hS'
    (told_opens_key hW hdec hC noCoin asks once spare word tS hS)

/-- **The commitment of the told system binds to what `T.extractor` gives.** -/
theorem told_bindsWith (hW : R.queryLayout.OKG)
    (hdec : ∀ i r s, R.protocol.decodeIndex (R.protocol.encodeIndex i r) (R.protocol.recOf i r s) = some i)
    {ri : Enum R.protocol.EncodingRandomness} {sl : Enum (ℕ → Bits)} {b₀ : R.LeafBody}
    {isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK} (hC : CommitsBehind T ri sl b₀ isk)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    (hcode : (ZKCP.SpecialAny.oneOf T.scheme).KeysHaveCodes T.encT)
    (tS : ℕ) (hS : ∀ i, (T.commit i).QueryBound tS)
    (hS' : ∀ i, ((ZKCP.SpecialAny.oneOf T.scheme).C i).QueryBound tS)
    (ε : ℕ → ℝ≥0∞) (hε : ∀ tC tO, epsOpensTold tS tC tO ≤ ε (tC + tO)) :
    BindsWith T.system T.extractor ε :=
  Rec.bindsWith_systemE T.scheme T.ext T.encT R.coinBound R.buildInstance T.π₀ R.nextToken
    (told_opens hW hdec hC noCoin asks once spare word code hcode tS hS hS') hε

/-! ## At a cut type of indices -/

section On
variable {J : Type}

/-- `good_committerOverTypedOracles` (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean) with hdec asked at the one index i. Its
proof is that theorem's. -/
theorem good_committerOverTypedOracles_at {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type}
    {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (hlam : 0 < lam) (hW : W.OKG) (i : I)
    (hdec : ∀ r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits))
    (b₀ : Bd) (n : ℕ)
    {trC trP trV : Trace (rom lam)} {o : KeyRoot lam L × (I × L.EncodingRandomness × (ℕ → Bits))}
    (h : RunsIn trV (((committerOverTypedOracles W S ri sl b₀ i).overOne m).withCoins n) o)
    (hM : ¬ EM (singleTr m (trC ++ (trP ++ trV))))
    (he : extEnc W (singleTr m trC) o.1.cm =
      extEnc W (singleTr m (trC ++ (trP ++ trV))) o.1.cm) :
    (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W)).Ei o.1 trC = some i := by
  obtain ⟨-, ht, s, hs⟩ := run_committerOverTypedOracles W S hlam m ri sl b₀ i n h
  have hsub : singleTr m trV ⊆ singleTr m (trC ++ (trP ++ trV)) := by
    rw [singleTr_append, singleTr_append]
    exact fun e he => List.mem_append_right _ (List.mem_append_right _ he)
  show L.decodeIndex (extEnc W (singleTr m trC) o.1.cm) o.1.rcd = some i
  rw [he, word_committerTreeRoot W hW b₀ _ _ hM (ht.mono hsub), hs]
  exact hdec _ _

variable (T)

/-- The told scheme with its committer at back j: the indices are the members of J. -/
def LayoutsByPublicReading.schemeOn (back : J → R.Index) : ZKCP.Gen.Arg (rom 256) J R.Instance Unit
    (Dig 256 × KeyRoot 256 R.protocol) T.ISK (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) where
  C := fun j => T.commit (back j)
  P := T.prove
  V := T.scheme.V

/-- `T.ext`, then φ, by bind. -/
def LayoutsByPublicReading.extOn (φ : R.Index → Option J) : ZKCP.Gen.Extractor (rom 256) J R.Instance Unit
    (Dig 256 × KeyRoot 256 R.protocol) (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) where
  Ei := fun k tr => (T.ext.Ei k tr).bind φ
  Ew := fun _ _ _ _ _ => ()

/-- The argument system over J: the commitment is the hash function's answer at the told code. -/
def LayoutsByPublicReading.systemOn (back : J → R.Index) (nt : J → List Token → Option Token) : ArgumentSystem :=
  Rec.tokenArgumentSystem (T.schemeOn back) T.encT R.coinBound R.buildInstance T.π₀ nt

/-- The named extractor over J. -/
def LayoutsByPublicReading.extractorOn (φ : R.Index → Option J) : Commitment → QueryLog → Option J :=
  (Rec.tokenExtractorE (X := R.Instance) (T.extOn φ) T.encT).Ei

/-- It is `T.extractor`, then φ, by bind. -/
theorem LayoutsByPublicReading.extractorOn_eq (φ : R.Index → Option J) :
    T.extractorOn φ = fun commitment queryLog => (T.extractor commitment queryLog).bind φ := by
  funext commitment queryLog
  show ((ZKCP.firstKey T.encT commitment queryLog).bind fun key =>
      ((ZKCP.Special.extOf T.ext).Ei key queryLog).bind φ) =
    ((ZKCP.firstKey T.encT commitment queryLog).bind fun key =>
      (ZKCP.Special.extOf T.ext).Ei key queryLog).bind φ
  cases ZKCP.firstKey T.encT commitment queryLog <;> rfl

variable {T}

/-- **Said of logs, at a cut type of indices.** hdec is asked at the indices back j alone. -/
theorem good_told_on (hW : R.queryLayout.OKG) (back : J → R.Index) (φ : R.Index → Option J)
    (hφ : ∀ j, φ (back j) = some j)
    (hdec : ∀ j r s, R.protocol.decodeIndex (R.protocol.encodeIndex (back j) r) (R.protocol.recOf (back j) r s) = some (back j))
    {ri : Enum R.protocol.EncodingRandomness} {sl : Enum (ℕ → Bits)} {b₀ : R.LeafBody}
    {isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK} (hC : CommitsBehind T ri sl b₀ isk)
    (noCoin : T.Pub.NoCoin)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (g : Fam (rom 256)) (key : Dig 256 × KeyRoot 256 R.protocol) (j : J) (n : ℕ)
    (trC trP trV : Trace (rom 256))
    (hans : ∀ e ∈ trC ++ (trP ++ trV), e.2.2 = g e.1 e.2.1)
    (hrun : RunsIn trV ((T.schemeOn back).commitAt j n) key)
    (hM : ¬ EM (singleTr (T.m (T.Pub.det g)) (trC ++ (trP ++ trV))))
    (he : extEnc R.queryLayout (singleTr (T.m (T.Pub.det g)) trC) key.2.cm =
      extEnc R.queryLayout (singleTr (T.m (T.Pub.det g)) (trC ++ (trP ++ trV))) key.2.cm) :
    (T.extOn φ).Ei key trC = some j := by
  classical
  have hrun : RunsIn trV (((T.commit (back j)).withCoins n).bind fun keys =>
      OComp.pure keys.1) key := hrun
  rw [hC (back j), OComp.withCoins_bind_of_noCoin _ _ _ noCoin] at hrun
  obtain ⟨keys, h1, h2⟩ := (runsIn_bind_iff _ _ _).1 hrun
  obtain rfl := runsIn_pure_iff.1 h2
  obtain ⟨d, hd, h3⟩ := (runsIn_bind_iff _ _ _).1 h1
  rw [OComp.withCoins_bind_pure (fun o : KeyRoot 256 R.protocol × (R.Index × R.protocol.EncodingRandomness × (ℕ → Bits)) =>
    ((T.part d, o.1), isk d o.2))] at h3
  obtain ⟨o, ho, h4⟩ := (runsIn_bind_iff _ _ _).1 h3
  obtain rfl := runsIn_pure_iff.1 h4
  have hdg : T.Pub.det g = d :=
    TypedOracleCompiler.Joined.det_of_runsIn (fun e he' => (hans e
              (List.mem_append_right _ (List.mem_append_right _ he'))).symm) hd
  rw [hdg] at hM he
  have key := good_committerOverTypedOracles_at R.queryLayout (T.Sd d) (by norm_num) hW (back j) (hdec j) (T.m d) ri sl b₀ n
    ho hM he
  have hex : ∃ d', T.part d' = T.part d := ⟨d, rfl⟩
  show (if h : ∃ d', T.part d' = T.part d then
    (extractorOverOneHashFunction (T.m h.choose) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei o.1 trC else none).bind φ = some j
  rw [dif_pos hex, word hex.choose d hex.choose_spec, key]
  exact hφ j

/-- **Whoever opens a key opens it to what `T.ext`, then φ, gives: at a cut type of indices.** -/
theorem told_opens_key_on (hW : R.queryLayout.OKG) (back : J → R.Index) (φ : R.Index → Option J)
    (hφ : ∀ j, φ (back j) = some j)
    (hdec : ∀ j r s, R.protocol.decodeIndex (R.protocol.encodeIndex (back j) r) (R.protocol.recOf (back j) r s) = some (back j))
    {ri : Enum R.protocol.EncodingRandomness} {sl : Enum (ℕ → Bits)} {b₀ : R.LeafBody}
    {isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK} (hC : CommitsBehind T ri sl b₀ isk)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (tS : ℕ) (hS : ∀ j, (T.commit (back j)).QueryBound tS) :
    HasIndexBindingWith (openingRelation J) (SpecialAny.oneOf (T.schemeOn back)).withOpenings
      (Special.extOf (T.extOn φ)).withOpenings
      fun tC tO => 2 * ((tC + (tO + tS) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  Rom.binding_withOpenings_rom _ _ _
    (binding_of_badW (W := R.queryLayout) (by norm_num) T.m T.Pt spare T.Pub noCoin asks once
      (T.schemeOn back) (T.extOn φ) (fun k => k.2.cm) tS hS
      (fun g key j n trC trP trV hans hrun hM he =>
        good_told_on hW back φ hφ hdec hC noCoin word g key j n trC trP trV hans hrun hM he))

/-- **Whoever opens a commitment opens it to what `T.extractor`, then φ, gives: at a cut type of
indices.** -/
theorem told_opens_on (hW : R.queryLayout.OKG) (back : J → R.Index) (φ : R.Index → Option J)
    (hφ : ∀ j, φ (back j) = some j)
    (hdec : ∀ j r s, R.protocol.decodeIndex (R.protocol.encodeIndex (back j) r) (R.protocol.recOf (back j) r s) = some (back j))
    {ri : Enum R.protocol.EncodingRandomness} {sl : Enum (ℕ → Bits)} {b₀ : R.LeafBody}
    {isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK} (hC : CommitsBehind T ri sl b₀ isk)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    (hcode : (ZKCP.SpecialAny.oneOf (T.schemeOn back)).KeysHaveCodes T.encT)
    (tS : ℕ) (hS : ∀ j, (T.commit (back j)).QueryBound tS)
    (hS' : ∀ j, ((ZKCP.SpecialAny.oneOf (T.schemeOn back)).C j).QueryBound tS) :
    ZKCP.OpensToExtracted (Rec.digestKeyScheme (T.schemeOn back) T.encT) (T.extractorOn φ)
      (epsOpensTold tS) :=
  Rec.opens_digestSchemeE (T.schemeOn back) (T.extOn φ) T.encT code hcode hS'
    (told_opens_key_on hW back φ hφ hdec hC noCoin asks once spare word tS hS)

/-- **The commitment of the told system over J binds to what `T.extractor`, then φ, gives.** -/
theorem told_bindsWith_on (hW : R.queryLayout.OKG) (back : J → R.Index) (φ : R.Index → Option J)
    (hφ : ∀ j, φ (back j) = some j)
    (hdec : ∀ j r s, R.protocol.decodeIndex (R.protocol.encodeIndex (back j) r) (R.protocol.recOf (back j) r s) = some (back j))
    {ri : Enum R.protocol.EncodingRandomness} {sl : Enum (ℕ → Bits)} {b₀ : R.LeafBody}
    {isk : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → T.ISK} (hC : CommitsBehind T ri sl b₀ isk)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    (hcode : (ZKCP.SpecialAny.oneOf (T.schemeOn back)).KeysHaveCodes T.encT)
    (tS : ℕ) (hS : ∀ j, (T.commit (back j)).QueryBound tS)
    (hS' : ∀ j, ((ZKCP.SpecialAny.oneOf (T.schemeOn back)).C j).QueryBound tS)
    (nt : J → List Token → Option Token)
    (ε : ℕ → ℝ≥0∞) (hε : ∀ tC tO, epsOpensTold tS tC tO ≤ ε (tC + tO)) :
    BindsWith (T.systemOn back nt)
      (fun commitment queryLog => (T.extractor commitment queryLog).bind φ) ε := by
  have key : BindsWith (T.systemOn back nt) (T.extractorOn φ) ε :=
    Rec.bindsWith_systemE (T.schemeOn back) (T.extOn φ) T.encT R.coinBound R.buildInstance T.π₀ nt
      (told_opens_on hW back φ hφ hdec hC noCoin asks once spare word code hcode tS hS hS') hε
  exact T.extractorOn_eq φ ▸ key

end On

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.good_told
#print axioms VerifiableInference.OnPublicFiles.told_opens_key
#print axioms VerifiableInference.OnPublicFiles.told_opens
#print axioms VerifiableInference.OnPublicFiles.told_bindsWith
#print axioms VerifiableInference.OnPublicFiles.good_committerOverTypedOracles_at
#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.extractorOn_eq
#print axioms VerifiableInference.OnPublicFiles.good_told_on
#print axioms VerifiableInference.OnPublicFiles.told_opens_key_on
#print axioms VerifiableInference.OnPublicFiles.told_opens_on
#print axioms VerifiableInference.OnPublicFiles.told_bindsWith_on
