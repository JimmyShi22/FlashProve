-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OnFilesArmsCD.lean: the main soundness statement arm by arm with the public data in the
typed key (Johnson/Top/OnFilesArmsC.lean), where the word under a root, the promises and the
extractor read a value that a public reading draws from the hash function
(Johnson/Top/OnFilesArmsD.lean).

Why both. The commitment ID's own string holds the public files' digest c: so that the key's code is
one function, fixed before the hash function, c must stand in the key (OnFilesArmsC.lean). The arms'
codings hold more answers of the hash function than c (at the entry file: the digest of the link's
parameters too). These cannot stand in the key: the ID's string does not hold them, and the step
behind the commitment ID asks that the code is one to one in what of the public data the key holds.
So the word under a root and the promises are read at the whole value d of a public reading, as in
OnFilesArmsD.lean, and the extractor runs that reading; the key holds the one part of d that the
ID's string spells.

The input r is that of OnFilesArmsC.lean, unturned. This file is OnFilesArmsD.lean's text at that
input: k.2 for k.
Main names (namespace `VerifiableInference.OnPublicFiles`):
  `BesideArmsCD r`: what only the theorems need: the type D, the reading `rd` at a key and its
    budget `q₀`, `wordOf` at d, the relaxed relation, three errors.
  `KeyHoldsCD`, `EntryHoldsCD`, `ProofHoldsCD`: the three promises at d.
  `extArmsCD b`: the extractor "run the reading, then decode, at the key's record, the word under
    the key's root, read at d off the committer's log".
  `CoreArmsCD b`: five named hypotheses: the three arms' bounds (`ZKCP.Gen.ArmBoundD`), the reading
    draws no coin and asks at most q₀ queries, no arm draws a coin.
  `CoreArmsCD.binds`: index binding of the scheme whose verifier holds the key itself, with that
    extractor.
  `HoleArmsCD.commitmentOO`: the hypothesis on the commitment, from that game.
  `verify_sound_arms_CD`: `SoundForWithO` (Johnson/Top/SoundO.lean) of `systemArmsC r`.
Limits: those of the two files named, of ArmsD.lean, GameOGen.lean and SoundO.lean. All premises are
hypotheses of the theorems: Lean's list of axioms does not show them. Nothing here says that the
arms draw the same d as the reading, or that they refuse a key whose c is not the part of d that is
meant: that stands inside each arm's bound. The error of the conclusion is the letter εO of the
hypothesis on the commitment. No input is given. Soundness alone.


-/
import Johnson.Top.OnFilesArmsC
import Johnson.Top.OnFilesArmsD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What only the theorems need. -/
structure BesideArmsCD (r : InputArmsC) where
  /-- what the public reading gives -/
  D : Type
  /-- the public reading, at a key -/
  rd : r.C × KeyRoot 256 r.L → Rom.OComp (rom 256) D
  /-- the reading's budget of queries -/
  q₀ : ℕ
  /-- the word under a root, read at d off a log of strings -/
  wordOf : D → Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol
  /-- witnesses -/
  Wn : Type
  /-- the relaxed relation -/
  Rno : r.I → r.X → Wn → Prop
  /-- the stated error of the key file's arm, in the committer's and the prover's bounds on queries
  -/
  εK : ℕ → ℕ → ℝ≥0∞
  /-- the stated error of the entry file's arm -/
  εE : ℕ → ℕ → ℝ≥0∞
  /-- the stated error of the proof file's arm -/
  εP : ℕ → ℕ → ℝ≥0∞
  /-- any instance -/
  x₀ : r.X

variable {r : InputArmsC} (b : BesideArmsCD r)

/-- The instance is true at the index: the relaxed relation has a witness. -/
def IsTrueArmsCD (i : r.I) (x : r.X) : Prop := ∃ w, b.Rno i x w

/-- What the key file's arm promises, at d. -/
def KeyHoldsCD (d : b.D) (k : r.C × KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (_ : r.X)
    (_ : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (_ : Rom.Trace (rom 256)) : Prop :=
  r.L.hasCollisionAt (b.wordOf d trC k.2.cm) k.2.rcd.1 ∨ r.L.decodeIndex (b.wordOf d trC k.2.cm) k.2.rcd ≠ none

/-- What the entry file's arm promises, at d. -/
def EntryHoldsCD (d : b.D) (k : r.C × KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (_ : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256)) : Prop :=
  ¬ r.L.hasCollisionAt (b.wordOf d trC k.2.cm) k.2.rcd.1 ∧
    ¬ r.L.hasCollisionAt (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1.1 ∧
    (r.L.decodeIndex (b.wordOf d trC k.2.cm) k.2.rcd = none ∨
      r.L.decodeIndex (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1 =
        r.L.decodeIndex (b.wordOf d trC k.2.cm) k.2.rcd)

/-- What the proof file's arm promises, at d. -/
def ProofHoldsCD (d : b.D) (_ : r.C × KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (x : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256)) : Prop :=
  r.L.hasCollisionAt (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1.1 ∨
    r.L.decodeIndex (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1 = none ∨
    ∃ i, r.L.decodeIndex (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1 = some i ∧ IsTrueArmsCD b i x

/-- The extractor of the scheme whose verifier holds the key itself: run the reading, then decode,
at the key's record, the word under the key's root, read at d off the committer's log. -/
def extArmsCD : ZKCP.Gen.ExtractorO (rom 256) r.I r.X Unit (r.C × KeyRoot 256 r.L)
    (OfflineLinkOnlineProof 256 r.L r.aT r.aL) :=
  ZKCP.Gen.extD b.rd (fun d k trC => r.L.decodeIndex (b.wordOf d trC k.2.cm) k.2.rcd) fun _ _ _ _ _ => ()

/-- No arm draws a coin. -/
def HoleArmsC.noCoin (r : InputArmsC) : Prop :=
  (∀ c cm rc p, (r.armK c cm rc p).NoCoin) ∧
    (∀ c cm cm' rc rc' p, (r.armE c cm cm' rc rc' p).NoCoin) ∧
    ∀ c cm x rc n p, (r.armP c cm x rc n p).NoCoin

/-- The named hypotheses but for the commitment and the meaning. -/
structure CoreArmsCD : Prop where
  keyArm   : ZKCP.Gen.ArmBoundD b.rd (liftKC r) (KeyHoldsCD b) b.εK
  entryArm : ZKCP.Gen.ArmBoundD b.rd (liftEC r) (EntryHoldsCD b) b.εE
  proofArm : ZKCP.Gen.ArmBoundD b.rd (liftPC r) (ProofHoldsCD b) b.εP
  reading  : ∀ k, (b.rd k).NoCoin ∧ (b.rd k).QueryBound b.q₀
  noCoin   : HoleArmsC.noCoin r

/-- The commitment: index binding of the scheme whose verifier holds the key itself, with
`extArmsCD b`, gives index binding behind the hash function's answer at the key's code, with
`extO`. -/
def HoleArmsCD.commitmentOO
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞) : Prop :=
  Rec.CommitmentBindsOO (schemeArmsC r) (extArmsCD b) b.q₀ r.enc extO q (IsTrueArmsCD b)
    (fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP)) εO

/-- The meaning, for a claim. -/
def HoleArmsCD.soundFor (claim : r.I → List Token → List Token → Prop) : Prop :=
  ∀ i (x' : List Token × List Token) a x, r.build x' a = some x → IsTrueArmsCD b i x →
    claim i x'.1 x'.2

variable {b}

/-- Index binding of the scheme whose verifier holds the key itself, with the extractor that runs
the public reading, at the sum of the three arms' errors. -/
theorem CoreArmsCD.binds (h : CoreArmsCD b) :
    ZKCP.Gen.HasIndexBindingWithO
      (ZKCP.Special.toPair (ZKCP.languageRelation (IsTrueArmsCD b))) (schemeArmsC r) (extArmsCD b)
      b.q₀ fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP) := by
  refine ZKCP.Gen.binds_of_armsD (vK := liftKC r) (vE := liftEC r) (vP := liftPC r) rfl
    (fun k => (h.reading k).1) (fun k => (h.reading k).2) h.keyArm h.entryArm h.proofArm
    fun d k trC x π trP hK hL hP => ?_
  obtain ⟨n0, n1, hl⟩ := hL
  have d0 : r.L.decodeIndex (b.wordOf d trC k.2.cm) k.2.rcd ≠ none := hK.resolve_left n0
  have e := hl.resolve_left d0
  obtain ⟨i, hi, ht⟩ := (hP.resolve_left n1).resolve_left fun hn => d0 (e.symm.trans hn)
  have hi' : r.L.decodeIndex (b.wordOf d trC k.2.cm) k.2.rcd = some i := e.symm.trans hi
  rw [hi']
  exact ⟨⟨(), ht⟩, ht⟩

/-- Where no arm draws a coin, the scheme's verifier draws none. -/
theorem noCoin_schemeArmsC (hn : HoleArmsC.noCoin r) (k : r.C × KeyRoot 256 r.L) (x : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) : ((schemeArmsC r).V k x π).NoCoin := by
  obtain ⟨a1, a2, a3⟩ := hn
  have c1 : (liftKC r k x π).NoCoin := by
    unfold liftKC
    split
    · exact a1 _ _ _ _
    · trivial
  have c2 : (liftEC r k x π).NoCoin := by
    unfold liftEC
    split
    · exact a2 _ _ _ _ _ _
    · trivial
  have c3 : (liftPC r k x π).NoCoin := by
    unfold liftPC
    split
    · exact a3 _ _ _ _ _ _
    · trivial
  exact c1.bind fun _ => c2.bind fun _ => c3.bind fun _ => trivial

/-- Under the 5 named hypotheses `CoreArmsCD b`, `HoleArmsCD.commitmentOO b extO q εO`,
`HoleArmsCD.soundFor b claim` and εO tC tP ≤ ε (tC + tP) (hypotheses of the theorem: Lean's list of
axioms does not show them): for every committer and every prover whose bounds on queries to the hash
function add up to t, the probability that the verifier of `systemArmsC r` accepts while the
extractor, which reads the commitment and the committer's log and asks the hash function at most q
times, gives no index, or an index at which the claim fails, is at most ε t. -/
theorem verify_sound_arms_CD (claim : r.I → List Token → List Token → Prop)
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞)
    (ε : ℕ → ℝ≥0∞) (h : CoreArmsCD b) (hc : HoleArmsCD.commitmentOO b extO q εO)
    (hs : HoleArmsCD.soundFor b claim) (hε : ∀ tC tP, εO tC tP ≤ ε (tC + tP)) :
    SoundForWithO (systemArmsC r) (fun c l => deterministicOf (extO.Ei c l)) q claim ε :=
  Rec.soundForWithO_systemE_O (schemeArmsC r) (extArmsCD b) b.q₀ r.enc extO q r.bound r.π₀
    r.nextToken h.binds (noCoin_schemeArmsC h.noCoin) hc claim b.x₀ hs hε

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.CoreArmsCD.binds
#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms_CD
