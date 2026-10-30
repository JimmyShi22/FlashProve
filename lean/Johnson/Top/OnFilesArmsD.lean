-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OnFilesArmsD.lean: the main soundness statement arm by arm
(Johnson/Top/OnFilesArms.lean) where the word under a root, the promises and the extractor read a
value that a public reading draws from the hash function.

Why. The verifier's public digests are answers of the hash function at public strings. If they stand
in the input r as constants, r holds values of the fixed hash function, and soundness over a random
function says nothing of it. Here r's three arms are to draw them by their own queries; the codings,
and with them the word under a root, then hang on the value d that is drawn; so `wordOf` takes d,
the three promises are read at d, and the extractor runs the public reading first
(Johnson/Top/ArmsD.lean). The input r is that of Johnson/Top/OnFilesArms.lean, unturned.
Main names (namespace `VerifiableInference.OnPublicFiles`):
  `BesideArmsD r`: what only the theorems need: the type D, the reading `rd` at a key and its budget
    `q₀`, `wordOf` at d, the relaxed relation, three errors.
  `KeyHoldsD`, `EntryHoldsD`, `ProofHoldsD`: the three promises of Johnson/Top/OnFilesArms.lean at
    d.
  `extArmsD b`: the extractor "run the reading, then decode, at the key's record, the word under the
    key's root, read at d off the committer's log".
  `CoreArmsD b`: five named hypotheses: the three arms' bounds, the reading draws no coin and asks
    at most q₀ queries, no arm draws a coin.
  `CoreArmsD.binds`: index binding of the scheme whose verifier holds the key itself, with that
    extractor.
  `HoleArmsD.commitmentOO`: the hypothesis on the commitment, from that game.
  `verify_sound_arms_D`: `SoundForWithO` (Johnson/Top/SoundO.lean) of `systemArms r`.
Limits: those of Johnson/Top/OnFilesArms.lean, ArmsD.lean, GameOGen.lean and SoundO.lean. All
premises are hypotheses of the theorems: Lean's list of axioms does not show them. Nothing here
says that the arms draw the same d as the reading: that stands inside each arm's bound. The key's
code `r.enc` is still a function of the key alone: a code that holds a public digest must take it
from the key. The key's type here has no place for it: at the input that is meant today the digest
stands in the code as a constant, and nothing is said of that input yet;
Johnson/Top/OnFilesArmsC.lean has the wider key. The error of the conclusion is the letter εO of
the hypothesis on the commitment. No input is given.

-/
import Johnson.Top.OnFilesArms
import Johnson.Top.GameOGen

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What only the theorems need. -/
structure BesideArmsD (r : InputArms) where
  /-- what the public reading gives -/
  D : Type
  /-- the public reading, at a key -/
  rd : KeyRoot 256 r.L → Rom.OComp (rom 256) D
  /-- the reading's budget of queries -/
  q₀ : ℕ
  /-- the word under a root, read at d off a log of strings -/
  wordOf : D → Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol
  Wn : Type
  Rno : r.I → r.X → Wn → Prop
  εK : ℕ → ℕ → ℝ≥0∞
  εE : ℕ → ℕ → ℝ≥0∞
  εP : ℕ → ℕ → ℝ≥0∞
  x₀ : r.X

variable {r : InputArms} (b : BesideArmsD r)

/-- The instance is true at the index: the relaxed relation has a witness. -/
def IsTrueArmsD (i : r.I) (x : r.X) : Prop := ∃ w, b.Rno i x w

/-- What the key file's arm promises, at d. -/
def KeyHoldsD (d : b.D) (k : KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (_ : r.X)
    (_ : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (_ : Rom.Trace (rom 256)) : Prop :=
  r.L.hasCollisionAt (b.wordOf d trC k.cm) k.rcd.1 ∨ r.L.decodeIndex (b.wordOf d trC k.cm) k.rcd ≠ none

/-- What the entry file's arm promises, at d. -/
def EntryHoldsD (d : b.D) (k : KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (_ : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256)) : Prop :=
  ¬ r.L.hasCollisionAt (b.wordOf d trC k.cm) k.rcd.1 ∧
    ¬ r.L.hasCollisionAt (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1.1 ∧
    (r.L.decodeIndex (b.wordOf d trC k.cm) k.rcd = none ∨
      r.L.decodeIndex (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1 =
        r.L.decodeIndex (b.wordOf d trC k.cm) k.rcd)

/-- What the proof file's arm promises, at d. -/
def ProofHoldsD (d : b.D) (_ : KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (x : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256)) : Prop :=
  r.L.hasCollisionAt (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1.1 ∨
    r.L.decodeIndex (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1 = none ∨
    ∃ i, r.L.decodeIndex (b.wordOf d (trC ++ trP) π.link.1) π.link.2.1 = some i ∧ IsTrueArmsD b i x

/-- The extractor of the scheme whose verifier holds the key itself: run the reading, then decode,
at the key's record, the word under the key's root, read at d off the committer's log. -/
def extArmsD : ZKCP.Gen.ExtractorO (rom 256) r.I r.X Unit (KeyRoot 256 r.L)
    (OfflineLinkOnlineProof 256 r.L r.aT r.aL) :=
  ZKCP.Gen.extD b.rd (fun d k trC => r.L.decodeIndex (b.wordOf d trC k.cm) k.rcd) fun _ _ _ _ _ => ()

/-- The named hypotheses but for the commitment and the meaning. -/
structure CoreArmsD : Prop where
  keyArm   : ZKCP.Gen.ArmBoundD b.rd (liftK r) (KeyHoldsD b) b.εK
  entryArm : ZKCP.Gen.ArmBoundD b.rd (liftE r) (EntryHoldsD b) b.εE
  proofArm : ZKCP.Gen.ArmBoundD b.rd (liftP r) (ProofHoldsD b) b.εP
  reading  : ∀ k, (b.rd k).NoCoin ∧ (b.rd k).QueryBound b.q₀
  noCoin   : HoleArms.noCoin (r := r)

/-- The commitment: index binding of the scheme whose verifier holds the key itself, with `extArmsD
b`, gives index binding behind the hash function's answer at the key's code, with `extO`. -/
def HoleArmsD.commitmentOO
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      (KeyRoot 256 r.L × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞) : Prop :=
  Rec.CommitmentBindsOO (schemeArms r) (extArmsD b) b.q₀ r.enc extO q (IsTrueArmsD b)
    (fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP)) εO

/-- The meaning, for a claim. -/
def HoleArmsD.soundFor (claim : r.I → List Token → List Token → Prop) : Prop :=
  ∀ i (x' : List Token × List Token) a x, r.build x' a = some x → IsTrueArmsD b i x →
    claim i x'.1 x'.2

variable {b}

/-- Index binding of the scheme whose verifier holds the key itself, with the extractor that runs
the public reading, at the sum of the three arms' errors. -/
theorem CoreArmsD.binds (h : CoreArmsD b) :
    ZKCP.Gen.HasIndexBindingWithO
      (ZKCP.Special.toPair (ZKCP.languageRelation (IsTrueArmsD b))) (schemeArms r) (extArmsD b) b.q₀
      fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP) := by
  refine ZKCP.Gen.binds_of_armsD (vK := liftK r) (vE := liftE r) (vP := liftP r) rfl
    (fun k => (h.reading k).1) (fun k => (h.reading k).2) h.keyArm h.entryArm h.proofArm
    fun d k trC x π trP hK hL hP => ?_
  obtain ⟨n0, n1, hl⟩ := hL
  have d0 : r.L.decodeIndex (b.wordOf d trC k.cm) k.rcd ≠ none := hK.resolve_left n0
  have e := hl.resolve_left d0
  obtain ⟨i, hi, ht⟩ := (hP.resolve_left n1).resolve_left fun hn => d0 (e.symm.trans hn)
  have hi' : r.L.decodeIndex (b.wordOf d trC k.cm) k.rcd = some i := e.symm.trans hi
  rw [hi']
  exact ⟨⟨(), ht⟩, ht⟩

/-- Under the 5 named hypotheses `CoreArmsD b`, `HoleArmsD.commitmentOO b extO q εO`,
`HoleArmsD.soundFor b claim` and εO tC tP ≤ ε (tC + tP) (hypotheses of the theorem: Lean's list of
axioms does not show them): for every committer and every prover whose bounds on queries to the hash
function add up to t, the probability that `verifyArms r` accepts while the extractor gives no
index, or an index at which the claim fails, is at most ε t. -/
theorem verify_sound_arms_D (claim : r.I → List Token → List Token → Prop)
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      (KeyRoot 256 r.L × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (h : CoreArmsD b) (hc : HoleArmsD.commitmentOO b extO q εO)
    (hs : HoleArmsD.soundFor b claim) (hε : ∀ tC tP, εO tC tP ≤ ε (tC + tP)) :
    SoundForWithO (systemArms r) (fun c l => deterministicOf (extO.Ei c l)) q claim ε :=
  Rec.soundForWithO_systemE_O (schemeArms r) (extArmsD b) b.q₀ r.enc extO q r.bound r.π₀
    r.nextToken h.binds (noCoin_schemeArms h.noCoin) hc claim b.x₀ hs hε

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.CoreArmsD.binds
#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms_D
