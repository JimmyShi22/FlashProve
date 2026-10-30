-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontPaid.lean: the named hypotheses of Johnson/Top/FrontParts.lean on the three checks,
parted by file, so that what is proved for one file's check at a concrete input (defined in this
library, not a parameter) can be substituted and what is left can be read off by name.

What this file states. `EntryPaid b`: three: the entry file's check's bound over a drawn function
(`entryArm` of `CoreArmsCD`, Johnson/Top/OnFilesArmsCD.lean), the entry file's check's share of "no
check tosses a coin", and that the public reading tosses no coin and keeps its budget (`reading`).
The reading (a computation that queries the hash function) is not the entry file's own: it serves
all three checks' bounds. It appears here because it is proved where b is concrete. `ArmsLeft b`:
the four that are left of `CoreArmsCD b`: the key file's and the proof file's checks' bounds, and
that neither tosses a coin.
`coreArmsCD_of`: the two give `CoreArmsCD b`; `CoreArmsCD.entryPaid`, `CoreArmsCD.armsLeft`: back.
`FrontFieldsLeft p b claim extO q εO ε`: `FrontFields` without `EntryPaid`: `parts`, `arms` (the
four), `commitment`, `meaning`, `error`. `front_sound_left`: `front_sound` from `EntryPaid b` and
`FrontFieldsLeft …`.

Under which hypotheses. `EntryPaid b` and `FrontFieldsLeft …` are themselves the hypotheses of
`front_sound_left`; this file proves neither.

What it does not show. All that the head of FrontParts.lean does not claim. Pure logic: the same
hypotheses in another order; none is made weaker or stronger, and none is proved. All is for
arbitrary parameters; no input is given here. Where `EntryPaid b` is proved (`entryPaid_toldFull`,
`entryPaid_toldSmall`, Johnson/Top/Pub/FrontTold.lean [not in this library]), the entry file's
check's bound rests on the statement on codes (`Cb.BCHKS46At`), which this library proves in
Cb/Bridge (`bchks46At`) from files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15) (lean/ThirdParty/). For proofs only; the program does not import
this file.


-/
import Johnson.Top.FrontParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC} (p : PortArmsC r) (b : BesideArmsCD r)

/-- The entry file's check's bound over a drawn function; that the public reading, which serves all
three checks, tosses no coin and keeps its budget; the entry file's check tosses no coin. -/
structure EntryPaid : Prop where
  entryArm : ZKCP.Gen.ArmBoundD b.rd (liftEC r) (EntryHoldsCD b) b.εE
  reading : ∀ k, (b.rd k).NoCoin ∧ (b.rd k).QueryBound b.q₀
  noCoinE : ∀ c cm cm' rc rc' p, (r.armE c cm cm' rc rc' p).NoCoin

/-- What is left of `CoreArmsCD b` beside `EntryPaid b`. -/
structure ArmsLeft : Prop where
  /-- the key file's check's bound -/
  keyArm : ZKCP.Gen.ArmBoundD b.rd (liftKC r) (KeyHoldsCD b) b.εK
  /-- the proof file's check's bound -/
  proofArm : ZKCP.Gen.ArmBoundD b.rd (liftPC r) (ProofHoldsCD b) b.εP
  /-- the key file's check tosses no coin -/
  noCoinK : ∀ c cm rc p, (r.armK c cm rc p).NoCoin
  /-- the proof file's check tosses no coin -/
  noCoinP : ∀ c cm x rc n p, (r.armP c cm x rc n p).NoCoin

variable {b}

/-- The two are `CoreArmsCD b`. -/
theorem coreArmsCD_of (e : EntryPaid b) (a : ArmsLeft b) : CoreArmsCD b :=
  ⟨a.keyArm, e.entryArm, a.proofArm, e.reading, a.noCoinK, e.noCoinE, a.noCoinP⟩

theorem CoreArmsCD.entryPaid (h : CoreArmsCD b) : EntryPaid b :=
  ⟨h.entryArm, h.reading, h.noCoin.2.1⟩

theorem CoreArmsCD.armsLeft (h : CoreArmsCD b) : ArmsLeft b :=
  ⟨h.keyArm, h.proofArm, h.noCoin.1, h.noCoin.2.2⟩

variable (b)

/-- All named hypotheses of `front_sound` beside `EntryPaid b`. -/
structure FrontFieldsLeft (claim : r.I → List Token → List Token → Prop)
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞)
    (ε : ℕ → ℝ≥0∞) : Prop where
  /-- the four parts, the request, the parser's budget, the bound on the exception's probability -/
  parts : FrontParts p
  /-- the key file's and the proof file's checks -/
  arms : ArmsLeft b
  /-- the commitment -/
  commitment : HoleArmsCD.commitmentOO b extO q εO
  /-- the meaning -/
  meaning : HoleArmsCD.soundFor b claim
  /-- the error's name -/
  error : ∀ tC tP, εO tC tP ≤ ε (tC + tP)

variable {p b}

/-- `front_sound` from `EntryPaid b` and `FrontFieldsLeft …`. -/
theorem front_sound_left {claim : r.I → List Token → List Token → Prop}
    {extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)} {q : ℕ} {εO : ℕ → ℕ → ℝ≥0∞}
    {ε : ℕ → ℝ≥0∞} (e : EntryPaid b) (h : FrontFieldsLeft p b claim extO q εO ε) :
    SoundForWithO (systemPortC p) (fun c l => deterministicOf (extO.Ei c l)) q claim
      fun t => ε (t + p.n) + p.δ t :=
  front_sound ⟨h.parts, coreArmsCD_of e h.arms, h.commitment, h.meaning, h.error⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.coreArmsCD_of
#print axioms VerifiableInference.OnPublicFiles.front_sound_left
