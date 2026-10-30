-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/FirstBlock.lean: the letters for saying that the compiled prover reads the answer of
a try that fails through its first block alone. DEFINITIONS ALONE: nothing is stated here. The
statements: Johnson/Prover/Law/FirstBlockLaws.lean, CountF.lean, PassAt.lean. The prover's text
is in OnBytes/Prover/Defs.lean.

Main names.
  `Pass`       a letter: of a Fiat-Shamir query and its answer's first block: is the test of work
               passed (yes also where the query's round has no test).
  `agP pass`   the relation on typed answers: equal; or, at a Fiat-Shamir query, the same first
               block at which the test is not passed.
  `moreP pass` the test of Rom/OverOneF.lean: `pass` at a Fiat-Shamir query, yes at all others.
  `costP pass` what a typed answer costs in hash calls: K + 1 or 1 at a Fiat-Shamir query; nothing
               at `ann`; 1 at all others.
  `TestsAt pass t i s A W embP`   the wire's tests ARE `pass`, AT THE QUERIES THAT THE CHAIN ASKS:
               in round number i + j the record of the test that the chain uses (the slot's in a
               local round, the shared one's in a shared round) says ok at a verifier's message made
               of the blocks u just where `pass` says yes at u 0, at every query with that number
               and a plain part of that round's component; where the record is missing, `pass` says
               yes there. Of other queries with that number nothing is asked.
  `AskedWhole pass`   of a query: no Fiat-Shamir query, or `pass` says yes at every first block.
  `FirstIs m`  the encoding's first hash block of a Fiat-Shamir answer is the answer's block 0.

Limits. `pass` is a letter: nothing says here that a wire has such a function. 0 < K is a letter's
premise hK: an answer has a block 0 beside the chaining value.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Defs
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import Rom.OverOneF

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The names of oracles under OnBytes/TypedOracleCompiler/. (The library's type OracleName is in sight too.) -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-- Of a Fiat-Shamir query and its answer's first block: is the test of work passed. -/
abbrev Pass (lam : ℕ) (L : BatchProtocolWithLeafBody I X) : Type := (t : Tag) → FbIn lam L t → Dig lam → Bool

/-- The relation on typed answers: equal; or, at a Fiat-Shamir query, the same first block at which
the test is not passed. -/
def agP (hK : 0 < K) (pass : Pass lam L) : (o : ON₂) → domOf lam L o → rngOf lam K o →
    rngOf lam K o → Prop
  | .fb t, q, r, r' => r = r' ∨ (pass t q (r.1 ⟨0, hK⟩) = false ∧ r.1 ⟨0, hK⟩ = r'.1 ⟨0, hK⟩)
  | _, _, r, r' => r = r'

/-- The test of Rom/OverOneF.lean. -/
def moreP (pass : Pass lam L) : More (typedOracleFamily lam K L) lam
  | .fb t, q, b => pass t q b
  | _, _, _ => true

/-- What a typed answer costs in hash calls. -/
def costP (hK : 0 < K) (pass : Pass lam L) : (o : ON₂) → domOf lam L o → rngOf lam K o → ℕ
  | .fb t, q, r => if pass t q (r.1 ⟨0, hK⟩) = true then K + 1 else 1
  | .fbw _ _, _, _ => K + 1
  | .ann, _, _ => 0
  | _, _, _ => 1

/-- A query that is asked whole, whatever its answer's first block is. -/
def AskedWhole (pass : Pass lam L) : (o : ON₂) → domOf lam L o → Prop
  | .fb t, q => ∀ b, pass t q b = true
  | _, _ => True

/-- One record of a test against `pass`, at the queries that the chain asks in round number i: any
head, any roots, a plain part of that round's component (plOf). -/
def TestIs {C P : Type} (hK : 0 < K) (pass : Pass lam L) (t : Tag) (i : ℕ)
    (chal : (Fin K → Dig lam) → C) (plOf : P → PlainPart (shapeOf L t) (annOf L t)) :
    Option (GrW C P) → Prop
  | none => ∀ h rt α b, pass t ⟨i, h, rt, plOf α⟩ b = true
  | some g => ∀ h rt α u, g.ok (chal u) = pass t ⟨i, h, rt, plOf α⟩ (u ⟨0, hK⟩)

/-- The wire's tests are `pass`. i: the number of the first of the rounds s. -/
def TestsAt (hK : 0 < K) (pass : Pass lam L) (t : Tag) :
    ℕ → (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
      (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → Prop
  | _, [], _, _, _ => True
  | i, _ :: s, (a, A), (w, W), embP =>
    (match a.kind with
      | .lo => TestIs hK pass t i w.chal (fun α => embP (.inl (.inr α))) w.grJ
      | .sh => TestIs hK pass t i w.chal (fun α => embP (.inl (.inl α))) w.gr0) ∧
      TestsAt hK pass t (i + 1) s A W fun z => embP (.inr z)

/-- The encoding's first hash block of a Fiat-Shamir answer is the answer's block 0; and the numbers
of blocks are the family's. -/
structure FirstIs (hK : 0 < K) (m : OracleCoding (typedOracleFamily lam K L) lam) : Prop where
  blocks : ∀ o, m.blocks o = blk K o
  first : ∀ (t : Tag) (r : rngOf lam K (.fb t)) (h : 0 < m.blocks (.fb t)),
    m.rng (.fb t) r ⟨0, h⟩ = r.1 ⟨0, hK⟩

end OnBytes.Prover
