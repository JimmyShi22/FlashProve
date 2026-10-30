-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/PrepCore.lean: Prep · famPrep · famPrep_hint (told in Johnson/PV/MvPrep.lean's head) AND
  famPrepQ · shoutAt · shoutAt_eq (told in Johnson/PV/MvPrepQ.lean's head),
  OVER FamCutL | FamCutQ ALONE: so that a native library can take in all that answers
  a query.


-/
import Johnson.PV.FamCutQ

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.Maker OnBytes.Maker.Page Johnson.RunOne
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What of the fast family does not hang on the query. -/
structure Prep {I X : Type} (L : BatchProtocolWithLeafBody I X) (K : ℕ) where
  P : PageJ L K
  ΦK : FitJ L .test
  ΦP : FitJ L .onl
  R : RunJ P

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **The family at a prepared value.** -/
def famPrep (pr : Prep L K) (e : Unit → List Bool) (O : ByteArray → ByteArray) (mK mP : ℕ → ℕ) : Fam
    (typedOracleFamily 256 K L) :=
  famCutL pr.P pr.ΦK pr.ΦP pr.R e O mK mP

/-- **A hint is for speed and memory alone**: at any two pairs of hints the family is one. -/
theorem famPrep_hint (pr : Prep L K) (e : Unit → List Bool) (O : ByteArray → ByteArray) (mK mP mK'
    mP' : ℕ → ℕ) :
    famPrep pr e O mK mP = famPrep pr e O mK' mP' := by
  unfold famPrep
  rw [famCutL_eq, famCutL_eq]

/-- **The family at a prepared value and any bk.** -/
def famPrepQ (pr : Prep L K) (bk : AllPts 256 K L → List Bool) (O : ByteArray → ByteArray) (mK mP :
    ℕ → ℕ) :
    Fam (typedOracleFamily 256 K L) :=
  famCutQ pr.P pr.ΦK pr.ΦP pr.R bk O mK mP

/-- bk, with a line on the error stream whenever it is called. -/
def shoutAt (bk : AllPts 256 K L → List Bool) (p : AllPts 256 K L) : List Bool :=
  dbgTrace "  BK IS READ: a string behind the escape is hashed" fun _ => bk p

/-- A trace is no part of a value. -/
theorem shoutAt_eq (bk : AllPts 256 K L → List Bool) : shoutAt bk = bk := rfl

end W4M

#print axioms W4M.famPrep_hint
