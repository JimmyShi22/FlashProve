-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/AsmRuns.lean: what the assembled lookup's verifier puts out is ONE plain function of
the flat transcript, if each stretch's output is.

A typed transcript is read flat: round by round the scalars sent and the elements drawn
(Cb/Pv/KeyLookup/Flat.lean: `Flat.RV`, `Flat.Runs`). `Flat.Runs b fm run` says of a block b: its
verifier rejects nothing, and for all transcripts its output is `run` of the flat view; typed
transcripts and flat lists that fit the formats fm are one-to-one.

It imports Cb/Pv/KeyLookup/Asm.lean and Cb/Pv/KeyLookup/Flat.lean; no file of the port.

  `RunD A`        for each of the eight stretches: the formats of its rounds and a plain function
                  from (state, flat rounds) to the next state.
  `D.fm`          all formats in a row, bracketed as the chain is.
  `D.run`         THE ONE FUNCTION: each stretch's function on its own rounds, one behind the other;
                  then the read-out.
  `B.Runs D`      what is asked of the letters: each block `Flat.Runs` with its formats and its
                  function.
  `lam1_runs`     B.Runs D gives `Flat.Runs B.lam1 D.fm D.run`: for all st y τ: B.lam1.R.out st y τ
                  = some (D.run st (view τ)).
Not claimed: that blocks with `Runs` exist (files of their own); anything on an honest side.

-/
import Cb.Pv.KeyLookup.Asm
import Cb.Pv.KeyLookup.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn Flat

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]

/-- The eight stretches' formats and plain functions. -/
structure RunD (A : Dat E) where
  fHead  : List Fm
  fParts : List Fm
  fJoin  : List Fm
  fKeys  : List Fm
  fTable : List Fm
  fClo   : List Fm
  fZero  : List Fm
  fBits  : List Fm
  rHead  : A.St → List (RV E) → A.XS
  rParts : A.XS → List (RV E) → A.XS
  rJoin  : A.XS → List (RV E) → A.XS
  rKeys  : A.XS → List (RV E) → A.XS
  rTable : A.XS → List (RV E) → A.XS
  rClo   : A.XS → List (RV E) → A.XS
  rZero  : A.XS → List (RV E) → A.XS
  rBits  : A.XS → List (RV E) → A.XS

namespace RunD
variable {A : Dat E} (D : RunD A)

/-- the formats up to each joint -/
def f2 : List Fm := D.fHead ++ D.fParts
def f3 : List Fm := D.f2 ++ D.fJoin
def f4 : List Fm := D.f3 ++ D.fKeys
def f5 : List Fm := D.f4 ++ D.fTable
def f6 : List Fm := D.f5 ++ D.fClo
def f7 : List Fm := D.f6 ++ D.fZero

/-- All formats in a row. -/
def fm : List Fm := D.f7 ++ D.fBits

/-- The chain before the read-out, as one function. -/
def chn : A.St → List (RV E) → A.XS :=
  seqRun D.f7.length (seqRun D.f6.length (seqRun D.f5.length (seqRun D.f4.length (seqRun D.f3.length
    (seqRun D.f2.length (seqRun D.fHead.length D.rHead D.rParts) D.rJoin) D.rKeys) D.rTable) D.rClo)
    D.rZero) D.rBits

/-- THE ONE FUNCTION. -/
def run : A.St → List (RV E) → A.Out := fun st f => A.rd (D.chn st f)

end RunD

namespace Bks
variable {A : Dat E} {Ex : ExtSpec} (B : Bks A Ex)

/-- What is asked of the letters. -/
structure Runs (D : RunD A) where
  head  : Flat.Runs B.head D.fHead D.rHead
  parts : Flat.Runs B.parts D.fParts D.rParts
  join  : Flat.Runs B.join D.fJoin D.rJoin
  keys  : Flat.Runs B.keys D.fKeys D.rKeys
  table : Flat.Runs B.table D.fTable D.rTable
  clo   : Flat.Runs B.clo D.fClo D.rClo
  zero  : Flat.Runs B.zero D.fZero D.rZero
  bits  : Flat.Runs B.bits D.fBits D.rBits

/-- The lookup's output is the one function of the flat view. -/
noncomputable def lam1_runs (D : RunD A) (h : B.Runs D) : Flat.Runs B.lam1 D.fm D.run :=
  (((((((h.head.seq h.parts).seq h.join).seq h.keys).seq h.table).seq h.clo).seq h.zero).seq
    h.bits).postM A.rd

end Bks
end Lk6
