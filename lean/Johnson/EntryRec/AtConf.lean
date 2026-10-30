-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/AtConf.lean: the configuration of a stored table with a record
(`OnBytes.Slice.DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean) is a configuration with words of length 2 ^ a
over `SgX` in the sense of OnBytes/Maker/ConfLetters.lean's `ConfLetters.conf`, by unfolding. So
Johnson/EntryRec/AtFiles.lean's `filesOf` and `obj_objF` stand at it.

  `lettersAt A R`: the configuration's fields but for the word length and the alphabet.
  `conf_lettersAt`: `(lettersAt A R).conf = DecR.configurationOfStoredTable A R`, by unfolding.
  `filesAt`: three files' protocols as a value of `Files (DecR.configurationOfStoredTable A R)`: the key file's and the
    proof file's made by the makers, the entry file's a letter.

Limits: those of Johnson/EntryRec/OkcFiles.lean's head. The decoder's data D, the claims A and the
rest R are letters.


-/
import Johnson.EntryRec.AtFiles
import OnBytes.Slice.ConfOf

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ Iop Hiop OnBytes.Maker OnBytes.Flat OnBytes.Slice
open TypedOracleCompiler.Compile.Batch.Cms (Bodies)

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

variable {D : DecR} {X : Type} (A : D.Claims X) (R : D.RelationsAndEncoding A)

/-- The configuration's fields but for the word length and the alphabet. -/
noncomputable def lettersAt : ConfLetters D.T.a where
  I := (DecR.configurationOfStoredTable A R).I
  X := (DecR.configurationOfStoredTable A R).X
  Cells := (DecR.configurationOfStoredTable A R).Cells
  Ryes := (DecR.configurationOfStoredTable A R).Ryes
  Rno := (DecR.configurationOfStoredTable A R).Rno
  Msg := (DecR.configurationOfStoredTable A R).Msg
  Rnd := (DecR.configurationOfStoredTable A R).Rnd
  finRnd := (DecR.configurationOfStoredTable A R).finRnd
  neRnd := (DecR.configurationOfStoredTable A R).neRnd
  enc := (DecR.configurationOfStoredTable A R).enc
  Pad := (DecR.configurationOfStoredTable A R).Pad
  finPad := (DecR.configurationOfStoredTable A R).finPad
  nePad := (DecR.configurationOfStoredTable A R).nePad
  hold := (DecR.configurationOfStoredTable A R).hold
  held := (DecR.configurationOfStoredTable A R).held
  Seed := (DecR.configurationOfStoredTable A R).Seed
  finSeed := (DecR.configurationOfStoredTable A R).finSeed
  neSeed := (DecR.configurationOfStoredTable A R).neSeed
  Ans := (DecR.configurationOfStoredTable A R).Ans
  smp := (DecR.configurationOfStoredTable A R).smp
  coll := (DecR.configurationOfStoredTable A R).coll
  dcd := (DecR.configurationOfStoredTable A R).dcd
  trace := (DecR.configurationOfStoredTable A R).trace
  cells0 := (DecR.configurationOfStoredTable A R).cells0

/-- **The configuration of a stored table with a record is of that form**, by unfolding. -/
theorem conf_lettersAt : (lettersAt A R).conf = DecR.configurationOfStoredTable A R := rfl

variable (f : _root_.Fmt.Fld) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : (DecR.configurationOfStoredTable A R).Rec → TFk → TJk → T3k → Bool)
  (runK : (DecR.configurationOfStoredTable A R).Rec → View → View → View → Bool)
  (silP : X × (DecR.configurationOfStoredTable A R).Rec → TFp → TJp → T3p → Bool)
  (runP : X × (DecR.configurationOfStoredTable A R).Rec → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (DecR.configurationOfStoredTable A R).Rec D.T.a) (N : ℕ) (early : X → X) (late : Option ℕ)

/-- **Three files' protocols over that configuration**: the key file's and the proof file's made by
the makers; the entry file's a letter. -/
noncomputable def filesAt : Files (DecR.configurationOfStoredTable A R) :=
  filesOf (lettersAt A R) f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early late

end OnBytes.RunA
