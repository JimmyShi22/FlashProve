-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmPlain.lean: values for three more letters of the statements on the entry's arm: the
plain part that stands in the seeds' two queries, the test "is it that plain part?", and the test
"is it the plain part of the link's first query?"; each test with its law.

The coding of typed queries as strings (OnBytes/TypedOracleCompiler/Run/ArmDirect.lean,
OnBytes/TypedOracleCompiler/Slice/ArmRead.lean) takes two plain parts p0, p1 under the tag of Test, tests isP0, isP1
that tell them, and a test isPL that tells the plain part of the link's first query. Here they are
written.

The tests are REAL DECISIONS, not choices by classical logic: `isAt S a x` compares the two strings
of bits that a serialiser S writes for x and for a. A serialiser writes no two elements alike
(`Iop.Ser.put_injective`), so the test tells a (`isAt_iff`). Under the tag of Test the serialiser is
that of Johnson/Flat/SerArmAt.lean (`pTFilesFull` | `pTFilesSmall`); for the link it is the entry's
own, carried along the correspondence pbF of plain parts (as in OnBytes/TypedOracleCompiler/Run/ArmBack.lean).

Main definitions.
 `isAt`           the test, from a serialiser.
 `p0Full`, `isP0Full` (Small likewise)   the plain part (`SeedVals.plainFirst` at the key file's
                  first round), meant for p0 and for p1 alike, and its test.
 `serLink`, `isPLAt`   the link's serialiser along pbF; the test at the first query's plain part.
Main theorems: `isAt_iff`, `hp0Full`, `hp0Small`, `hpLAt`.

Not claimed here: soundness or hiding. That no round of the key file sends `p0Full`: its first round
can send it: an accepted key file does so exactly where the record's answers are those of the sample
record `G.rec₀` (see OnBytes/TypedOracleCompiler/Run/SeedVals.lean, "Limits"). So the plain part of the seeds' two
typed queries hangs on `G.rec₀`: a constant once G is fixed. That a term here
can be evaluated at the sizes in use. The correspondence pbF stays a parameter. For proofs only; no
program imports this file.


-/
import Johnson.Flat.SerArmAt
import Johnson.Flat.ArmData
import OnBytes.TypedOracleCompiler.Run.SeedVals
import OnBytes.TypedOracleCompiler.Slice.EntryFill
import OnBytes.TypedOracleCompiler.Run.EntryFb

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat

open Hiop Cb Cb.Ood OnBytes.Slice OnBytes.Maker TypedOracleCompiler.Iop
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms _root_.Compile
open TypedOracleCompiler.Run TypedOracleCompiler.Slice TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.PageEBack TypedOracleCompiler.Run.SeedVals
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.RunA (RestR LrG)

/-! ## The test, from a serialiser -/

/-- Is x the element a? By the strings of bits that the serialiser writes. -/
def isAt {α : Type} (S : Ser α) (a x : α) : Bool := decide (S.put x = S.put a)

/-- It tells a. -/
theorem isAt_iff {α : Type} (S : Ser α) (a x : α) : isAt S a x = true ↔ x = a := by
  unfold isAt
  rw [decide_eq_true_iff]
  exact ⟨fun h => S.put_injective h, fun h => by rw [h]⟩

/-! ## The link's first query -/

section
variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))

/-- The serialiser of the link's plain parts over L2: the entry's own, along pbF. -/
def serLink : Ser (PlainPart (shapeOf L2 .link) (annOf L2 .link)) :=
  Ser.ofEquiv pbF
    (pbE (Bd := List Bool) D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) .link)

/-- Is a plain part of the link that of the first query? -/
def isPLAt : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool :=
  isAt (serLink D d₁ L2 pbF)
    (pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))

/-- It tells that one. -/
theorem hpLAt (p : PlainPart (shapeOf L2 .link) (annOf L2 .link)) :
    isPLAt D d₁ L2 pbF p = true ↔
      p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)) :=
  isAt_iff _ _ p

end

/-! ## The full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (G : FilesParameters X RecFull) (P : (threeProtocolsFromDryRunAtFullSize A R G).Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))
  (aL : RoundSplits (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)).link.shape)

/-- The plain part that stands in the seeds' two queries: the slot's component of the fixed message
of the key file's first round. -/
def p0Full :
    PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .test) :=
  plainFirst _ _ _ _

/-- Is a plain part under the tag of Test that one? By the strings that the serialiser writes. -/
def isP0Full :
    PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .test) → Bool :=
  isAt (pTFilesFull A R G P hL aL) (p0Full A R G P hL aL)

/-- It tells that one. -/
theorem hp0Full
    (p : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .test)) :
    isP0Full A R G P hL aL p = true ↔ p = p0Full A R G P hL aL :=
  isAt_iff _ _ p

end

/-! ## The small size -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (G : FilesParameters X RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A R G).Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))
  (aL : RoundSplits (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)).link.shape)

/-- The plain part that stands in the seeds' two queries: the slot's component of the fixed message
of the key file's first round. -/
def p0Small :
    PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .test) :=
  plainFirst _ _ _ _

/-- Is a plain part under the tag of Test that one? By the strings that the serialiser writes. -/
def isP0Small :
    PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .test) → Bool :=
  isAt (pTFilesSmall A R G P hL aL) (p0Small A R G P hL aL)

/-- It tells that one. -/
theorem hp0Small
    (p : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .test)) :
    isP0Small A R G P hL aL p = true ↔ p = p0Small A R G P hL aL :=
  isAt_iff _ _ p

end

end OnBytes.Flat
