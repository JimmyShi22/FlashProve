-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/Known.lean: TESTS THAT RUN THE VERY TERM OF THE COMMIT FIELD, Letters.commitAt
(Johnson/Bind/Cpp/Defs.lean), at theTwin g, at a toy shape. Tests alone: each is a #guard, which
Lean's evaluator runs when the file is compiled; a #guard leaves no theorem.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.

Why. The commit field of theCpp (theTwin g) prove is Letters.commitAt at the full size's shape,
where it can never be run. The tests of Johnson/Bind/TwinKnown.lean run Bind.Twin.commit: the same
text (commitW) at the identity monad and the format's own hash. Here the algorithm itself is
evaluated, at the hash function on bit strings that the format's realised oracle gives (Run.oBitsAt
Fmt.oracle), at TwinKnown's first small shape, files and table.

What is tried.
  1. At coins: the ID is TwinKnown's known ID at that shape. Controls: one entry bent; another hash
    function; each must part.
  2. At a seed, with a toy generator: at the seed at which it gives the toy table's coins, the same
    known ID; at another seed, the ID at the coins that the generator gives at the two answers c and
    I, computed apart. Controls: that ID is not the known one; with c in I's place it parts.
Limits. One toy shape (4, 8, 3, 1, 1, 40): 16 leaves, 2 rows. The known ID is TwinKnown.lean's: by
that file's head the answer of a short Python program, written from the same description of the
programs as the Lean text: it is not the programs' value. The toy generator is no program's. entryOf
(the weights' digits) is not run here. Nothing at the full size.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.Defs
import Johnson.Bind.TwinKnown
import Run.OracleBitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Cpp.Known
open VerifiableInference
open Bind.Twin (Shape)
open Bind.Twin.Known (toy shapeA bent)

/-- TwinKnown's three short public files. -/
def zToy : VerifierAndGoals.PublicFiles := ⟨Fmt.ascii "toy\n", Fmt.ascii "lay\n", ⟨#[0, 1, 2, 3, 4, 5, 6, 7]⟩⟩

/-- The hash function on bit strings that the format's realised oracle gives. -/
def plug : Hash := _root_.Run.oBitsAt Fmt.oracle ()

/-- Another hash function: one byte is laid behind every string. -/
def plugOther : Hash := _root_.Run.oBitsAt (fun s => Fmt.oracle (s ++ ⟨#[0]⟩)) ()

/-- The toy table's coins. -/
def coinsToy : Coins := ⟨toy.tail, toy.pad, toy.salt⟩

/-- A toy generator: at the seed 7 the toy table's coins; elsewhere the same with salts made of the
two answers. -/
def gToy : Shape → Seed → Digest → Digest → Coins := fun _ seed c I =>
  if seed.val == 7 then coinsToy
  else { coinsToy with salt := fun _ => _root_.Run.digToBytes I ++ _root_.Run.digToBytes c }

/-- The very term's value, as hexadecimal digits. -/
def idHex (hash : Hash) (entry : ℕ → ℕ → UInt64) (ρ : Rand) : String :=
  Fmt.hex (_root_.Run.digToBytes (((theTwin gToy).commitAt shapeA zToy entry ρ).evaluate hash))

/-- TwinKnown's known ID at the first small shape. -/
def knownA : String := "b8d7312c1b374bcc0e6dfdda3391a8e998b63da37555f7da57975f452642fc59"

/-- The two answers that the committer asks for at a seed. -/
def cToy : Digest := plug (VerifierAndGoals.configString zToy)
def iToy : Digest := plug (VerifierAndGoals.Fit.anchorString cToy (words shapeA))

-- 1. at coins
#guard idHex plug toy.entry (.inr coinsToy) == knownA
#guard idHex plug (bent toy.entry 1 2) (.inr coinsToy) != knownA
#guard idHex plugOther toy.entry (.inr coinsToy) != knownA
-- 2. at a seed
#guard idHex plug toy.entry (.inl 7) == knownA
#guard idHex plug toy.entry (.inl 8) == idHex plug toy.entry (.inr (gToy shapeA 8 cToy iToy))
#guard idHex plug toy.entry (.inl 8) != knownA
#guard idHex plug toy.entry (.inl 8) != idHex plug toy.entry (.inr (gToy shapeA 8 cToy cToy))

end Bind.Cpp.Known
