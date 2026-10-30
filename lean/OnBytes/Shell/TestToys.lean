-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/TestToys.lean: a second opinion on the program's verdicts on two small test protocols.

Fmt/ has a description and a decision of its own for the product test and for the chain of links,
independent of the checks of OnBytes/Toy/. Here both are applied to the same files, at the tiny
size: the honest proof and three altered copies, the first four rows of a table in Fmt/ that records
each file's expected result. The two verdicts must agree with each other and with that result.
Three of the false proofs that every verifier must refuse are put to the program as well. The tests
of OnBytes/Toy/ try the whole table; here that would take too long. The tests try examples and prove
nothing about other inputs. The program does not import this file.
-/
import OnBytes.Shell.Toys
import Fmt.M1Prog
import Fmt.M1ProgPTFiles
import Fmt.M2All
import Fmt.M2ParOf
import Fmt.M2ProgLTFiles

namespace OnBytes.ShellTest

open OnBytes.Shell

/-- True if Fmt/'s own reader and decision accept a proof file of the product test. -/
def productSecond (params file : ByteArray) : Bool :=
  match Fmt.M1.whoFromF params file with
  | some .accepted => true
  | _ => false

/-- True if Fmt/'s own reader and decision accept a proof file of the chain of links. -/
def linksSecond (params file : ByteArray) : Bool :=
  match Fmt.M2.specFrom params with
  | none => false
  | some (P, S) =>
    match Fmt.wholeChainF S file with
    | none => false
    | some o => Fmt.M2.dec P (Fmt.viewOf S.firstTree o)

/-- True if the verdict is a yes. -/
def isYes : Verdict → Bool
  | .accepted => true
  | .refused _ => false

/-- The public file of the tiny product test. Its target is 10 bits. -/
def productPublic : ByteArray := Fmt.M1.ProgPT.pubs.headD ByteArray.empty

/-- The public file of the tiny chain of links. Its target is 10 bits. -/
def linksPublic : ByteArray := Fmt.M2.ProgLT.pubs.headD ByteArray.empty

-- the product test
#guard (Fmt.M1.ProgPT.table.take 4).all fun x =>
  isYes (product 10 productPublic x.2.1) == productSecond Fmt.M1.ProgPT.params x.2.1 &&
    isYes (product 10 productPublic x.2.1) == (x.2.2 == 0)
#guard (Fmt.M1.ProgPT.mustBeRefused.take 3).all fun x => !isYes (product 10 productPublic x.2.1)
-- at 128 bits, which the program asks if the caller names none, the tiny size is refused
#guard !isYes (product 128 productPublic Fmt.M1.ProgPT.proof)

-- the chain of links
#guard (Fmt.M2.ProgLT.table.take 4).all fun x =>
  isYes (links 10 linksPublic x.2.1) == linksSecond Fmt.M2.ProgLT.params x.2.1 &&
    isYes (links 10 linksPublic x.2.1) == (x.2.2 == 0)
#guard (Fmt.M2.ProgLT.mustBeRefused.take 3).all fun x => !isYes (links 10 linksPublic x.2.1)
#guard !isYes (links 128 linksPublic Fmt.M2.ProgLT.proof)

end OnBytes.ShellTest
