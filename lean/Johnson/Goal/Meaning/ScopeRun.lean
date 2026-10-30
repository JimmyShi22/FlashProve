-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ScopeRun.lean: the three public facts under which the theorems "in scope" of
this folder stand hold together at real files: a run.

Why. These theorems stand under "Z is in the goals' scope" (VerifierAndGoals.InScope Z = true), "the goals'
reader returns" (VerifierAndGoals.readFiles Z = .ok pp) and "the verifier's publicOf returns" (publicOf Z.pol
Z.KL lay = .ok X). A theorem under premises that no files meet would say nothing. This file
evaluates the three at the stored full-size example's public files, at the same files with the other
named policy, and at files in scope made from the reference's by changing a few of their numbers.

What a run is. A line "#guard" is evaluated by Lean's evaluator when this file is compiled, and the
build fails if it is false. It is no theorem.

The last guard holds Hd.PublicCore, which is a theorem at all files in scope (Hd.core_of_scope),
against an evaluation at the stored files.
-/
import Johnson.Goal.Meaning.ScopeCore

set_option autoImplicit false

namespace Meaning.Run

open VerifierAndGoals
open OnBytes.Model.Verify (publicOf)

/-- The three facts, with the layout file handed to publicOf. -/
def allThree (Z : PublicFiles) : Bool :=
  InScope Z && (readFiles Z).toOption.isSome && (publicOf Z.pol Z.KL (some Z.lay)).toOption.isSome

/-- A scale file: for each of the 48 layers the thirteen numbers that record gives; then 24 times
the stored file's three numbers of a layer with experts. -/
def scaleFileBy (record : Nat → List Nat) : ByteArray :=
  OnBytes.Tie.Pv.Plan.wordsFile
    (((List.range 48).flatMap record) ++ (List.range 24).flatMap fun _ => [17, 16, 20])

/-- A scale file with the same twelve numbers in every layer and the rotary flags of the reference
pattern. -/
def scaleFileOf (record : List Nat) : ByteArray :=
  scaleFileBy fun L => record ++ [if L % 4 = 3 then 0 else 1]

/-- The stored scale file's twelve numbers of a layer. -/
def storedRecord : List Nat := [29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8]

/-- The stored scale file with the rotary flag of layer 5 turned from 1 to 0. -/
def flagTurned : ByteArray :=
  scaleFileBy fun L => storedRecord ++ [if L % 4 = 3 || L = 5 then 0 else 1]

/-- The stored scale file with the shift 9 in layer 5 alone: two shifts in the group of layers 4 to
7. -/
def twoShifts : ByteArray :=
  scaleFileBy fun L =>
    (if L = 5 then [29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 9] else storedRecord) ++
      [if L % 4 = 3 then 0 else 1]

#guard allThree storedPublicFiles
#guard allThree zGap
-- the reference's free numbers with one or two of them changed, in three of the five lines by one
#guard allThree { storedPublicFiles with pol := policyFile { storedLines with eps1 := 53688 } }
#guard allThree { storedPublicFiles with pol := policyFile { storedLines with eps2 := 1, epsF := 2 } }
#guard allThree { storedPublicFiles with pol := policyFile { storedLines with eps1 := 2 ^ 32 + 5 } }
#guard allThree { storedPublicFiles with pol := policyFile { storedLines with MF := 43 } }
#guard allThree { storedPublicFiles with pol := policyFile { storedLines with KF := 31 } }
-- the reference's scale file, then the same with five of each layer's twelve numbers moved by one
#guard scaleFileOf storedRecord == storedPublicFiles.KL
#guard allThree { storedPublicFiles with KL := scaleFileOf [29, 28, 17, 16, 15, 20, 19, 44, 30, 43, 31, 8] }
-- the theorem's conclusion, evaluated
#guard match publicOf storedPublicFiles.pol storedPublicFiles.KL (some storedPublicFiles.lay) with
  | .ok X => decide (OnBytes.Road.Hd.PublicCore X.P)
  | .error _ => false

end Meaning.Run
