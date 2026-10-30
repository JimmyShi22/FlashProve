-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/Part1MarksCode.lean: PART 1's MARKS AT THE PROOF FILE's FIRST CHAIN AT THE FULL SIZE,
AS ONE LIST (`Mark`, Johnson/Desc/ProofFile/Honest/Law/Marks.lean: a place, a test on challenges, a
stated number). DEFINITIONS ALONE: CODE IN THIS FILE, LAWS IN ANOTHER
(Johnson/P1K8R/Part1Marks.lean), so that whoever names the list imports no law's ground. NO LAW IS
STATED HERE, AND NONE OF THE LIBRARY's GOALS. NO NUMBER HERE IS HELD AGAINST ITS TEST.

  `szAt`   the sizes at a built segment
  `walkCode`, `mergeBadCode`, `deadRec`, `mergeRec`   SECOND TEXTS, written out in place, since
      the definitions that they repeat stand in files with laws: `anyBad`, `mergeBad`, `deadMark`,
      `headMergeMark`. That each is the named one is said in the file of laws, with no hypothesis.
      BANKED, NOT SEATED: the firsts stay the ones of which our laws and pages speak. The test
      `deadT` is the library's own (Johnson/Desc/K8/Honest/DeadTest.lean): imported, not copied
  **`part1Marks Zp G₀`**   the list: 25 times `deadRec`, then `mergeRec`
Limits. WHERE A LOOK-UP DOES NOT RETURN A RECORD IS LEFT OUT IN SILENCE: that none is, under the
library's one head, is said in the file of laws. It stands over the frame's Marks.lean with what
that imports. THE LIST HOLDS THE MARKS THAT PART 1 OWNS, NOT ALL THAT ITS BOUNDS WANT SILENT.
Nothing is claimed on completeness, soundness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.Marks
import Johnson.Desc.First.K8.Law
import Johnson.Desc.K8.Honest.DeadTest
import Johnson.Desc.K9.Honest.SlotsLive
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Desc.ProofFile.Lot.K11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest (deadT)
open VerifiableInference.Desc.K9H (notZero)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest (Odds Mark)

/-- The typed sizes of the smallness test at a built segment: the lot's own numbers of the place
(ProofFile.k8Par, Johnson/Desc/ProofFile/Lot/K8.lean) laid into the seal's `Size` by `K8.sizeAt`
(Johnson/Desc/First/K8/Law.lean): how many matrices, each one's columns, how many combinations. The
six other fields, which the mark does not read, are 0. -/
def szAt (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (X : LinkH) (l : ℕ) : Size :=
  K8.sizeAt (ProofFile.k8Par Zp G₀ X l) ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, 0, 0, 0⟩

/-- Some listed round's drawn value is bad. A SECOND TEXT of `anyBad`
(Johnson/P1K8R/MarkRounds.lean). -/
def walkCode (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) : ℕ → List Fmt.Drawn → Bool
  | _, [] => false
  | j, x :: l => (mk j && bad x) || walkCode bad mk (j + 1) l

/-- The merge's test at one round's drawn value. A SECOND TEXT of `mergeBad`
(Johnson/Desc/ProofFile/Honest/K11/Mark/Statement.lean). -/
def mergeBadCode (dr : Fmt.Drawn) : Bool :=
  match dr.elems with
  | [t] => !notZero (E.ofTriple t)
  | _ => true

/-- The mark "a column of the drawn matrix is all 0", written out. A SECOND TEXT of `deadMark`
(Johnson/P1K8R/DeadMark.lean). THE SHARE IS A WRITTEN PAIR OF NUMBERS. -/
def deadRec (link o : Nat) (sz : Size) : Mark :=
  { place := ⟨1, some link, 5 + o, .K8⟩
    test := fun _ own =>
      if deadT sz own then some "the smallness test: a column of the drawn matrix is all 0"
      else none
    share := ⟨sz.columns, 2 ^ sz.tau⟩ }

/-- The merge's mark, written out. A SECOND TEXT of `headMergeMark`
(Johnson/Desc/ProofFile/Honest/K11/Mark/Statement.lean). THE SHARE IS A WRITTEN PAIR OF NUMBERS. -/
def mergeRec (P : HeadMergeP) : Mark :=
  { place := ⟨1, some P.link, P.piece, .K11⟩
    test := fun _ own =>
      if walkCode mergeBadCode (fun i => decide (i ∈ List.range' 1 (P.lay.lk + 1))) 0 own then
        some "the merge: the summand's factor or a round's challenge is 0"
      else none
    share := ⟨2 * (List.range' 1 (P.lay.lk + 1)).length * (2 ^ 128 + 1) ^ 3,
      _root_.Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ }

/-- **PART 1's MARKS AT THE PROOF FILE's FIRST CHAIN AT THE FULL SIZE**, read off the public part
and the ground. In each of the 25 segments l, at the built segment G₀.built[l]? = some X, with o :=
1 at l = 24 and 0 elsewhere: `deadRec l o (szAt Zp G₀ X l)`; where the look-up does not return, no
record. Then `mergeRec` at the lot's own numbers K11.parOf Zp G₀. No argument stays open. -/
def part1Marks (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) : List Mark :=
  ((List.range 25).filterMap fun l => (G₀.built[l]?).map fun X =>
      deadRec l (if l = 24 then 1 else 0) (szAt Zp G₀ X l)) ++
    [mergeRec (_root_.K11.parOf Zp G₀)]

end P1K8

#print axioms P1K8.szAt
#print axioms P1K8.walkCode
#print axioms P1K8.mergeBadCode
#print axioms P1K8.deadRec
#print axioms P1K8.mergeRec
#print axioms P1K8.part1Marks
