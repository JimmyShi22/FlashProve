-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/TestsAtWritten.lean: a proximity test behind its batching as ONE object: its folded
stages, its last stage, and the code switches between them MADE OF THESE, so that each stage has one
radius in all its rounds; and the nine tests of a key file, an entry file and a proof file, at two
sizes, cut out of the written lists: at each, every fold, every code switch and the base case are
taken off, and every error count is at most 2^-128 of its round's written verifier messages.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Johnson/Bridge/FoldAtWritten.lean, CsAtWritten.lean and BaseAtWritten.lean have three lists that no
theorem ties to each other. Here they are tied. Definitions, statements and proofs.

Main names:
  `switchesOf`: the code switches between the neighbours of a list of stages with radii.
  `TestAt`: the folded places and the last place of a test. `TestAt.stages`: its stages with their
    radii. `TestAt.switches`: its code switches, with the last place's bits of work.
  `TestAt.ok`: all tests of all its places. `TestAt.Paid`, `TestAt.paid`: what a yes gives.
  `cutTests`: cuts tests out of a list of folded places and a list of last places.
  `testsFull`, `testsSmall`: nine tests each, in the order: the key file's proof of the ranges,
    folded row, Omega, own test; the entry file's test; the proof file's last test behind the links,
    folded row, Omega, own test. `tests_nine`: there are nine and nine.
  `tests_switches`: the code switches made here are the written lists `switchFull`, `switchSmall`.
  `tests_all`: the tests' folded and last places are the written lists', but for the links' groups.
  `tests_ok`; `TestsPaid`, `testsPaid`: THE STATEMENT: `TestAt.Paid` at each of the eighteen.

Limits: those of the three files named: above all, THAT THESE NUMBERS ARE THOSE OF A FILE's PLAN IS
NOT PROVED HERE, and that they are the stages of the description of the protocol that a verifier
runs is open. `tests_switches` and `tests_all` tie written lists of this folder to each other and to
nothing else. The groups of a proof file's links are in no test. The batching in front of a test
is not here. That a test's code switches have the bits of work of its last round is so in the
written lists (`tests_switches`); it is no law. No chain (`OnBytes.Slice.Chain`) is built here. No
sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.FoldAtWritten
import Johnson.Bridge.BaseAtWritten
import Johnson.Bridge.CsAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb

/-- The code switches between the neighbours of a list of stages with radii, with w bits of work. -/
def switchesOf (w : ℕ) : List (Sg × ℕ) → List SwitchPlace
  | p :: p' :: r => ⟨p.1, p'.1, p.2, p'.2, w⟩ :: switchesOf w (p' :: r)
  | _ => []

/-- A proximity test behind its batching: the places that are folded, and the last. -/
structure TestAt where
  folds : List FoldedPlace
  last : LastPlace

namespace TestAt
variable (T : TestAt)

/-- The test's stages, each with its one radius. -/
def stages : List (Sg × ℕ) := T.folds.map (fun x => (x.s, x.e)) ++ [(T.last.s, T.last.e)]

/-- The test's code switches. -/
def switches : List SwitchPlace := switchesOf T.last.work T.stages

/-- All tests of all places. -/
def ok : Bool :=
  (T.folds.all fun x => x.good && x.priced) && (T.switches.all fun x => x.good && x.priced) &&
    (T.last.good && T.last.priced)

/-- What is said of a test. -/
structure Paid (T : TestAt) : Prop where
  folds : ∀ x ∈ T.folds, x.Paid
  switches : ∀ x ∈ T.switches, x.Paid
  last : T.last.Paid

variable {T}

theorem paid (h : T.ok = true) : T.Paid := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun x hx => FoldedPlace.paid (h.1.1 x hx).1 (h.1.1 x hx).2,
    fun x hx => SwitchPlace.paid (h.1.2 x hx).1 (h.1.2 x hx).2, LastPlace.paid h.2.1 h.2.2⟩

end TestAt

/-- Cuts tests out of a list of folded places and a list of last places: of each test the place of
its first folded stage, the number of its folded stages, and the place of its last stage. -/
def cutTests (F : List FoldedPlace) (L : List LastPlace) (cuts : List (ℕ × ℕ × ℕ)) : List TestAt :=
  cuts.flatMap fun c => (L[c.2.2]?).toList.map fun l => ⟨(F.drop c.1).take c.2.1, l⟩

/-- The nine tests at full size. -/
def testsFull : List TestAt :=
  cutTests foldFull lastFull
    [(0, 3, 4), (3, 4, 5), (7, 3, 6), (10, 4, 7), (14, 4, 8), (20, 5, 0), (25, 4, 1), (29, 3, 2),
      (32, 4, 3)]

/-- The nine tests at the small size. -/
def testsSmall : List TestAt :=
  cutTests foldSmall lastSmall
    [(0, 3, 4), (3, 2, 5), (5, 2, 6), (7, 2, 7), (9, 2, 8), (14, 4, 0), (18, 2, 1), (20, 2, 2),
      (22, 2, 3)]

theorem tests_nine : testsFull.length = 9 ∧ testsSmall.length = 9 := ⟨rfl, rfl⟩

/-- The code switches made of the folded and the last places are the written lists. -/
theorem tests_switches :
    testsFull.flatMap TestAt.switches = switchFull ∧
      testsSmall.flatMap TestAt.switches = switchSmall := ⟨rfl, rfl⟩

/-- The tests' folded places, in a row, are the written list without the links' groups (two at full
size, from the place 18 on; three at the small size, from the place 11 on); the tests' last places
are the written list, the key file's and the entry file's five first. -/
theorem tests_all :
    (testsFull.flatMap TestAt.folds = foldFull.take 18 ++ foldFull.drop 20 ∧
      testsFull.map TestAt.last = lastFull.drop 4 ++ lastFull.take 4) ∧
    (testsSmall.flatMap TestAt.folds = foldSmall.take 11 ++ foldSmall.drop 14 ∧
      testsSmall.map TestAt.last = lastSmall.drop 4 ++ lastSmall.take 4) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem tests_ok : ((testsFull ++ testsSmall).all fun T => T.ok) = true := by decide +kernel

/-- **Every block of every test taken off, and every count against 2^-128, each stage at one
radius.** -/
def TestsPaid : Prop := ∀ T ∈ testsFull ++ testsSmall, T.Paid

theorem testsPaid : TestsPaid := fun T hT => TestAt.paid (List.all_eq_true.1 tests_ok T hT)

end Johnson.Bridge

#print axioms Johnson.Bridge.tests_switches
#print axioms Johnson.Bridge.tests_ok
#print axioms Johnson.Bridge.testsPaid
