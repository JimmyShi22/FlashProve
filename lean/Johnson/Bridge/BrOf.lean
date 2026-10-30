-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/BrOf.lean: the brackets of `Cb.bchksBound` as a function of the code's numbers, so
that a stage of a proximity test is tested with no written numeral; and two tests on lists of stages
whose yes gives, at every stage of the list, what Johnson/Bridge/FoldPriced.lean and
Johnson/Bridge/BaseAtWritten.lean say of one place.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions with code, and statements that follow from the two files named, or are proved by
evaluation on natural numbers.

Main names:
  `rootDown n K i r`: bit by bit, from bit i - 1 down: the largest number r + x, x below 2^i, whose
    square times n is at most K. By recursion on i: the kernel can run it.
  `brOf n k e`: a bracket (`Br`): a: the largest number below 2^128 with a² n ≤ k 2^128; b: a if
    that is an equation, else a + 1; m: the least number, at least 3, with
    b n ≤ m (2^64 n - b n - 2^64 e); N: 2^64 ((2m+1)^5 n² + 24 (2m+1) k (e+1)) / (48 k a), rounded
    up.
  `brUp`, `brEnds`: its two steps: b from a; m and N from a and b. `Br.same`: two brackets are the
    same, number by number.
  `mainOf s e`, `maskOf s e`: `brOf` at a stage's main code, and at its mask code repeated to the
    main rows' length.
  `FoldedPlace.of s e`, `LastPlace.of s e work`: a place with its two brackets by `brOf`.
  `foldsB`, `lastsB`: the two tests (`good`, `priced`) at every stage of a list.
  `foldsB_paid`, `lastsB_paid`: a yes gives `FoldedPlace.Paid`, `LastPlace.Paid` at every stage.
  `written_are_brOf`, `writtenFolds_are_brOf`: at the eighteen written last stages of
    Johnson/Bridge/BaseAtWritten.lean and the sixty written folded stages of
    Johnson/Bridge/FoldAtWritten.lean the written brackets are `brOf`'s.
  `lastsB_written`, `foldsB_written`: the tests say yes at these stages, radii and bits of work.

Limits: NOTHING IS PROVED OF `brOf`: no statement says that its numbers bracket anything. It
proposes; `Br.ok` (by `Cb.CntLe`) tests what it proposes, inside `good`; where it proposes
badly the test says no. Where a divisor is 0 Lean's division gives 0, and `Br.ok` says no. BOTH
TESTS SAY YES AT AN EMPTY LIST: who calls them asks that the list is whole. The radii are handed to
the tests with the stages: they are tied to nothing here. That a list's stages are those of a file's
plan is not said here (Johnson/Bridge/PlanStages.lean makes such lists of a plan's records). The
eighteen and sixty written places are tied to a plan by no theorem (the limits of the two files that
hold them). No sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.FoldPriced
import Johnson.Bridge.BaseAtWritten
import Johnson.Bridge.FoldAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb

/-- Bit by bit, from bit i - 1 down to bit 0: a bit is taken if the square, times n, stays at most
K. -/
def rootDown (n K : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | i + 1, r =>
    bif Nat.ble ((r + 2 ^ i) * (r + 2 ^ i) * n) K then rootDown n K i (r + 2 ^ i)
    else rootDown n K i r

/-- m and N of a bracket, from its two ends. -/
def brEnds (n k e a b : ℕ) : Br :=
  let den := 2 ^ 64 * n - b * n - e * 2 ^ 64
  let m := max 3 ((b * n + den - 1) / den)
  ⟨m, a, b,
    (2 ^ 64 * ((2 * m + 1) ^ 5 * n ^ 2 + 24 * (2 * m + 1) * k * (e + 1)) + 48 * k * a - 1) /
      (48 * k * a)⟩

/-- The upper end, from the lower. -/
def brUp (n k e a : ℕ) : Br :=
  brEnds n k e a (bif Nat.ble (k * 2 ^ 128) (a * a * n) then a else a + 1)

/-- **A bracket of `Cb.bchksBound n k e`, proposed.** -/
def brOf (n k e : ℕ) : Br := brUp n k e (rootDown n (k * 2 ^ 128) 128 0)

/-- Two brackets are the same, number by number. -/
def Br.same (u v : Br) : Bool :=
  Nat.beq u.m v.m && Nat.beq u.a v.a && Nat.beq u.b v.b && Nat.beq u.N v.N

/-- The main code's bracket at a stage and a radius. -/
def mainOf (s : Sg) (e : ℕ) : Br := brOf (2 ^ s.C.a) (s.C.r + s.C.l - 1) e

/-- The bracket of the mask code, repeated to the main rows' length. -/
def maskOf (s : Sg) (e : ℕ) : Br :=
  brOf (2 ^ s.C.a) (2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1)) e

/-- A stage that is folded, with its radius; the brackets by `brOf`. -/
def FoldedPlace.of (s : Sg) (e : ℕ) : FoldedPlace := ⟨s, e, mainOf s e, maskOf s e⟩

/-- A last stage, with its radius and the bits of work of its second round; the brackets by
`brOf`. -/
def LastPlace.of (s : Sg) (e work : ℕ) : LastPlace := ⟨s, e, work, mainOf s e, maskOf s e⟩

/-- **The two tests at every stage of a list of folded stages**: (stage, radius). -/
def foldsB (l : List (Sg × ℕ)) : Bool :=
  l.all fun p => (FoldedPlace.of p.1 p.2).good && (FoldedPlace.of p.1 p.2).priced

/-- **The two tests at every stage of a list of last stages**: (stage, radius, bits of work). -/
def lastsB (l : List (Sg × ℕ × ℕ)) : Bool :=
  l.all fun p => (LastPlace.of p.1 p.2.1 p.2.2).good && (LastPlace.of p.1 p.2.1 p.2.2).priced

/-- **A yes of the test: every folded stage of the list is paid.** No hypothesis on codes. -/
theorem foldsB_paid {l : List (Sg × ℕ)} (h : foldsB l = true) :
    ∀ p ∈ l, (FoldedPlace.of p.1 p.2).Paid := fun p hp =>
  have h1 := Bool.and_eq_true_iff.1 (List.all_eq_true.1 h p hp)
  FoldedPlace.paid h1.1 h1.2

/-- **A yes of the test: every last stage of the list is paid.** No hypothesis on codes. -/
theorem lastsB_paid {l : List (Sg × ℕ × ℕ)} (h : lastsB l = true) :
    ∀ p ∈ l, (LastPlace.of p.1 p.2.1 p.2.2).Paid := fun p hp =>
  have h1 := Bool.and_eq_true_iff.1 (List.all_eq_true.1 h p hp)
  LastPlace.paid h1.1 h1.2

/-- At the eighteen written last stages the written brackets are `brOf`'s. -/
theorem written_are_brOf :
    ((lastFull ++ lastSmall).all fun x =>
      x.main.same (mainOf x.s x.e) && x.mask.same (maskOf x.s x.e)) = true := by
  decide +kernel

/-- The test says yes at the eighteen written stages, radii and bits of work. -/
theorem lastsB_written :
    lastsB ((lastFull ++ lastSmall).map fun x => (x.s, x.e, x.work)) = true := by
  decide +kernel

/-- At the sixty written folded stages the written brackets are `brOf`'s. -/
theorem writtenFolds_are_brOf :
    ((foldFull ++ foldSmall).all fun x =>
      x.main.same (mainOf x.s x.e) && x.mask.same (maskOf x.s x.e)) = true := by
  decide +kernel

/-- The test says yes at the sixty written folded stages and radii. -/
theorem foldsB_written : foldsB ((foldFull ++ foldSmall).map fun x => (x.s, x.e)) = true := by
  decide +kernel

end Johnson.Bridge

#print axioms Johnson.Bridge.foldsB_paid
#print axioms Johnson.Bridge.lastsB_paid
#print axioms Johnson.Bridge.written_are_brOf
#print axioms Johnson.Bridge.lastsB_written
#print axioms Johnson.Bridge.writtenFolds_are_brOf
#print axioms Johnson.Bridge.foldsB_written
