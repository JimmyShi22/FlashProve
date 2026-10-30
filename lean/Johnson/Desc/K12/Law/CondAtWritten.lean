-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondAtWritten.lean: the condition of the law of a proximity test (the kind
K12), `K12Condition`, at a place whose stages and bits of work are those of a written test of
Johnson/Bridge/TestsAtWritten.lean. Definitions, statements and proofs; tests by evaluation.

Why. At each of the eighteen written tests `TestAt.ok` is a theorem, evaluated in the kernel
(`tests_ok`). By `k12Condition_of_test` (Johnson/Desc/K12/Law/CondOfTest.lean) the condition then
wants, beside the block's test on the plan and `pubOk`, that the place's own test is a written one.
Here that is an equation on a list of stages and a number, and it is shown at eight lists.
Main names:
  `sgEq`, `radOf T`, `brOfT T`: the radius and the two brackets that a test has at a stage, looked
    up by the stage's nine numbers.
  `testAtStages`, `testOf_eq`: `testOf`'s term at a list of stages and the bits of work.
  `Trial Ts i S w`: the test number i of the list Ts is the test of S and w, at the radii and
    brackets read off it.
  `trialB`, `bump`: the same as a test that can be evaluated, and a plant.
  `k12Condition_at_written`: every test of Ts says yes; `Trial Ts i S w`; the place's stages are S
    and its work is w; the block's test on the plan; `pubOk p K`: then the test T of the number i
    has `K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) p K (2⁻¹ ^ 128)`.
  `stUSmall` … `stLFull`; `trial_U_small` … `trial_L_full`: eight lists of stages, and the trial at
    each: the proof file's folded row (U), Omega (O), own test (W) and last test behind the links
    (L), at the smaller and the full-size stored example proof.
  The `#guard` lines: the trial says yes at the eight; it says no with one position more at the
    second stage, with one bit of work more, and at the neighbouring test.
It stands over files of Johnson/Bridge/, and so over Cb/Bridge/CodeListRSProved.lean and
the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15). It takes no run of their text; it calls their names.
Limits: the eight lists were typed by a program off prints of runs at the two stored example proofs
[the prints are not in this library]: that they are the stages of a place of a file's plan is not
shown here. No place is shown with the block's test on the plan and `pubOk`. That the written radii
are the planner's is not stated here. The limits of the condition stand: one round's share of its
written verifier messages, test bits among them: W of the 128 bits are work; no sum over rounds; the
round "BAT" stands in front of the chain and is not in it; of the chain, not of the block. No
soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.CondOfTest
import Johnson.Bridge.BrOf

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (Br FoldedPlace SwitchPlace LastPlace TestAt testsFull testsSmall tests_ok)
open scoped ENNReal

/-- Two stages have the same nine numbers. -/
def sgEq (s s' : Sg) : Bool :=
  s.C == s'.C && s.Z == s'.Z && s.h == s'.h && s.g == s'.g && s.t == s'.t

/-- The radius that a test has at a stage: looked up; 0 where the test has no such stage. -/
def radOf (T : TestAt) (s : Sg) : ℕ := ((T.stages.find? fun x => sgEq x.1 s).map (·.2)).getD 0

/-- The two brackets that a test has at a stage: looked up among the folded places; else the last
place's. -/
def brOfT (T : TestAt) (s : Sg) : Br × Br :=
  match T.folds.find? fun x => sgEq x.s s with
  | some x => (x.main, x.mask)
  | none => (T.last.main, T.last.mask)

/-- `testOf`'s term, at a list of stages and the bits of work. -/
def testAtStages (rad : Sg → ℕ) (B : Sg → Br × Br) (S : List Fmt.M1.Stage) (w : ℕ) :
    Option TestAt :=
  S.getLast?.map fun z => ⟨S.dropLast.map (foldAt rad B), lastAt rad B w z⟩

theorem testOf_eq (rad : Sg → ℕ) (B : Sg → Br × Br) (p : P12) :
    testOf rad B p = testAtStages rad B p.nums.stages p.nums.work := rfl

/-- **The trial**: the test number i of a list IS the test of the stages S and the work w, at the
radii and brackets read off it. -/
def Trial (Ts : List TestAt) (i : ℕ) (S : List Fmt.M1.Stage) (w : ℕ) : Prop :=
  ∃ T, Ts[i]? = some T ∧ testAtStages (radOf T) (brOfT T) S w = some T

def foldSame (x y : FoldedPlace) : Bool :=
  sgEq x.s y.s && x.e == y.e && x.main.same y.main && x.mask.same y.mask

def lastSame (x y : LastPlace) : Bool :=
  sgEq x.s y.s && x.e == y.e && x.work == y.work && x.main.same y.main && x.mask.same y.mask

def testSame (x y : TestAt) : Bool :=
  x.folds.length == y.folds.length && ((x.folds.zip y.folds).all fun z => foldSame z.1 z.2) &&
    lastSame x.last y.last

/-- The trial as a test that can be evaluated: for the plants. -/
def trialB (Ts : List TestAt) (i : ℕ) (S : List Fmt.M1.Stage) (w : ℕ) : Bool :=
  match Ts[i]? with
  | some T =>
    match testAtStages (radOf T) (brOfT T) S w with
    | some T' => testSame T' T
    | none => false
  | none => false

/-- A plant: the second stage draws one position more. -/
def bump : List Fmt.M1.Stage → List Fmt.M1.Stage
  | a :: b :: l => a :: { b with t := b.t + 1 } :: l
  | l => l

theorem ok_small {T : TestAt} (h : T ∈ testsSmall) : T.ok = true :=
  List.all_eq_true.1 tests_ok T (List.mem_append_right _ h)

theorem ok_full {T : TestAt} (h : T ∈ testsFull) : T.ok = true :=
  List.all_eq_true.1 tests_ok T (List.mem_append_left _ h)

/-- **At a written test.** -/
theorem k12Condition_at_written {Cl : Type} (Ts : List TestAt) (hTs : ∀ T ∈ Ts, T.ok = true)
    (i : ℕ) (S : List Fmt.M1.Stage) (w : ℕ) (h : Trial Ts i S w) (p : P12) (K : Codes)
    (hS : p.nums.stages = S) (hw : p.nums.work = w)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Cl).planOk = true) (hpub : pubOk p K = true) :
    ∃ T, Ts[i]? = some T ∧
      K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) p K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, h1, h2⟩ := h
  refine ⟨T, h1, k12Condition_of_test (radOf T) (brOfT T) p K T ?_
    (hTs T (List.mem_of_getElem? h1)) hp hpub⟩
  rw [testOf_eq, hS, hw]
  exact h2

/-- The stages of the place U of the smaller stored example proof. -/
def stUSmall : List Fmt.M1.Stage :=
  [⟨⟨17, 32768, 101⟩, ⟨13, 64, 156⟩, 5, 0, 101⟩,
    ⟨⟨14, 2048, 68⟩, ⟨12, 256, 68⟩, 4, 2, 68⟩,
    ⟨⟨14, 2048, 68⟩, ⟨14, 1024, 68⟩, 0, 0, 68⟩]

theorem trial_U_small : Trial testsSmall 6 stUSmall 28 := ⟨_, rfl, rfl⟩

/-- The stages of the place O of the smaller stored example proof. -/
def stOSmall : List Fmt.M1.Stage :=
  [⟨⟨18, 16384, 3831⟩, ⟨13, 64, 156⟩, 2, 0, 55⟩,
    ⟨⟨14, 1024, 69⟩, ⟨13, 1024, 69⟩, 4, 3, 69⟩,
    ⟨⟨15, 1024, 68⟩, ⟨15, 4096, 68⟩, 0, 0, 68⟩]

theorem trial_O_small : Trial testsSmall 7 stOSmall 28 := ⟨_, rfl, rfl⟩

/-- The stages of the place W of the smaller stored example proof. -/
def stWSmall : List Fmt.M1.Stage :=
  [⟨⟨18, 16384, 3831⟩, ⟨13, 256, 59⟩, 3, 0, 59⟩,
    ⟨⟨14, 1024, 75⟩, ⟨13, 1024, 75⟩, 4, 3, 75⟩,
    ⟨⟨15, 1024, 73⟩, ⟨15, 4096, 73⟩, 0, 0, 73⟩]

theorem trial_W_small : Trial testsSmall 8 stWSmall 20 := ⟨_, rfl, rfl⟩

/-- The stages of the place L of the smaller stored example proof. -/
def stLSmall : List Fmt.M1.Stage :=
  [⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 1, 0, 218⟩,
    ⟨⟨17, 8192, 55⟩, ⟨17, 4096, 55⟩, 4, 3, 55⟩,
    ⟨⟨16, 1024, 44⟩, ⟨16, 2048, 44⟩, 3, 3, 44⟩,
    ⟨⟨15, 128, 44⟩, ⟨15, 1024, 44⟩, 3, 3, 44⟩,
    ⟨⟨15, 128, 73⟩, ⟨15, 4096, 73⟩, 0, 0, 73⟩]

theorem trial_L_small : Trial testsSmall 5 stLSmall 20 := ⟨_, rfl, rfl⟩

/-- The stages of the place U of the full-size stored example proof. -/
def stUFull : List Fmt.M1.Stage :=
  [⟨⟨24, 4194304, 101⟩, ⟨13, 64, 152⟩, 7, 0, 101⟩,
    ⟨⟨21, 131072, 54⟩, ⟨12, 256, 54⟩, 5, 2, 54⟩,
    ⟨⟨17, 8192, 54⟩, ⟨12, 256, 54⟩, 4, 2, 54⟩,
    ⟨⟨13, 512, 54⟩, ⟨12, 256, 54⟩, 4, 2, 54⟩,
    ⟨⟨14, 512, 51⟩, ⟨14, 1024, 51⟩, 0, 0, 51⟩]

theorem trial_U_full : Trial testsFull 6 stUFull 28 := ⟨_, rfl, rfl⟩

/-- The stages of the place O of the full-size stored example proof. -/
def stOFull : List Fmt.M1.Stage :=
  [⟨⟨22, 262144, 3571⟩, ⟨13, 64, 152⟩, 4, 0, 51⟩,
    ⟨⟨18, 16384, 51⟩, ⟨14, 512, 51⟩, 4, 3, 51⟩,
    ⟨⟨14, 1024, 51⟩, ⟨13, 256, 51⟩, 4, 3, 51⟩,
    ⟨⟨15, 1024, 41⟩, ⟨15, 1024, 41⟩, 0, 0, 41⟩]

theorem trial_O_full : Trial testsFull 7 stOFull 28 := ⟨_, rfl, rfl⟩

/-- The stages of the place W of the full-size stored example proof. -/
def stWFull : List Fmt.M1.Stage :=
  [⟨⟨22, 262144, 3571⟩, ⟨13, 256, 55⟩, 5, 1, 55⟩,
    ⟨⟨18, 16384, 55⟩, ⟨15, 1024, 55⟩, 4, 3, 55⟩,
    ⟨⟨15, 2048, 55⟩, ⟨14, 512, 55⟩, 3, 3, 55⟩,
    ⟨⟨13, 256, 46⟩, ⟨13, 256, 46⟩, 3, 3, 46⟩,
    ⟨⟨15, 256, 44⟩, ⟨15, 1024, 44⟩, 0, 0, 44⟩]

theorem trial_W_full : Trial testsFull 8 stWFull 20 := ⟨_, rfl, rfl⟩

/-- The stages of the place L of the full-size stored example proof. -/
def stLFull : List Fmt.M1.Stage :=
  [⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 1, 0, 219⟩,
    ⟨⟨22, 262144, 55⟩, ⟨17, 4096, 55⟩, 4, 3, 55⟩,
    ⟨⟨19, 32768, 55⟩, ⟨16, 2048, 55⟩, 3, 3, 55⟩,
    ⟨⟨16, 4096, 55⟩, ⟨15, 1024, 55⟩, 3, 3, 55⟩,
    ⟨⟨13, 256, 46⟩, ⟨13, 256, 46⟩, 4, 4, 46⟩,
    ⟨⟨15, 256, 44⟩, ⟨15, 1024, 44⟩, 0, 0, 44⟩]

theorem trial_L_full : Trial testsFull 5 stLFull 20 := ⟨_, rfl, rfl⟩

#guard trialB testsSmall 6 stUSmall 28
#guard !trialB testsSmall 6 (bump stUSmall) 28
#guard !trialB testsSmall 6 stUSmall 29
#guard !trialB testsSmall 7 stUSmall 28
#guard trialB testsSmall 7 stOSmall 28
#guard !trialB testsSmall 7 (bump stOSmall) 28
#guard !trialB testsSmall 7 stOSmall 29
#guard !trialB testsSmall 8 stOSmall 28
#guard trialB testsSmall 8 stWSmall 20
#guard !trialB testsSmall 8 (bump stWSmall) 20
#guard !trialB testsSmall 8 stWSmall 21
#guard !trialB testsSmall 5 stWSmall 20
#guard trialB testsSmall 5 stLSmall 20
#guard !trialB testsSmall 5 (bump stLSmall) 20
#guard !trialB testsSmall 5 stLSmall 21
#guard !trialB testsSmall 6 stLSmall 20
#guard trialB testsFull 6 stUFull 28
#guard !trialB testsFull 6 (bump stUFull) 28
#guard !trialB testsFull 6 stUFull 29
#guard !trialB testsFull 7 stUFull 28
#guard trialB testsFull 7 stOFull 28
#guard !trialB testsFull 7 (bump stOFull) 28
#guard !trialB testsFull 7 stOFull 29
#guard !trialB testsFull 8 stOFull 28
#guard trialB testsFull 8 stWFull 20
#guard !trialB testsFull 8 (bump stWFull) 20
#guard !trialB testsFull 8 stWFull 21
#guard !trialB testsFull 5 stWFull 20
#guard trialB testsFull 5 stLFull 20
#guard !trialB testsFull 5 (bump stLFull) 20
#guard !trialB testsFull 5 stLFull 21
#guard !trialB testsFull 6 stLFull 20

end H2K.Pub

#print axioms H2K.Pub.ok_small
#print axioms H2K.Pub.ok_full
#print axioms H2K.Pub.k12Condition_at_written
#print axioms H2K.Pub.trial_W_small
#print axioms H2K.Pub.trial_L_full
