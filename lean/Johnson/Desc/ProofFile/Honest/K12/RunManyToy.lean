-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunManyToy.lean: tests (`#guard`) of a `ManyJob` (RunMany.lean) at
ToyWideJob.lean's small made-up example: three members in three trees (three main rows over the base
field; two main rows and a mask row; a mask row alone, in a shorter tree) and the first fold's own
fresh table of two rows in a fourth tree. Three of the first stage's eight main rows are no
member's. Three stages, (k, h) = (3, 1), (1, 1), (0, 0).

What is checked. The comment above each `#guard` says what it checks.
- `layFits` is true at the state on entry, and false with one of the job's public numbers changed.
  `rowsFit` is true, and false with a member's row or tail short or left out. The stages pass
  `StagesOk`.
- At two lists of challenges: `runBy` at the `RunIn` built from the members' lists of words gives
  the rounds, trees (positions 0 to 39) and opened columns of `testAll` at ToyWideJob.lean's own
  job, which gives its tables and trees over the field (no theorem covers this comparison), and
  those of `testAll` at the derived job, as `runJob_eq` (RunJobLaw.lean) says. The block accepts the
  output. There is no warning. With `Seams.fast` (FastW.lean) the output again agrees with
  ToyWideJob.lean's own job.
- Negative tests, at the first list: a member's rows said to begin one row later; two pieces of a
  tree exchanged; the base-field member marked as over the extension field; an entry of each
  member's rows made one larger, each alone; the job's argument w made one larger. Each time the
  block rejects.

Limits. Tiny sizes. The members' random values are not read in this example (its tails are fixed
numbers), so that member t receives `mem t` is not tested here (see JobSharedToy.lean). The clauses
of `layFits` on kept members are under no test. No pair of parts of a `ManyJob` is played. `#guard`
runs compiled code outside Lean's kernel and leaves no theorem. That the block accepts the output is
a test at one example. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ToyWideJob
import Johnson.Desc.ProofFile.Honest.K12.RunByToy
import Johnson.Desc.ProofFile.Honest.K12.RunMany
import Johnson.Desc.ProofFile.Honest.K12.FastW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.ManyToy
open ProofFile.Honest.K12.ToyWide (p m0E m0Tl m1E m1Tl m1Z m1ZTl m2Z m2ZTl stateAt sender coins genOf
  declared)
open ProofFile.Honest.K12.Light.ByToy (at' same)
open VerifiableInference.Desc (noDigest roundsFit Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Johnson.Prover.Link (BOut)
open Fmt.M1.Own (PSt)

/-- r rows of n entries. -/
def tab (r n : ℕ) (f : ℕ → ℕ → OnBytes.E) : List (List Fmt.M1.E) :=
  (List.range r).map fun i => (List.range n).map fun e => (f i e).triple

/-- What a test can change: the three shapes; the trees; each member's rows. -/
structure Turn where
  sh0 : MemShape := ⟨0, 3, 0, 0, true⟩
  sh1 : MemShape := ⟨4, 2, 0, 1, false⟩
  sh2 : MemShape := ⟨0, 0, 1, 1, false⟩
  trees : List (ℕ × List Piece) :=
    [(5, [.main 0]), (5, [.main 1, .mask 1]), (4, [.mask 2]), (4, [.fresh])]
  f0 : PSt → PSt := id
  f1 : PSt → PSt := id
  f2 : PSt → PSt := id

def job (u : Turn) : ManyJob ℕ Unit :=
  { p := p
    mems :=
      [⟨(sender, 0, ⟨0, 7⟩), u.sh0, fun w _ _ =>
          u.f0 { M := tab 3 4 (m0E w), Rh := tab 3 2 m0Tl, W := [], Sg := [], P := [], Pi := [] }⟩,
        ⟨(sender, 1, ⟨0, 7⟩), u.sh1, fun _ _ _ =>
          u.f1 { M := tab 2 4 m1E, Rh := tab 2 2 m1Tl, W := tab 1 8 fun _ => m1Z
                 Sg := tab 1 2 fun _ => m1ZTl, P := [], Pi := [] }⟩,
        ⟨(sender, 2, ⟨0, 3⟩), u.sh2, fun _ _ _ =>
          u.f2 { M := [], Rh := [], W := tab 1 8 fun _ => m2Z, Sg := tab 1 2 fun _ => m2ZTl
                 P := [], Pi := [] }⟩]
    fresh := none, rec₀ := fun _ _ => stateAt OnBytes.zeroE, trees := u.trees }

/-- Nothing precedes the test, and the toy stands where no column is handed: `Seen.bare []`. -/
def fr : Front Unit := ⟨[], (), Seen.bare []⟩
def light (S : Seams) (u : Turn) (n : ℕ) (w : ℕ := 0) : RunOut :=
  runBy S (RunIn.ofRun (job u).toRun w fr coins) (at' (genOf declared n))
def own (n : ℕ) : BOut := testAll (ProofFile.Honest.K12.ToyWide.J OnBytes.zeroE) 0 fr coins
  (at' (genOf declared n))
def derived (u : Turn) (n : ℕ) : BOut := testAll (job u).toRun.toTest 0 fr coins
  (at' (genOf declared n))
def accepts (a : RunOut) : Bool :=
  roundsFit (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds a.rs &&
    Except.isOk ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide (stateAt OnBytes.zeroE)
      (a.rs.map noDigest) a.gs)

def up (x : Fmt.M1.E) : Fmt.M1.E := (x.1 + 1, x.2.1, x.2.2)
def upM (q : PSt) : PSt := { q with M := q.M.modify 0 fun r => r.modify 0 up }
def upW (q : PSt) : PSt := { q with W := q.W.modify 0 fun r => r.modify 0 up }

/-- `RunJob.rowsFit` at a job. -/
def fits (u : Turn) : Bool := (job u).toRun.rowsFit 0 fr coins.mem
/-- `ManyJob.layFits` at the state on entry. -/
def lays (u : Turn) : Bool := (job u).layFits (stateAt OnBytes.zeroE)

-- the job's public numbers are those of the state on entry; the stages pass StagesOk
#guard lays {} && StagesOk p.nums.stages
-- layFits is false with one number changed: a first row (main, mask), a count (main, mask), base
#guard !lays { sh1 := ⟨5, 2, 0, 1, false⟩ } && !lays { sh2 := ⟨0, 0, 0, 1, false⟩ }
#guard !lays { sh0 := ⟨0, 2, 0, 0, true⟩ } && !lays { sh1 := ⟨4, 2, 0, 2, false⟩ }
#guard !lays { sh0 := ⟨0, 3, 0, 0, false⟩ }
-- and with one number of the first stage changed: of its main code, of its mask code, k, h
#guard [fun (s : Fmt.M1.Stage) => { s with C := { s.C with r := s.C.r + 1 } },
    fun s => { s with Z := { s.Z with l := 2 * s.Z.l } },
    fun s => { s with C := { s.C with a := 6 } }, fun s => { s with k := s.k + 1 },
    fun s => { s with h := s.h + 1 }].all fun f =>
  !({ job {} with p := { p with nums := { p.nums with stages := p.nums.stages.modify 0 f } } } :
    ManyJob ℕ Unit).layFits (stateAt OnBytes.zeroE)
-- and with a member left out
#guard !({ job {} with mems := (job {}).mems.dropLast } : ManyJob ℕ Unit).layFits
  (stateAt OnBytes.zeroE)
-- the rows as given have the stage's sizes, though rows 3, 6 and 7 are no member's
#guard fits {}
-- rowsFit is false with a member's tail one entry short, a member's row or tail left out, a mask
-- row one entry short
#guard !fits { f0 := fun q => { q with Rh := q.Rh.modify 1 (·.dropLast) } }
-- the block accepts that run, which has a 0 where a tail's random value is due: rowsFit alone tells
#guard accepts (light .lib { f0 := fun q => { q with Rh := q.Rh.modify 1 (·.dropLast) } } 0)
#guard !fits { f1 := fun q => { q with M := q.M.dropLast } } &&
  !fits { f1 := fun q => { q with Sg := [] } }
#guard !fits { f2 := fun q => { q with W := q.W.modify 0 (·.dropLast) } }
-- against testAll at ToyWideJob.lean's own job, and at the derived job, at both lists
#guard same (light .lib {} 0) (own 0) && same (light .lib {} 1) (own 1)
#guard same (light .lib {} 0) (derived {} 0) && same (light .lib {} 1) (derived {} 1)
-- the block accepts; no warning
#guard accepts (light .lib {} 0) && accepts (light .lib {} 1)
#guard (light .lib {} 0).no == [] && (light .lib {} 1).no == []
-- with Seams.fast
#guard same (light .fast {} 0) (own 0) && same (light .fast {} 1) (own 1)
-- negative tests
#guard !accepts (light .lib { sh1 := ⟨5, 2, 0, 1, false⟩ } 0)
#guard !accepts (light .lib
  { trees := [(5, [.main 0]), (5, [.mask 1, .main 1]), (4, [.mask 2]), (4, [.fresh])] } 0)
#guard !accepts (light .lib { sh0 := ⟨0, 3, 0, 0, false⟩ } 0)
#guard !accepts (light .lib { f0 := upM } 0) && !accepts (light .lib { f1 := upM } 0)
#guard !accepts (light .lib { f1 := upW } 0) && !accepts (light .lib { f2 := upW } 0)
#guard !accepts (light .lib {} 0 1)

end ProofFile.Honest.K12.Light.ManyToy

#print axioms ProofFile.Honest.K12.Light.ManyToy.tab
#print axioms ProofFile.Honest.K12.Light.ManyToy.Turn
#print axioms ProofFile.Honest.K12.Light.ManyToy.job
#print axioms ProofFile.Honest.K12.Light.ManyToy.fr
#print axioms ProofFile.Honest.K12.Light.ManyToy.light
#print axioms ProofFile.Honest.K12.Light.ManyToy.own
#print axioms ProofFile.Honest.K12.Light.ManyToy.derived
#print axioms ProofFile.Honest.K12.Light.ManyToy.accepts
#print axioms ProofFile.Honest.K12.Light.ManyToy.up
#print axioms ProofFile.Honest.K12.Light.ManyToy.upM
#print axioms ProofFile.Honest.K12.Light.ManyToy.upW
#print axioms ProofFile.Honest.K12.Light.ManyToy.fits
#print axioms ProofFile.Honest.K12.Light.ManyToy.lays
