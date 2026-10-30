-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/BaseCodesAt.lean: what the base case of a proximity test asks of its codes
(`BaseCodes`, OnBytes/Slice/Base.lean), at every stage and radius with `Sg.StageJ` (sizes in order,
two coefficients or more in each code, a radius that is not 0 and is below the stage's Johnson
radius), with no hypothesis on codes; the same at counts that are written whole numbers; and the
mask row's count by itself.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

OnBytes/Slice/ManyHoldsJoh.lean has these facts under the statement on codes, taken as given
(`Cb.BCHKS46At GF GE`). Cb/Bridge/CodeListRSProved.lean proves that statement. Here the two are put
together. Definitions, statements and proofs.

Main names:
  `baseCodes_at`: at a stage and radius with `Sg.StageJ`: `BaseCodes` at the counts `Sg.flC` +
    `Sg.flZ` and the Johnson bound's list `Sg.lstJ`.
  `baseCodes_le`: the same at any whole numbers that are at least the integer parts of the two
    values of `Cb.bchksBound`.
  `maskCount_at`, `maskCount_own`, `MaskCountWithin`, `maskCountWithin`: one mask row, under the
    mask code repeated to the main rows' length: a line through two words has at most `Sg.flZ`
    exceptional points at every radius with `Sg.StageJ`, and at most `Sg.cntZ` at a radius below
    half the repeated code's own distance (e + 1 below a third of it).
  `Br`, `Br.ok`: numbers that bracket a value of `Cb.bchksBound`, and the test on them (`Cb.CntLe`).
  `LastPlace`: a last stage with its radius, the bits of work of its second round and two brackets.
  `LastPlace.exc`, `LastPlace.lst`: the two letters of `BaseCodes` there, as numbers that can be
    evaluated.
  `LastPlace.good`, `LastPlace.baseCodes`: a test on natural numbers; its yes gives `BaseCodes`.
  `LastPlace.radius_lt`, `LastPlace.listIn`: the radius is below the distance; the lists of the
    stage's tables, which the code switch into the stage asks.

Limits: nothing on a protocol, a verifier, a plan or a file. `BaseCodes` holds of large letters for
little reason: what a place's letters are worth is a matter of their size
(Johnson/Bridge/BasePriced.lean). That a place's numbers are those of a file's plan is not said
here.

-/
import OnBytes.Slice.ManyHoldsJoh
import OnBytes.Slice.BlocksBySource
import Johnson.Top.H.CountsBridge
import Cb.Ref.CntLe
import Cb.Bridge.CodeListRSProved

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb

/-- **What the base case asks of its codes, below the Johnson radius. No hypothesis on codes.** -/
theorem baseCodes_at {s : Sg} {e : ℕ} (h : s.StageJ e) :
    BaseCodes s e (s.flC e + s.flZ e) (s.lstJ e) :=
  OnBytes.Slice.baseCodes_joh h.sized h.joh (h.counts (Cb.Bridge.bchks46At GF GE))

/-- The same at whole numbers that are at least the integer parts of the two values of
`Cb.bchksBound`. -/
theorem baseCodes_le {s : Sg} {e bC bZ : ℕ} (h : s.StageJ e)
    (hC : ⌊bchksBound (2 ^ s.C.a) (s.C.r + s.C.l - 1) e⌋₊ ≤ bC)
    (hZ : ⌊bchksBound (2 ^ s.C.a) (2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1)) e⌋₊ ≤ bZ) :
    BaseCodes s e (bC + (bZ + listMax (2 ^ s.C.a) s.dZ e)) (s.lstJ e) :=
  OnBytes.Slice.baseCodes_joh h.sized h.joh
    (Sg.countsAt_bchks_fl (Cb.Bridge.bchks46At GF GE) h.sized h.pos h.twoC h.twoZ h.rad h.joh bC bZ
      hC hZ)

/-! ## The mask row's count by itself -/

/-- One mask row, repeated to the main rows' length, at a radius below the stage's Johnson radius.
-/
theorem maskCount_at {s : Sg} {e : ℕ} (h : s.StageJ e) : s.cZ.MCAat e (s.flZ e) :=
  (h.counts (Cb.Bridge.bchks46At GF GE)).mask

/-- One mask row, at a radius below half the repeated mask code's OWN distance, whatever the main
code's: at most `Sg.cntZ` exceptional points: e + 1 below a third of that distance, else the number
of positions. The statement on codes is not used. -/
theorem maskCount_own {s : Sg} {e : ℕ} (h : s.Sized) (hp : s.Pos) (h2 : 2 * e < s.dZ) :
    s.cZ.MCAat e (s.cntZ e) := by
  unfold Sg.cntZ
  split
  · exact Sg.mcaThird_cZ h ‹_›
  · exact mca_half_rep s.Z s.C.a h.short h.small hp.someZ h.roomZ e h2

/-- **The mask code's count within the repeated code's distance**, as one proposition: of every
stage and radius. First clause: below the stage's Johnson radius. Second clause: below half the
repeated mask code's own distance. -/
def MaskCountWithin : Prop :=
  (∀ (s : Sg) (e : ℕ), s.StageJ e → s.cZ.MCAat e (s.flZ e)) ∧
    ∀ (s : Sg) (e : ℕ), s.Sized → s.Pos → 2 * e < s.dZ → s.cZ.MCAat e (s.cntZ e)

theorem maskCountWithin : MaskCountWithin :=
  ⟨fun _ _ h => maskCount_at h, fun _ _ h hp h2 => maskCount_own h hp h2⟩

/-- The second clause is not empty where the first stage of a proof file's last test stands (numbers
read off a print of the planner's functions, as those of Johnson/Bridge/BaseAtWritten.lean; no
theorem ties them to a plan): at full size and at the small size the sizes are in order, each code
has a coefficient, and three times the radius is below the repeated mask code's own distance (so
the count is e + 1), while twice the radius is not below the main code's. -/
theorem maskCount_firstStages :
    ∀ p ∈ [((⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 0, 1, 219⟩ : Sg), 2433820),
        (⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, 1, 218⟩, 76267)],
      p.1.Sized ∧ p.1.Pos ∧ 3 * p.2 < p.1.dZ ∧ p.1.dC ≤ 2 * p.2 := by
  have h : ([((⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 0, 1, 219⟩ : Sg), 2433820),
      (⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, 1, 218⟩, 76267)].all fun p =>
        Johnson.Top.H.sizedB p.1 && decide (0 < p.1.C.r + p.1.C.l) &&
          decide (0 < p.1.Z.r + p.1.Z.l) && decide (3 * p.2 < p.1.dZ) &&
          decide (p.1.dC ≤ 2 * p.2)) = true := by decide +kernel
  intro p hp
  have h1 := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨Johnson.Top.H.sized_of h1.1.1.1.1, ⟨h1.1.1.1.2, h1.1.1.2⟩, h1.1.2, h1.2⟩

/-! ## A last stage in numbers -/

/-- Numbers that bracket a value of `Cb.bchksBound`: m, the two ends a / 2^64 and b / 2^64 of a
bracket of the square root of the rate, and the bound N. -/
structure Br where
  m : ℕ
  a : ℕ
  b : ℕ
  N : ℕ

/-- The test of Cb/Ref/CntLe.lean on a bracket. -/
def Br.ok (w : Br) (n k e : ℕ) : Bool := decide (CntLe n k e w.m w.a w.b (2 ^ 64) w.N)

theorem Br.le {w : Br} {n k e : ℕ} (h : w.ok n k e = true) : ⌊bchksBound n k e⌋₊ ≤ w.N :=
  floor_le_of_cntLe (of_decide_eq_true h)

/-- A last stage with its radius, the bits of work of its second round, and the brackets of its two
counts. -/
structure LastPlace where
  s : Sg
  e : ℕ
  work : ℕ
  main : Br
  mask : Br

namespace LastPlace
variable (x : LastPlace)

/-- The bound on the exceptional points of a line: for the main row, and for the mask row with the
list at the repeated mask code's own distance. -/
def exc : ℕ := x.main.N + (x.mask.N + listMax (2 ^ x.s.C.a) x.s.dZ x.e)

/-- The bound on a list of pairs: the Johnson bound's. -/
def lst : ℕ := x.s.lstJ x.e

/-- The test on the place's numbers: sizes and radius (`Johnson.Top.H.stB`), one row a table, and
the two brackets. -/
def good : Bool :=
  Johnson.Top.H.stB x.s x.e && decide (x.s.h = 0) && decide (x.s.g = 0) &&
    x.main.ok (2 ^ x.s.C.a) (x.s.C.r + x.s.C.l - 1) x.e &&
    x.mask.ok (2 ^ x.s.C.a) (2 ^ (x.s.C.a - x.s.Z.a) * (x.s.Z.r + x.s.Z.l - 1)) x.e

variable {x}

theorem stageJ (h : x.good = true) : x.s.StageJ x.e := by
  simp only [good, Bool.and_eq_true] at h
  exact Johnson.Top.H.stJ_of h.1.1.1.1

theorem oneRow (h : x.good = true) : x.s.h = 0 ∧ x.s.g = 0 := by
  simp only [good, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2⟩

/-- **A yes of the test gives what the base case asks of its codes, at the place's two numbers.** -/
theorem baseCodes (h : x.good = true) : BaseCodes x.s x.e x.exc x.lst := by
  have hJ := stageJ h
  simp only [good, Bool.and_eq_true] at h
  exact baseCodes_le hJ (Br.le h.1.2) (Br.le h.2)

/-- The radius is below the stage's distance. -/
theorem radius_lt (h : x.good = true) : x.e < x.s.d := (stageJ h).joh.1

/-- The lists of the stage's tables, which the code switch into the stage asks: the Johnson bound's.
The statement on codes is not used. -/
theorem listIn (h : x.good = true) : x.s.cIn.ListAt x.e x.lst :=
  Sg.listJ_of (Sg.fit_cIn (stageJ h).sized) (stageJ h).joh

end LastPlace

end Johnson.Bridge

#print axioms Johnson.Bridge.baseCodes_at
#print axioms Johnson.Bridge.baseCodes_le
#print axioms Johnson.Bridge.maskCountWithin
#print axioms Johnson.Bridge.LastPlace.baseCodes
