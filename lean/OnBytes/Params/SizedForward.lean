-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/SizedForward.lean: the sizes of a proximity test, of a link and of an entry, forward:
from the parts' values to the whole's value.

OnBytes/Params/EntrySizedLaws.lean goes from a yes of sizing
routines to what their parts returned. This file goes the other way, for all lines: if each part
returns a given value, the whole returns the value that is put together of them. `solveLater_step`:
one step of `solveLater`: where a stage's line passes the four tests and the stage is solved as x
from the shape `laterShape`, the later stages are the stage `laterStage` before those that follow
x's group. `solveStages_of`, `solveTest_of`: a test's stages and sizes from its solved group and
later stages. `linkSized_of`: a link's sizes from the table's admission, the two numbers of columns,
neither 0, the two tests on the table's shape, the solved test and the numbering of its stages.
`entrySized_of`: an entry's sizes from the table, the link and the finished plan.
`finishHeld_holds`: a plan that `finishHeld` returns holds in the planner's reckoning. The use: at
one set of lines each part is a closed statement that Lean's kernel can evaluate by itself. Under
the Johnson radius, at the lines of OnBytes/Params/EntryStagesRecord.lean and under a limit of 24 GB
of address space, Lean ran out of memory on `decide +kernel` for `solveTest` and for `entrySized` in
one piece. That file, which has the kernel evaluate the parts one after the other, compiled in less
than 10 GB.

Main definitions: `laterMaskEll`, `laterShape`, `laterStage`.
Main theorems: `solveLater_step`, `solveStages_of`, `solveTest_of`, `linkSized_of`,
`finishHeld_holds`, `entrySized_of`.
What is not claimed: that any part returns a value: these are hypotheses. `laterMaskEll`,
`laterShape` and `laterStage` repeat terms of `solveLater`'s text; `solveLater_step` proves that
they are its terms. Nothing for a key's or a proof's sizes. The figures on memory are of four runs,
on one machine. For proofs only; the program, that is the Lean port built from OnBytes/, does not
import this file.

-/
import OnBytes.Params.EntrySizedLaws

set_option autoImplicit false

namespace OnBytes.Params

/-- The length of a mask message of the stage that follows the group o under the line c. -/
def laterMaskEll (s : Setting) (o : GroupSize) (c : StageLine) : Nat :=
  max (pow2AtLeast ((2 * o.mask.ell + o.main.r * o.slots + 2 * o.mask.r + s.samples + 2 ^ c.h - 1) /
      2 ^ c.h))
    (pow2AtLeast (if c.k != 0 then 2 * c.k + 1 - c.h else 1))

/-- The shape from which that stage is solved. -/
def laterShape (s : Setting) (o : GroupSize) (c : StageLine) : GroupSize :=
  { main := { logN := c.logN, ell := o.main.ell * o.slots / 2 ^ c.k, overE := true }
    mask := { logN := c.maskLogN, ell := laterMaskEll s o c, overE := true }
    k := c.k
    h := c.h }

/-- The stage that is made of what was solved. -/
def laterStage (s : Setting) (o : GroupSize) (c : StageLine) (x : Solved) : StageSize :=
  ⟨x.group, x.t,
    laterMaskEll s o c * 2 ^ c.h - (2 * o.mask.ell + o.main.r * o.slots + 2 * o.mask.r)⟩

/-- **One step of `solveLater`**: where the line passes the four tests and the stage is solved as x,
the later stages, if any follow, are x's stage before the stages that follow x's group. -/
theorem solveLater_step {s : Setting} {scope : Scope} {o : GroupSize}
    {c : StageLine} {rest : List StageLine} {x : Solved}
    (hc : (c.k < c.h || 32 < c.k || (if rest.isEmpty then c.k != 0 else c.k == 0) ||
      o.main.ell * o.slots % 2 ^ c.k != 0) = false)
    (hx : solveStageFrom s scope o.main.r (laterShape s o c) 32 0 = some x) :
    solveLater s scope o (c :: rest) =
      (solveLater s scope x.group rest).map (laterStage s o c x :: ·) := by
  rw [solveLater]
  simp only [hc, Bool.false_eq_true, if_false]
  have e : solveStageFrom s scope o.main.r
      { main := { logN := c.logN, ell := o.main.ell * o.slots / 2 ^ c.k, overE := true }
        mask := { logN := c.maskLogN,
                  ell := max (pow2AtLeast ((2 * o.mask.ell + o.main.r * o.slots + 2 * o.mask.r +
                    s.samples + 2 ^ c.h - 1) / 2 ^ c.h))
                    (pow2AtLeast (if c.k != 0 then 2 * c.k + 1 - c.h else 1)), overE := true }
        k := c.k
        h := c.h } 32 0 = some x := hx
  rw [e]
  rfl

/-- The stages of a test, from its later stages. -/
theorem solveStages_of {s : Setting} {scope : Scope} {first : GroupSize} {firstT : Nat}
    {choice : List StageLine} {later : List StageSize}
    (h0 : (choice.isEmpty || first.k == 0) = false)
    (hl : solveLater s scope first choice = some later) :
    solveStages s scope first firstT choice = some (⟨first, firstT, 0⟩ :: later) := by
  unfold solveStages
  rw [h0, hl]
  rfl

/-- A test's sizes, from its solved group and its stages. -/
theorem solveTest_of {s : Setting} {scope : Scope} {l : GroupLine} {load : GroupLoad}
    {draws : Nat → Nat} {shape : GroupSize} {x : Solved} {st : List StageSize}
    (hg : solveGroup s scope load draws shape = some x)
    (hs : solveStages s scope x.group x.t l.stages = some st) :
    solveTest s scope l load draws shape = some ⟨x.group, x.t, st⟩ := by
  unfold solveTest
  simp only [hg, hs, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- **A link's sizes, forward**: from the table's admission, the two numbers of columns, neither 0,
the two tests on the table's shape, the solved test and the numbering of its stages. -/
theorem linkSized_of {s : Setting} {l : Lines} {T : TableSize} {codes codes' : Codes}
    {first further : Nat} {x : TestSizes} {g : IoppStage} {later : List IoppStage}
    (hA : tableAdmitted T (tableAnalysis s T) = true)
    (h1 : scopePositions s .once (tableAnalysis s T).later.agree = first)
    (h2 : scopePositions s .once (tableAnalysis s T).once.agree = further)
    (h0 : (first == 0 || further == 0) = false)
    (hI : (decide (40 < (indexShapeOf s T).v) ||
      decide ((indexShapeOf s T).code.ell ≤ 3 * (indexShapeOf s T).answers)) = false)
    (hx : solveTest s .once l.onceFolded
      { cubeBits := stageCubeBits (shapeOf l.onceFolded (1 + clog2 (linRowsOf
          (foldedEntries (indexShapeOf s T) + s.samples) (2 ^ l.onceFolded.logL) true)) true),
        messages := 2,
        batchedRows := 2 * (indexShapeOf s T).answers + first + further + 1 + 2 * s.samples } id
      (shapeOf l.onceFolded (1 + clog2 (linRowsOf
        (foldedEntries (indexShapeOf s T) + s.samples) (2 ^ l.onceFolded.logL) true)) true) =
        some x)
    (hio : ioppStages x.stages codes = (g :: later, codes')) :
    linkSized s l T codes =
      some (⟨{ table := indexShapeOf s T, columnsFirst := first, columnsFurther := further,
               code := g.code, maskCode := g.maskCode,
               rows := linRowsOf (foldedEntries (indexShapeOf s T) + s.samples)
                 (2 ^ l.onceFolded.logL) true,
               rowsHigh := true, leafClass := 0, masksAhead := true, later := later,
               choice := ⟨true⟩ }, T, x⟩, codes') := by
  unfold linkSized
  simp only [hA, h1, h2, h0, hI, hx, hio, Bool.not_true, Bool.false_eq_true, if_false,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- A plan that `finishHeld` returns holds in the planner's reckoning. -/
theorem finishHeld_holds {s : Setting} {scope : Scope} {x : Planning Unit} {P : Planned}
    (h : finishHeld s scope x = .ok P) : P.holds = true := by
  unfold finishHeld at h
  cases hf : finish s scope x with
  | error e =>
    rw [hf] at h
    cases h
  | ok p =>
    rw [hf] at h
    have h' : (if p.holds then (pure p : Except String Planned) else throw notAdmitted) =
        .ok P := h
    split at h'
    · rename_i hh
      cases h'
      exact hh
    · cases h'

/-- **An entry's sizes, forward.** -/
theorem entrySized_of {l : Lines} {T : TableSize} {x : LinkSized} {codes : Codes} {P : Planned}
    (hT : deriveTable (settingOf l) l = some T)
    (hL : linkSized (settingOf l) l T {} = some (x, codes))
    (hP : finishHeld (settingOf l) .once (linkPlan x) = .ok P) :
    entrySized l = .ok (x, codes, P) := by
  unfold entrySized
  simp only [hT, orRefuse, bind, Except.bind, hL, hP, pure, Except.pure]

end OnBytes.Params
