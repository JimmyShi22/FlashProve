-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/KeySizedForward.lean: the sizes of a key's blocks, forward: from the parts'
values and the tests' answers to the whole's value.

OnBytes/Params/Fit/KeySizedParts.lean goes from a yes of the sizing of a key to what its parts
returned. This file goes the other way, for all lines, as OnBytes/Params/SizedForward.lean does for
a link and an entry: if no test refuses and each part returns a given value, the whole returns the
value that is put together of them. The use: at one set of lines each premise is a closed statement
that Lean's kernel can evaluate by itself.

Main names.
  opt_pass, opt_step, opt_ite_step   a test that does not refuse; a step that returns; one of two
                                     steps that returns.
  linSized_of       the test on the table: from its six tests, the iteration's answer, that all
                    groups serve, and the three tests' stages: linSized = linFinish of these.
  rangesX           the item "ranges" with its codes and stages filled in.
  rangesSized_of    the proof of the ranges: from its tests, the last block of the layout, the
                    solved test, the numbering, and Wf.admitted of the item.
  keySized_of       a key's sizes: from the table, the lines of the ranges, mask rows other than 0,
                    linSized and rangesSized.

Limits. That any premise holds is not said here. rangesX repeats a term of the sizing's text;
rangesSized_of proves that it is its term. Nothing on soundness. For proofs only; the program does
not import this file.

-/
import OnBytes.Params.Fit.KeySizedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params
open OnBytes.Plan

/-- A test that does not refuse. -/
theorem opt_pass {β : Type} {c : Prop} [Decidable c] {next : PUnit → Option β} (h : ¬ c) :
    (if c then (none : Option PUnit) >>= next else pure PUnit.unit >>= next) =
      next PUnit.unit := by
  rw [if_neg h]
  rfl

/-- A step that returns. -/
theorem opt_step {α β : Type} {x : Option α} {next : α → Option β} {a : α} (h : x = some a) :
    (x >>= next) = next a := by
  rw [h]
  rfl

/-- One of two steps, which returns. -/
theorem opt_ite_step {α β : Type} {c : Prop} [Decidable c] {x y : Option α}
    {next : α → Option β} {a : α} (h : (if c then x else y) = some a) :
    (if c then x >>= next else y >>= next) = next a := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢
    exact opt_step h
  · rw [if_neg hc] at h ⊢
    exact opt_step h

/-- A Bool that is false is not true. -/
theorem not_true_of {b : Bool} (h : b = false) : ¬ b = true := by
  rw [h]
  exact Bool.false_ne_true

/-- **The test on the table, forward.** -/
theorem linSized_of {s : Setting} {L : LinLines} {T : TableSize} {codes : Codes} {X Y Z : Sizing}
    {stU stO stW : List StageSize}
    (g1 : (L.own.logN != L.omega.logN || L.own.logL != L.omega.logL) = false)
    (g2 : (linSplit L && (L.folded.maskLogN != L.omega.maskLogN ||
      L.folded.maskLogL != L.omega.maskLogL)) = false)
    (g3 : ¬ T.code.n < T.code.dim)
    (g4 : tableAdmitted T (tableAnalysis s T) = true)
    (g5 : (linColumnsOf s L T == 0) = false)
    (g6 : (decide (40 < (indexShapeOf s T).v) ||
      decide ((indexShapeOf s T).code.ell ≤ 3 * (indexShapeOf s T).answers)) = false)
    (hT : linTurns s L (linGroupsOf s L T) 33 {} {} {} = some (X, Y, Z))
    (g7 : (!X.serves || (linSplit L && !Y.serves) || !Z.serves) = false)
    (hU : solveStages s (linScopeShared L) X.group X.t L.folded.stages
      = some stU)
    (hO : (if linSplit L then
        solveStages s (linScopeShared L) Y.group Y.t L.omega.stages
      else pure []) = some stO)
    (hW : solveStages s (linScopeOwn L) Z.group Z.t L.own.stages =
      some stW) :
    linSized s L T codes = linFinish s L T codes X Y Z stU stO stW := by
  unfold linSized
  extract_lets
  refine (opt_pass (not_true_of g1)).trans ?_
  refine (opt_pass (not_true_of g2)).trans ?_
  refine (opt_pass g3).trans ?_
  refine (opt_pass (not_true_of (by rw [g4]; rfl))).trans ?_
  refine (opt_pass (not_true_of g5)).trans ?_
  refine (opt_pass (not_true_of g6)).trans ?_
  refine (opt_step hT).trans ?_
  refine (opt_pass (not_true_of g7)).trans ?_
  refine (opt_step hU).trans ?_
  refine (opt_ite_step hO).trans ?_
  refine (opt_step hW).trans ?_
  rfl

/-- The item "ranges" with its codes and stages filled in. -/
def rangesX (s : Setting) (L : RangesLines) (row : Nat) (stages : List IoppStage)
    (first : IoppStage) : WfPublic :=
  { rangesX0 s L row with
    message := ⟨{ rangesO s L row with code := first.code, maskCode := first.maskCode }, 0⟩
    stages := stages }

set_option maxRecDepth 10000 in
/-- **The proof of the ranges, forward.** -/
theorem rangesSized_of {s : Setting} {L : RangesLines} {codes codes' : Codes} {last : Wf.Block}
    {test : TestSizes} {stages : List IoppStage} {first : IoppStage}
    (g1 : L.lookups.isEmpty = false)
    (g2 : (L.lookups.all fun l =>
      decide (1 ≤ l.mu) && decide (l.mu ≤ 6) && decide (l.live ≤ 2 ^ l.mu) &&
      decide (1 ≤ l.d) && decide (l.d ≤ 40) && !l.parts.isEmpty) = true)
    (g3 : ((Wf.layout L.lookups (2 ^ L.group.logL)).all fun b =>
      decide (2 ^ b.bits ≤ 2 ^ L.group.logL)) = true)
    (hl : (Wf.layout L.lookups (2 ^ L.group.logL)).getLast? = some last)
    (g4 : ¬ 2 ^ L.group.maskLogL ≤ s.samples)
    (g5 : ((rangesO s L last.row).maskRows == 0) = false)
    (ht : solveTest s .once L.group (rangesLoad s L last.row) id (rangesGroup s L last.row) =
      some test)
    (hio : ioppStages test.stages codes = (stages, codes'))
    (hf : stages.head? = some first)
    (ha : Wf.admitted codes' (rangesX s L last.row stages first) ⟨L.kCol, L.matrixRows⟩ = true) :
    rangesSized s L codes =
      some (⟨L, ⟨L.kCol, L.matrixRows⟩, rangesX s L last.row stages first, test,
        (L.lookups.map (·.parts.length)).sum⟩, codes') := by
  unfold rangesSized
  extract_lets
  refine (opt_pass (not_true_of g1)).trans ?_
  refine (opt_pass (not_true_of (by rw [g2]; rfl))).trans ?_
  refine (opt_pass (not_true_of (by rw [g3]; rfl))).trans ?_
  refine (opt_step hl).trans ?_
  refine (opt_pass g4).trans ?_
  have g5' : ¬ (Send.maskRowsFor (Wf.ownMasks (rangesX0 s L last.row) ⟨L.kCol, L.matrixRows⟩)
      (2 ^ L.group.maskLogL) s.samples == 0) = true := not_true_of g5
  refine (opt_pass g5').trans ?_
  refine (opt_step ht).trans ?_
  show (match ioppStages test.stages codes with
    | (stages, codes') => _) = _
  rw [hio]
  refine (opt_step hf).trans ?_
  have ha' : ¬ (!Wf.admitted codes' (rangesX s L last.row stages first)
      ⟨L.kCol, L.matrixRows⟩) = true := not_true_of (by rw [ha]; rfl)
  refine (opt_pass ha').trans ?_
  rfl

/-- **A key's sizes, forward.** -/
theorem keySized_of {l : Lines} {shape : Shape} {T : TableSize} {L : RangesLines}
    {once : LinSized} {codes1 codes : Codes} {ranges : RangesSized}
    (hT : deriveTable (settingOf l) l = some T)
    (hL : rangesLines { shape with kCol := l.blockLog } l.onceRanges l.rangesPart = some L)
    (g : (keyMaskRows l L == 0) = false)
    (ho : linSized (settingOf l) (linLines l L.matrixRows (keyMaskRows l L) true) T {} =
      some (once, codes1))
    (hr : rangesSized (settingOf l) L codes1 = some (ranges, codes)) :
    keySized l shape = some ⟨settingOf l, once, ranges, codes⟩ := by
  unfold keySized
  extract_lets
  refine (opt_step hT).trans ?_
  refine (opt_step hL).trans ?_
  refine (opt_pass (not_true_of g)).trans ?_
  refine (opt_step ho).trans ?_
  refine (opt_step hr).trans ?_
  rfl

end OnBytes.Params

#print axioms OnBytes.Params.linSized_of
#print axioms OnBytes.Params.rangesSized_of
#print axioms OnBytes.Params.keySized_of
