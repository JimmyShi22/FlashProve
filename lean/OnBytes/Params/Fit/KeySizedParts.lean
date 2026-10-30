-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/KeySizedParts.lean: what Plan.keySized returns, part by part, with every argument
of every part named: so that at one set of lines and one shape each part is a closed statement that
Lean's kernel can evaluate by itself.

OnBytes/Params/Fit/LinParts.lean and SizedParts.lean take the sizing of a key apart, and leave some
arguments under "there is" (the record of the three groups but for its shapes, the two scopes, the
mask rows of the index-mask message, the load and the oracle message of the proof of the ranges).
Here they are named. The names repeat terms of the sizing's text; each law proves that they are its
terms.

Main names.
  linTurns_step     one turn of the iteration over the three groups, from the three sizings, where
                    the folded row and Omega have groups of their own.
  linGroupsOf       the record of the three groups as linSized's text forms it.
  linFinish         linSized's text behind its solving steps: the numbering of the codes and the
                    putting together.
  linSized_named    what linSized returns: the iteration at linGroupsOf; the three tests' stages;
                    linFinish of these.
  rangesX0, rangesO, rangesGroup, rangesLoad   the item, the oracle message, the group's shape and
                    the load as rangesSized's text forms them, from the last block's row.
  rangesSized_named what rangesSized returns: the last block of the layout; the test solved at
                    rangesLoad and rangesGroup; the numbering; the oracle message.
  keySized_named    what Plan.keySized returns: the table, the lines of the ranges, linSized at
                    Params.keyMaskRows mask rows, rangesSized at the codes that linSized hands on.

Limits. One direction: from a sizing that returns. Nothing at any number. Nothing on soundness.
linGroupsOf, linFinish, rangesX0 and their like are a second text of terms of the sizing; the laws
tie them to the first, and will have to be turned with it when the sizing's text is turned. The four
instances of decidable equality that are derived here reach whoever imports this file.
For proofs only; the program does not import this file.

-/
import OnBytes.Params.Fit.SizedParts
import OnBytes.Model.FitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params
open OnBytes.Plan

deriving instance DecidableEq for Sizing
deriving instance DecidableEq for TestSizes
deriving instance DecidableEq for LinLines
deriving instance DecidableEq for LinSized

/-! ## 1. The iteration over the three groups -/

/-- **One turn**, where the folded row and Omega have groups of their own, from what the three
sizings return. -/
theorem linTurns_step {s : Setting} {L : LinLines} {G : LinGroups} {fuel : Nat}
    {x y z x' y' z' : Sizing} (hs : G.split = true)
    (hx : sizeOne s G.foldedShape L.folded G.shared x.t (x.t + y.t) G.foldedRows x = some x')
    (hy : sizeOne s G.omegaShape L.omega G.shared (y.t + L.requests * z.t) (x.t + y.t)
      (1 + 2 * s.samples) y = some y')
    (hz : sizeOne s G.ownShape L.own G.request (y.t + L.requests * z.t) z.t (2 + 3 * s.samples) z =
      some z') :
    linTurns s L G (fuel + 1) x y z =
      if x'.t == x.t && y'.t == y.t && z'.t == z.t then some (x', y', z')
      else linTurns s L G fuel x' y' z' := by
  rw [linTurns]
  simp only [hs, ↓reduceIte, hx, hy, hz, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- One of two steps is taken, and what follows returns a value: the step that was taken returned a
value on which what follows returned that one. -/
theorem opt_ite_bind {α β : Type} {c : Prop} [Decidable c] {x y : Option α} {next : α → Option β}
    {b : β} (h : (if c then x >>= next else y >>= next) = some b) :
    ∃ a, (if c then x else y) = some a ∧ next a = some b := by
  split at h
  · rename_i hc
    obtain ⟨a, ha, h⟩ := opt_bind h
    exact ⟨a, by rw [if_pos hc]; exact ha, h⟩
  · rename_i hc
    obtain ⟨a, ha, h⟩ := opt_bind h
    exact ⟨a, by rw [if_neg hc]; exact ha, h⟩

/-! ## 2. The test on the table -/

/-- The scope of the batch's rounds. -/
def linScopeShared (L : LinLines) : Scope := if L.oneTime then .once else .shared

/-- The scope of a request's rounds. -/
def linScopeOwn (L : LinLines) : Scope := if L.oneTime then .once else .request

/-- The columns of the table that a test draws. -/
def linColumnsOf (s : Setting) (L : LinLines) (T : TableSize) : Nat :=
  scopePositions s (linScopeShared L)
    (if L.oneTime then (tableAnalysis s T).once.agree
      else (tableAnalysis s T).later.agree)

/-- The record of the three groups. -/
def linGroupsOf (s : Setting) (L : LinLines) (T : TableSize) : LinGroups :=
  { split := linSplit L, shared := linScopeShared L, request := linScopeOwn L
    foldedShape := withBits L.folded (linGroupBits
      (if linSplit L then [linU s L T, linSplitMsg s] else [linU s L T, linOmega s L]))
    omegaShape := withBits L.omega (linGroupBits [linOmega s L, linSplitMsg s])
    ownShape := withBits L.own (linGroupBits [linInput s L, linW s L T, linOmega s L])
    foldedRows := (indexShapeOf s T).answers + linColumnsOf s L T + 1 + 2 * s.samples }

/-- The batches that a stored copy of the table covers. -/
def linBatchesOf (s : Setting) (L : LinLines) (T : TableSize) : Nat :=
  if scopePositions s .once (tableAnalysis s T).once.agree < (indexShapeOf s T).code.r then
    ((indexShapeOf s T).code.r - scopePositions s .once (tableAnalysis s T).once.agree) /
      linColumnsOf s L T
  else 0

/-- linSized's text behind its solving steps. -/
def linFinish (s : Setting) (L : LinLines) (T : TableSize) (codes : Codes) (x y z : Sizing)
    (stU stO stW : List StageSize) : Option (LinSized × Codes) :=
  let (testU, codes1) := ioppStages stU codes
  let (testOmega, codes2) := ioppStages stO codes1
  let (testOwn, codes3) := ioppStages stW codes2
  match testU, testOwn with
  | gu :: _, gw :: _ =>
    let S : LinShape :=
      { fold := { index := indexShapeOf s T, u := canonical { linU s L T with code := gu.code },
                  rowsHigh := true, leafClass := 0, columns := linColumnsOf s L T }
        kLo := L.kLo
        matrixRows := L.matrixRows
        omega := canonical { linOmega s L with code := gw.code }
        w := canonical { linW s L T with code := gw.code, maskCode := gw.maskCode }
        omegaRowsHigh := true
        wRowsHigh := true
        sharedSplit := canonical { linSplitMsg s with maskCode := gu.maskCode }
        ownSplit := canonical {}
        omegaLeafClass := 1
        sharedSplitLeafClass := 2
        wLeafClass := 0
        ownSplitLeafClass := 3
        sharedMaskCode := gu.maskCode
        ownMaskCode := gw.maskCode
        masksAhead := true
        testU := testU
        testOmega := testOmega
        testOwn := testOwn
        testOwnOmega := []
        choice := ⟨true⟩ }
    some (⟨L, S, ⟨canonical { linInput s L with maskCode := gw.maskCode }, 0⟩, T,
      ⟨x.group, x.t, stU⟩, ⟨y.group, y.t, stO⟩, ⟨z.group, z.t, stW⟩, linBatchesOf s L T⟩, codes3)
  | _, _ => none

/-- **What linSized returns, every argument named.** -/
theorem linSized_named {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) :
    ∃ (X Y Z : Sizing) (stU stO stW : List StageSize),
      linTurns s L (linGroupsOf s L T) 33 {} {} {} = some (X, Y, Z) ∧
      solveStages s (linScopeShared L) X.group X.t L.folded.stages =
        some stU ∧
      (if linSplit L then
          solveStages s (linScopeShared L) Y.group Y.t L.omega.stages
        else pure []) = some stO ∧
      solveStages s (linScopeOwn L) Z.group Z.t L.own.stages =
        some stW ∧
      linFinish s L T codes X Y Z stU stO stW = some (x, c) := by
  unfold linSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨⟨X, Y, Z⟩, hT, h⟩ := opt_bind h
  replace h := opt_guard h
  obtain ⟨stU, hU, h⟩ := opt_bind h
  obtain ⟨stO, hO, h⟩ := opt_ite_bind h
  obtain ⟨stW, hW, h⟩ := opt_bind h
  exact ⟨X, Y, Z, stU, stO, stW, hT, hU, hO, hW, h⟩

/-! ## 3. The proof of the ranges -/

/-- The item "ranges" before its codes and stages are filled in. row: the last block's row. -/
def rangesX0 (s : Setting) (L : RangesLines) (row : Nat) : WfPublic :=
  { lookups := L.lookups
    message := ⟨{ mainRows := row + 1, mainDeg := 1, answers := s.samples }, 0⟩
    messageId := L.messageId
    stages := []
    choice := ⟨L.masksRide⟩ }

/-- The oracle message with the multiplicities, before its codes are filled in. -/
def rangesO (s : Setting) (L : RangesLines) (row : Nat) : OracleShape :=
  { (rangesX0 s L row).message.shape with
    maskRows := Send.maskRowsFor (Wf.ownMasks (rangesX0 s L row) ⟨L.kCol, L.matrixRows⟩)
      (2 ^ L.group.maskLogL) s.samples }

/-- The shape from which the group of that message is solved. -/
def rangesGroup (s : Setting) (L : RangesLines) (row : Nat) : GroupSize :=
  { shapeOf L.group (linGroupBits [rangesO s L row]).1 false with
    h := (linGroupBits [rangesO s L row]).2 }

/-- The load under which it is solved. -/
def rangesLoad (s : Setting) (L : RangesLines) (row : Nat) : GroupLoad :=
  { cubeBits := stageCubeBits (rangesGroup s L row), messages := 1,
    batchedRows := Wf.rowsBatched (rangesX0 s L row) ⟨L.kCol, L.matrixRows⟩ }

/-- **What rangesSized returns, every argument named.** -/
theorem rangesSized_named {s : Setting} {L : RangesLines} {codes c : Codes} {z : RangesSized}
    (h : rangesSized s L codes = some (z, c)) :
    ∃ (last : Wf.Block) (first : IoppStage),
      (Wf.layout L.lookups (2 ^ L.group.logL)).getLast? = some last ∧
      solveTest s .once L.group (rangesLoad s L last.row) id (rangesGroup s L last.row) =
        some z.test ∧
      ioppStages z.test.stages codes = (z.x.stages, c) ∧ z.x.stages.head? = some first ∧
      z.x.message =
        ⟨{ rangesO s L last.row with code := first.code, maskCode := first.maskCode }, 0⟩ ∧
      z.x.choice = ⟨L.masksRide⟩ ∧ z.pending = (L.lookups.map (·.parts.length)).sum := by
  unfold rangesSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨last, hl, h⟩ := opt_bind h
  replace h := opt_guard h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨test, ht, h⟩ := opt_bind h
  split at h
  rename_i stages codes' he
  obtain ⟨first, hf, h⟩ := opt_bind h
  try extract_lets at h
  obtain ⟨_, h⟩ := opt_guard_not h
  cases h
  exact ⟨last, first, hl, ht, he, hf, rfl, rfl, rfl⟩

/-! ## 4. A key's sizes -/

/-- **What Plan.keySized returns, every argument named.** -/
theorem keySized_named {l : Lines} {shape : Shape} {z : KeySized}
    (h : keySized l shape = some z) :
    ∃ (T : TableSize) (L : RangesLines) (codes1 : Codes),
      deriveTable (settingOf l) l = some T ∧
      rangesLines { shape with kCol := l.blockLog } l.onceRanges l.rangesPart = some L ∧
      linSized (settingOf l) (linLines l L.matrixRows (keyMaskRows l L) true) T {} =
        some (z.once, codes1) ∧
      rangesSized (settingOf l) L codes1 = some (z.ranges, z.codes) ∧ z.set = settingOf l := by
  unfold keySized at h
  extract_lets at h
  obtain ⟨T, hT, h⟩ := opt_bind h
  obtain ⟨L, hL, h⟩ := opt_bind h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨⟨once, c1⟩, ho, h⟩ := opt_bind h
  obtain ⟨⟨ranges, c2⟩, hr, h⟩ := opt_bind h
  cases h
  exact ⟨T, L, c1, hT, hL, ho, hr, rfl⟩

end OnBytes.Params

#print axioms OnBytes.Params.linTurns_step
#print axioms OnBytes.Params.linSized_named
#print axioms OnBytes.Params.rangesSized_named
#print axioms OnBytes.Params.keySized_named
