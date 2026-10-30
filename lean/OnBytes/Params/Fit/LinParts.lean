-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/LinParts.lean: what linSized returns, part by part.

linSized (OnBytes/Params/DeriveLin.lean) sizes the test on the table in one long text: the shapes
of five oracle messages and of three groups; then positions and random entries, all groups
together (linTurns); then the stages of three proximity tests (solveStages). This file unfolds the
text once and says of what it returns: from which calls its three tests come, which numbers of
rows its five oracle messages have, and which list of codes it hands on.

Main definitions: linMsg, linU, linOmega, linWRows, linW, linSplitMsg, linInput (the five oracle
messages as linSized's text forms them, before their codes are filled in); withBits (a line's group
with its two numbers of row variables); linSplit; SameRows (two shapes have the same numbers of
rows).
Main theorem: linSized_parts.

Left free under "there is", though the text fixes them: the two scopes; of the record of the three
groups: whether it is split (the text: linSplit L), its two scopes and its number of batched rows.

What is not claimed: that linSized returns. Nothing on soundness. For proofs only; the program
does not import this file.

-/
import OnBytes.Params.PlanListsChains

set_option autoImplicit false

namespace OnBytes.Params

/-- A step that refuses under a condition: the condition failed, and what follows returned. -/
theorem opt_guard_not {β : Type} {c : Prop} [Decidable c] {next : PUnit → Option β} {b : β}
    (h : (if c then (none : Option PUnit) >>= next else pure PUnit.unit >>= next) = some b) :
    ¬ c ∧ next PUnit.unit = some b := by
  split at h
  · cases h
  · rename_i hc
    exact ⟨hc, h⟩

/-- One of two steps: which value went on. -/
theorem opt_either_or {α β : Type} {c : Prop} [Decidable c] {x y : Option α}
    {next : α → Option β} {b : β} (h : (if c then x >>= next else y >>= next) = some b) :
    ∃ a, ((c ∧ x = some a) ∨ y = some a) ∧ next a = some b := by
  split at h
  · rename_i hc
    obtain ⟨a, e, h⟩ := opt_bind h
    exact ⟨a, Or.inl ⟨hc, e⟩, h⟩
  · obtain ⟨a, e, h⟩ := opt_bind h
    exact ⟨a, Or.inr e, h⟩

/-- An oracle message of the test on the table, before its codes are filled in. -/
def linMsg (s : Setting) (mainRows maskRows : Nat) : OracleShape :=
  { mainRows := mainRows, mainDeg := 3, maskRows := maskRows, answers := s.samples }

/-- The folded row, encoded anew. -/
def linU (s : Setting) (L : LinLines) (T : TableSize) : OracleShape :=
  linMsg s (linRowsOf (foldedEntries (indexShapeOf s T) + s.samples) (2 ^ L.folded.logL) true) 0

/-- Omega. -/
def linOmega (s : Setting) (L : LinLines) : OracleShape :=
  linMsg s (linRowsOf (L.matrixRows + s.samples) (2 ^ L.omega.logL) true) 0

/-- The main rows of W. -/
def linWRows (s : Setting) (L : LinLines) (T : TableSize) : Nat :=
  linRowsOf (2 ^ (L.kLo + (indexShapeOf s T).v)) (2 ^ L.omega.logL) true

/-- W. -/
def linW (s : Setting) (L : LinLines) (T : TableSize) : OracleShape :=
  linMsg s (linWRows s L T)
    (if linWRows s L T * 2 ^ L.omega.logL - 2 ^ (L.kLo + (indexShapeOf s T).v) < s.samples then 1
      else 0)

/-- The mask message of the shared chain's split. -/
def linSplitMsg (s : Setting) : OracleShape := linMsg s 0 1

/-- The request's mask message. -/
def linInput (s : Setting) (L : LinLines) : OracleShape := linMsg s 0 L.inputMaskRows

/-- A line's group with its two numbers of row variables. -/
def withBits (line : GroupLine) (b : Nat × Nat) : GroupSize :=
  { shapeOf line b.1 true with h := b.2 }

/-- The folded row and Omega differ in code. -/
def linSplit (L : LinLines) : Bool :=
  L.folded.logN != L.omega.logN || L.folded.logL != L.omega.logL

/-- Two shapes have the same numbers of rows. -/
def SameRows (a b : OracleShape) : Prop := a.mainRows = b.mainRows ∧ a.maskRows = b.maskRows

/-- **What linSized returns, part by part.** -/
theorem linSized_parts {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) :
    ∃ (G : LinGroups) (X Y Z : Sizing) (a b : Scope) (stU stO stW : List StageSize),
      G.foldedShape = withBits L.folded (linGroupBits
        (if linSplit L then [linU s L T, linSplitMsg s] else [linU s L T, linOmega s L])) ∧
      G.omegaShape = withBits L.omega (linGroupBits [linOmega s L, linSplitMsg s]) ∧
      G.ownShape = withBits L.own (linGroupBits [linInput s L, linW s L T, linOmega s L]) ∧
      linTurns s L G 33 {} {} {} = some (X, Y, Z) ∧
      solveStages s a X.group X.t L.folded.stages = some stU ∧
      ((G.split = true ∧
          solveStages s a Y.group Y.t L.omega.stages = some stO) ∨
        stO = []) ∧
      solveStages s b Z.group Z.t L.own.stages = some stW ∧
      x.folded = ⟨X.group, X.t, stU⟩ ∧ x.omega = ⟨Y.group, Y.t, stO⟩ ∧
      x.own = ⟨Z.group, Z.t, stW⟩ ∧ (indexShapeOf s T).v ≤ 40 ∧ x.shape.kLo = L.kLo ∧
      x.shape.matrixRows = L.matrixRows ∧ SameRows x.shape.fold.u (linU s L T) ∧
      SameRows x.shape.omega (linOmega s L) ∧ SameRows x.shape.w (linW s L T) ∧
      SameRows x.shape.sharedSplit (linSplitMsg s) ∧ SameRows x.input.shape (linInput s L) ∧
      c = (ioppStages stW (ioppStages stO (ioppStages stU codes).2).2).2 := by
  unfold linSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨hv, h⟩ := opt_guard_not h
  obtain ⟨⟨X, Y, Z⟩, hT, h⟩ := opt_bind h
  replace h := opt_guard h
  obtain ⟨stU, hU, h⟩ := opt_bind h
  obtain ⟨stO, hO, h⟩ := opt_either_or h
  obtain ⟨stW, hW, h⟩ := opt_bind h
  have hv' : (indexShapeOf s T).v ≤ 40 := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hv
    exact hv.1
  have hO' := hO.imp id fun e => (Option.some.inj e).symm
  repeat' split at h
  all_goals first
    | (cases h
       exact ⟨_, X, Y, Z, _, _, stU, stO, stW, rfl, rfl, rfl, hT, hU, hO', hW, rfl, rfl, rfl, hv',
         rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
         by simp only [*]⟩)
    | cases h

end OnBytes.Params
