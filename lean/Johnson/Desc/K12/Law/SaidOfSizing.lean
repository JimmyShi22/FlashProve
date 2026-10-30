-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SaidOfSizing.lean: a group that the planner's sizing returns has the rule
johnson or named, or its m is 0.

Why. OneRadOfPlan.lean asks this of every stage. Every group of a proof file's four proximity tests
is a return of `sizeGroup` (OnBytes/Params/Group.lean), which lays the rule johnson.
This file walks the makers that call it.
Main names:
  `MSaid g`: the rule of g is johnson or named, or g.m = 0. No maker returns the rule named; it is
    let in because a plan says m under it too.
  `said_byRule`, `said_turn`, `said_stageFrom`, `said_groupFrom`, `said_later`, `said_stages`,
    `said_sizeOne`, `said_linTurns`: `MSaid` at what each maker returns.
Limits: on the planner's makers alone: no plan, no protocol. Nothing on soundness. Nothing on
hiding.

-/
import OnBytes.Params.ConfigureLaws
import OnBytes.Params.DeriveReq

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params

/-- A plan says this group's m, or the m is 0. -/
def MSaid (g : GroupSize) : Prop := g.rule = .johnson ∨ g.rule = .named ∨ g.m = 0

theorem said_byRule (s : Setting) (sc : Scope) (shape : GroupSize) (load : GroupLoad) : MSaid (sizeGroup s sc shape load) := by
  exact Or.inl rfl

theorem said_turn {s : Setting} {sc : Scope} {load : GroupLoad} {shape : GroupSize}
    {a b t t2 : Nat} {g : GroupSize} (h : turn s sc load shape a b t = .settled g t2) :
    MSaid g := by
  unfold turn at h
  extract_lets g0 sized serves an t3 at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · injection h with h1 _
        rw [← h1]
        exact said_byRule _ _ _ _
      · cases h

theorem said_stageFrom {s : Setting} {sc : Scope} {bR : Nat} {shape : GroupSize} :
    ∀ (fuel t : Nat) (x : Solved), solveStageFrom s sc bR shape fuel t = some x →
      MSaid x.group
  | 0, _, _, h => by
    unfold solveStageFrom at h
    cases h
  | fuel + 1, t, x, h => by
    unfold solveStageFrom at h
    dsimp only at h
    split at h
    · cases h
    · rename_i g _ ht
      cases h
      exact said_turn ht
    · exact said_stageFrom fuel _ x h

theorem said_groupFrom {s : Setting} {sc : Scope} {load : GroupLoad}
    {draws : Nat → Nat} {shape : GroupSize} :
    ∀ (fuel t : Nat) (x : Solved), solveGroupFrom s sc load draws shape fuel t = some x →
      MSaid x.group
  | 0, _, _, h => by
    unfold solveGroupFrom at h
    cases h
  | fuel + 1, t, x, h => by
    unfold solveGroupFrom at h
    split at h
    · cases h
    · rename_i g t2 ht
      split at h
      · cases h
      · cases h
        exact said_turn ht
    · exact said_groupFrom fuel _ x h

theorem said_later {s : Setting} {sc : Scope} :
    ∀ (lines : List StageLine) (o : GroupSize) (l : List StageSize),
      solveLater s sc o lines = some l → ∀ y ∈ l, MSaid y.g
  | [], _, l, h => by
    unfold solveLater at h
    cases h
    intro y hy
    cases hy
  | c :: rest, o, l, h => by
    unfold solveLater at h
    extract_lets at h
    repeat' split at h
    all_goals
      first
      | cases h
      | (rename_i x hx
         obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.1 h
         intro y hy
         rcases List.mem_cons.1 hy with rfl | hy
         · exact said_stageFrom _ _ _ hx
         · exact said_later rest _ l' hl' y hy)

theorem said_stages {s : Setting} {sc : Scope} {first : GroupSize} {firstT : Nat}
    {choice : List StageLine} {l : List StageSize} (h0 : MSaid first)
    (h : solveStages s sc first firstT choice = some l) : ∀ y ∈ l, MSaid y.g := by
  unfold solveStages at h
  split at h
  · cases h
  · obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.1 h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h0
    · exact said_later _ _ l' hl' y hy

theorem said_sizeOne {s : Setting} {shape : GroupSize} {line : GroupLine} {sc : Scope}
    {a b rows : Nat} {before x : Sizing} (h : sizeOne s shape line sc a b rows before = some x) :
    MSaid x.group := by
  unfold sizeOne at h
  extract_lets g0 rule load sized serves more at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h1
      rw [← h1]
      exact said_byRule _ _ _ _

theorem either_or {α β : Type} {c : Prop} [Decidable c] {x y : Option α} {next : α → Option β}
    {b : β} (h : (if c then x >>= next else y >>= next) = some b) :
    ∃ a, (x = some a ∨ y = some a) ∧ next a = some b := by
  split at h
  · obtain ⟨a, e, h⟩ := opt_bind h
    exact ⟨a, Or.inl e, h⟩
  · obtain ⟨a, e, h⟩ := opt_bind h
    exact ⟨a, Or.inr e, h⟩

theorem said_linTurns {s : Setting} {L : LinLines} {G : LinGroups} :
    ∀ (fuel : Nat) (x y z : Sizing) (r : Sizing × Sizing × Sizing), MSaid y.group →
      linTurns s L G fuel x y z = some r →
      MSaid r.1.group ∧ MSaid r.2.1.group ∧ MSaid r.2.2.group
  | 0, _, _, _, _, _, h => by
    unfold linTurns at h
    cases h
  | fuel + 1, x, y, z, r, hy, h => by
    unfold linTurns at h
    extract_lets at h
    obtain ⟨x', hx', h⟩ := opt_bind h
    obtain ⟨y', hy', h⟩ := either_or h
    obtain ⟨z', hz', h⟩ := opt_bind h
    have sy : MSaid y'.group := by
      rcases hy' with e | e
      · exact said_sizeOne e
      · cases e
        exact hy
    split at h
    · cases h
      exact ⟨said_sizeOne hx', sy, said_sizeOne hz'⟩
    · exact said_linTurns fuel x' y' z' r sy h

end H2K.Pub

#print axioms H2K.Pub.said_stages
#print axioms H2K.Pub.said_linTurns
#print axioms H2K.Pub.said_groupFrom
