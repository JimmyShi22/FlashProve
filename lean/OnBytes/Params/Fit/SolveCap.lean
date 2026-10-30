-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/SolveCap.lean: every group that the derivation solves has, at both its codes, a
message that fits the code's length; so where the lengths are the parameter file's, which its reader
holds at or below 2 ^ 32, no message has more than 2 ^ 32 entries.

The routines that size a group ("turn", OnBytes/Params/Group.lean; "sizeOne",
OnBytes/Params/DeriveLin.lean) set the random entries of the two codes of a shape, refuse where a
code's length is below its dimension, and then fix the distance ("sizeGroup"), which changes the
fields m and rule alone. So what they return has the shape's lengths, messages and row variables,
and at both codes: message and random entries together are at most the length.

Main names.
 - Solves shape g: g has shape's logN and ell at both codes, shape's k, h and slots, and at both
   codes dim ≤ n.
 - CodeFit c: logN ≤ 32 and ell ≤ 2 ^ 32. GroupFit g: both codes of g.
 - turn_settled, solveGroup_solves, solveStage_solves, sizeOne_solves, linTurns_solves: Solves, of
   what these routines return (of linTurns' middle group: where the row is split).
 - fit_of_solves: Solves shape g and shape's two logN ≤ 32 give GroupFit g.
 - solveLater_fit, **solveStages_fit**: under the ranges of the stages' lines (StageCap,
   OnBytes/Params/Fit/LinesCap.lean) every later stage's group is GroupFit with k ≤ 8 and h ≤ 8;
   every stage that solveStages returns is the group that went in or such a later stage.

Limits. Nothing on the formulas for a later stage's message lengths: the bound comes from the
refusal alone. Nothing on distances, positions or whether a group's rounds hold. The program does
not import this file.

-/
import OnBytes.Params.ConfigureLaws
import OnBytes.Params.Fit.LinesCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- g is shape with its random entries set and its distance fixed, and fits its codes' lengths. -/
structure Solves (shape g : GroupSize) : Prop where
  mainN : g.main.logN = shape.main.logN
  mainL : g.main.ell = shape.main.ell
  maskN : g.mask.logN = shape.mask.logN
  maskL : g.mask.ell = shape.mask.ell
  k : g.k = shape.k
  h : g.h = shape.h
  slots : g.slots = shape.slots
  mainFit : g.main.dim ≤ g.main.n
  maskFit : g.mask.dim ≤ g.mask.n

/-- A code of a length of at most 2 ^ 32 with a message of at most 2 ^ 32 entries. -/
def CodeFit (c : CodeSize) : Prop := c.logN ≤ 32 ∧ c.ell ≤ 2 ^ 32

/-- Both codes of a group. -/
def GroupFit (g : GroupSize) : Prop := CodeFit g.main ∧ CodeFit g.mask

theorem codeFit_of_dim {c : CodeSize} (hN : c.logN ≤ 32) (hd : c.dim ≤ c.n) : CodeFit c := by
  unfold CodeSize.dim CodeSize.n at hd
  have hp : 2 ^ c.logN ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hN
  exact ⟨hN, by omega⟩

/-- Where the shape's lengths are at most 2 ^ 32. -/
theorem fit_of_solves {shape g : GroupSize} (S : Solves shape g) (hN : shape.main.logN ≤ 32)
    (hZ : shape.mask.logN ≤ 32) : GroupFit g :=
  ⟨codeFit_of_dim (by rw [S.mainN]; exact hN) S.mainFit,
    codeFit_of_dim (by rw [S.maskN]; exact hZ) S.maskFit⟩

/-- Fixing the distance changes m and rule alone. -/
theorem sizeGroup_keeps (s : Setting) (scope : Scope) (g : GroupSize) (load : GroupLoad) :
    (sizeGroup s scope g load).main = g.main ∧
      (sizeGroup s scope g load).mask = g.mask ∧
      (sizeGroup s scope g load).k = g.k ∧ (sizeGroup s scope g load).h = g.h ∧
      (sizeGroup s scope g load).slots = g.slots := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The group with its random entries set, behind the refusal, with its distance fixed. -/
theorem solves_byRule (s : Setting) (scope : Scope) (shape : GroupSize) (load : GroupLoad)
    (mr zr : Nat)
    (hc : ¬ (decide (({ shape.main with r := mr } : CodeSize).n <
        ({ shape.main with r := mr } : CodeSize).dim) ||
      decide (({ shape.mask with r := zr } : CodeSize).n <
        ({ shape.mask with r := zr } : CodeSize).dim)) = true) :
    Solves shape (sizeGroup s scope
      { shape with main := { shape.main with r := mr }, mask := { shape.mask with r := zr } }
      load) := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := sizeGroup_keeps s scope
    { shape with main := { shape.main with r := mr }, mask := { shape.mask with r := zr } }
    load
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hc
  refine ⟨?_, ?_, ?_, ?_, k3, k4, k5, ?_, ?_⟩
  · rw [k1]
  · rw [k1]
  · rw [k2]
  · rw [k2]
  · rw [k1]
    exact hc.1
  · rw [k2]
    exact hc.2

/-- The two arms of a test. -/
theorem ite_cases {α : Type} {c : Prop} [Decidable c] {x y z : α} (h : (if c then x else y) = z) :
    (c ∧ x = z) ∨ (¬ c ∧ y = z) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact .inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact .inr ⟨hc, h⟩

/-- What a turn settles. -/
theorem turn_settled {s : Setting} {scope : Scope} {load : GroupLoad}
    {shape g : GroupSize} {mr zr t t2 : Nat}
    (h : turn s scope load shape mr zr t = .settled g t2) : Solves shape g := by
  unfold turn at h
  rcases ite_cases h with ⟨_, h⟩ | ⟨hc, h⟩
  · cases h
  · rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
    · cases h
    · rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
      · cases h
        exact solves_byRule s scope shape load mr zr hc
      · cases h

theorem solveGroupFrom_solves {s : Setting} {scope : Scope} {load : GroupLoad}
    {draws : Nat → Nat} {shape : GroupSize} : ∀ (fuel t : Nat) (x : Solved),
    solveGroupFrom s scope load draws shape fuel t = some x → Solves shape x.group := by
  intro fuel
  induction fuel with
  | zero =>
    intro t x h
    cases h
  | succ n ih =>
    intro t x h
    unfold solveGroupFrom at h
    split at h
    · cases h
    · rename_i g t2 ht
      split at h
      · cases h
      · cases h
        exact turn_settled ht
    · exact ih _ x h

/-- What solveGroup returns. -/
theorem solveGroup_solves {s : Setting} {scope : Scope} {load : GroupLoad}
    {draws : Nat → Nat} {shape : GroupSize} {t0 : Nat} {x : Solved}
    (h : solveGroup s scope load draws shape t0 = some x) : Solves shape x.group :=
  solveGroupFrom_solves 32 t0 x h

/-- What the turns of a later stage return. -/
theorem solveStage_solves {s : Setting} {scope : Scope} {beforeR : Nat}
    {shape : GroupSize} : ∀ (fuel t : Nat) (x : Solved),
    solveStageFrom s scope beforeR shape fuel t = some x → Solves shape x.group := by
  intro fuel
  induction fuel with
  | zero =>
    intro t x h
    cases h
  | succ n ih =>
    intro t x h
    unfold solveStageFrom at h
    dsimp only at h
    split at h
    · cases h
    · rename_i g t2 ht
      cases h
      exact turn_settled ht
    · exact ih _ x h

/-- What sizeOne returns. -/
theorem sizeOne_solves {s : Setting} {shape : GroupSize} {line : GroupLine} {scope : Scope}
    {mainDraws maskDraws rows : Nat} {before y : Sizing}
    (h : sizeOne s shape line scope mainDraws maskDraws rows before = some y) :
    Solves shape y.group := by
  unfold sizeOne at h
  rcases ite_cases h with ⟨_, h⟩ | ⟨hc, h⟩
  · cases h
  · rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
    · cases h
    · cases h
      exact solves_byRule s scope shape _ _ _ hc

/-- What the turns over the three groups of the test on the table return. -/
theorem linTurns_solves {s : Setting} {L : LinLines} {G : LinGroups} :
    ∀ (fuel : Nat) (x y z : Sizing) (r : Sizing × Sizing × Sizing),
    linTurns s L G fuel x y z = some r →
    Solves G.foldedShape r.1.group ∧ (G.split = true → Solves G.omegaShape r.2.1.group) ∧
      Solves G.ownShape r.2.2.group := by
  intro fuel
  induction fuel with
  | zero =>
    intro x y z r h
    cases h
  | succ n ih =>
    intro x y z r h
    unfold linTurns at h
    dsimp only at h
    obtain ⟨x', hx, h⟩ := opt_bind h
    rcases ite_cases h with ⟨hs, h⟩ | ⟨hs, h⟩
    · obtain ⟨y', hy, h⟩ := opt_bind h
      obtain ⟨z', hz, h⟩ := opt_bind h
      rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
      · cases h
        exact ⟨sizeOne_solves hx, fun _ => sizeOne_solves hy, sizeOne_solves hz⟩
      · exact ih x' y' z' r h
    · obtain ⟨y', _, h⟩ := opt_bind h
      obtain ⟨z', hz, h⟩ := opt_bind h
      rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
      · cases h
        exact ⟨sizeOne_solves hx, fun hs' => absurd hs' hs, sizeOne_solves hz⟩
      · exact ih x' y' z' r h

/-- **The later stages.** -/
theorem solveLater_fit {s : Setting} {scope : Scope} :
    ∀ (choice : List StageLine) (o : GroupSize) (st : List StageSize),
    (∀ c ∈ choice, StageCap c) → solveLater s scope o choice = some st →
    ∀ y ∈ st, GroupFit y.g ∧ y.g.k ≤ 8 ∧ y.g.h ≤ 8 := by
  intro choice
  induction choice with
  | nil =>
    intro o st _ h y hy
    unfold solveLater at h
    cases h
    exact (List.not_mem_nil hy).elim
  | cons c rest ih =>
    intro o st hc h y hy
    have C := hc c List.mem_cons_self
    unfold solveLater at h
    rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
    · cases h
    · extract_lets carried ownFold maskEll shape at h
      split at h
      · cases h
      · rename_i x hx
        cases hr : solveLater s scope x.group rest with
        | none =>
          rw [hr] at h
          cases h
        | some st' =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          have S := solveStage_solves 32 0 x hx
          rcases List.mem_cons.1 hy with rfl | hy'
          · refine ⟨fit_of_solves S C.logN (Nat.le_trans C.mask C.logN), ?_, ?_⟩
            · show x.group.k ≤ 8
              rw [S.k]
              exact C.k
            · show x.group.h ≤ 8
              rw [S.h]
              exact Nat.le_trans C.h C.k
          · exact ih x.group st' (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')) hr y hy'

/-- **The stages of a proximity test**: every stage is the group that went in, or fits. -/
theorem solveStages_fit {s : Setting} {scope : Scope} {first : GroupSize}
    {firstT : Nat} {choice : List StageLine} {st : List StageSize}
    (hc : ∀ c ∈ choice, StageCap c)
    (h : solveStages s scope first firstT choice = some st) :
    ∀ y ∈ st, y.g = first ∨ (GroupFit y.g ∧ y.g.k ≤ 8 ∧ y.g.h ≤ 8) := by
  unfold solveStages at h
  rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  · cases hr : solveLater s scope first choice with
    | none =>
      rw [hr] at h
      cases h
    | some st' =>
      rw [hr] at h
      obtain rfl := Option.some.inj h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact .inl rfl
      · exact .inr (solveLater_fit choice first st' hc hr y hy')

end OnBytes.Params

#print axioms OnBytes.Params.turn_settled
#print axioms OnBytes.Params.solveGroup_solves
#print axioms OnBytes.Params.sizeOne_solves
#print axioms OnBytes.Params.linTurns_solves
#print axioms OnBytes.Params.solveLater_fit
#print axioms OnBytes.Params.solveStages_fit
