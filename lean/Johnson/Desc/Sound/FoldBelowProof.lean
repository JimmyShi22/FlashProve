-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldBelowProof.lean: the test in front of the fold is the blocks' own tests: the
proof of `FoldBelow` (Johnson/Desc/Sound/ChainRule.lean).

How. A block `below b` steps as b does where its rounds and the columns that it takes pass the test,
and refuses elsewhere (`step_below`: as options: the words of a refusal are dropped). By induction
on the list of blocks the fold of the blocks `below b`, at its end, is the fold of the blocks b with
the test on all rounds and columns in front (`endOk_below`). `Block.step` hands `decide` its rounds
without the sealed digest, which the test does not read (`okViewW_noDigest`).

Limits: those of Johnson/Desc/Sound/ChainRule.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldLawBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

variable {S Cl : Type}

theorem and4 (a b c d : Bool) : ((a && b) && (c && d)) = ((a && c) && (b && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The test at rounds and columns in a row. -/
theorem okViewW_app (R₁ R₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) :
    viewWordsBelowPrime ⟨R₁ ++ R₂, c₁ ++ c₂⟩ = (viewWordsBelowPrime ⟨R₁, c₁⟩ && viewWordsBelowPrime ⟨R₂, c₂⟩) := by
  simp only [viewWordsBelowPrime, List.all_append]
  exact and4 _ _ _ _

/-- The test looks at a column's words alone. -/
theorem okViewW_cols (R : List Fmt.RoundView) (c : List OpenedColumn) :
    viewWordsBelowPrime ⟨R, (c.map fun x => (x.2.1, x.2.2)).map fun x => (0, x.1, x.2)⟩ = viewWordsBelowPrime ⟨R, c⟩ := by
  simp only [viewWordsBelowPrime, List.all_map]
  rfl

/-- The test does not read the sealed digest. -/
theorem okViewW_noDigest (R : List Fmt.RoundView) (c : List OpenedColumn) :
    viewWordsBelowPrime ⟨R.map noDigest, c⟩ = viewWordsBelowPrime ⟨R, c⟩ := by
  simp only [viewWordsBelowPrime, List.all_map]
  rfl

/-- Columns laid into groups, and the groups in a row again. -/
theorem regroup_flat : ∀ (ns : List Nat) (cols : List OpenedColumn),
    (regroup ns cols).flatMap id = (cols.take ns.sum).map fun c => (c.2.1, c.2.2)
  | [], cols => by simp [regroup]
  | n :: ns, cols => by
    simp only [regroup, List.flatMap_cons, id, regroup_flat ns (cols.drop n), List.sum_cons]
    rw [← List.map_append, List.take_add]

theorem sum_lengths {α : Type} : ∀ g : List (List α), (g.map (·.length)).sum = (g.flatMap id).length
  | [] => rfl
  | x :: g => by
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, id, List.length_append,
      sum_lengths g]

theorem ite_swap {α β : Type} (A B O : Bool) (D : Except String α) (f : α → Except String β)
    (e₁ e₂ e₃ : String) :
    (if A = true then (if B = true then ((if O = true then D else .error e₃) >>= f)
      else .error e₂) else .error e₁ : Except String β).toOption =
    if O = true then
      (if A = true then (if B = true then D >>= f else .error e₂) else .error e₁ :
        Except String β).toOption
    else none := by
  cases A <;> cases B <;> cases O <;> rfl

/-- A block `below b` steps as b does where its rounds and the columns that it takes pass the test,
and refuses elsewhere. -/
theorem step_below (ft : Nat) (b : Block S Cl) (s : S) (R : List Fmt.RoundView) (c : List OpenedColumn) :
    ((below b).step ft s R c).toOption =
      if viewWordsBelowPrime ⟨R, c.take ((b.reads ft (R.map (·.drawn))).flatMap id).length⟩ then
        (b.step ft s R c).toOption
      else none := by
  have e : ∀ g : List (List (Nat × Nat × Nat)),
      viewWordsBelowPrime ⟨R.map noDigest,
                    ((regroup (g.map (·.length)) (c.take (g.flatMap id).length)).flatMap id).map
                      fun x => (0, x.1, x.2)⟩ = viewWordsBelowPrime ⟨R, c.take (g.flatMap id).length⟩ := by
    intro g
    rw [okViewW_noDigest, regroup_flat, sum_lengths, List.take_take, Nat.min_self, okViewW_cols]
  simp only [Block.step_eq, below, Block.reads, e]
  exact ite_swap _ _ _ _ _ _ _ _

theorem ite_none {α : Type} (c : Bool) : (if c = true then (none : Option α) else none) = none := by
  cases c <;> rfl

theorem error_of_none {α : Type} (x : Except String α) (h : x.toOption = none) :
    ∃ e, x = .error e := by
  cases x with
  | error e => exact ⟨e, rfl⟩
  | ok a => cases h

theorem ok_of_some {α : Type} (x : Except String α) (a : α) (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok y =>
    have h' : some y = some a := h
    cases h'
    rfl

/-- The fold of the blocks `below b`, at its end. -/
theorem endOk_below (ft : Nat) : ∀ (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cs : List OpenedColumn),
    endOk (foldBlocks ft (bs.map below) s rs cs) =
      if viewWordsBelowPrime ⟨rs, cs⟩ then endOk (foldBlocks ft bs s rs cs) else none
  | [], s, rs, cs => by
    show endOk (.ok (s, rs, cs)) = if viewWordsBelowPrime ⟨rs, cs⟩ then endOk (.ok (s, rs, cs)) else none
    cases rs with
    | nil =>
      cases cs with
      | nil => rfl
      | cons _ _ => exact (ite_none _).symm
    | cons _ _ => exact (ite_none _).symm
  | b :: bs, s, rs, cs => by
    rw [List.map_cons]
    by_cases hl : b.rounds.length ≤ rs.length
    · -- the stretch is there: cut the rounds
      have hlen : (rs.take b.rounds.length).length = b.rounds.length := by
        rw [List.length_take]
        omega
      have hrs : rs = rs.take b.rounds.length ++ rs.drop b.rounds.length :=
        (List.take_append_drop _ _).symm
      generalize rs.take b.rounds.length = R₁ at hlen hrs
      generalize rs.drop b.rounds.length = R₂ at hrs
      subst hrs
      have hlen' : R₁.length = (below b).rounds.length := hlen
      have hb := step_below ft b s R₁ cs
      cases hs : b.step ft s R₁ cs with
      | error e =>
        rw [hs] at hb
        obtain ⟨e', he'⟩ := error_of_none _ (hb.trans (ite_none _))
        rw [foldBlocks_error ft (below b) _ s R₁ R₂ cs hlen' e' he',
          foldBlocks_error ft b _ s R₁ R₂ cs hlen e hs]
        exact (ite_none _).symm
      | ok x =>
        obtain ⟨s', k⟩ := x
        have hk := step_count ft b s R₁ cs s' k hs
        rw [← hk, hs] at hb
        have hcs : cs = cs.take k ++ cs.drop k := (List.take_append_drop _ _).symm
        have hok : viewWordsBelowPrime ⟨R₁ ++ R₂, cs⟩ =
            (viewWordsBelowPrime ⟨R₁, cs.take k⟩ && viewWordsBelowPrime ⟨R₂, cs.drop k⟩) := by
          conv_lhs => rw [hcs]
          exact okViewW_app _ _ _ _
        rw [foldBlocks_ok ft b _ s R₁ R₂ cs hlen s' k hs, hok]
        cases ho : viewWordsBelowPrime ⟨R₁, cs.take k⟩ with
        | false =>
          rw [ho] at hb
          obtain ⟨e', he'⟩ := error_of_none _ (hb.trans rfl)
          rw [foldBlocks_error ft (below b) _ s R₁ R₂ cs hlen' e' he']
          rfl
        | true =>
          rw [ho] at hb
          have hb' : (below b).step ft s R₁ cs = .ok (s', k) := ok_of_some _ _ (hb.trans rfl)
          rw [foldBlocks_ok ft (below b) _ s R₁ R₂ cs hlen' s' k hb',
            endOk_below ft bs s' R₂ (cs.drop k)]
          simp
    · -- the stretch is short: both folds refuse
      have hl' : ¬ (below b).rounds.length ≤ rs.length := hl
      rw [foldBlocks_short ft (below b) _ s rs cs hl', foldBlocks_short ft b _ s rs cs hl]
      exact (ite_none _).symm

theorem foldBelow : FoldBelow := by
  intro S Cl F name bs back hback
  funext s v
  have hv : viewWordsBelowPrime ⟨v.rounds ++ back, v.opened⟩ = viewWordsBelowPrime v := by
    have t := okViewW_app v.rounds back v.opened []
    rw [List.append_nil, hback, Bool.and_true] at t
    exact t
  cases bs with
  | nil =>
    show (none : Option S) = if viewWordsBelowPrime v = true then (none : Option S) else none
    exact (ite_none _).symm
  | cons b bs =>
    have h1 : ((b :: bs).map below).isEmpty = false := rfl
    have h2 : (b :: bs).isEmpty = false := rfl
    simp only [foldRun, foldRunW, chainAt_toOption, h1, h2, Bool.false_eq_true, if_false,
      endOk_below, hv]

end VerifiableInference.Desc.Sound
