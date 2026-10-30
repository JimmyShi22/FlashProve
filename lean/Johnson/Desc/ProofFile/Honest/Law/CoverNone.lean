-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverNone.lean: «NOTHING SITS HERE: 0». A debt (`DebtAt`,
Honest/Law/CoverSplit.lean) is owed at every member of a chain; at most of them no fall and no mark
sits. Here the payer. What the narrow event (`runFall`, Honest/Law/CoverLocal.lean) reaches: with
just the rounds of the member c that is being played laid, `frontsOf` lists c and the members
WITHOUT A ROUND right behind it, and no other: `groupOf`. So: where these rounds are not yet all
laid the event is false; where they are, and no fall of the list sits at a member of the group, it
is false.

WHAT THIS IS. A definition, and lemmas on the frame's own `frontsOf`, `chainFall` (Honest/Fall.lean)
and on definitions of ours. The last is on the library's own measure. None of the library's goals.

  1  `groupOf`, `fronts_quiet`, `fronts_group`, `chainFall_group`   what is reached
  2  `runFall_len`, `runFall_nil`, `runFall_short`, `runFall_group`   the narrow event is false
  3  `markOf_none`, `zero_of_not`   no mark; the measure of an event that never holds

Limits. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-! ## 1 What is reached -/

/-- **A member and the members without a round right behind it.** -/
def groupOf (c : Block S Cl) (t : List (Block S Cl)) : List (Block S Cl) :=
  c :: t.takeWhile fun d => d.rounds.isEmpty

/-- With no round left: the members without a round in front of the next one that has one. -/
theorem fronts_quiet (ft : Nat) : ∀ (t : List (Block S Cl)) (s : S) (cols : List OpenedColumn),
    ∀ e ∈ frontsOf ft t s [] cols, ∃ d ∈ t.takeWhile (fun d => d.rounds.isEmpty), d.place = e.1
  | [], _, _, e, he => by simp [frontsOf] at he
  | d :: t, s, cols, e, he => by
    cases hr : d.rounds with
    | cons r l =>
      exfalso
      rw [frontsOf_few ft d t s [] cols (by rw [hr]; exact Nat.succ_pos _)] at he
      cases he
    | nil =>
      have e0 : (d :: t).takeWhile (fun d : Block S Cl => d.rounds.isEmpty) =
          d :: t.takeWhile (fun d : Block S Cl => d.rounds.isEmpty) := by
        rw [List.takeWhile_cons, hr]
        rfl
      rw [e0]
      have hm : (([] : List Fmt.RoundView).take d.rounds.length).length = d.rounds.length := by
        rw [hr]
        rfl
      cases hs : d.step ft s (([] : List Fmt.RoundView).take d.rounds.length) cols with
      | error w =>
        rw [frontsOf_err ft d t s [] cols w hm hs] at he
        obtain rfl := List.mem_singleton.1 he
        exact ⟨d, List.mem_cons_self, rfl⟩
      | ok y =>
        obtain ⟨s', k⟩ := y
        rw [frontsOf_ok ft d t s s' k [] cols hm hs] at he
        rcases List.mem_cons.1 he with rfl | he'
        · exact ⟨d, List.mem_cons_self, rfl⟩
        · rw [List.drop_nil] at he'
          obtain ⟨x, hx, hp⟩ := fronts_quiet ft t s' _ e he'
          exact ⟨x, List.mem_cons_of_mem _ hx, hp⟩

/-- **With just c's rounds: c and the members without a round right behind it.** -/
theorem fronts_group (ft : Nat) (c : Block S Cl) (t : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hl : rs.length = c.rounds.length) :
    ∀ e ∈ frontsOf ft (c :: t) s rs cols, ∃ d ∈ groupOf c t, d.place = e.1 := by
  intro e he
  have hm : (rs.take c.rounds.length).length = c.rounds.length := by
    rw [← hl, List.take_length]
  cases hs : c.step ft s (rs.take c.rounds.length) cols with
  | error w =>
    rw [frontsOf_err ft c t s rs cols w hm hs] at he
    obtain rfl := List.mem_singleton.1 he
    exact ⟨c, List.mem_cons_self, rfl⟩
  | ok y =>
    obtain ⟨s', k⟩ := y
    rw [frontsOf_ok ft c t s s' k rs cols hm hs] at he
    rcases List.mem_cons.1 he with rfl | he'
    · exact ⟨c, List.mem_cons_self, rfl⟩
    · rw [← hl, List.drop_length] at he'
      obtain ⟨x, hx, hp⟩ := fronts_quiet ft t s' _ e he'
      exact ⟨x, List.mem_cons_of_mem _ hx, hp⟩

/-- **Where no fall of the list sits at a member of the group, none is met.** -/
theorem chainFall_group (fs : List (Fall S)) (ft : Nat) (c : Block S Cl) (t : List (Block S Cl))
    (h : ∀ d ∈ groupOf c t, ∀ f ∈ fs, f.place ≠ d.place) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hl : rs.length = c.rounds.length) :
    chainFall fs ft (c :: t) s ⟨rs, cols⟩ = none := by
  cases hc : chainFall fs ft (c :: t) s ⟨rs, cols⟩ with
  | none => rfl
  | some _ =>
    exfalso
    obtain ⟨e, he, hf⟩ := (chainFall_iff fs ft (c :: t) s ⟨rs, cols⟩).1 (by rw [hc]; rfl)
    obtain ⟨d, hd, hp⟩ := fronts_group ft c t s rs cols hl e he
    rw [fallOf_none fs e.1 (fun f hf' => by rw [← hp]; exact h d hd f hf')] at hf
    cases hf

/-! ## 2 The narrow event is false -/

/-- As many rounds are laid since as challenges are handed. -/
theorem runFall_len {L : Lay} {ss' : List (Step W Y)} {z z' : ChainProgress S Cl W Y}
    {ext : List Fmt.Drawn} {ps : List Played} (hw : walk L ss' ext z = .ok z')
    (g : z'.laid = z.laid ++ ps) : ps.length = ext.length := by
  have hdw := walk_shows L _ _ z z' hw
  rw [g, List.map_append] at hdw
  have h3 := congrArg List.length (List.append_cancel_left hdw)
  rw [List.length_map] at h3
  exact h3

/-- No member is left. -/
theorem runFall_nil {fs : List (Fall S)} {L : Lay} {ss' : List (Step W Y)} {z : ChainProgress S Cl W Y}
    {s' : S} {ext : List Fmt.Drawn} (ht : z.todo = []) : ¬ runFall fs L ss' z s' ext := by
  rintro ⟨z', ps, cs, -, -, -, h4⟩
  rw [ht] at h4
  cases h4

/-- **The rounds of the member that is being played are not yet all laid.** -/
theorem runFall_short {fs : List (Fall S)} {L : Lay} {ss' : List (Step W Y)} {z : ChainProgress S Cl W Y}
    {s' : S} {ext : List Fmt.Drawn} {c : Block S Cl} {t : List (Block S Cl)}
    (ht : z.todo = c :: t) (hl : z.own.length + ext.length < c.rounds.length) :
    ¬ runFall fs L ss' z s' ext := by
  rintro ⟨z', ps, cs, hw, g, -, h4⟩
  have hp := runFall_len hw g
  rw [ht] at h4
  unfold chainFall at h4
  rw [frontsOf_few L.firstTree c t s' _ cs (by
    rw [roundsOf_length, List.length_append, hp]
    exact hl)] at h4
  cases h4

/-- **They are, and no fall of the list sits at a member of the group.** -/
theorem runFall_group {fs : List (Fall S)} {L : Lay} {ss' : List (Step W Y)} {z : ChainProgress S Cl W Y}
    {s' : S} {ext : List Fmt.Drawn} {c : Block S Cl} {t : List (Block S Cl)}
    (ht : z.todo = c :: t) (hl : z.own.length + ext.length = c.rounds.length)
    (h : ∀ d ∈ groupOf c t, ∀ f ∈ fs, f.place ≠ d.place) : ¬ runFall fs L ss' z s' ext := by
  rintro ⟨z', ps, cs, hw, g, -, h4⟩
  have hp := runFall_len hw g
  rw [ht, chainFall_group fs L.firstTree c t h s' _ cs (by
    rw [roundsOf_length, List.length_append, hp]
    exact hl)] at h4
  cases h4

/-! ## 3 No mark; the measure of an event that never holds -/

theorem markOf_none (ms : List Mark) (a : Place) (h : ∀ m ∈ ms, m.place ≠ a)
    (fr own : List Fmt.Drawn) : markOf ms a fr own = none := by
  unfold markOf
  have e : (ms.filter fun m => m.place == a) = [] :=
    List.filter_eq_nil_iff.2 fun m hm => by
      have := h m hm
      simpa using this
  rw [e]
  rfl

/-- An event that never holds has at most any number as its measure. -/
theorem zero_of_not (C : CK) (ds : List RDT) (E : Iop.Rho (uLT C ds) → Prop) (h : ∀ ρ, ¬ E ρ)
    (q : ℝ≥0∞) : Iop.prRho {ρ : Iop.Rho (uLT C ds) | E ρ} ≤ q :=
  le_trans (Iop.prRho_empty _ fun ρ hρ => h ρ hρ) (zero_le _)

end ProofFile.Honest

#print axioms ProofFile.Honest.fronts_quiet
#print axioms ProofFile.Honest.fronts_group
#print axioms ProofFile.Honest.chainFall_group
#print axioms ProofFile.Honest.runFall_len
#print axioms ProofFile.Honest.runFall_nil
#print axioms ProofFile.Honest.runFall_short
#print axioms ProofFile.Honest.runFall_group
#print axioms ProofFile.Honest.markOf_none
#print axioms ProofFile.Honest.zero_of_not
