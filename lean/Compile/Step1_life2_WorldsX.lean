-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_life2_WorldsX.lean: lemmas on the renumbering of tokens
(Compile/Step1_life2_Virt.lean), and the state at the start of a session. Generic in the family of
oracles.

  `dummy`                The state with one more token, for the empty string.
  `gap`                  The number of tokens that a new session must not see.
  `getD_of_take_eq`      Two lists with the same first n entries agree at every index below n.

Notation: `N₀`, `δ`: natural numbers; `vis N₀ δ t`: a `Bool`, true if t < N₀ or N₀ + δ ≤ t;
`up N₀ δ v`: v if v < N₀, else v + δ; `down N₀ δ t`: t if t < N₀, else t - δ; `viewShown N₀ δ l`:
the t in l with `vis N₀ δ t` true, each under `down N₀ δ`; `deadEvs N₀ δ l`: the e in l with
`vis N₀ δ e.charged` false (these five: Compile/Step1_life2_Virt.lean); `Tok`: ℕ; `DSt.vals`: a list
of bit strings: the value of token i is at place i; `Ev`: the record of one marked evaluation;
`Ev.charged`: a `Tok` (these four: Rom/Defer.lean).

Limits: it does not prove that a run of a challenger keeps the rules and the counts (`Rules`, `nEv`:
Compile/SpecDiscipline.lean).
-/
import Compile.DisciplineCounts
import Compile.DisciplineWorld
import Compile.Step1_life2_Chall

set_option autoImplicit false

noncomputable section

namespace Compile
namespace Life2
namespace WorldsX
open Iop Rom Prob Disc

/-! ## The view and the start of a session, for any family of oracles -/

section Generic

variable {S : OSpec} {sp : Split S} {α : Type} {Rl : Rules S} {N₀ δ : ℕ}

theorem mem_viewShown {l : List ℕ} {v : ℕ} : v ∈ viewShown N₀ δ l ↔ up N₀ δ v ∈ l := by
  have h := contains_viewShown N₀ δ l v
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem] at h
  exact h

theorem mem_deadEvs {l : List (Ev S)} {x : Ev S} :
    x ∈ deadEvs N₀ δ l ↔ x ∈ l ∧ vis N₀ δ x.charged = false := by
  simp [deadEvs]

theorem not_vis_iff (t : ℕ) : vis N₀ δ t = false ↔ N₀ ≤ t ∧ t < N₀ + δ := by
  rw [← Bool.not_eq_true, vis_iff]
  omega

/-- for a visible t and N₀ + δ ≤ n: `down` t is below n - δ if and only if t is below n -/
theorem down_lt {t n : ℕ} (hv : vis N₀ δ t = true) (hn : N₀ + δ ≤ n) :
    down N₀ δ t < n - δ ↔ t < n := by
  rw [vis_iff] at hv
  unfold down
  split_ifs <;> omega

theorem down_of_lt {t : ℕ} (h : t < N₀) : down N₀ δ t = t := if_pos h

theorem lt_of_down_lt {t : ℕ} (hv : vis N₀ δ t = true) (h : down N₀ δ t < N₀) : t < N₀ := by
  rw [vis_iff] at hv
  unfold down at h
  split_ifs at h <;> omega

/-- the state with one more token, for the empty string -/
abbrev dummy (D : DSt S) : DSt S := { D with vals := D.vals ++ [[]] }

/-- the number of tokens that a new session must not see -/
abbrev gap (N₀ : ℕ) (D : DSt S) : ℕ := D.vals.length + 1 - N₀

theorem getD_of_take_eq {l l' : List Bits} {n c : ℕ} (h : l'.take n = l.take n) (hc : c < n) :
    l'.getD c [] = l.getD c [] := by
  have h1 : (l'.take n).getD c [] = (l.take n).getD c [] := by rw [h]
  simpa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hc] using h1

end Generic

end WorldsX

end Life2
end Compile
