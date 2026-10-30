-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Widths.lean: kind K5: the numbers of columns of the ledger's arrays
stay under every verb of the ledger.

Why: every form of the kind that names an entry of the vector of reads holds the entry's number
divided by, and modulo, the number K of columns of the array of the reads, which the claims' seat
reads off the ledger (cols, Johnson/Desc/First/Att/RunsK.lean).
Main names:
  `widths F`: F.trees.map (·.K). `cols_of_widths`: two ledgers with one widths give one K at every
    array's number.
  `widths_of_frame`: what keeps treesFrame (OnBytes/Model/HideLaws.lean) keeps widths.
  `widths_rootTaken`, `_slots`, `_hide`, `_hideRun`, `_push`, `_batchBy`, `_kapTake`, `_kap`,
    `_owe`, `_paid`, `_lin`, `_trimL`, `_fillL` (the verbs of OnBytes/Model/Hide.lean that return a
    ledger), `_onRow` (OnBytes/Model/Tail.lean).
Used of OnBytes/Model: the record Fork and these pure functions on it; map_modify_same,
pushEnt_frame, treesFrame.
Limits: nothing is said of a step of a chain: that every step between a segment's opening and the
kind's claims writes the ledger through these verbs alone is not shown. pushRun
(OnBytes/Model/Trees.lean) keeps treesFrame by OnBytes/Model/TreesLaws.lean; it is not restated
here.

Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Model.HideLaws
import OnBytes.Model.Tail

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model

/-- The numbers of columns of the ledger's arrays. -/
def widths (F : Fork) : Array ℕ := F.trees.map (·.K)

/-- Two ledgers with one widths give one number of columns at every array's number. -/
theorem cols_of_widths {F G : Fork} (h : widths G = widths F) (t : ℕ) :
    (G.trees[t]?).map (·.K) = (F.trees[t]?).map (·.K) := by
  have e := congrArg (fun a : Array ℕ => a[t]?) h
  simp only [widths, Array.getElem?_map] at e
  exact e

/-- What keeps the arrays' frame keeps their numbers of columns. -/
theorem widths_of_frame {T T' : Array HTree} (h : treesFrame T' = treesFrame T) :
    T'.map (·.K) = T.map (·.K) := by
  have e := congrArg (fun a => a.map fun x : HTree × Array (HRow × Nat) => x.1.K) h
  simp only [treesFrame, Array.map_map] at e
  exact e

theorem widths_rootTaken (F : Fork) (t w : ℕ) : widths (F.rootTaken t w) = widths F := by
  show (F.trees.modify t fun X => { X with root := some w }).map (fun X : HTree => X.K) = _
  apply map_modify_same (fun X : HTree => X.K)
  intro X
  rfl

theorem widths_slots (F : Fork) (n : ℕ) : widths (F.slots n) = widths F := rfl

theorem widths_hide {F G : Fork} {j : ℕ} {y f : E} (h : F.hide j y f = some G) : widths G = widths F := by
  unfold Fork.hide at h
  split at h
  · rw [← Option.some.inj h]; rfl
  · cases h

theorem widths_hideRun {F G : Fork} {first : ℕ} {v : Array E} {f : E} (h : F.hideRun first v f = some G) :
    widths G = widths F := by
  unfold Fork.hideRun at h
  have key : ∀ (l : List E) (x y : ℕ × Fork), l.foldlM (Fork.hideStep f) x = some y →
      widths y.2 = widths x.2 := by
    intro l
    induction l with
    | nil => intro x y e; rw [← Option.some.inj e]
    | cons a l ih =>
      intro x y e
      rw [List.foldlM_cons] at e
      cases hs : Fork.hideStep f x a with
      | none => rw [hs] at e; cases e
      | some z =>
        rw [hs] at e
        have e1 := ih z y e
        obtain ⟨j, H⟩ := x
        have hs' : (H.hide j a f).map (fun H' => (j + 1, H')) = some z := hs
        clear hs
        rename' hs' => hs
        cases hh : H.hide j a f with
        | none => rw [hh] at hs; cases hs
        | some H' =>
          rw [hh] at hs
          rw [e1, ← Option.some.inj hs]
          exact widths_hide hh
  cases hv : v.foldlM (Fork.hideStep f) (first, F) with
  | none => rw [hv] at h; cases h
  | some x =>
    rw [hv] at h
    rw [← Option.some.inj h]
    rw [← Array.foldlM_toList] at hv
    exact key _ _ _ hv

theorem widths_push {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) : widths G = widths F := by
  unfold Fork.push at h
  split at h
  · cases h
  · dsimp only at h
    have key : ∀ (l : List Ent) (T T' : Array HTree), l.foldlM (Fork.pushEnt w) T = some T' →
        treesFrame T' = treesFrame T := by
      intro l
      induction l with
      | nil => intro T T' e; rw [← Option.some.inj e]
      | cons x l ih =>
        intro T T' e
        rw [List.foldlM_cons] at e
        cases hs : Fork.pushEnt w T x with
        | none => rw [hs] at e; cases e
        | some T1 =>
          rw [hs] at e
          exact (ih T1 T' e).trans (pushEnt_frame w T T1 x hs)
    split at h
    · rename_i T' LS' hT hL
      rw [← Option.some.inj h]
      rw [← Array.foldlM_toList] at hT
      exact widths_of_frame (key _ _ _ hT)
    · cases h

theorem widths_batchBy {F G : Fork} {d : E} (h : F.batchBy d = some G) : widths G = widths F := by
  unfold Fork.batchBy at h
  split at h
  · cases h
  · rw [← Option.some.inj h]; rfl

theorem widths_kapTake {F : Fork} {c : ℕ} {x : E × Fork} (h : F.kapTake c = some x) :
    widths x.2 = widths F := by
  unfold Fork.kapTake at h
  split at h
  · cases h
  · split at h
    · obtain ⟨k, _, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl
    · split at h
      · obtain ⟨k, _, rfl⟩ := Option.map_eq_some_iff.1 h
        rfl
      · cases h

theorem widths_kap {F : Fork} {x : E × Fork} (h : F.kap = some x) : widths x.2 = widths F := by
  unfold Fork.kap at h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  exact (widths_kapTake hy : widths y.2 = widths F)

theorem widths_owe (F : Fork) (what : String) : widths (F.owe what).2 = widths F := rfl

theorem widths_paid (F : Fork) (i : ℕ) : widths (F.paid i) = widths F := rfl

theorem widths_lin {F G : Fork} {f : Aff} (h : F.lin f = some G) : widths G = widths F := by
  unfold Fork.lin at h
  obtain ⟨x, hx, hp⟩ := Option.bind_eq_some_iff.1 h
  exact (widths_push hp).trans (widths_kap hx)

theorem widths_trimL (F : Fork) : widths F.trimL = widths F := by
  unfold widths Fork.trimL
  rw [Array.map_map]
  rfl

theorem widths_fillL (F : Fork) : widths F.fillL = widths F := by
  unfold widths Fork.fillL
  rw [Array.map_map]
  rfl

theorem widths_onRow (F : Fork) (t r : ℕ) (f : HRow → HRow) : widths (HTailF2.onRow F t r f) = widths F := by
  show (F.trees.modify t fun X => { X with rows := X.rows.modify r f }).map (fun X : HTree => X.K) = _
  apply map_modify_same (fun X : HTree => X.K)
  intro X
  rfl

end K5Law
