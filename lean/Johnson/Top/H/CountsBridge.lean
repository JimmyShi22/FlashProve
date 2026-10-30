-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/CountsBridge.lean: the condition on counts of Johnson/Top/H/StageJ.lean is that of
OnBytes/Slice/BlocksJohnson.lean; and the conditions of a key file's four proximity tests from it,
stage by stage.

`CountsAt` is stated twice over the same terms. Whoever proves the one of OnBytes/Slice/ at a
stage has the other. Definitions, statements and proofs.
Main names:
  `countsAt_iff`: the two conditions are one.
  `stB`, `stJ_of`: the conditions of `Sg.StageJ` (OnBytes/Slice/ManyHoldsJoh.lean) as a test that
    can be evaluated; a yes gives them.
  `lRng`, `cRng_of` and the like for `Row`, `Omg`, `Own`: the stages of a test behind its first;
    the condition of Johnson/Top/H/KeyTowers.lean from `Sg.CountsAt` at each of them.
  `cntL_of`: the same for the condition `CntL` of Johnson/Top/H/TowerOf.lean, for every list of
    stages.
Limits: no count is proved here.

-/
import OnBytes.Slice.BlocksJohnson
import OnBytes.Slice.ManyHoldsJoh
import Johnson.Top.H.KeyTowers
import Johnson.Top.H.TowerOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Prob

/-- The two conditions are one. -/
theorem countsAt_iff {s : Sg} {e bC bZ : ℕ} : CountsAt s e bC bZ ↔ s.CountsAt e bC bZ :=
  ⟨fun h => ⟨h.main, h.mask⟩, fun h => ⟨h.main, h.mask⟩⟩

/-- The conditions of `Sg.StageJ` as a test. -/
def stB (s : Sg) (e : ℕ) : Bool :=
  sizedB s && inJB s e && decide (0 < s.C.r + s.C.l - 1) && decide (0 < s.Z.r + s.Z.l - 1) &&
    decide (0 < e)

theorem stJ_of {s : Sg} {e : ℕ} (h : stB s e = true) : s.StageJ e := by
  simp only [stB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨sized_of h1, ⟨by omega, by omega⟩, h3, h4, h5, ⟨(inJ_of h2).1, (inJ_of h2).2⟩⟩

section Key
variable {bC bZ : Sg → ℕ → ℕ}

/-- The stages of the test behind its first, each with its radius. -/
def lRng : List (Sg × ℕ) := [(sRng2, eRng2), (sRng3, eRng3), (sRng4, eRng4)]

theorem cRng_of (h : ∀ p ∈ lRng, p.1.CountsAt p.2 (bC p.1 p.2) (bZ p.1 p.2)) : cRng bC bZ :=
  ⟨countsAt_iff.2 (h (sRng2, eRng2) (by simp [lRng])),
    countsAt_iff.2 (h (sRng3, eRng3) (by simp [lRng])),
    countsAt_iff.2 (h (sRng4, eRng4) (by simp [lRng]))⟩

/-- The stages of the test behind its first, each with its radius. -/
def lRow : List (Sg × ℕ) := [(sRow2, eRow2), (sRow3, eRow3), (sRow4, eRow4), (sRow5, eRow5)]

theorem cRow_of (h : ∀ p ∈ lRow, p.1.CountsAt p.2 (bC p.1 p.2) (bZ p.1 p.2)) : cRow bC bZ :=
  ⟨countsAt_iff.2 (h (sRow2, eRow2) (by simp [lRow])),
    countsAt_iff.2 (h (sRow3, eRow3) (by simp [lRow])),
    countsAt_iff.2 (h (sRow4, eRow4) (by simp [lRow])),
    countsAt_iff.2 (h (sRow5, eRow5) (by simp [lRow]))⟩

/-- The stages of the test behind its first, each with its radius. -/
def lOmg : List (Sg × ℕ) := [(sOmg2, eOmg2), (sOmg3, eOmg3), (sOmg4, eOmg4)]

theorem cOmg_of (h : ∀ p ∈ lOmg, p.1.CountsAt p.2 (bC p.1 p.2) (bZ p.1 p.2)) : cOmg bC bZ :=
  ⟨countsAt_iff.2 (h (sOmg2, eOmg2) (by simp [lOmg])),
    countsAt_iff.2 (h (sOmg3, eOmg3) (by simp [lOmg])),
    countsAt_iff.2 (h (sOmg4, eOmg4) (by simp [lOmg]))⟩

/-- The stages of the test behind its first, each with its radius. -/
def lOwn : List (Sg × ℕ) := [(sOwn2, eOwn2), (sOwn3, eOwn3), (sOwn4, eOwn4), (sOwn5, eOwn5)]

theorem cOwn_of (h : ∀ p ∈ lOwn, p.1.CountsAt p.2 (bC p.1 p.2) (bZ p.1 p.2)) : cOwn bC bZ :=
  ⟨countsAt_iff.2 (h (sOwn2, eOwn2) (by simp [lOwn])),
    countsAt_iff.2 (h (sOwn3, eOwn3) (by simp [lOwn])),
    countsAt_iff.2 (h (sOwn4, eOwn4) (by simp [lOwn])),
    countsAt_iff.2 (h (sOwn5, eOwn5) (by simp [lOwn]))⟩

/-- The condition of a list of stages, from the condition at each. -/
theorem cntL_of : ∀ (l : List (Sg × ℕ)) (s : Sg) (e : ℕ),
    (∀ p ∈ (s, e) :: l, p.1.CountsAt p.2 (bC p.1 p.2) (bZ p.1 p.2)) → CntL bC bZ l s e
  | [], s, e, h => countsAt_iff.2 (h (s, e) (List.mem_cons_self ..))
  | x :: l, s, e, h =>
    ⟨countsAt_iff.2 (h (s, e) (List.mem_cons_self ..)),
      cntL_of l x.1 x.2 fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

end Key

end Johnson.Top.H

#print axioms Johnson.Top.H.countsAt_iff
#print axioms Johnson.Top.H.stJ_of
#print axioms Johnson.Top.H.cntL_of
