-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsBools.lean: THREE CONDITIONS ON PUBLIC LETTERS, AS TESTS WITH CODE: `SitsIn`
(Johnson/Road/K4/K4PinsRead.lean), `Covers` (K4PinsPlanes.lean), `SymsOne` (K4PinsSym.lean). For
each a Bool and the theorem "a yes of the test gives the condition". THIS FILE STANDS IN NO
`noncomputable section`: a test for which Lean can make no code does not compile here.

  `sitsInB`, `sitsIn_of_B` · `coversB`, `covers_of_B`.
  `symOneB … μ r c`: the test at one symbol; `symsOneB`: the walk over all symbols of the sizes;
    `symsOne_of_each`: the condition from a yes at each symbol (for whoever walks otherwise, by
    blocks or in parts); `symsOne_of_B`: from a yes of the walk.
  GENERAL LAWS ON WHERE A TEST SAYS NO: `sitsInB_no_member`: the test says no where ms is empty and
    the list is not · `symOneB_no_seat`: it says no at a symbol for which `seatCalls` finds no seat
    ·
    `coversB_zero`: it says no at nM = 0 where tl has a matrix.

OBJECT: none of its own. USER: none yet; meant: the sheet that evaluates the conditions of K4's row
at the real plan. LETTERS: those of the three conditions.

Limits. K04_law IS NOT PROVED BY THIS. NOTHING IS EVALUATED HERE. ONE DIRECTION: a no of a test does
not refute the condition by any theorem here (by reading each test is the condition's own text,
clause by clause). `symsOneB` walks every symbol: at the full size that is long.
-/
import Johnson.Road.K4.K4PinsSym
import Johnson.Road.K4.K4PinsPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls cellJ szOf)
open VerifiableInference.Desc.Sound (Mem seatOf)
open Cb.Pv.Tail (Size)

/-! ## 1 `SitsIn` -/

/-- The test for `SitsIn`. -/
def sitsInB (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (ms : List Mem)
    (N : Numbers) (m : ℕ) : Bool :=
  (List.finRange l.length).all fun i =>
    (N.sent m 0 ++ [N.index]).contains (seat i) &&
      match ms.find? fun y => decide (seatOf y = seat i) with
      | some u => decide ((u.1.l.get u.2).1 = (l.get i).1)
      | none => false

theorem sitsIn_of_B {l : List (OnBytes.OracleShape × ℕ)} {seat : Fin l.length → ℕ × ℕ}
    {ms : List Mem} {N : Numbers} {m : ℕ} (h : sitsInB l seat ms N m = true) :
    SitsIn l seat ms N m := by
  intro i
  have h0 := List.all_eq_true.1 h i (List.mem_finRange i)
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h0
  refine ⟨List.contains_iff_mem.1 h1, ?_⟩
  cases hu : ms.find? fun y => decide (seatOf y = seat i) with
  | none =>
    rw [hu] at h2
    exact absurd h2 Bool.false_ne_true
  | some u =>
    rw [hu] at h2
    exact ⟨u, hu, of_decide_eq_true h2⟩

/-- A general law: no member, no yes. -/
theorem sitsInB_no_member {l : List (OnBytes.OracleShape × ℕ)} (seat : Fin l.length → ℕ × ℕ)
    (N : Numbers) (m : ℕ) (i : Fin l.length) : sitsInB l seat [] N m = false := by
  cases h : sitsInB l seat [] N m with
  | false => rfl
  | true =>
    obtain ⟨_, u, hu, _⟩ := sitsIn_of_B h i
    exact nomatch hu

/-! ## 2 `Covers` -/

/-- The test for `Covers`. -/
def coversB (tl : HTailF2) (nM nR nC : ℕ) : Bool :=
  (List.range (szOf tl).NM).all fun a =>
    decide (a < nM) && ((szOf tl).m a == 0 || (szOf tl).k a == 0 ||
      (decide ((szOf tl).m a ≤ nR) && decide ((szOf tl).k a ≤ nC)))

theorem covers_of_B {tl : HTailF2} {nM nR nC : ℕ} (h : coversB tl nM nR nC = true) :
    Covers tl nM nR nC := by
  intro a r c hs
  unfold cellJ at hs
  by_cases hc : a < (szOf tl).NM ∧ c < (szOf tl).k a ∧ r < (szOf tl).m a
  · have h0 := List.all_eq_true.1 h a (List.mem_range.2 hc.1)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h0
    obtain ⟨h1, h2⟩ := h0
    rcases h2 with (h2 | h2) | h2
    · omega
    · omega
    · exact ⟨h1, by omega, by omega⟩
  · rw [dif_neg hc] at hs
    exact absurd hs Bool.false_ne_true

/-- A general law: no room for a matrix, no yes. -/
theorem coversB_zero (tl : HTailF2) (nR nC : ℕ) (h : 0 < (szOf tl).NM) :
    coversB tl 0 nR nC = false := by
  cases hb : coversB tl 0 nR nC with
  | false => rfl
  | true =>
    have h0 := List.all_eq_true.1 hb 0 (List.mem_range.2 h)
    simp at h0

/-! ## 3 `SymsOne` -/

section
variable {Cells : Type} (A : PinPlan Cells) (tl : HTailF2) (arr : ℕ → ℕ → ℕ) (N : Numbers)
  (k : ℕ) (sz : Size) (seat' : Fin sz.NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- The test at one symbol. -/
def symOneB (μ : Fin sz.NM) (r c : ℕ) : Bool :=
  match seatCalls A.D A.link (.cell (tl.gtTree.getD μ.val 0) r c) with
  | none => false
  | some s =>
    if hk : s.msg < (sigListCalls A.D A.rad A.link).length then
      !s.mask &&
      decide (s.row < ((sigListCalls A.D A.rad A.link).get ⟨s.msg, hk⟩).1.mainRows) &&
      decide (s.place <
        (pMain A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨s.msg, hk⟩).1).ell) &&
      decide ((seat' μ r c).2 = (s.row, s.place)) &&
      decide (((N.group k).find? fun x => arr x.1 x.2 == (seat' μ r c).1) =
        some (A.seatT ⟨s.msg, hk⟩))
    else false

/-- The walk over all symbols of the sizes. -/
def symsOneB : Bool :=
  (List.finRange sz.NM).all fun μ =>
    (List.range (Alg.symRows (sz.m μ))).all fun r =>
      (List.range (sz.k μ)).all fun c => symOneB A tl arr N k sz seat' μ r c

/-- **The condition, from a yes at each symbol.** -/
theorem symsOne_of_each
    (h : ∀ (μ : Fin sz.NM) (r : Fin (Alg.symRows (sz.m μ))) (c : Fin (sz.k μ)),
      symOneB A tl arr N k sz seat' μ r.val c.val = true) : SymsOne A tl arr N k sz seat' := by
  intro μ r c
  have h0 := h μ r c
  unfold symOneB at h0
  cases hs : seatCalls A.D A.link (.cell (tl.gtTree.getD μ.val 0) r.val c.val) with
  | none =>
    rw [hs] at h0
    exact absurd h0 Bool.false_ne_true
  | some s =>
    rw [hs] at h0
    by_cases hk : s.msg < (sigListCalls A.D A.rad A.link).length
    · simp only [dif_pos hk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h0
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h0
      exact ⟨s, hk, rfl, h1, h2, h3, h4, h5⟩
    · simp only [dif_neg hk] at h0
      exact absurd h0 Bool.false_ne_true

/-- **The condition, from a yes of the walk.** -/
theorem symsOne_of_B (h : symsOneB A tl arr N k sz seat' = true) :
    SymsOne A tl arr N k sz seat' :=
  symsOne_of_each A tl arr N k sz seat' fun μ r c =>
    List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h μ (List.mem_finRange μ)) r.val
      (List.mem_range.2 r.isLt)) c.val (List.mem_range.2 c.isLt)

/-- A general law: no seat, no yes. -/
theorem symOneB_no_seat (μ : Fin sz.NM) (r c : ℕ)
    (h : seatCalls A.D A.link (.cell (tl.gtTree.getD μ.val 0) r c) = none) :
    symOneB A tl arr N k sz seat' μ r c = false := by
  unfold symOneB
  rw [h]

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sitsIn_of_B
#print axioms OnBytes.Road.K4.sitsInB_no_member
#print axioms OnBytes.Road.K4.covers_of_B
#print axioms OnBytes.Road.K4.coversB_zero
#print axioms OnBytes.Road.K4.symsOne_of_each
#print axioms OnBytes.Road.K4.symsOne_of_B
#print axioms OnBytes.Road.K4.symOneB_no_seat
