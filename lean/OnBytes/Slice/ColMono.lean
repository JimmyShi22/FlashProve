-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ColMono.lean: a block of the format's decision that succeeds on some opened columns
succeeds, with the same result, when more columns are shown.

Three functions of the format's decision read opened columns through a function from positions to
optional columns: the code switch (`csStep`, Fmt/M1Cs.lean), the base case (`baseOK`,
Fmt/M1Fold.lean) and the batching of the link's rows (`batchLit`, Fmt/M3Link.lean, which reads the
two stored tables of a view). Each of them fails as soon as a column that it asks for is not shown,
and does not look at any other column. So if it gives a row, or says yes, it does the same at every
function that shows the same values and perhaps more.

Main definition.
 `Below c c'`      c' shows every value that c shows.
Main theorems.
 `csStep_mono`     the code switch gives the same row.
 `baseOK_mono`     the base case says yes as well.
 `batchLit_mono`   the batching gives the same row.

Not claimed. Nothing in the other direction: with more columns shown, a block may succeed where it
failed before.
-/
import Fmt.M3Dec

set_option autoImplicit false

namespace OnBytes.Slice

/-- The second function shows every value that the first shows. -/
def Below {α : Type} (c c' : Nat → Option α) : Prop := ∀ x w, c x = some w → c' x = some w

/-! ## A loop that stops at the first failure -/

/-- A loop whose step keeps a failure ends in failure when it starts from one. -/
private theorem foldl_none {β : Type} (F : Option β → Nat → Option β) (hn : ∀ x, F none x = none)
    (xs : List Nat) : xs.foldl F none = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, hn, ih]

/-- Two loops over the same list from the same start. If the first loop's step keeps a failure, and
the second step succeeds with the same value wherever the first succeeds, then the second loop ends
in the value in which the first ends. -/
private theorem foldl_some_mono {β : Type} (F F' : Option β → Nat → Option β)
    (hn : ∀ x, F none x = none) (hs : ∀ a x r, F a x = some r → F' a x = some r)
    (xs : List Nat) (a : Option β) (r : β) (h : xs.foldl F a = some r) :
    xs.foldl F' a = some r := by
  induction xs generalizing a with
  | nil => exact h
  | cons x xs ih =>
    rw [List.foldl_cons] at h ⊢
    cases hF : F a x with
    | none =>
      rw [hF, foldl_none F hn] at h
      exact (Option.some_ne_none _ h.symm).elim
    | some st =>
      rw [hF] at h
      rw [hs a x st hF]
      exact ih _ h

/-! ## The code switch -/

/-- The code switch gives the same row when more columns are shown. -/
theorem csStep_mono (f : Fmt.Fld) (old new : Fmt.M1.Stage) (s : Fmt.M1.SRow)
    (sample : Fmt.M1.GRow) (xs : List Nat) (theta : Fmt.M1.E) (c c' : Nat → Option Fmt.M1.Col)
    (h : Below c c') (G : Fmt.M1.GRow)
    (hG : Fmt.M1.csStep f old new s sample xs theta c = some G) :
    Fmt.M1.csStep f old new s sample xs theta c' = some G := by
  have h0 : Fmt.M1.csRows f old new s sample [] c' = Fmt.M1.csRows f old new s sample [] c := rfl
  unfold Fmt.M1.csStep at hG ⊢
  rw [h0]
  cases hr : Fmt.M1.csRows f old new s sample [] c with
  | none =>
    rw [hr] at hG
    exact (Option.some_ne_none _ hG.symm).elim
  | some two =>
    rw [hr] at hG
    simp only [Option.bind_some, Option.map_eq_some_iff] at hG ⊢
    obtain ⟨st, hst, hGe⟩ := hG
    refine ⟨st, foldl_some_mono _ _ (fun _ => rfl) ?_ xs _ st hst, hGe⟩
    intro a x r hm
    cases a with
    | none => exact (Option.some_ne_none _ hm.symm).elim
    | some st0 =>
      cases hc : c x with
      | none =>
        simp only [hc] at hm
        exact (Option.some_ne_none _ hm.symm).elim
      | some cl =>
        simp only [hc] at hm
        simp only [h x cl hc]
        exact hm

/-! ## The base case -/

/-- If the base case says yes, it says yes as well when more columns are shown. -/
theorem baseOK_mono (f : Fmt.Fld) (C Z : Fmt.M1.Code) (c d : Array Fmt.M1.E)
    (tau tauS lam : Fmt.M1.E) (M0 M1 R0 R1 : List Fmt.M1.E) (xs : List Nat)
    (l l' : Nat → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)) (h : Below l l')
    (hb : Fmt.M1.baseOK f C Z c d tau tauS lam M0 M1 R0 R1 xs l = true) :
    Fmt.M1.baseOK f C Z c d tau tauS lam M0 M1 R0 R1 xs l' = true := by
  unfold Fmt.M1.baseOK at hb ⊢
  rw [Bool.and_eq_true] at hb ⊢
  refine ⟨hb.1, ?_⟩
  have h2 := hb.2
  rw [List.all_eq_true] at h2 ⊢
  intro x hx
  have h3 := h2 x hx
  cases hl : l x with
  | none =>
    simp only [hl] at h3
    exact (Bool.false_ne_true h3).elim
  | some o =>
    simp only [hl] at h3
    simp only [h x o hl]
    exact h3

/-! ## The batching of the link's rows -/

/-- Every draw of the link is a draw of the table 0 or of the table 1. -/
theorem drawsOf_lt (P : Fmt.M3.Par) (xs : List Nat) (p : Nat × Nat)
    (hp : p ∈ Fmt.M3.drawsOf P xs) : p.1 < 2 := by
  unfold Fmt.M3.drawsOf at hp
  rw [List.mem_append, List.mem_map, List.mem_map] at hp
  rcases hp with ⟨x, _, rfl⟩ | ⟨x, _, rfl⟩
  · exact Nat.zero_lt_two
  · exact Nat.one_lt_two

/-- The draws' rows are the same when more columns of the two stored tables are shown. -/
theorem colRows_mono (P : Fmt.M3.Par) (V V' : Fmt.M3.View)
    (h : ∀ w x c, w < 2 → Fmt.M3.storedAt V w x = some c → Fmt.M3.storedAt V' w x = some c)
    (gamma : List Fmt.M1.E) (ds : List (Nat × Nat)) (hd : ∀ p ∈ ds, p.1 < 2)
    (rs : List Fmt.M2.MRow) (hr : Fmt.M3.colRows P V gamma ds = some rs) :
    Fmt.M3.colRows P V' gamma ds = some rs := by
  induction ds generalizing rs with
  | nil => exact hr
  | cons p ds ih =>
    obtain ⟨w, x⟩ := p
    have hw : w < 2 := hd (w, x) List.mem_cons_self
    have hd' : ∀ p ∈ ds, p.1 < 2 := fun p hp => hd p (List.mem_cons_of_mem _ hp)
    rw [Fmt.M3.colRows] at hr ⊢
    cases hs : Fmt.M3.storedAt V w x with
    | none =>
      simp only [hs] at hr
      exact (Option.some_ne_none _ hr.symm).elim
    | some col =>
      cases hc : Fmt.M3.colRows P V gamma ds with
      | none =>
        simp only [hs, hc] at hr
        exact (Option.some_ne_none _ hr.symm).elim
      | some rs0 =>
        simp only [hs, hc] at hr
        simp only [h w x col hw hs, ih hd' rs0 hc]
        exact hr

/-- The batching of the link's rows gives the same row when more columns of the two stored tables
are shown. -/
theorem batchLit_mono (P : Fmt.M3.Par) (V V' : Fmt.M3.View)
    (h : ∀ w x c, w < 2 → Fmt.M3.storedAt V w x = some c → Fmt.M3.storedAt V' w x = some c)
    (gamma z : List Fmt.M1.E) (beta y0 yj : Fmt.M1.E) (xs : List Nat) (phi : List Fmt.M1.E)
    (theta : Fmt.M1.E) (R : Fmt.M2.KRow)
    (hR : Fmt.M3.batchLit P V gamma z beta y0 yj xs phi theta = some R) :
    Fmt.M3.batchLit P V' gamma z beta y0 yj xs phi theta = some R := by
  unfold Fmt.M3.batchLit Fmt.M3.rowsLit at hR ⊢
  cases hc : Fmt.M3.colRows P V gamma (Fmt.M3.drawsOf P xs) with
  | none =>
    rw [hc] at hR
    exact (Option.some_ne_none _ hR.symm).elim
  | some rs =>
    rw [colRows_mono P V V' h gamma _ (drawsOf_lt P xs) rs hc]
    rw [hc] at hR
    exact hR

end OnBytes.Slice

#print axioms OnBytes.Slice.csStep_mono
#print axioms OnBytes.Slice.baseOK_mono
#print axioms OnBytes.Slice.batchLit_mono
