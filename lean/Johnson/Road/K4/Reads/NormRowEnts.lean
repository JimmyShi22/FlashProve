-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Reads/NormRowEnts.lean: GROUPS 4 TO 6: the norms' rows name entries inside the
families of tables alone: `rowsForms_in` (`rowsForms`, OnBytes/Desc/First/K4/Claims.lean; the
formulas: OnBytes/Desc/First/P6/NormRow.lean). Every form is made of slots, constants and the row's
99 digits, and a digit is a cell of the reads plus 128. Each formula is walked by an explicit term:
a search by a tactic made Lean hang where 2 ^ 47 and 2 ^ 48 stand.
-/
import Johnson.Road.K4.Reads.TermsEnts
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 40000

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road OnBytes.Road.Rows

variable {Q : ℕ → ℕ → ℕ → Prop}

/-! ### The norms' rows -/

theorem entsIn_sumTo (n : ℕ) {f : ℕ → Aff} (h : ∀ i, EntsIn Q (f i)) :
    EntsIn Q (P6.sumTo n f) :=
  entsIn_foldl _ (fun _ _ hf => entsIn_add hf (h _)) _ _ (entsIn_ofConst _)

/-! P6's formulas are written with three notations that are local to its file (a natural number as a
form; k • f). Here each formula is written out by `Aff.ofConst` and `Aff.scale`; that it is the same
is `rfl`. -/

/-- n digits from j on, as a number to the base 256. -/
def digs (D : ℕ → Aff) (j n : ℕ) : Aff :=
  P6.sumTo n fun i => Aff.scale (D (j + i)) (ofNat (256 ^ i))

/-- A natural number as a form. -/
abbrev cst (n : ℕ) : Aff := Aff.ofConst (ofNat n)

/-- k times a form. -/
abbrev tms (k : ℕ) (f : Aff) : Aff := Aff.scale f (ofNat k)

/-- The field a of a row. -/
def fa (D : ℕ → Aff) : Aff := tms 2 (D 58) + D 59 + tms (2 ^ 8) (D 60) + tms (2 ^ 16) (D 61)

/-- The field b of a row. -/
def fb (D : ℕ → Aff) : Aff := D 62 + tms (2 ^ 8) (D 63)

theorem ofDigits_eq (D : ℕ → Aff) : P6.Row.ofDigits D =
    { Vlo := digs D 0 6, Vhi := digs D 6 4, a := fa D, b := fb D, s0 := D 59,
      sig := fa D + tms (2 ^ 24) (fb D), l1 := digs D 64 5, h1 := digs D 69 5, Blo := digs D 74 3,
      Bhi := digs D 77 2, kap := D 79 - cst 4, Rlo := digs D 80 3, Rhi := digs D 83 3,
      R := digs D 80 3 + tms (2 ^ 24) (digs D 83 3), q1 := digs D 86 3, rr := digs D 89 5,
      rq := digs D 94 5,
      c := fun s => if s == 0 then cst 0 else if s == 9 then D 9
        else digs D (10 + 6 * (s - 1)) 6 - cst (2 ^ 47) } := rfl

theorem carries_eq (r : P6.Row) (D W : ℕ → Aff) : P6.carries r D W =
    (List.range 9).map fun s => W s + r.c s - D s - tms 256 (r.c (s + 1)) := rfl

theorem lines_eq (r : P6.Row) (P : ℕ → Aff) (eps : E) (two : Aff) : P6.lines r P eps two =
    [P 1 - r.Blo - tms (2 ^ 23) r.Bhi,
     r.Vlo + Aff.ofConst eps - P 0 - tms (2 ^ 25) r.Blo - r.l1 + tms (2 ^ 48) r.kap,
     r.Vhi - r.Bhi - P 2 - r.kap,
     r.l1 + r.h1 - tms 2 r.sig,
     P 4 + P 5 - r.q1,
     P 6,
     two + r.sig - r.s0 - tms 2 (P 3) - tms (2 ^ 25) r.q1 - tms 2 r.rr,
     r.rr + r.rq - r.sig + cst 1] := rfl

section Row
variable {D : ℕ → Aff} (hD : ∀ j, EntsIn Q (D j))
include hD

theorem entsIn_digs (j n : ℕ) : EntsIn Q (digs D j n) :=
  entsIn_sumTo n fun _ => entsIn_scale _ (hD _)

theorem entsIn_fa : EntsIn Q (fa D) :=
  entsIn_add (entsIn_add (entsIn_add (entsIn_scale _ (hD 58)) (hD 59)) (entsIn_scale _ (hD 60)))
    (entsIn_scale _ (hD 61))

theorem entsIn_fb : EntsIn Q (fb D) := entsIn_add (hD 62) (entsIn_scale _ (hD 63))

theorem ofDigits_c (s : ℕ) : EntsIn Q ((P6.Row.ofDigits D).c s) := by
  rw [ofDigits_eq]
  show EntsIn Q (if s == 0 then cst 0 else if s == 9 then D 9
    else digs D (10 + 6 * (s - 1)) 6 - cst (2 ^ 47))
  by_cases h0 : (s == 0) = true
  · rw [if_pos h0]
    exact entsIn_ofConst _
  · rw [if_neg h0]
    by_cases h9 : (s == 9) = true
    · rw [if_pos h9]
      exact hD 9
    · rw [if_neg h9]
      exact entsIn_sub (entsIn_digs hD _ _) (entsIn_ofConst _)

theorem ofDigits_four : ∀ x ∈ [(P6.Row.ofDigits D).a, (P6.Row.ofDigits D).b,
    (P6.Row.ofDigits D).Rlo, (P6.Row.ofDigits D).Rhi], EntsIn Q x := by
  intro x hx
  rw [ofDigits_eq] at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact entsIn_fa hD
  rcases List.mem_cons.mp hx with rfl | hx
  · exact entsIn_fb hD
  rcases List.mem_cons.mp hx with rfl | hx
  · exact entsIn_digs hD _ _
  rcases List.mem_cons.mp hx with rfl | hx
  · exact entsIn_digs hD _ _
  cases hx

theorem entsIn_carries {W : ℕ → Aff} (hW : ∀ s, EntsIn Q (W s)) :
    ∀ f ∈ P6.carries (P6.Row.ofDigits D) D W, EntsIn Q f := by
  intro f hf
  rw [carries_eq] at hf
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hf
  exact entsIn_sub (entsIn_sub (entsIn_add (hW s) (ofDigits_c hD s)) (hD s))
    (entsIn_scale _ (ofDigits_c hD (s + 1)))

theorem entsIn_lines {P : ℕ → Aff} (hP : ∀ s, EntsIn Q (P s)) (eps : E) {two : Aff}
    (h2 : EntsIn Q two) : ∀ f ∈ P6.lines (P6.Row.ofDigits D) P eps two, EntsIn Q f := by
  intro f hf
  rw [lines_eq, ofDigits_eq] at hf
  have hd := entsIn_digs hD
  have ha := entsIn_fa hD
  have hb := entsIn_fb hD
  have hsig : EntsIn Q (fa D + tms (2 ^ 24) (fb D)) := entsIn_add ha (entsIn_scale _ hb)
  have hkap : EntsIn Q (D 79 - cst 4) := entsIn_sub (hD 79) (entsIn_ofConst _)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_sub (hP 1) (hd _ _)) (entsIn_scale _ (hd _ _))
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_add (entsIn_sub (entsIn_sub (entsIn_sub (entsIn_add (hd _ _) (entsIn_ofConst _))
      (hP 0)) (entsIn_scale _ (hd _ _))) (hd _ _)) (entsIn_scale _ hkap)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_sub (entsIn_sub (hd _ _) (hd _ _)) (hP 2)) hkap
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_add (hd _ _) (hd _ _)) (entsIn_scale _ hsig)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_add (hP 4) (hP 5)) (hd _ _)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hP 6
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_sub (entsIn_sub (entsIn_sub (entsIn_add h2 hsig) (hD 59))
      (entsIn_scale _ (hP 3))) (entsIn_scale _ (hd _ _))) (entsIn_scale _ (hd _ _))
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_add (entsIn_sub (entsIn_add (hd _ _) (hd _ _)) hsig) (entsIn_ofConst _)
  cases hf

end Row

variable {v : Env}

/-- A digit is a cell of the reads plus 128. -/
theorem digitsAt_in {P : String} {i : ℕ} {D : ℕ → Aff} (h : digitsAt v P i = some D) (j : ℕ) :
    InTab v (D j) := by
  unfold digitsAt at h
  obtain ⟨cells, hc, e⟩ := map_some h
  subst e
  exact entsIn_add (inTab_rowCells hc j) (entsIn_ofConst _)

/-- **Groups 4 to 6.** -/
theorem rowsForms_in {H : Heard} {l : List Aff} (h : rowsForms v H = some l) :
    ∀ f ∈ l, InTab v f := by
  have h2 : ∀ i, InTab v (twoM v i) := fun i => by
    unfold twoM
    exact entsIn_ofConst _
  unfold rowsForms at h
  obtain ⟨ends, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Ds, hDs, h⟩ := Option.bind_eq_some_iff.mp h
  have e := Option.some.inj h
  have hAll : ∀ D ∈ Ds, ∀ j, InTab v (D j) :=
    all_mapM (Pr := fun D : ℕ → Aff => ∀ j, InTab v (D j)) (fun _ _ hb => digitsAt_in hb) _ Ds hDs
  intro f hf
  rw [← e] at hf
  simp only [List.mem_append] at hf
  rcases hf with (hf | hf) | hf
  · refine all_flatten_mapM (Pr := InTab v) (fun i x hx => ?_) _ ends h1 f hf
    obtain ⟨D, hD, e'⟩ := map_some hx
    subst e'
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact entsIn_sub (entsIn_slot _)
      (ofDigits_four (fun j => digitsAt_in hD j) z.1 (List.fst_mem_of_mem_zipIdx hz))
  · obtain ⟨c, hc, hfc⟩ := List.mem_flatten.mp hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact entsIn_carries (hAll x.1 (List.fst_mem_of_mem_zipIdx hx)) (fun _ => entsIn_slot _) f hfc
  · obtain ⟨c, hc, hfc⟩ := List.mem_flatten.mp hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact entsIn_lines (hAll x.1 (List.fst_mem_of_mem_zipIdx hx)) (fun _ => entsIn_slot _) _
      (h2 _) f hfc

end OnBytes.Desc.First.K4.Reads
