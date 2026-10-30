-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Reads/RowsEnts.lean: three more of K4's makers of forms name entries inside
the families of tables alone (`InTab`, Johnson/Road/K4/Reads/TermsEnts.lean). Statements and
proofs.

`entsIn_rowForm`: the claim that a sumcheck leaves (`Psc.rowForm`) names what its start form and
what is kept name, and slots. After `rowsIn_rowForm`
(OnBytes/Tie/Pv/Led/LedRowsPsc.lean).
`rowsForms_in`: GROUPS 4 TO 6: the norms' rows: the four shown values, the nine carries and the
eight lines of each norm (`rowsForms`, OnBytes/Desc/First/K4/Claims.lean; the formulas:
OnBytes/Desc/First/P6/NormRow.lean): every form is made of slots, constants and the row's 99 digits,
and a digit is a cell of the reads plus 128.
`planesParts_in`: GROUP 11: what is kept in the leaves' sumcheck's own claim, and the second and
third claim on the planes (`planesParts`).

`ents`: a tactic: it walks a form through sums, differences, factors and `if`s down to slots,
constants and what the hypotheses give.

Limits: as TermsEnts.lean's.
-/
import Johnson.Road.K4.Reads.TermsEnts
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road OnBytes.Road.Rows

variable {Q : ℕ → ℕ → ℕ → Prop}

/-! ### The claim that a sumcheck leaves -/

theorem entsIn_addSlots {a : Aff} (first : Nat) (form : Array E) (ha : EntsIn Q a) :
    EntsIn Q (addSlots a first form) := by
  unfold addSlots
  rw [← Array.foldl_toList]
  have key : ∀ (l : List E) (s : Nat × Aff), EntsIn Q s.2 → EntsIn Q (l.foldl addSlot s).2 := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons x l ih =>
      rintro ⟨j, u⟩ h
      exact ih _ (entsIn_addMul x h (entsIn_slot j))
  exact key _ _ ha

/-- The claim that a sumcheck leaves. -/
theorem entsIn_rowForm (p : Psc) (S0 : E) {kept : Aff} (hs : EntsIn Q p.start)
    (hk : EntsIn Q kept) : EntsIn Q (p.rowForm S0 kept) := by
  unfold Psc.rowForm
  exact entsIn_addMul _ (entsIn_addMul _ (entsIn_addSlots _ _ (entsIn_ofConst _))
    (entsIn_sub (entsIn_ofConst _) hs)) hk

variable {v : Env}

/-! ### The planes -/

/-- A sum made by a fold that may refuse, each member under a weight. -/
theorem inTab_foldlM_addMul {g : ℕ → Option Aff} {w : ℕ → E}
    (hg : ∀ x a, g x = some a → InTab v a) : ∀ (l : List ℕ) (a s : Aff), InTab v a →
      l.foldlM (fun (f : Aff) c => (g c).map fun x => Aff.addMul f x (w c)) a = some s → InTab v s
  | [], a, s, ha, h => by
    cases h
    exact ha
  | x :: l, a, s, ha, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨p, hp, e⟩ := map_some hb
    subst e
    exact inTab_foldlM_addMul hg l _ s (entsIn_addMul _ ha (hg x p hp)) h

/-- The same for a plain sum. -/
theorem inTab_foldlM_add {g : ℕ → Option Aff} (hg : ∀ x a, g x = some a → InTab v a) :
    ∀ (l : List ℕ) (a s : Aff), InTab v a →
      l.foldlM (fun (f : Aff) c => (g c).map fun x => f + x) a = some s → InTab v s
  | [], a, s, ha, h => by
    cases h
    exact ha
  | x :: l, a, s, ha, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨p, hp, e⟩ := map_some hb
    subst e
    exact inTab_foldlM_add hg l _ s (entsIn_add ha (hg x p hp)) h

theorem planesAt_in {g : Forest.Heard} {lm e : ℕ} {bit : ℕ → ℕ → Option Aff} {s : Aff}
    (hb : ∀ e x a, bit e x = some a → InTab v a) (h : planesAt g lm e bit = some s) :
    InTab v s := by
  unfold planesAt at h
  exact inTab_foldlM_addMul (fun x a ha => hb e x a ha) _ _ s (entsIn_ofConst _) h

/-- **Group 11.** -/
theorem planesParts_in {fo : Forest.Heard} {pp : Aff × List Aff}
    (h : planesParts v fo = some pp) : InTab v pp.1 ∧ ∀ f ∈ pp.2, InTab v f := by
  unfold planesParts at h
  obtain ⟨tB0, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tB1, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tP, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨count, hc, h⟩ := Option.bind_eq_some_iff.mp h
  have e := Option.some.inj h
  have hcol : ∀ (t x : ℕ) (a : Aff),
      (if x < v.y.kbm then v.U3at t x else none) = some a → InTab v a := by
    intro t x a ha
    split at ha
    · exact inTab_U3at ha
    · cases ha
  rw [← e]
  refine ⟨entsIn_scale _ (planesAt_in (fun e x a ha => hcol _ x a ha) h0), ?_⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact entsIn_sub (entsIn_slot _) (planesAt_in (fun e x a ha => hcol _ x a ha) h1)
  · exact inTab_foldlM_add (fun x a ha => hcol _ x a ha) _ _ _ (entsIn_ofConst _) hc

end OnBytes.Desc.First.K4.Reads
