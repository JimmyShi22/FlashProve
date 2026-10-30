-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Reads/GatedEnts.lean: the claims on the end values of the gated products'
layers, and the embedding's claim, name entries inside the families of tables alone. Statements and
proofs.

MADE BY PROGRAM out of the same walk for the array alone, which is not in this file:
`RowsIn` became `EntsIn`, its form at the array became `InTab`
(Johnson/Road/K4/Reads/TermsEnts.lean). No proof is new.

Main names: `entsIn_longA`, `entsIn_xbA`, `entsIn_endForm`, `entsIn_endsL`, `entsIn_gatedL2`,
`entsIn_gatedL`, `entsIn_embL`. The layers' own claims (`Level.row`) are premises.
-/
import Johnson.Road.K4.Reads.TermsEnts
import Johnson.Road.Rows.GatedClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Reads

open OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (Aff Level)
open OnBytes.Model.Layer (Env Heard Pub Ten)

/-! ## Two more readers of the tables -/

theorem entsIn_longA {v : Env} {t : ℕ} {X : Ten} {i jh : ℕ} {a : Aff}
    (h : v.longA t X i jh = some a) : InTab v a := inTab_limbs h

theorem entsIn_xbA {v : Env} {t kh : ℕ} {a : Aff} (h : v.xbA t kh = some a) :
    InTab v a := inTab_limbs h

/-! ## The claims on the gated products -/

theorem entsIn_endForm {v : Env} {t : ℕ} {X : Ten} {e : Array E} {rows blocks stride : ℕ}
    {lamOf : ℕ → ℕ} {first : ℕ} {a : Aff}
    (h : endForm v t X e rows blocks stride lamOf first = some a) : InTab v a := by
  unfold endForm at h
  refine inTab_sumForms (fun x p hp => ?_) h
  obtain ⟨a', ha, e1⟩ := map_some hp
  subst e1
  exact entsIn_longA ha

theorem entsIn_endsL {v : Env} {o : Level} {e : Array E} {t rows blocks stride : ℕ}
    {lamOf : ℕ → ℕ} {first : ℕ} {l : List Aff}
    (h : endsL v o e t rows blocks stride lamOf first = some l) :
    ∀ f ∈ l, InTab v f := by
  unfold endsL at h
  obtain ⟨ts, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tu, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aS, hS, h⟩ := Option.bind_eq_some_iff.mp h
  unfold appL at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z, hz, e1⟩ := map_some h
  obtain ⟨aU, hU, hz⟩ := Option.bind_eq_some_iff.mp hz
  cases hx
  cases hz
  subst e1
  intro f hf
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl
  · exact entsIn_add (entsIn_slot _) (entsIn_endForm hS)
  · exact entsIn_add (entsIn_slot _) (entsIn_endForm hU)

/-- A list laid behind another. -/
theorem entsIn_appL {Q : ℕ → ℕ → ℕ → Prop} {a b : Option (List Aff)} {l : List Aff}
    (h : appL a b = some l) (ha : ∀ x, a = some x → ∀ f ∈ x, EntsIn Q f)
    (hb : ∀ x, b = some x → ∀ f ∈ x, EntsIn Q f) : ∀ f ∈ l, EntsIn Q f := by
  unfold appL at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z, hz, e1⟩ := map_some h
  subst e1
  intro f hf
  rcases List.mem_append.mp hf with h1 | h1
  · exact ha x hx f h1
  · exact hb z hz f h1

theorem entsIn_gatedL2 {P : Pub} {v : Env} {hd2 : Option Level} {l : List Aff}
    (h : gatedL2 P v hd2 = some l) (hr : ∀ o, hd2 = some o → InTab v o.row) :
    ∀ f ∈ l, InTab v f := by
  cases hd2 with
  | none =>
    cases h
    intro f hf
    cases hf
  | some o =>
    refine entsIn_appL h (fun x hx f hf => ?_) fun x hx => ?_
    · cases hx
      rw [List.mem_singleton.mp hf]
      exact hr o rfl
    · obtain ⟨e, -, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨t, -, hx⟩ := Option.bind_eq_some_iff.mp hx
      exact entsIn_endsL hx

/-- Every form of gatedL names entries of the array of the reads alone, if the rows of the two
levels do. -/
theorem entsIn_gatedL {P : Pub} {v : Env} {hd : Level} {hd2 : Option Level} {l : List Aff}
    (h : gatedL P v hd hd2 = some l) (hr : InTab v hd.row)
    (hr2 : ∀ o, hd2 = some o → InTab v o.row) : ∀ f ∈ l, InTab v f := by
  refine entsIn_appL h (fun x hx f hf => ?_) fun x hx => ?_
  · cases hx
    rw [List.mem_singleton.mp hf]
    exact hr
  · obtain ⟨e, -, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨t, -, hx⟩ := Option.bind_eq_some_iff.mp hx
    exact entsIn_appL hx (fun y hy => entsIn_endsL hy) fun y hy => entsIn_gatedL2 hy hr2

/-! ## The claim on the embedding -/

/-- The form of embL names entries of the array of the reads alone. -/
theorem entsIn_embL {v : Env} {H : Heard} {sVE : ℕ} {l : List Aff} (h : embL v H sVE = some l) :
    ∀ f ∈ l, InTab v f := by
  unfold embL at h
  obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  intro f hf
  rw [List.mem_singleton.mp hf]
  refine entsIn_add (entsIn_scale _ (entsIn_slot _)) ?_
  unfold embSum at hs
  refine inTab_sumForms (fun kh p hp => ?_) hs
  obtain ⟨a, ha, e⟩ := map_some hp
  subst e
  exact entsIn_xbA ha

end OnBytes.Desc.First.K4.Reads
