--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/OutCallBack.lean: THE WAY BACK, BY THE CALL: from the nine keys' fields of
the output head's two relations on cells to "every place of every call's table, read, is a row's
number of that call's table". Statements and proofs. NO ACCEPTANCE OF ANY TEXT THAT RUNS IS CLAIMED.

Why. Law/OutCall.lean's backCall leads from the six calls' tables to the nine keys, and
Law/TableTie.lean's tie_law from a row's number to a row in the kind's sense InTable: what soundness
spends. Whoever wants to show that honest cells stand in front of the lookup needs both the other
way.

Main names.
  slot_place    key number s of call number call has the place (call, s).
  NineKeys tab c   the nine fields: BackCallStatement's conclusion; nineKeys_of_calls: backCall ends
    in it.
  forthCall     THE CONVERSE OF backCall: if each of the nine keys, at every entry and position, is
    a row of its table, and row 0 of the table of Lemma 1 holds 2^F, then every place of every
    call's table is a row of the call's table: AT EVERY COLUMN, those beyond 2^lJ too: a column is
    an entry's (Law/Columns.lean: tableOf_entry) or nobody's, and then it holds the padding key
    (tableOf_pad), which is a row (Law/OutCall.lean: pads).
  tieBack       THE CONVERSE OF tie_law's step: where the test rowsOk passes on the rows as numbers,
    a row in the sense InTable (tabOf row) is the image of a row's number.
  rows_back     the two together, read into the field.

Limits. ONE WAY each. The tests on the plan (planOk) and on the rows (rowsOk) are premises. The nine
fields are a premise: from the library's clauses to them: Law/LibBack.lean, Law/LibBackNorm.lean.
Positions below T alone. c is a letter. No chance in it.
Not claimed: anything on completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Kinds.Law.TableTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E okE)
open Norm (lt ls d S2 T)

/-- Key number s of call number call has the place (call, s). -/
theorem slot_place : ∀ call, call < 6 → ∀ s, s < (callKeys call).length →
    placeOf (slot (callKeys call) s) = (call, s) := by decide

section Sized
variable [Sizes] [Policy] [Request] [Token]

/-- The nine keys' fields of the head's two relations on cells: BackCallStatement's conclusion
(HeadOutLaw.lean), to the letter. -/
def NineKeys (tab : Nat → Nat) (c : NCells) : Prop :=
  (∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c.toCells (corner x t) .marginTop)) ∧
  (∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c.toCells (corner x t) .marginMid)) ∧
  (∀ t, t < T → ∀ x, x < JV → InBits 8 (keyAt c.toCells (corner x t) .marginLow)) ∧
  (∀ t, t < T → ∀ x, x < len .tableA → IsRow tab (keyAt c.toCells (corner x t) .tableA)) ∧
  (∀ t, t < T → ∀ x, x < len .tableB → IsRow tab (keyAt c.toCells (corner x t) .tableB)) ∧
  (∀ t, t < T → ∀ x, x < d → InBits 16 (keyNAt c (cornerN x t) .remLow)) ∧
  (∀ t, t < T → ∀ x, x < d → InBits 16 (keyNAt c (cornerN x t) .remHigh)) ∧
  (∀ t, t < T → ∀ x, x < d → IsClampRow (keyNAt c (cornerN x t) .clamp)) ∧
  (∀ t, t < T → ∀ j, j < NR + 21 → InBits 8 (keyNAt c (cornerN j t) .digits))

/-- backCall ends in it. -/
theorem nineKeys_of_calls (sT floor : Nat) (tab : Nat → Nat) (c : NCells)
    (hplan : planOk sT = true)
    (h : ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      InTable tab call (keyTable c call col t)) : NineKeys tab c :=
  backCall sT floor tab c hplan h

/-- **FORTH, BY THE CALL.** -/
theorem forthCall (sT : Nat) (tab : Nat → Nat) (c : NCells) (hplan : planOk sT = true)
    (h0 : tab 0 = 2 ^ F) (h : NineKeys tab c) :
    ∀ call, call < 6 → ∀ col t, t < T → InTable tab call (keyTable c call col t) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := h
  have key : ∀ (k : PlaceKey) (x t : Nat), x < lenOf k → t < T →
      InTable tab (placeOf k).1 (cornerKey c k x t) := by
    intro k x t hx ht
    rcases k with k | k <;> cases k
    · exact k6 t ht x hx
    · exact k7 t ht x hx
    · exact k8 t ht x hx
    · exact k9 t ht x hx
    · exact k1 t ht x hx
    · exact k2 t ht x hx
    · exact k3 t ht x hx
    · exact k4 t ht x hx
    · exact k5 t ht x hx
  intro call hcall col t ht
  unfold keyTable callTable
  by_cases hc : ∃ s x, x < ((callKeys call).map lenOf).getD s 0 ∧
      column ((callKeys call).map lenOf) s x = col
  · obtain ⟨s, x, hx, rfl⟩ := hc
    rw [tableOf_entry (lens41 hplan call) _ _ hx]
    have hs : s < (callKeys call).length := by
      have h1 := lt_length_of_getD hx
      rwa [List.length_map] at h1
    have e : ((callKeys call).map lenOf).getD s 0 = lenOf (slot (callKeys call) s) := by
      unfold slot
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hs),
        List.getD_eq_getElem _ _ hs, List.getElem_map]
    have h1 := key (slot (callKeys call) s) x t (by rw [← e]; exact hx) ht
    rw [slot_place call hcall s hs] at h1
    exact h1
  · rw [tableOf_pad _ _ _ fun s x hx he => hc ⟨s, x, hx, he⟩]
    exact pads tab h0 call hcall

end Sized

/-- **THE TIE, BACK.** -/
theorem tieBack [Sizes] (row : Nat → Nat → Nat) (h : rowsOk row = true) :
    ∀ call, call < 6 → ∀ e : E, InTable (tabOf row) call e →
      ∃ u, u < 2 ^ bitsOf call ∧ e = ((row call u : Nat) : E) := by
  obtain ⟨h16, h8, -⟩ := rowsOk_spec h
  have hrow3 : ∀ u, u < 2 ^ 16 → row 3 u = u + 2 ^ 16 * tabOf row u := by
    intro u hu
    unfold tabOf
    rw [if_pos hu]
    have h1 := Nat.div_add_mod (row 3 u) (2 ^ 16)
    rw [(h16 u hu).2.2.1] at h1
    omega
  intro call hcall e he
  interval_cases call
  · obtain ⟨u, hu, rfl⟩ := he
    exact ⟨u, hu, by rw [(h16 u hu).1]⟩
  · obtain ⟨u, hu, rfl⟩ := he
    exact ⟨u, hu, by rw [(h16 u hu).2.1]⟩
  · obtain ⟨u, hu, rfl⟩ := he
    exact ⟨u, hu, by rw [h8 u hu]⟩
  · obtain ⟨u, hu, rfl⟩ := he
    exact ⟨u, hu, by rw [hrow3 u hu]⟩
  · obtain ⟨u, hu, rfl⟩ := he
    exact ⟨u, hu, by rw [(h16 u hu).2.2.2.2.2.1, hrow3 u hu]⟩
  · obtain ⟨u, hu, rfl⟩ := he
    exact ⟨u, hu, by rw [(h16 u hu).2.2.2.2.2.2]; rfl⟩

/-- **Every place of every call's table, read, is a row's number**, from the nine keys' fields. -/
theorem rows_back [Sizes] [Policy] [Request] [Token] (sT : Nat) (row : Nat → Nat → Nat)
    (c : NCells) (hplan : planOk sT = true) (hrows : rowsOk row = true)
    (h : NineKeys (tabOf row) c) :
    ∀ call, call < 6 → ∀ col t, t < T → ∃ u, u < 2 ^ bitsOf call ∧
      rd (keyTable c call col t) = ((row call u : Nat) : K) := by
  intro call hcall col t ht
  obtain ⟨u, hu, e⟩ := tieBack row hrows call hcall _
    (forthCall sT (tabOf row) c hplan (tables_law row hrows).1.1 h call hcall col t ht)
  exact ⟨u, hu, by rw [e, rd_natCast]⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.slot_place
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.nineKeys_of_calls
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.forthCall
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.tieBack
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rows_back
