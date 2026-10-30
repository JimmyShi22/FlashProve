-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/RowMaps.lean: what the rows' tables hold, entry by entry.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: entry i of table 4 ν + k
of rowMaps (Johnson/Desc/K4/Honest/Norms.lean) is the value, on the honest reads with the point
r_tV laid at the bits of token i and with 0 under every slot, of the verifier's form of field k of
norm ν's row. Statements and proofs.

  `flat_get?`, `mapM_eq_map`, `amapM_get`   lists made of stretches; members of what mapM returns.
  `fieldsOf`      the four forms of a row's fields.
  `rowForms_at`   the list of the rows' forms, member by member.
  `rowMaps_at`    the tables, entry by entry.

Not shown here. What a value means: these are laws on how a maker's tables are laid. That the maker
returns anywhere: the statements start from its return.
No property is claimed.
-/
import Johnson.Road.K4.C.CornerKit
import Johnson.Road.K4.C.NormsKit
import OnBytes.Desc.First.K4.RowsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env aff0)
open OnBytes.Desc.First
open OnBytes.Desc.First.K4 (digitsAt mapM_get mapM_range_get)
open OnBytes.Desc.First.K4.Honest

/-- A member of a list made of stretches of one length. -/
theorem flat_get? {α β : Type} (G : α → List β) (k : ℕ) (hk : ∀ a, (G a).length = k) :
    ∀ (l : List α) (i r : ℕ) (hi : i < l.length), r < k →
      (l.flatMap G)[k * i + r]? = (G l[i])[r]?
  | [], i, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, 0, r, _, hr => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
      List.getElem?_append_left (by rw [hk]; exact hr)]
    rfl
  | a :: l, i + 1, r, hi, hr => by
    have e : k * (i + 1) + r = (G a).length + (k * i + r) := by
      rw [hk, Nat.mul_succ]
      omega
    rw [List.flatMap_cons, e, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, flat_get? G k hk l i r (Nat.lt_of_succ_lt_succ hi) hr]
    rfl

/-- What mapM returns is the list of the values, if a total function gives them. -/
theorem mapM_eq_map {α β : Type} {f : α → Option β} (G : α → β) : ∀ (l : List α) (L : List β),
    l.mapM f = some L → (∀ x ∈ l, ∀ y, f x = some y → y = G x) → L = l.map G
  | [], L, h, _ => by
    rw [List.mapM_nil] at h
    exact (Option.some.inj h).symm
  | x :: l, L, h, hG => by
    rw [List.mapM_cons] at h
    obtain ⟨c, hc, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs, hcs, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain rfl : c :: cs = L := Option.some.inj h2
    rw [List.map_cons, hG x (List.mem_cons_self ..) c hc,
      mapM_eq_map G l cs hcs fun y hy => hG y (List.mem_cons_of_mem _ hy)]

/-- Member i of an array made by mapM is made of member i. -/
theorem amapM_get {α β : Type} {f : α → Option β} {a : Array α} {b : Array β}
    (h : a.mapM f = some b) {i : ℕ} {x : α} (hx : a[i]? = some x) :
    ∃ y, f x = some y ∧ b[i]? = some y := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨y, hy, hg⟩ := mapM_get f _ L hL i x (by rw [Array.getElem?_toList]; exact hx)
  exact ⟨y, hy, by rw [List.getElem?_toArray]; exact hg⟩

/-- The verifier's forms of the four fields a, b, Rlo, Rhi of a row of digits. -/
def fieldsOf (Dg : ℕ → Aff) : List Aff :=
  [(P6.Row.ofDigits Dg).a, (P6.Row.ofDigits Dg).b, (P6.Row.ofDigits Dg).Rlo,
    (P6.Row.ofDigits Dg).Rhi]

/-- **The list of the rows' forms, member by member.** -/
theorem rowForms_at {v : Env} {fs : Array Aff} (hfs : rowForms v = some fs) {ν : ℕ}
    (hν : ν < v.y.NI) :
    ∃ Dg, digitsAt v "r_tV" ν = some Dg ∧
      ∀ k, k < 4 → fs[4 * ν + k]? = some ((fieldsOf Dg).getD k aff0) := by
  unfold rowForms at hfs
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hfs
  have e : L = (List.range v.y.NI).map fun ν =>
      fieldsOf ((digitsAt v "r_tV" ν).getD fun _ => aff0) :=
    mapM_eq_map _ _ L hL fun x _ y hy => by
      obtain ⟨Dg, hD, rfl⟩ := Option.map_eq_some_iff.mp hy
      rw [hD]
      rfl
  obtain ⟨b, hb, _⟩ := mapM_range_get _ hL hν
  obtain ⟨Dg, hD, _⟩ := Option.map_eq_some_iff.mp hb
  refine ⟨Dg, hD, fun k hk => ?_⟩
  rw [List.getElem?_toArray, e, ← List.flatMap_def,
    flat_get? _ 4 (fun _ => rfl) (List.range v.y.NI) ν k (by rw [List.length_range]; exact hν) hk,
    List.getElem_range, hD]
  interval_cases k <;> rfl

/-- **The rows' tables, entry by entry.** -/
theorem rowMaps_at {Q : K4Pub} {w : K4In} {p : Pts} {v : Env} {ms : Array Tab}
    (hms : rowMaps Q w p = some ms) (hv : envOf Q p = some v) {ν i : ℕ} (hν : ν < v.y.NI)
    (hi : i < 2 ^ Q.P.y.h.lt) :
    ∃ (Dg : ℕ → Aff) (R : Reads) (fs : Array Aff), digitsAt v "r_tV" ν = some Dg ∧
      readsAt Q w p.fo [("r_tV", cornerPt Q.P.y.h.lt i)] = some R ∧ rowForms v = some fs ∧
      ∀ k, k < 4 → (fieldsOf Dg).getD k aff0 ∈ fs.toList ∧
        affFits v R ((fieldsOf Dg).getD k aff0) = true ∧
        (ms.getD (4 * ν + k) #[]).getD i zeroE =
          valAff v R (fun _ => zeroE) ((fieldsOf Dg).getD k aff0) := by
  unfold rowMaps at hms
  obtain ⟨v', hv', h⟩ := Option.bind_eq_some_iff.mp hms
  obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
  obtain ⟨fs, hfs, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨Rs, hRs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Dg, hD, hk⟩ := rowForms_at hfs hν
  obtain ⟨R, hR, hRi⟩ := amapM_get hRs (i := i) (x := i) (by simp [hi])
  refine ⟨Dg, R, fs, hD, hR, hfs, fun k hk4 => ?_⟩
  obtain ⟨tab, htab, hm1⟩ := amapM_get h (hk k hk4)
  obtain ⟨y, hy, hm2⟩ := amapM_get htab hRi
  unfold valAff? at hy
  split at hy
  · rename_i hfit
    refine ⟨List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk k hk4), hfit, ?_⟩
    have e1 : ms.getD (4 * ν + k) #[] = tab := by
      rw [Array.getD_eq_getD_getElem?, hm1, Option.getD_some]
    have e2 : tab.getD i zeroE = y := by
      rw [Array.getD_eq_getD_getElem?, hm2, Option.getD_some]
    rw [e1, e2]
    exact (Option.some.inj hy).symm
  · cases hy

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.flat_get?
#print axioms OnBytes.Road.K4.C.mapM_eq_map
#print axioms OnBytes.Road.K4.C.amapM_get
#print axioms OnBytes.Road.K4.C.rowForms_at
#print axioms OnBytes.Road.K4.C.rowMaps_at
