-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SmpHeldStays.lean: the sample that the record holds of a tenant of a tree stays,
where the statement keeps every sampled message (`SmpStay`, Johnson/Desc/K1/Law/SmpStay.lean) and
the book of trees grows at its end alone. The four readers are those of Johnson/Desc/SmpRows.lean.

Main names: `find?_congr_mem`; `oracleNo_grows`; `SmpHeldStays` (the statement, as a definition);
`smpHeldStays` (its proof).

What is not claimed. Nothing on a tenant whose sample the record does not hold in front. That a
block's yes gives `SmpStay`, or that the book grows at its end alone, is not shown here. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.SmpRows
import Johnson.Desc.K1.Law.SmpStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1

/-- Two tests that agree on a list's members find the same member. -/
theorem find?_congr_mem {α : Type} {p q : α → Bool} :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
      have ha : p a = q a := h a (by simp)
      have hl := find?_congr_mem l fun b hb => h b (List.mem_cons_of_mem _ hb)
      simp only [List.find?_cons, ha, hl]

/-- A tenant's number in the statement stays where the book grows at its end alone. -/
theorem oracleNo_grows (bk bk' : OnBytes.TreeBook) (more : Array (Nat × Nat)) (j t o : Nat)
    (hp : bk'.place = bk.place ++ more) (h : oracleNo bk j t = some o) :
    oracleNo bk' j t = some o := by
  unfold oracleNo at h ⊢
  rw [hp, Array.size_append, List.range_add, List.find?_append]
  have e : (List.range bk.place.size).find? (fun o => (bk.place ++ more)[o]? == some (j, t)) =
      (List.range bk.place.size).find? (fun o => bk.place[o]? == some (j, t)) :=
    find?_congr_mem _ fun a ha => by
      rw [Array.getElem?_append_left (List.mem_range.1 ha)]
  rw [e, h]
  rfl

/-- A, bk: the statement and the book in front; B, bk': behind; more: the places that the book
gains. -/
def SmpHeldStays : Prop :=
  ∀ (A B : OnBytes.Statement) (bk bk' : OnBytes.TreeBook) (more : Array (Nat × Nat)) (j t : Nat),
    SmpStay A B → bk'.place = bk.place ++ more → smpHeld A bk j t = true →
      oracleNo bk' j t = oracleNo bk j t ∧ smpRows B bk' j t = smpRows A bk j t ∧
        smpSeed B bk' j t = smpSeed A bk j t ∧ smpHeld B bk' j t = true

/-- **The sample that the record holds of tenant t of tree j stays.** -/
theorem smpHeldStays : SmpHeldStays := by
  intro A B bk bk' more j t hS hp hh
  have hh' : (smpSeed A bk j t).isSome = true := hh
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hh'
  unfold smpSeed at hv
  obtain ⟨o, ho, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨rows, hr, -⟩ := Option.bind_eq_some_iff.1 hv
  unfold smpRows at hr
  obtain ⟨o', ho', hr⟩ := Option.bind_eq_some_iff.1 hr
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
  obtain ⟨y, hy, hr⟩ := Option.bind_eq_some_iff.1 hr
  obtain rfl : y = x := Option.some.inj (hy.symm.trans hx)
  have hs : y.sampled = true := by
    by_cases c : (y.sampled && decide (0 < y.shape.answers) &&
        y.sampleRows.size == y.shape.answers) = true
    · simp only [Bool.and_eq_true] at c
      exact c.1.1
    · rw [if_neg c] at hr
      cases hr
  obtain ⟨x', hx', e1, e2, e3⟩ := hS.2 o' y hx hs
  have ho2 : oracleNo bk' j t = some o' := oracleNo_grows bk bk' more j t o' hp ho
  have hrows : smpRows B bk' j t = smpRows A bk j t := by
    unfold smpRows
    rw [ho2, ho]
    show (B.oracles[o']?).bind _ = (A.oracles[o']?).bind _
    rw [hx', hx]
    show (if x'.sampled && decide (0 < x'.shape.answers) &&
        x'.sampleRows.size == x'.shape.answers then some x'.sampleRows else none) =
      (if y.sampled && decide (0 < y.shape.answers) &&
        y.sampleRows.size == y.shape.answers then some y.sampleRows else none)
    rw [e1, e2, e3, hs]
  have hseed : smpSeed B bk' j t = smpSeed A bk j t := by
    unfold smpSeed
    rw [hrows, ho2, ho]
    show (B.oracles[o']?).bind _ = (A.oracles[o']?).bind _
    rw [hx', hx]
    show ((smpRows A bk j t).bind fun rows => (rows[0]?).bind fun r =>
        (seedOf B.codes x'.shape r).map fun sd => (sd, rows.toList.map (·.target))) =
      ((smpRows A bk j t).bind fun rows => (rows[0]?).bind fun r =>
        (seedOf A.codes y.shape r).map fun sd => (sd, rows.toList.map (·.target)))
    rw [hS.1, e1]
  refine ⟨ho2.trans ho.symm, hrows, hseed, ?_⟩
  show (smpSeed B bk' j t).isSome = true
  rw [hseed]
  exact hh'

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.smpHeldStays
