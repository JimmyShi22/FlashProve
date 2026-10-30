-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHeadB0.lean: helper B0 of
LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: A CALL THAT THE PROGRAMS' RULE HAS PLACED, AT LETTERS. A WORKING FILE.

No scope, no public files: lists of names and lengths alone.
  placedSegments                 a placed call has a segment for each ask, with the ask's name and length
  tableOfAPlacedCallAtAnEntry    where the layout's search (H.colH's) finds entry x of segment sn in a column, the kind's table (tableOf) holds that entry's value
  tableOfAPlacedCallAtNoEntry    where it finds nothing, the kind's table holds the padding's value
  callTableAtAPlacedCall         so: the kind's callTable at a call IS the match on H.colH, where the layout's call is placed over asks that bear the names
                                 and lengths of the kind's keys of that call
By place_column (Johnson/Desc/Kinds/Law/PlaceColumn.lean), tableOf_entry | tableOf_pad (Kinds/Law/Columns.lean), place_map (Johnson/Road/FormsKeysPos.lean).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadNames
import Johnson.Desc.Kinds.HeadCallLaw
import Johnson.Desc.Kinds.Law.Columns
import Johnson.Desc.Kinds.Law.PlaceColumn
import Johnson.Road.FormsKeysPos
import OnBytes.Tie.Pv.Lookup.Ends.H

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Kinds.Head (Sizes PlaceKey lenOf column)
open VerifiableInference.Desc.Kinds.Head.Law (callTable tableOf callKeys slot place_column)
open VerifiableInference.Desc.Kinds.Head.Law.Came (tableOf_entry tableOf_pad lt_length_of_getD)
open OnBytes.Model (place SegAsk Seg)

/-! ## A placed call, at letters -/

section Placed
variable (name kind : String) (asks : List SegAsk) (floorLg : Nat)

/-- A placed call has a segment for each ask, with the ask's name and length. -/
theorem placedSegments :
    (place name kind asks floorLg).segs.length = asks.length ∧
      ∀ a (h1 : a < (place name kind asks floorLg).segs.length) (h2 : a < asks.length),
        (place name kind asks floorLg).segs[a].name = asks[a].1 ∧
          (place name kind asks floorLg).segs[a].n = asks[a].2.1 := by
  have hm := OnBytes.Road.place_map (fun n k _ => (n, k)) name kind asks floorLg
  have hl : (place name kind asks floorLg).segs.length = asks.length := by
    simpa using congrArg List.length hm
  refine ⟨hl, fun a h1 h2 => ?_⟩
  have e := List.getElem_of_eq hm (i := a) (by simpa using h1)
  simp only [List.getElem_map] at e
  exact ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩

theorem lengthAt {a : Nat} (h2 : a < asks.length) : (asks.map (·.2.1)).getD a 0 = asks[a].2.1 := by
  rw [List.getD_eq_getElem _ _ (by simpa using h2), List.getElem_map]

variable {name kind asks floorLg}
variable {α : Type} (lengthsSmall : ∀ n ∈ asks.map (·.2.1), n < 2 ^ 41)
  (oneColumnAnEntry : ∀ g ∈ (place name kind asks floorLg).segs, g.pos.size = g.n)
  (kinds : Nat → Nat → α) (librarys : String → Nat → α)
  (agree : ∀ a (h2 : a < asks.length) x, x < asks[a].2.1 → kinds a x = librarys asks[a].1 x)
  (pad : α) (col : Nat)

include lengthsSmall oneColumnAnEntry agree in
/-- Where the layout's search finds entry x of the segment named sn in a column, the kind's table holds that entry's value. -/
theorem tableOfAPlacedCallAtAnEntry {sn : String} {x : Nat}
    (found : (place name kind asks floorLg).segs.findSome?
      (fun g => (g.pos.findIdx? (· == col)).map fun x => (g.name, x)) = some (sn, x)) :
    tableOf (asks.map (·.2.1)) kinds pad col = librarys sn x := by
  obtain ⟨hl, facts⟩ := placedSegments name kind asks floorLg
  obtain ⟨g0, hg0, h0⟩ := List.exists_of_findSome?_eq_some found
  cases hx0 : g0.pos.findIdx? (· == col) with
  | none =>
    rw [hx0] at h0
    cases h0
  | some x0 =>
    rw [hx0] at h0
    have e : (g0.name, x0) = (sn, x) := Option.some.inj h0
    obtain ⟨hi, hp0, _⟩ := Array.findIdx?_eq_some_iff_getElem.1 hx0
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨a, h1, hga⟩ := List.getElem_of_mem hg0
    have h2 : a < asks.length := hl ▸ h1
    obtain ⟨f1, f2⟩ := facts a h1 h2
    rw [hga] at f1 f2
    have hxa : x0 < asks[a].2.1 := by
      rw [← f2, ← oneColumnAnEntry g0 hg0]
      exact hi
    have hx : x0 < (asks.map (·.2.1)).getD a 0 := by
      rw [lengthAt asks h2]
      exact hxa
    have pc := place_column name kind asks floorLg a x0 h2 lengthsSmall hx
    rw [List.getD_eq_getElem _ _ h1, hga] at pc
    have h9 : g0.pos[x0] = col := by simpa using hp0
    have h10 : g0.pos.getD x0 0 = g0.pos[x0] := by simp [Array.getD, hi]
    rw [h10, h9] at pc
    rw [pc, tableOf_entry lengthsSmall kinds pad hx, agree a h2 x0 hxa, ← f1, e1, e2]

include lengthsSmall oneColumnAnEntry in
/-- Where the layout's search finds nothing in a column, the kind's table holds the padding's value. -/
theorem tableOfAPlacedCallAtNoEntry
    (found : (place name kind asks floorLg).segs.findSome?
      (fun g => (g.pos.findIdx? (· == col)).map fun x => (g.name, x)) = none) :
    tableOf (asks.map (·.2.1)) kinds pad col = pad := by
  obtain ⟨hl, facts⟩ := placedSegments name kind asks floorLg
  refine tableOf_pad _ kinds pad fun s x hx hcol => ?_
  have h2 : s < asks.length := by simpa using lt_length_of_getD hx
  have h1 : s < (place name kind asks floorLg).segs.length := hl ▸ h2
  have hg : (place name kind asks floorLg).segs[s] ∈ (place name kind asks floorLg).segs :=
    List.getElem_mem h1
  have h4 := List.findSome?_eq_none_iff.mp found _ hg
  have h5 : (place name kind asks floorLg).segs[s].pos.findIdx? (· == col) = none := by
    cases h : (place name kind asks floorLg).segs[s].pos.findIdx? (· == col) with
    | none => rfl
    | some a =>
      rw [h] at h4
      cases h4
  have hxs : x < (place name kind asks floorLg).segs[s].pos.size := by
    rw [oneColumnAnEntry _ hg, (facts s h1 h2).2, ← lengthAt asks h2]
    exact hx
  have h6 := Array.findIdx?_eq_none_iff.1 h5 _ (Array.getElem_mem hxs)
  have pc := place_column name kind asks floorLg s x h2 lengthsSmall hx
  rw [List.getD_eq_getElem _ _ h1,
    show (place name kind asks floorLg).segs[s].pos.getD x 0 =
      (place name kind asks floorLg).segs[s].pos[x] from by simp [Array.getD, hxs], hcol] at pc
  simp [pc] at h6

end Placed

/-! ## A call of the kind against a call of a layout -/

/-- **At one call**: where the layout's call is placed over asks that bear the names and lengths of the kind's keys of that call. -/
theorem callTableAtAPlacedCall {K : Type} [sizes : Sizes] (layout : OnBytes.Model.Head.HL) (call : Nat)
    (name kind : String) (asks : List SegAsk) (floorLg : Nat)
    (callIsPlaced : layout.calls.getD call default = place name kind asks floorLg)
    (keysAreTheAsks : (callKeys call).map (fun k => (segmentName k, lenOf k)) =
      asks.map fun a => (a.1, a.2.1))
    (lengthsSmall : ∀ n ∈ asks.map (·.2.1), n < 2 ^ 41)
    (oneColumnAnEntry : ∀ g ∈ (layout.calls.getD call default).segs, g.pos.size = g.n)
    (kindsValues : PlaceKey → Nat → Nat → K) (librarysValues : String → Nat → Nat → K) (t : Nat)
    (valuesAgree : ∀ key x, x < lenOf key →
      kindsValues key x t = librarysValues (segmentName key) x t) (pad : K) (col : Nat) :
    callTable call kindsValues pad col t =
      match OnBytes.Ends.H.colH layout call col with
      | some (sn, x) => librarysValues sn x t
      | none => pad := by
  have hlens : (callKeys call).map lenOf = asks.map (·.2.1) := by
    have e := congrArg (List.map Prod.snd) keysAreTheAsks
    simpa [List.map_map, Function.comp_def] using e
  have hlen : (callKeys call).length = asks.length := by
    simpa using congrArg List.length keysAreTheAsks
  have agree : ∀ a (h2 : a < asks.length) x, x < asks[a].2.1 →
      kindsValues (slot (callKeys call) a) x t = librarysValues asks[a].1 x t := by
    intro a h2 x hx
    have h3 : a < (callKeys call).length := hlen ▸ h2
    have e := List.getElem_of_eq keysAreTheAsks (i := a) (by simpa using h3)
    simp only [List.getElem_map] at e
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    have hs : slot (callKeys call) a = (callKeys call)[a] := by
      unfold slot
      exact List.getD_eq_getElem _ _ h3
    rw [hs, valuesAgree _ x (by rw [e2]; exact hx), e1]
  rw [callIsPlaced] at oneColumnAnEntry
  unfold callTable
  rw [hlens]
  cases hc : OnBytes.Ends.H.colH layout call col with
  | none =>
    unfold OnBytes.Ends.H.colH at hc
    rw [callIsPlaced] at hc
    exact tableOfAPlacedCallAtNoEntry lengthsSmall oneColumnAnEntry _ pad col hc
  | some p =>
    obtain ⟨sn, x⟩ := p
    unfold OnBytes.Ends.H.colH at hc
    rw [callIsPlaced] at hc
    exact tableOfAPlacedCallAtAnEntry lengthsSmall oneColumnAnEntry _
      (fun sn x => librarysValues sn x t) agree pad col hc

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.placedSegments
#print axioms ProofFile.Honest.K3.Term.tableOfAPlacedCallAtAnEntry
#print axioms ProofFile.Honest.K3.Term.tableOfAPlacedCallAtNoEntry
#print axioms ProofFile.Honest.K3.Term.callTableAtAPlacedCall
