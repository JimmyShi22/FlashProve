-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Decode.lean: SMALL BRIDGES FOR LEMMA 2b (B7 of the road). `ofK`: from an element
of the field back to its one canonical writing; a set of the field's elements as a list of such.
`roundsOf`: a sumcheck's rounds read by a plain map; it gives what the part's own reader gives.
`movesOf_take`, `movesOf_poly`: a run's moves in front of a round, and that round's polynomial, hang
on the rounds in front and that round's message alone. `hidingAt_length`: the hiding polynomial has
as many coefficients as the sumcheck has scalars of its own.
-/
import Mathlib
import Johnson.Desc.Part.MaskedSumProducts
import Johnson.Desc.Kinds.Law.Ledger
import Johnson.Desc.Kinds.Law.Mle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE okE)
open OnBytes.Model (Aff Fork Reading World)
open Part.MaskedSum (Var VarsRead Sent scalars movesOf hidingAt ownSlots powersFrom)

/-! ## From the field back to E -/

/-- The canonical writing of an element of the field. -/
def ofK (x : K) : E := E.ofTriple (OnBytes.Slice.ofE x)

theorem rd_ofK (x : K) : rd (ofK x) = x := by
  show OnBytes.Slice.toE (E.ofTriple (OnBytes.Slice.ofE x)).triple = x
  rw [E.triple_ofTriple]
  exact OnBytes.Slice.toE_ofE x

theorem okE_ofK (x : K) : okE (ofK x) = true := by
  unfold ofK
  rw [OnBytes.okE_triple, E.triple_ofTriple]
  simp [Fmt.Fld.okE, OnBytes.Slice.ofE, OnBytes.Slice.ok_ofF]

theorem ofK_rd {x : E} (h : okE x = true) : ofK (rd x) = x := eq_of_rd (okE_ofK _) h (rd_ofK _)

/-- A canonical element that is not in the list of a set's writings is not read into the set. -/
theorem not_mem_of_list {s : Finset K} {x : E} (hx : okE x = true)
    (h : x ∉ s.toList.map ofK) : rd x ∉ s := by
  intro hm
  apply h
  rw [List.mem_map]
  exact ⟨rd x, Finset.mem_toList.mpr hm, ofK_rd hx⟩

/-! ## The rounds, by a plain map -/

def roundsOf (rs : List Fmt.RoundView) : List (List E × E) :=
  rs.map fun r => ((scalars r.vals).getD [], E.ofTriple (r.drawn.elems.headD (0, 0, 0)))

theorem roundsOf_read : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    VarsRead vs used l → roundsOf used = l
  | [], [], [], _ => rfl
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim
  | v :: vs, r :: rs, (s, g) :: l, h => by
    obtain ⟨⟨h1, _, h3, h4⟩, h5⟩ := h
    have ih := roundsOf_read h5
    unfold roundsOf at ih ⊢
    rw [List.map_cons, ih, h1]
    cases he : r.drawn.elems with
    | nil => rw [he] at h3; simp at h3
    | cons e es =>
      rw [he] at h4
      simp only [List.map_cons, List.cons.injEq] at h4
      simp only [Option.getD_some, List.headD_cons]
      rw [h4.1]

/-! ## A run's moves hang on what stands in front -/

theorem movesOf_take (ρ : Reading K) : ∀ (j : Nat) (vs : List Var) (l l' : List (List E × E)) (c : E),
    l.take j = l'.take j → (movesOf ρ vs l c).take j = (movesOf ρ vs l' c).take j
  | 0, _, _, _, _, _ => by simp
  | j + 1, [], l, l', c, _ => by simp [movesOf]
  | j + 1, v :: vs, [], [], c, _ => rfl
  | j + 1, v :: vs, [], x :: xs, c, h => by simp at h
  | j + 1, v :: vs, x :: xs, [], c, h => by simp at h
  | j + 1, v :: vs, x :: xs, x' :: xs', c, h => by
    simp only [List.take_succ_cons, List.cons.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [movesOf, List.take_succ_cons]
    rw [movesOf_take ρ j vs xs xs' _ h2]

theorem movesOf_poly (ρ : Reading K) : ∀ (j : Nat) (vs : List Var) (l l' : List (List E × E)) (c : E),
    l.take j = l'.take j → (l[j]?).map (·.1) = (l'[j]?).map (·.1) →
    ((movesOf ρ vs l c)[j]?).map (·.1) = ((movesOf ρ vs l' c)[j]?).map (·.1)
  | _, [], l, l', c, _, _ => by simp [movesOf]
  | 0, v :: vs, [], [], c, _, _ => rfl
  | 0, v :: vs, [], x :: xs, c, _, h => by simp at h
  | 0, v :: vs, x :: xs, [], c, _, h => by simp at h
  | 0, v :: vs, x :: xs, x' :: xs', c, _, h => by
    simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at h
    simp only [movesOf, List.getElem?_cons_zero, Option.map_some]
    rw [h]
  | j + 1, v :: vs, [], [], c, _, _ => rfl
  | j + 1, v :: vs, [], x :: xs, c, h, _ => by simp at h
  | j + 1, v :: vs, x :: xs, [], c, h, _ => by simp at h
  | j + 1, v :: vs, x :: xs, x' :: xs', c, h, h' => by
    simp only [List.take_succ_cons, List.cons.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [List.getElem?_cons_succ] at h'
    simp only [movesOf, List.getElem?_cons_succ]
    exact movesOf_poly ρ j vs xs xs' _ h2 h'

/-! ## The hiding polynomial's coefficients -/

theorem hidingAt_length : ∀ vr : List (Var × E), vr ≠ [] → (∀ x ∈ vr, 1 ≤ x.1.d) →
    (hidingAt vr).1.length = ownSlots (vr.map (·.1))
  | [], h, _ => absurd rfl h
  | [(v, r)], _, hd => by
    have h1 : 1 ≤ v.d := hd (v, r) (by simp)
    show (powersFrom r v.d oneE).length = ownSlots [v]
    rw [Part.MaskedSum.powersFrom_length, Part.MaskedSum.ownSlots_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | (v, r) :: y :: rest, _, hd => by
    have ih := hidingAt_length (y :: rest) (by simp) fun x hx => hd x (by simp [hx])
    show (powersFrom r (v.d - 1) _ ++ (hidingAt (y :: rest)).1).length = _
    rw [List.length_append, Part.MaskedSum.powersFrom_length, ih, Part.MaskedSum.ownSlots_eq,
      Part.MaskedSum.ownSlots_eq]
    simp only [List.map_cons, List.sum_cons]
    omega

end VerifiableInference.Desc.Kinds.Head.Law
