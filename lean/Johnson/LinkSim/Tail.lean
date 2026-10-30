-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/Tail.lean: a tail of r coefficients can take any values at r points, so at up to r
points any change of a code word's message has a compensating change of its tail. Pure algebra over
any field.
Terms of this folder: Johnson/LinkSim/Spec.lean.

The setting. A code word's symbol at a point p is the value at p of the polynomial whose
coefficients are first the r entries of a tail, then the l entries of a message. So the tail holds
the low powers.

What this file has.
  Spec.tailCovers, tailCovers   If pts has at most r points, the first r coefficients of tailFor
                    pts v give the value v x at each point x of pts. Here tailFor pts v is the
                    coefficient list of the polynomial of lowest degree that takes the value v x at
                    each x in pts (Lagrange.interpolate, Mathlib).
  sym_shift         Let pts have at most r points and let p be one of them. Then the message m + dm
                    with tail t has, at p, the same symbol as the message m with tail
                    t + tailShift r l pts dm.
  sym_shift_list    The same at a list of positions under any map from positions to points. The
                    list may repeat a position, and the map need not be injective: what must be at
                    most r is the length of the list.

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/AtText/Sym.lean applies sym_shift_list to the link prover's code words.

Other names (namespace OnBytes.LinkSim).
  tailFor           defined above. It is total, and 0 from the number of points on (tailFor_high).
  tailFor_congr, tailFor_zero, tailFor_add   it depends on v on pts alone; it is 0 where v is 0
                    on pts; it is additive in v.
  sym r l p m t     the symbol at the point p of the message m with the tail t.
  msgPart, tailShift   the message's share of a symbol; the compensating tail, whose values at the
                    points pts are these shares.
  no_cover_short    a negative test: a tail of one entry has the same value at all points, so it
                    cannot take two different values at two points.

Limits. Nothing is said on uniqueness: with fewer points than r other tails do the same. tailShift
is a function of the set of points and of dm.

Sources. sym follows the shape of a code word's symbol in the format's codes (genOf, ldOf,
OnBytes/Slice/LinkAt.lean): the weight of coefficient number k at the point z is z ^ k, the tail's
entries first.

Notes. That sym is the symbol of the format's codes is by inspection, not proved here.
Terms: lean/GLOSSARY.md.

-/
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim
open Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- Coefficient q of the polynomial of lowest degree that takes the value v x at each point x of pts
(Lagrange interpolation). -/
def tailFor (pts : Finset F) (v : F → F) (q : ℕ) : F := (Lagrange.interpolate pts id v).coeff q

/-- tailFor pts v q is 0 once q is at least the number of points. -/
theorem tailFor_high (pts : Finset F) (v : F → F) {q : ℕ} (h : pts.card ≤ q) :
    tailFor pts v q = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
    (Lagrange.degree_interpolate_lt v (Function.injective_id.injOn)) (by exact_mod_cast h))

/-- A tail of r coefficients takes any values at r points: for at most r points, the first r
coefficients of tailFor pts v give v x at each x in pts. Statement only; proved as tailCovers in
this file. -/
def Spec.tailCovers : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] (pts : Finset F) (v : F → F) (r : ℕ), pts.card ≤ r →
    ∀ x ∈ pts, ∑ q ∈ Finset.range r, x ^ q * tailFor pts v q = v x

theorem tailCovers : Spec.tailCovers := by
  intro F _ _ pts v r hr x hx
  have hd := Lagrange.degree_interpolate_lt v (s := pts) (v := id) (Function.injective_id.injOn)
  have hn : (Lagrange.interpolate pts id v).natDegree < r := by
    refine lt_of_lt_of_le ?_ hr
    by_cases h0 : Lagrange.interpolate pts id v = 0
    · rw [h0, natDegree_zero]
      exact Finset.card_pos.mpr ⟨x, hx⟩
    · exact (natDegree_lt_iff_degree_lt h0).mpr hd
  have he := Lagrange.eval_interpolate_at_node v (s := pts) (v := id)
    (Function.injective_id.injOn) hx
  rw [eval_eq_sum_range' hn] at he
  rw [← he]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

/-- tailFor depends on v only through its values on pts. -/
theorem tailFor_congr (pts : Finset F) {v w : F → F} (h : ∀ x ∈ pts, v x = w x) :
    tailFor pts v = tailFor pts w := by
  funext q
  unfold tailFor
  rw [Lagrange.interpolate_eq_of_values_eq_on v w h]

/-- tailFor is 0 when v is 0 on pts. -/
theorem tailFor_zero (pts : Finset F) {v : F → F} (h : ∀ x ∈ pts, v x = 0) :
    tailFor pts v = 0 := by
  rw [tailFor_congr pts (w := 0) h]
  funext q
  unfold tailFor
  rw [map_zero, coeff_zero]
  rfl

/-- tailFor is additive in v. -/
theorem tailFor_add (pts : Finset F) (v w : F → F) :
    tailFor pts (v + w) = tailFor pts v + tailFor pts w := by
  funext q
  show (Lagrange.interpolate pts id (v + w)).coeff q = _
  rw [map_add, coeff_add]
  rfl

/-! ## A code word's symbol -/

/-- The message's share of the symbol at the point p. -/
def msgPart (r l : ℕ) (p : F) (m : ℕ → F) : F := ∑ j ∈ Finset.range l, p ^ (r + j) * m j

/-- The symbol at the point p of the message m with the tail t. -/
def sym (r l : ℕ) (p : F) (m t : ℕ → F) : F :=
  ∑ q ∈ Finset.range r, p ^ q * t q + msgPart r l p m

/-- The compensating tail: its values at the points pts are dm's shares of the symbols there. -/
def tailShift (r l : ℕ) (pts : Finset F) (dm : ℕ → F) : ℕ → F :=
  tailFor pts fun p => msgPart r l p dm

/-- The message's share of a symbol is additive in the message. -/
theorem msgPart_add (r l : ℕ) (p : F) (m m' : ℕ → F) :
    msgPart r l p (m + m') = msgPart r l p m + msgPart r l p m' := by
  unfold msgPart
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => mul_add _ _ _

/-- At a point of pts, with at most r points, the message m + dm with the tail t has the symbol of
the message m with the tail t + tailShift r l pts dm (the compensating tail). -/
theorem sym_shift (r l : ℕ) (pts : Finset F) (hr : pts.card ≤ r) (m dm t : ℕ → F) {p : F}
    (hp : p ∈ pts) : sym r l p (m + dm) t = sym r l p m (t + tailShift r l pts dm) := by
  have h : ∑ q ∈ Finset.range r, p ^ q * tailShift r l pts dm q = msgPart r l p dm :=
    tailCovers F pts (fun p => msgPart r l p dm) r hr p hp
  have e : ∑ q ∈ Finset.range r, p ^ q * (t + tailShift r l pts dm) q =
      ∑ q ∈ Finset.range r, p ^ q * t q + msgPart r l p dm := by
    rw [← h, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => mul_add _ _ _
  unfold sym
  rw [e, msgPart_add]
  ring

/-- The same at a list of positions under a map pt from positions to points. The list's length must
be at most r. -/
theorem sym_shift_list (r l : ℕ) (Q : List ℕ) (pt : ℕ → F) (hQ : Q.length ≤ r) (m dm t : ℕ → F)
    {x : ℕ} (hx : x ∈ Q) :
    sym r l (pt x) (m + dm) t = sym r l (pt x) m (t + tailShift r l (Q.map pt).toFinset dm) :=
  sym_shift r l _ (le_trans (List.toFinset_card_le _) (by rw [List.length_map]; exact hQ)) m dm t
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩))

/-- A negative test: one entry does not take two different values. -/
theorem no_cover_short (v : F → F) {x y : F} (h : v x ≠ v y) :
    ¬ ∃ c : ℕ → F, ∑ q ∈ Finset.range 1, x ^ q * c q = v x ∧
      ∑ q ∈ Finset.range 1, y ^ q * c q = v y := by
  rintro ⟨c, h1, h2⟩
  rw [Finset.sum_range_one, pow_zero, one_mul] at h1 h2
  exact h (h1.symm.trans h2)

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.tailCovers
#print axioms OnBytes.LinkSim.sym_shift
#print axioms OnBytes.LinkSim.sym_shift_list
#print axioms OnBytes.LinkSim.no_cover_short
