-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/TextSum.lean: the code switch: «A ROW OF THE TEXT HOLDS» ON ENTRIES
(AfterText.lean's TextHolds) IS «THE ROW HOLDS» AS A SUM OVER ALL THAT A WORLD OF TABLES NAMES.

TextHolds sums over the entries of the new sending alone. Whoever closes the group will hold a row
in another dress: the sum, over some finite set F of triples (message, table, index), of the row's
coefficient times a table's value. The two agree if the messages' numbering ids is one to one, F has
every entry's triple, and at every other triple of F the coefficient or the table's value is 0.
hands_on_rows' fifth conjunct, OnlyAt, gives the first of these two inside the tables; a world whose
tables are 0 outside their ranges gives the second.
  nameOf, nameOf_inj  an entry's triple; the map is one to one if ids is
  sum_named    the sum over F is the sum over the entries
  off_of_only  what sum_named asks off the entries, from OnlyAt and «0 outside»
  textHolds_iff  TextHolds at the tables' values ↔ the sum over F is the row's target
LIMITS. tab and F are letters: no world of tables is named. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.AfterText

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H

variable (cs : Codes) (l : List (OracleShape × ℕ)) (ids : ℕ → ℕ)

/-- An entry's triple: message, table, index. -/
def nameOf (n : (sigOf cs l).Ent) : ℕ × Part × ℕ :=
  (ids (entAt cs l n).1, (entAt cs l n).2.1, (entAt cs l n).2.2)

theorem nameOf_inj (hids : Function.Injective ids) : Function.Injective (nameOf cs l ids) := by
  intro a b h
  unfold nameOf at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact entAt_inj cs l (Prod.ext (hids h1) h2)

/-- **The sum over F is the sum over the entries.** -/
theorem sum_named (hids : Function.Injective ids) (r : OnBytes.Row) (tab : ℕ → Part → ℕ → GE)
    (F : Finset (ℕ × Part × ℕ)) (hF : ∀ n, nameOf cs l ids n ∈ F)
    (hoff : ∀ x ∈ F, ¬ Named cs l ids x.1 x.2.1 x.2.2 →
      coefAt r x.1 x.2.1 x.2.2 * tab x.1 x.2.1 x.2.2 = 0) :
    ∑ x ∈ F, coefAt r x.1 x.2.1 x.2.2 * tab x.1 x.2.1 x.2.2 =
      ∑ n : (sigOf cs l).Ent,
        coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 *
          tab (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 := by
  classical
  have himg : Finset.univ.image (nameOf cs l ids) ⊆ F := fun x hx => by
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
    exact hF n
  rw [← Finset.sum_subset himg fun x hx hn => hoff x hx fun ⟨n, a, b, c⟩ =>
    hn (Finset.mem_image.2 ⟨n, Finset.mem_univ _, Prod.ext a (Prod.ext b c)⟩),
    Finset.sum_image fun a _ b _ h => nameOf_inj cs l ids hids h]
  rfl

theorem off_of_only {inside : ℕ → Part → ℕ → Prop} {r : OnBytes.Row} (h : OnlyAt cs l ids inside r)
    (tab : ℕ → Part → ℕ → GE) (F : Finset (ℕ × Part × ℕ))
    (h0 : ∀ x ∈ F, ¬ inside x.1 x.2.1 x.2.2 → tab x.1 x.2.1 x.2.2 = 0) :
    ∀ x ∈ F, ¬ Named cs l ids x.1 x.2.1 x.2.2 →
      coefAt r x.1 x.2.1 x.2.2 * tab x.1 x.2.1 x.2.2 = 0 := by
  intro x hx hn
  by_cases hi : inside x.1 x.2.1 x.2.2
  · have : coefAt r x.1 x.2.1 x.2.2 = 0 := by
      by_contra hc
      exact hn (h _ _ _ hi hc)
    rw [this, zero_mul]
  · rw [h0 x hx hi, mul_zero]

/-- **TextHolds is «the row holds».** -/
theorem textHolds_iff (hids : Function.Injective ids) {inside : ℕ → Part → ℕ → Prop}
    {r : OnBytes.Row} (h : OnlyAt cs l ids inside r) (tab : ℕ → Part → ℕ → GE)
    (F : Finset (ℕ × Part × ℕ)) (hF : ∀ n, nameOf cs l ids n ∈ F)
    (h0 : ∀ x ∈ F, ¬ inside x.1 x.2.1 x.2.2 → tab x.1 x.2.1 x.2.2 = 0) :
    TextHolds cs l ids r
        (fun n => tab (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2) ↔
      ∑ x ∈ F, coefAt r x.1 x.2.1 x.2.2 * tab x.1 x.2.1 x.2.2 = readE r.target := by
  unfold TextHolds
  rw [sum_named cs l ids hids r tab F hF (off_of_only cs l ids h tab F h0)]

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.textHolds_iff
