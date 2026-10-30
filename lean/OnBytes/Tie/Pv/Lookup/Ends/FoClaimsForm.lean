-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoClaimsForm.lean.
The claims of the lookup on the digits, as one list of forms on the committed entries, each under
its own power of theta.

States:
  powSum_zip: Fo.powSum as the sum over a list of (value, exponent) pairs, the exponents rising by
    one from the start.
  coOf f j: the coefficient of entry j in a form on the entries with one entry more (none, read as
    0).
  val_zext_co: over a finite set of entries the value of such a form, where the further entry is
    read as 0, is the sum over the entries of coefficient times entry, and the constant.
  claimsZ_forms_dig: at the letters of Fo.tail_look_dig
    (OnBytes/Tie/Pv/Lookup/Ends/FoTailLook.lean), over a field, there is one list of forms on the
    entries, as many as the flat function's rows and four, whose values are Fo.claimsZ for all
    values of the entries. It is found from the tail's record tl, the two maps of places, the shape,
    the first slot and the rounds rs: before the entries' values; no state of the sub-proof and no
    theta is among these arguments.
  look_batch: Fo.powSum at x from n0 on of the values of a list of forms is the sum over that list
    of x^(n0 + i) times the value of form i. So a total that has grown by Fo.powSum of Fo.claimsZ at
    theta has grown by that sum; no total stands in the statement.
Limit: that the fields of tl which the forms read, and the rounds rs, are fixed before theta is
drawn is not said here: it is the caller's to say of the tl and the rs that it hands in.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed which the coefficients are.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoClaimsAff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.DgP Cb.Fo Cb.LdLkp Finset

section
variable {K : Type} [CommRing K]

theorem powSum_zip (x : K) : ∀ (vals : List K) (s : ℕ),
    powSum x s vals = ((vals.zipIdx s).map fun p => x ^ p.2 * p.1).sum
  | [], _ => rfl
  | v :: vals, s => by
    show x ^ s * v + powSum x (s + 1) vals = _
    rw [powSum_zip x vals (s + 1), List.zipIdx_cons, List.map_cons, List.sum_cons]

variable {J : Type}

/-- The coefficient of entry j. -/
def coOf [DecidableEq J] (f : AffK (Option J) K) (j : J) : K :=
  (f.1.map fun p => if p.1 = some j then p.2 else 0).sum

theorem val_zext_co [Fintype J] [DecidableEq J] (f : AffK (Option J) K) (m : J → K) :
    AffK.val f (zext m) = ∑ j, coOf f j * m j + f.2 := by
  obtain ⟨l, c⟩ := f
  unfold AffK.val coOf
  congr 1
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    rw [ih]
    congr 1
    obtain ⟨o, a⟩ := p
    cases o with
    | none => simp [zext]
    | some i =>
      simp only [zext, Option.some.injEq]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro j _ hj
        rw [if_neg (Ne.symm hj), zero_mul]
      · exact fun h => absurd (Finset.mem_univ _) h

end

section
variable {K : Type} [Field K] {J₀ : Type}

/-- One list of forms for the claims of the lookup on the digits. -/
theorem claimsZ_forms_dig (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (h : FoNums.Sh) (jLK : ℕ)
    (rs : Rounds K) :
    ∃ forms : List (AffK J₀ K), forms.length = (endsOf h 5 jLK rs).rows.length + 4 ∧
      ∀ μ₀ : J₀ → K,
        claimsZ h 5 jLK rs (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (colsK h 5 (endsOf h 5 jLK rs).zb0 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (colsK h 5 (endsOf h 5 jLK rs).zb1 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (fun c => AffK.val (digKF tl en (fun c => (endsOf h 5 jLK rs).zk.getD c []) c) (zext μ₀))
              =
        forms.map fun f => AffK.val f μ₀ := by
  obtain ⟨forms, hf⟩ := claimsZ_forms mk (plV tl en) h 5 jLK rs
    (digKF tl en fun c => (endsOf h 5 jLK rs).zk.getD c [])
  refine ⟨forms, ?_, hf⟩
  have e := congrArg List.length (hf fun _ => 0)
  rw [List.length_map] at e
  rw [← e]
  unfold claimsZ
  simp

/-- Each form under its own power. -/
theorem look_batch (x : K) (n0 : ℕ) (forms : List (AffK J₀ K)) (μ₀ : J₀ → K) :
    powSum x n0 (forms.map fun f => AffK.val f μ₀) =
      ((forms.zipIdx n0).map fun p => x ^ p.2 * AffK.val p.1 μ₀).sum := by
  rw [powSum_zip, List.zipIdx_map, List.map_map]
  rfl

end
end Fo
