-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P6/PositionBridge.lean: THE BRIDGE FROM A NORM's POINT TO EVERY POSITION. The 17
identities of a norm's ledger, which the verifier's forms state AT ONE POINT over the positions,
hold AT EVERY POSITION, but for few points. Statements and proofs.

THE MATTER. For each norm nu and each position X below 2 ^ g there are digits D nu n X and sums
Ws nu s X. The verifier draws a point p of g elements BEHIND the commitment to these, and its 17
forms for the norm nu (OnBytes/Desc/First/P6/NormRow.lean) read, in its world: the digits'
multilinear extensions at p; nine hidden values; seven hidden values. By `carries_value` and
`lines_value` (NormRowLaw.lean) the forms' values are the library's identities with letters for
the products, `idnP`. These are affine in their letters, so they commute with the extension
(`ext_idnP`, Inst/Model/Common/LedgerForms.lean). So IF the nine hidden values are the
extensions of
the positions' sums AND the seven are the extensions of the positions' PRODUCTS, the k-th form of
the norm nu is worth the extension at p of the vector X ↦ idn (np nu) (Ws nu · X) (D nu · X) k; and
the extension of a vector that is not zero vanishes at few points.

  `family_bad`: for a FAMILY of vectors, however large, ONE set of at most g |K| ^ (g - 1) points:
    at a point outside it, if the extensions of ALL members vanish, all members vanish below 2 ^ g.
    (The set is the zeros of the extension of one chosen member that is not zero; none: the empty
    set.)
  `position_bridge`: FIXED FIRST: g; the norms' parameters; the sums; the digits. THEN there is a
    set Bad of at most g |K| ^ (g - 1) points such that at every p outside it: if for every norm and
    every k below 17 `idnP` at the extensions (of the sums, the digits, the products) is 0, then for
    every norm, every k and EVERY POSITION below 2 ^ g the identity `idn` holds at that position.
  `idnP_congr_lt`: the identities with letters read the sums below 9 and the digits below 99 alone.
  `forms_zero`: if the 17 forms are 0 in a world, the identities with letters are 0 at the forms'
    values.
  `position_bridge_forms_lt` (and, weaker, `position_bridge_forms`, which asks hD and hW at every
    number): the same in the forms' own language. The world, the forms and the point come BEHIND
    Bad.

WHAT A CALLER OWES, as named premises of `position_bridge_forms_lt`: hD: the digits' forms are worth
the digits' extensions at p (true reads, whose rows are the equality weights of p); hW: the nine
forms are worth the extensions of the positions' sums (the squares' sumcheck and its batchings); hP:
the seven are worth the extensions of the positions' products (the row products' sumcheck and its
batching); heps, htwo; that the 17 forms are 0. AND THE ORDER IN TIME: that the digits and the sums
are fixed before p is drawn: here it is the order of the letters alone. ALL POSITIONS BELOW 2 ^ g.
The conclusion speaks of every X below 2 ^ g, and so does the premise: the extension runs over all
of them. IF FEWER POSITIONS ARE IN USE, AN HONEST RUN MEETS THE PREMISE ONLY IF ITS TABLES SATISFY
THE IDENTITIES AT THE PADDED POSITIONS TOO: nothing here says that they do. (The library's own
target for a group of layers,
Johnson/Road/Rows/LayerStart.lean's `layer_start_base`, asks the same range.)
`position_bridge_conv`:
where the identities hold at every position below 2 ^ g, the premise holds at every point.
NOT HERE: the ranges of the digits; the step from the field to the integers. Sets are counted; no
probabilities. K is finite.

-/
import OnBytes.Desc.First.P6.NormRowLaw
import OnBytes.Desc.First.P1.BadSets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P6
open OnBytes OnBytes.Model
open Inst.Model (NormPar)
open Inst.Model.Ledger (idn idnP prods)

variable {K : Type} [Field K]

/-- **One bad set for a whole family of vectors.** -/
theorem family_bad [Fintype K] (g : ℕ) {ι : Type} (d : ι → ℕ → K) :
    ∃ Bad : Finset (Fin g → K), Bad.card ≤ g * Fintype.card K ^ (g - 1) ∧
      ∀ p ∉ Bad, (∀ i, Blocks.ext g (d i) (Blocks.nat p) = 0) → ∀ i, ∀ X < 2 ^ g, d i X = 0 := by
  classical
  by_cases h : ∃ i X, X < 2 ^ g ∧ d i X ≠ 0
  · obtain ⟨i0, X0, hX0, hne⟩ := h
    obtain ⟨Bad, hc, _, hb⟩ := OnBytes.Desc.First.P1.point_bad g (d i0)
    exact ⟨Bad, hc, fun p hp hz => absurd (hb p hp (hz i0) X0 hX0) hne⟩
  · refine ⟨∅, by simp, fun _ _ _ i X hX => ?_⟩
    by_contra hne
    exact h ⟨i, X, hX, hne⟩

/-- **THE BRIDGE, as algebra.** -/
theorem position_bridge [Fintype K] (g : ℕ) {ι : Type} (np : ι → NormPar)
    (Ws D : ι → ℕ → ℕ → K) :
    ∃ Bad : Finset (Fin g → K), Bad.card ≤ g * Fintype.card K ^ (g - 1) ∧
      ∀ p ∉ Bad,
        (∀ ν k, k < 17 →
          idnP (np ν) (fun s => Blocks.ext g (Ws ν s) (Blocks.nat p))
            (fun n => Blocks.ext g (D ν n) (Blocks.nat p))
            (fun j => Blocks.ext g (fun X => prods (fun n => D ν n X) j) (Blocks.nat p)) k = 0) →
        ∀ ν k X, X < 2 ^ g → idn (np ν) (fun s => Ws ν s X) (fun n => D ν n X) k = 0 := by
  obtain ⟨Bad, hc, hb⟩ := family_bad g (ι := ι × ℕ)
    (fun x X => idn (np x.1) (fun s => Ws x.1 s X) (fun n => D x.1 n X) x.2)
  refine ⟨Bad, hc, fun p hp hz ν k X hX => hb p hp ?_ (ν, k) X hX⟩
  rintro ⟨ν, k⟩
  show Blocks.ext g (fun X => idn (np ν) (fun s => Ws ν s X) (fun n => D ν n X) k)
    (Blocks.nat p) = 0
  have e : (fun X => idn (np ν) (fun s => Ws ν s X) (fun n => D ν n X) k) = fun X =>
      idnP (np ν) (fun s => Ws ν s X) (fun n => D ν n X)
        (fun j => prods (fun n => D ν n X) j) k := by
    funext X
    exact Inst.Model.Ledger.idn_eq_idnP _ _ _ _
  rw [e, Inst.Model.Ledger.ext_idnP g (D ν) (Blocks.nat p) (np ν) (Ws ν)
    (fun j X => prods (fun n => D ν n X) j) k]
  by_cases hk : k < 17
  · exact hz ν k hk
  · exact Inst.Model.Ledger.idnP_of_le _ _ _ _ (by omega)

/-- **The bridge's premise can hold**: if the identities hold at every position below 2 ^ g, its
premise holds at EVERY point. -/
theorem position_bridge_conv (g : ℕ) {ι : Type} (np : ι → NormPar) (Ws D : ι → ℕ → ℕ → K)
    (h : ∀ ν k X, X < 2 ^ g → idn (np ν) (fun s => Ws ν s X) (fun n => D ν n X) k = 0)
    (u : ℕ → K) (ν : ι) (k : ℕ) :
    idnP (np ν) (fun s => Blocks.ext g (Ws ν s) u) (fun n => Blocks.ext g (D ν n) u)
      (fun j => Blocks.ext g (fun X => prods (fun n => D ν n X) j) u) k = 0 := by
  rw [← Inst.Model.Ledger.ext_idnP g (D ν) u (np ν) (Ws ν)
    (fun j X => prods (fun n => D ν n X) j) k]
  refine Blocks.ext_zero_of_forall (fun X hX => ?_) u
  have e := Inst.Model.Ledger.idn_eq_idnP (np ν) (fun s => Ws ν s X) (fun n => D ν n X) k
  rw [h ν k X hX] at e
  exact e.symm

/-- If the 17 forms are 0 in a world, the identities with letters are 0 at the forms' values. -/
theorem forms_zero (ρ : Reading K) (W : World K) (D Wf P : Nat → Form) (np : NormPar) (eps : E)
    (two : Form) (heps : ρ.val eps = (np.eps : K)) (htwo : two.value ρ W = 2 ^ (np.M + 1))
    (hc : ∀ f ∈ carries (Row.ofDigits D) D Wf, f.value ρ W = 0)
    (hl : ∀ f ∈ lines (Row.ofDigits D) P eps two, f.value ρ W = 0) (k : ℕ) :
    idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) k = 0 := by
  by_cases h9 : k < 9
  · have h := carries_value ρ W D Wf P np
    have hm : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) k ∈
        (carries (Row.ofDigits D) D Wf).map (·.value ρ W) := by
      rw [h]
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr h9, rfl⟩
    obtain ⟨f, hf, hv⟩ := List.mem_map.mp hm
    rw [← hv]
    exact hc f hf
  · by_cases h17 : 17 ≤ k
    · exact Inst.Model.Ledger.idnP_of_le np _ _ _ h17
    · have h := lines_value ρ W D Wf P np eps two heps htwo
      obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
      have hm : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + j) ∈
          (lines (Row.ofDigits D) P eps two).map (·.value ρ W) := by
        rw [h]
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
      obtain ⟨f, hf, hv⟩ := List.mem_map.mp hm
      rw [← hv]
      exact hl f hf

/-! ### The identities read 99 digits and nine sums -/

section Reads
open Inst.Model.Ledger
variable {d d' : ℕ → K}

theorem b256_congr_lt (hD : ∀ n, n < 99 → d n = d' n) (a n : ℕ) (h : a + n ≤ 99) :
    b256 d a n = b256 d' a n := by
  unfold b256
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [hD (a + l) (by have := Finset.mem_range.mp hl; omega)]

theorem cs_congr_lt (hD : ∀ n, n < 99 → d n = d' n) (s : ℕ) (hs : s ≤ 9) : cs d s = cs d' s := by
  unfold cs
  by_cases h0 : s = 0
  · rw [if_pos h0, if_pos h0]
  · by_cases h9 : s = 9
    · rw [if_neg h0, if_neg h0, if_pos h9, if_pos h9, hD 9 (by omega)]
    · rw [if_neg h0, if_neg h0, if_neg h9, if_neg h9,
        b256_congr_lt hD (10 + 6 * (s - 1)) 6 (by omega)]

/-- The identities with letters read the sums below 9 and the digits below 99 alone. -/
theorem idnP_congr_lt (np : NormPar) {w w' : ℕ → K} (pv : ℕ → K)
    (hW : ∀ s, s < 9 → w s = w' s) (hD : ∀ n, n < 99 → d n = d' n) (k : ℕ) :
    idnP np w d pv k = idnP np w' d' pv k := by
  have eVlo : Vlo d = Vlo d' := b256_congr_lt hD 0 6 (by omega)
  have eVhi : Vhi d = Vhi d' := b256_congr_lt hD 6 4 (by omega)
  have el1 : l1 d = l1 d' := b256_congr_lt hD 64 5 (by omega)
  have eh1 : h1 d = h1 d' := b256_congr_lt hD 69 5 (by omega)
  have eBlo : Blo d = Blo d' := b256_congr_lt hD 74 3 (by omega)
  have eBhi : Bhi d = Bhi d' := b256_congr_lt hD 77 2 (by omega)
  have eq1 : q1 d = q1 d' := b256_congr_lt hD 86 3 (by omega)
  have err : rr d = rr d' := b256_congr_lt hD 89 5 (by omega)
  have erq : rq d = rq d' := b256_congr_lt hD 94 5 (by omega)
  have ekc : kc d = kc d' := by unfold kc; rw [hD 79 (by omega)]
  have es0 : s0 d = s0 d' := hD 59 (by omega)
  have esig : sig d = sig d' := by
    unfold sig sa sb
    rw [hD 58 (by omega), hD 59 (by omega), hD 60 (by omega), hD 61 (by omega),
      hD 62 (by omega), hD 63 (by omega)]
  by_cases hk9 : k < 9
  · rw [idnP_j1 np _ _ _ hk9, idnP_j1 np _ _ _ hk9, hW k hk9, cs_congr_lt hD k (by omega),
      hD k (by omega), cs_congr_lt hD (k + 1) (by omega)]
  · unfold idnP
    rw [if_neg hk9, if_neg hk9]
    split <;> first
      | rfl
      | simp only [eVlo, eVhi, el1, eh1, eBlo, eBhi, eq1, err, erq, ekc, es0, esig]

end Reads

/-- **THE BRIDGE, in the forms' own language**, the premises on the digits and the sums asked just
as far as they are read: 99 digits, nine sums. -/
theorem position_bridge_forms_lt [Fintype K] (ρ : Reading K) (g : ℕ) {ι : Type} (np : ι → NormPar)
    (Ws D : ι → ℕ → ℕ → K) :
    ∃ Bad : Finset (Fin g → K), Bad.card ≤ g * Fintype.card K ^ (g - 1) ∧
      ∀ p ∉ Bad, ∀ (W : World K) (Df Wf Pf : ι → Nat → Form) (eps : ι → E) (two : ι → Form),
        (∀ ν, ρ.val (eps ν) = ((np ν).eps : K)) →
        (∀ ν, (two ν).value ρ W = 2 ^ ((np ν).M + 1)) →
        (∀ ν n, n < 99 → (Df ν n).value ρ W = Blocks.ext g (D ν n) (Blocks.nat p)) →
        (∀ ν s, s < 9 → (Wf ν s).value ρ W = Blocks.ext g (Ws ν s) (Blocks.nat p)) →
        (∀ ν j, j < 7 → (Pf ν j).value ρ W =
          Blocks.ext g (fun X => prods (fun n => D ν n X) j) (Blocks.nat p)) →
        (∀ ν, ∀ f ∈ carries (Row.ofDigits (Df ν)) (Df ν) (Wf ν), f.value ρ W = 0) →
        (∀ ν, ∀ f ∈ lines (Row.ofDigits (Df ν)) (Pf ν) (eps ν) (two ν), f.value ρ W = 0) →
        ∀ ν k X, X < 2 ^ g → idn (np ν) (fun s => Ws ν s X) (fun n => D ν n X) k = 0 := by
  obtain ⟨Bad, hc, hb⟩ := position_bridge g np Ws D
  refine ⟨Bad, hc, fun p hp W Df Wf Pf eps two heps htwo hD hW hP hcar hlin => hb p hp ?_⟩
  intro ν k _
  have hz := forms_zero ρ W (Df ν) (Wf ν) (Pf ν) (np ν) (eps ν) (two ν) (heps ν) (htwo ν)
    (hcar ν) (hlin ν) k
  rw [← hz, idnP_congr_lt (np ν) (dv ρ W (Pf ν)) (hW ν) (hD ν) k]
  exact idnP_congr (np ν) _ _ _ _ (fun j hj => (hP ν j hj).symm) k

/-- The same with the two premises asked at every number: a weaker statement. -/
theorem position_bridge_forms [Fintype K] (ρ : Reading K) (g : ℕ) {ι : Type} (np : ι → NormPar)
    (Ws D : ι → ℕ → ℕ → K) :
    ∃ Bad : Finset (Fin g → K), Bad.card ≤ g * Fintype.card K ^ (g - 1) ∧
      ∀ p ∉ Bad, ∀ (W : World K) (Df Wf Pf : ι → Nat → Form) (eps : ι → E) (two : ι → Form),
        (∀ ν, ρ.val (eps ν) = ((np ν).eps : K)) →
        (∀ ν, (two ν).value ρ W = 2 ^ ((np ν).M + 1)) →
        (∀ ν n, (Df ν n).value ρ W = Blocks.ext g (D ν n) (Blocks.nat p)) →
        (∀ ν s, (Wf ν s).value ρ W = Blocks.ext g (Ws ν s) (Blocks.nat p)) →
        (∀ ν j, j < 7 → (Pf ν j).value ρ W =
          Blocks.ext g (fun X => prods (fun n => D ν n X) j) (Blocks.nat p)) →
        (∀ ν, ∀ f ∈ carries (Row.ofDigits (Df ν)) (Df ν) (Wf ν), f.value ρ W = 0) →
        (∀ ν, ∀ f ∈ lines (Row.ofDigits (Df ν)) (Pf ν) (eps ν) (two ν), f.value ρ W = 0) →
        ∀ ν k X, X < 2 ^ g → idn (np ν) (fun s => Ws ν s X) (fun n => D ν n X) k = 0 := by
  obtain ⟨Bad, hc, hb⟩ := position_bridge_forms_lt ρ g np Ws D
  exact ⟨Bad, hc, fun p hp W Df Wf Pf eps two heps htwo hD hW hP hcar hlin =>
    hb p hp W Df Wf Pf eps two heps htwo (fun ν n _ => hD ν n) (fun ν s _ => hW ν s) hP hcar hlin⟩

end OnBytes.Desc.First.P6
