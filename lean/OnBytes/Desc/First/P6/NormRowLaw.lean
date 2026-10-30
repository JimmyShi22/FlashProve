-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P6/NormRowLaw.lean: what the norm's row says: the 17 linear forms of
OnBytes/Desc/First/P6/NormRow.lean (nine carries, the root's four lines, the reciprocal's four),
read
in a world, ARE the library's 17 identities of a normalisation's ledger
(Inst/Model/Common/Ledger.lean, LedgerForms.lean: `idn`, `idnP`), at the values of the digits, of
the nine sums of limb products and of the seven row products.

The setting (OnBytes/Model/HideLaws.lean). A form is a public constant plus public coefficients on
hidden values and on entries of the reads. A reading ρ takes the program's field elements to a
commutative ring K and keeps 0, 1, sums, differences and products. A world W gives every hidden
value
and every entry a value in K. `Aff.value ρ W f` is the form's value there.

Main statements.
  `carries_value`: the nine carries' values are the identities number 0 to 8.
  `lines_value`: the eight lines' values are the identities number 9 to 16, with letters for the
    seven products.
  `row_says`: if all 17 forms are 0 in the world, and the seven forms P have the values of the seven
    products of the row's four fields, then all the library's identities hold at these values.
  `fields_value`: the four fields that the callers compare with shown values (a, b, Rlo, Rhi).
  `row_honest`: the premises of `row_says` can hold together: at one position's honest digits (the
    library's `hon`, under its `HonHyp`) all 17 forms are 0.

AT WHICH WORLD `row_says` IS TO BE LAID. AT EACH POSITION's OWN
WORLD: the world in which D has the values of that one position's digits. Its premise hP (the seven
forms P have the values of the seven PRODUCTS of the row's four fields) can hold only there. IT IS
NOT
MEANT FOR THE VERIFIER's WORLD at the norm's point over the positions, although NormRow.lean's head
speaks of "one norm at one point over the tokens": there the honest P is the extension of the
products, which is not the product of the extended fields: hP fails for honest runs, and `row_says`
is true and says nothing. `carries_value` and `lines_value` hold at every world, that one too, with
letters for the products (`idnP` is affine in the sums, the digits and these letters).
FROM THE VERIFIER's WORLD TO THE POSITIONS' WORLDS one gets by: (a) the reads' rows are the equality
weights of the point; (b) the squares' sumcheck: the nine slots W are the extensions of the
positions'
sums of limb products; (c) the row products' sumcheck at the same point: the seven slots P are the
extensions of the positions' products; then (d) a polynomial that is not zero vanishes at few
points,
the point being drawn behind the commitment to the rows. THAT BRIDGE IS OWED ELSEWHERE (the layers'
own
rounds' and the final norm's laws): nothing of it is here.
WHAT A CALLER OWES BESIDE: the ranges of all 99 digits (the lookup's; the library's step to the
integers needs every one); that the nine sums are the sums of limb products; the library's condition
of admissibility AT THE RUNNING PRIME with the running constants; that the values lie in the base
field, for the step to the integers; and the two premises heps and htwo.

There is no premise on the reading (of the caller's two premises see above): that it takes the
program's numeral n to n, for every n, is the
library's `Fo.ofNat_val` (the field's prime is 0 in every ring that has a reading). No digit is
bounded and nothing is said of integers: the identities hold in K. What they give in the integers,
under
ranges on the digits, is the library's Inst/Model/Common/LedgerSound.lean; the step from K to the
integers is not made here. Nothing is said of probabilities.
-/
import OnBytes.Desc.First.P6.NormRow
import OnBytes.Model.HideLaws
import OnBytes.Tie.Pv.Lookup.Ends.FoNatVal
import Inst.Model.Common.LedgerForms
import Inst.Model.Common.LedgerHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P6
open OnBytes OnBytes.Model
open Inst.Model (NormPar)
open Inst.Model.Ledger (b256 cs sa sb idn idnP prods hon HonHyp Wsum)

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-! ### The file's three notations, written out -/

/-- k times a form. -/
def sm (k : Nat) (f : Form) : Form := Aff.scale f (ofNat k)

/-- A number as a form. -/
def nat (n : Nat) : Form := Aff.ofConst (ofNat n)

/-- n digits from digit j on, in base 256, the lowest first. -/
def dig (D : Nat → Form) (j n : Nat) : Form := sumTo n fun i => sm (256 ^ i) (D (j + i))

theorem sumTo_zero (f : Nat → Form) : sumTo 0 f = nat 0 := rfl

theorem sumTo_succ (n : Nat) (f : Nat → Form) : sumTo (n + 1) f = sumTo n f + f n := by
  unfold sumTo
  rw [List.range_succ, List.foldl_append]
  rfl

theorem carries_eq (r : Row) (D Wf : Nat → Form) :
    carries r D Wf = (List.range 9).map fun s => Wf s + r.c s - D s - sm 256 (r.c (s + 1)) := rfl

theorem root_eq (r : Row) (P : Nat → Form) (eps : E) :
    root r P eps =
      [P 1 - r.Blo - sm (2 ^ 23) r.Bhi,
       r.Vlo + Aff.ofConst eps - P 0 - sm (2 ^ 25) r.Blo - r.l1 + sm (2 ^ 48) r.kap,
       r.Vhi - r.Bhi - P 2 - r.kap,
       r.l1 + r.h1 - sm 2 r.sig] := rfl

theorem reciprocal_eq (r : Row) (P : Nat → Form) (two : Form) :
    reciprocal r P two =
      [P 4 + P 5 - r.q1,
       P 6,
       two + r.sig - r.s0 - sm 2 (P 3) - sm (2 ^ 25) r.q1 - sm 2 r.rr,
       r.rr + r.rq - r.sig + nat 1] := rfl

/-! ### Values -/

section

theorem nat_value (n : Nat) : (nat n).value ρ W = (n : K) := by
  rw [nat, Aff.value_ofConst, Fo.ofNat_val]

theorem sm_value (k : Nat) (f : Form) : (sm k f).value ρ W = (k : K) * f.value ρ W := by
  rw [sm, Aff.value_scale, Fo.ofNat_val]

theorem sumTo_value (n : Nat) (f : Nat → Form) :
    (sumTo n f).value ρ W = ∑ i ∈ Finset.range n, (f i).value ρ W := by
  induction n with
  | zero => rw [sumTo_zero, nat_value ρ W]; simp
  | succ n ih => rw [sumTo_succ, Aff.value_add, ih, Finset.sum_range_succ]

variable (D : Nat → Form)

/-- The digits' values. -/
abbrev dv (ρ : Reading K) (W : World K) (D : Nat → Form) : ℕ → K := fun n => (D n).value ρ W

theorem dig_value (j n : Nat) : (dig D j n).value ρ W = b256 (dv ρ W D) j n := by
  rw [dig, sumTo_value ρ W, b256]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sm_value ρ W, Nat.cast_pow]
  norm_num

theorem Vlo_value : (Row.ofDigits D).Vlo.value ρ W = Inst.Model.Ledger.Vlo (dv ρ W D) :=
  dig_value ρ W D 0 6

theorem Vhi_value : (Row.ofDigits D).Vhi.value ρ W = Inst.Model.Ledger.Vhi (dv ρ W D) :=
  dig_value ρ W D 6 4

theorem l1_value : (Row.ofDigits D).l1.value ρ W = Inst.Model.Ledger.l1 (dv ρ W D) :=
  dig_value ρ W D 64 5

theorem h1_value : (Row.ofDigits D).h1.value ρ W = Inst.Model.Ledger.h1 (dv ρ W D) :=
  dig_value ρ W D 69 5

theorem Blo_value : (Row.ofDigits D).Blo.value ρ W = Inst.Model.Ledger.Blo (dv ρ W D) :=
  dig_value ρ W D 74 3

theorem Bhi_value : (Row.ofDigits D).Bhi.value ρ W = Inst.Model.Ledger.Bhi (dv ρ W D) :=
  dig_value ρ W D 77 2

theorem Rlo_value : (Row.ofDigits D).Rlo.value ρ W = Inst.Model.Ledger.Rlo (dv ρ W D) :=
  dig_value ρ W D 80 3

theorem Rhi_value : (Row.ofDigits D).Rhi.value ρ W = Inst.Model.Ledger.Rhi (dv ρ W D) :=
  dig_value ρ W D 83 3

theorem q1_value : (Row.ofDigits D).q1.value ρ W = Inst.Model.Ledger.q1 (dv ρ W D) :=
  dig_value ρ W D 86 3

theorem rr_value : (Row.ofDigits D).rr.value ρ W = Inst.Model.Ledger.rr (dv ρ W D) :=
  dig_value ρ W D 89 5

theorem rq_value : (Row.ofDigits D).rq.value ρ W = Inst.Model.Ledger.rq (dv ρ W D) :=
  dig_value ρ W D 94 5

theorem s0_value : (Row.ofDigits D).s0.value ρ W = Inst.Model.Ledger.s0 (dv ρ W D) := rfl

theorem a_value : (Row.ofDigits D).a.value ρ W = sa (dv ρ W D) := by
  show (sm 2 (D 58) + D 59 + sm (2 ^ 8) (D 60) + sm (2 ^ 16) (D 61)).value ρ W = _
  simp only [Aff.value_add, sm_value ρ W, sa]
  norm_num

theorem b_value : (Row.ofDigits D).b.value ρ W = sb (dv ρ W D) := by
  show (D 62 + sm (2 ^ 8) (D 63)).value ρ W = _
  simp only [Aff.value_add, sm_value ρ W, sb]
  norm_num

theorem sig_value : (Row.ofDigits D).sig.value ρ W = Inst.Model.Ledger.sig (dv ρ W D) := by
  show ((Row.ofDigits D).a + sm (2 ^ 24) (Row.ofDigits D).b).value ρ W = _
  rw [Aff.value_add, sm_value ρ W, a_value ρ W, b_value ρ W, Inst.Model.Ledger.sig]
  norm_num

theorem kap_value : (Row.ofDigits D).kap.value ρ W = Inst.Model.Ledger.kc (dv ρ W D) := by
  show (D 79 - nat 4).value ρ W = _
  rw [Aff.value_sub, nat_value ρ W, Inst.Model.Ledger.kc]
  norm_num

theorem c_value (s : Nat) : ((Row.ofDigits D).c s).value ρ W = cs (dv ρ W D) s := by
  show (if s == 0 then nat 0 else if s == 9 then D 9
    else dig D (10 + 6 * (s - 1)) 6 - nat (2 ^ 47)).value ρ W = _
  unfold cs
  by_cases h0 : s = 0
  · subst h0
    simp [nat_value ρ W]
  · by_cases h9 : s = 9
    · subst h9
      simp
    · have e0 : (s == 0) = false := by simpa using h0
      have e9 : (s == 9) = false := by simpa using h9
      rw [if_neg h0, if_neg h9]
      simp only [e0, e9, Bool.false_eq_true, if_false]
      rw [Aff.value_sub, dig_value ρ W, nat_value ρ W]
      norm_num

/-- The four fields that the callers compare with shown values. -/
theorem fields_value :
    (Row.ofDigits D).a.value ρ W = sa (dv ρ W D) ∧ (Row.ofDigits D).b.value ρ W = sb (dv ρ W D) ∧
      (Row.ofDigits D).Rlo.value ρ W = Inst.Model.Ledger.Rlo (dv ρ W D) ∧
      (Row.ofDigits D).Rhi.value ρ W = Inst.Model.Ledger.Rhi (dv ρ W D) :=
  ⟨a_value ρ W D, b_value ρ W D, Rlo_value ρ W D, Rhi_value ρ W D⟩

variable (Wf P : Nat → Form) (np : NormPar)

/-- **The nine carries are the identities number 0 to 8.** -/
theorem carries_value :
    (carries (Row.ofDigits D) D Wf).map (·.value ρ W) =
      (List.range 9).map fun s => idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) s := by
  rw [carries_eq, List.map_map]
  refine List.map_congr_left fun s hs => ?_
  have h9 : s < 9 := List.mem_range.mp hs
  rw [Inst.Model.Ledger.idnP_j1 np _ _ _ h9]
  show (Wf s + (Row.ofDigits D).c s - D s - sm 256 ((Row.ofDigits D).c (s + 1))).value ρ W = _
  rw [Aff.value_sub, Aff.value_sub, Aff.value_add, sm_value ρ W, c_value ρ W,
    c_value ρ W]
  norm_num

/-- **The eight lines are the identities number 9 to 16**, with the values of the forms P in the
places of the seven products. eps and two: the norm's constant and 2^(M + 1), as the caller lays
them. -/
theorem lines_value (eps : E) (two : Form) (heps : ρ.val eps = (np.eps : K))
    (htwo : two.value ρ W = 2 ^ (np.M + 1)) :
    (lines (Row.ofDigits D) P eps two).map (·.value ρ W) =
      (List.range 8).map fun k => idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + k) := by
  have hr : (List.range 8) = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [lines, root_eq, reciprocal_eq, hr]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
  have e9 : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + 0) =
      dv ρ W P 1 - Inst.Model.Ledger.Blo (dv ρ W D) - 2 ^ 23 * Inst.Model.Ledger.Bhi (dv ρ W D) :=
    rfl
  have e10 : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + 1) =
      Inst.Model.Ledger.Vlo (dv ρ W D) + (np.eps : K) - dv ρ W P 0 -
        2 ^ 25 * Inst.Model.Ledger.Blo (dv ρ W D) - Inst.Model.Ledger.l1 (dv ρ W D) +
        2 ^ 48 * Inst.Model.Ledger.kc (dv ρ W D) := rfl
  have e11 : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + 2) =
      Inst.Model.Ledger.Vhi (dv ρ W D) - Inst.Model.Ledger.Bhi (dv ρ W D) - dv ρ W P 2 -
        Inst.Model.Ledger.kc (dv ρ W D) := rfl
  have e12 : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + 3) =
      Inst.Model.Ledger.l1 (dv ρ W D) + Inst.Model.Ledger.h1 (dv ρ W D) -
        2 * Inst.Model.Ledger.sig (dv ρ W D) := rfl
  have e13 : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + 4) =
      dv ρ W P 4 + dv ρ W P 5 - Inst.Model.Ledger.q1 (dv ρ W D) := rfl
  have e14 : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + 5) = dv ρ W P 6 := rfl
  have e15 : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + 6) =
      2 ^ (np.M + 1) + Inst.Model.Ledger.sig (dv ρ W D) - Inst.Model.Ledger.s0 (dv ρ W D) -
        2 * dv ρ W P 3 - 2 ^ 25 * Inst.Model.Ledger.q1 (dv ρ W D) -
        2 * Inst.Model.Ledger.rr (dv ρ W D) := rfl
  have e16 : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + 7) =
      Inst.Model.Ledger.rr (dv ρ W D) + Inst.Model.Ledger.rq (dv ρ W D) -
        Inst.Model.Ledger.sig (dv ρ W D) + 1 := rfl
  rw [e9, e10, e11, e12, e13, e14, e15, e16]
  simp only [Aff.value_add, Aff.value_sub, Aff.value_ofConst, sm_value ρ W, nat_value ρ W,
    Vlo_value ρ W, Vhi_value ρ W, l1_value ρ W, h1_value ρ W, Blo_value ρ W,
    Bhi_value ρ W, q1_value ρ W, rr_value ρ W, rq_value ρ W, s0_value ρ W,
    sig_value ρ W, kap_value ρ W, heps, htwo]
  norm_num

/-- **What the row says.** If the nine carries and the eight lines are all 0 in the world, and the
seven forms P have the values of the seven products of the row's fields a, b, Rlo, Rhi, then every
identity of the library's ledger holds, in K, at the digits' values and the values of the nine
sums. -/
theorem row_says (eps : E) (two : Form) (heps : ρ.val eps = (np.eps : K))
    (htwo : two.value ρ W = 2 ^ (np.M + 1))
    (hc : ∀ f ∈ carries (Row.ofDigits D) D Wf, f.value ρ W = 0)
    (hl : ∀ f ∈ lines (Row.ofDigits D) P eps two, f.value ρ W = 0)
    (hP : ∀ j, j < 7 → (P j).value ρ W = prods (dv ρ W D) j) (k : ℕ) :
    idn np (dv ρ W Wf) (dv ρ W D) k = 0 := by
  -- with letters for the products
  have hz : ∀ k, idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) k = 0 := by
    intro k
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
  -- the identities read the products at seven places alone
  have hsame : idnP np (dv ρ W Wf) (dv ρ W D) (prods (dv ρ W D)) k =
      idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) k := by
    have p0 := hP 0 (by omega)
    have p1 := hP 1 (by omega)
    have p2 := hP 2 (by omega)
    have p3 := hP 3 (by omega)
    have p4 := hP 4 (by omega)
    have p5 := hP 5 (by omega)
    have p6 := hP 6 (by omega)
    unfold idnP
    split
    · rfl
    · split <;> simp only [dv, p0, p1, p2, p3, p4, p5, p6]
  rw [Inst.Model.Ledger.idn_eq_idnP, hsame]
  exact hz k

/-- The identities with letters read the letters at seven places alone. -/
theorem idnP_congr (w d pv pv' : ℕ → K) (h : ∀ j, j < 7 → pv j = pv' j) (k : ℕ) :
    idnP np w d pv k = idnP np w d pv' k := by
  have p0 := h 0 (by omega)
  have p1 := h 1 (by omega)
  have p2 := h 2 (by omega)
  have p3 := h 3 (by omega)
  have p4 := h 4 (by omega)
  have p5 := h 5 (by omega)
  have p6 := h 6 (by omega)
  unfold idnP
  split
  · rfl
  · split <;> simp only [p0, p1, p2, p3, p4, p5, p6]

/-- **The premises of `row_says` can hold together**: at one position's honest digits all 17 forms
are
0. d, b: the width and the limbs of that position's stream; `hon`: the library's honest ledger. -/
theorem row_honest {d : ℕ} {b : ℕ → ℕ → ℤ} (H : HonHyp np d b) (eps : E) (two : Form)
    (heps : ρ.val eps = (np.eps : K)) (htwo : two.value ρ W = 2 ^ (np.M + 1))
    (hD : ∀ n, (D n).value ρ W = ((hon np d b n : ℤ) : K))
    (hW : ∀ s, (Wf s).value ρ W = ((Wsum d b s : ℤ) : K))
    (hP : ∀ j, j < 7 → (P j).value ρ W = prods (dv ρ W D) j) :
    (∀ f ∈ carries (Row.ofDigits D) D Wf, f.value ρ W = 0) ∧
      ∀ f ∈ lines (Row.ofDigits D) P eps two, f.value ρ W = 0 := by
  have e1 : dv ρ W Wf = fun s => (Int.castRingHom K) (Wsum d b s) := funext hW
  have e2 : dv ρ W D = fun n => (Int.castRingHom K) (hon np d b n) := funext hD
  have hidn : ∀ k, idn np (dv ρ W Wf) (dv ρ W D) k = 0 := by
    intro k
    rw [e1, e2, ← Inst.Model.Ledger.map_idn]
    by_cases hk : k < 17
    · rw [Inst.Model.Ledger.hon_idn H k hk, map_zero]
    · rw [Inst.Model.Ledger.idn_of_le _ np _ (by omega), map_zero]
  have hz : ∀ k, idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) k = 0 := by
    intro k
    rw [idnP_congr np _ _ (dv ρ W P) (prods (dv ρ W D)) hP k, ← Inst.Model.Ledger.idn_eq_idnP]
    exact hidn k
  constructor
  · intro f hf
    have hm : f.value ρ W ∈ (carries (Row.ofDigits D) D Wf).map (·.value ρ W) :=
      List.mem_map_of_mem hf
    rw [carries_value ρ W D Wf P np] at hm
    obtain ⟨s, _, hs⟩ := List.mem_map.mp hm
    rw [← hs]
    exact hz s
  · intro f hf
    have hm : f.value ρ W ∈ (lines (Row.ofDigits D) P eps two).map (·.value ρ W) :=
      List.mem_map_of_mem hf
    rw [lines_value ρ W D Wf P np eps two heps htwo] at hm
    obtain ⟨s, _, hs⟩ := List.mem_map.mp hm
    rw [← hs]
    exact hz (9 + s)

end

end OnBytes.Desc.First.P6
