-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Led.lean: a ledger of claims as one type, and the draw that batches its claims into one, as a
block with `KnowAt` (Cb/G6/Cut.lean).

Definitions, statements and proofs. What the Lean model of the C++ verifier does
(OnBytes/Model/Hide.lean: its `Ent`, `Aff`, `Fork`): while the messages of a sub-proof are read, no
equation is tested. Each algebraic check becomes a claim: an affine form that must be 0. A form is
made of hidden values under slots (what was shown, less a public factor times an entry of the mask
row), of entries of virtual rows (public combinations of the cells of an array), and of a constant.
Claim number c gets the weight θ^c, and the sum is the one equation that goes on.

Main names:
  J: the entries that claims read, a finite type of the caller's.
  `Form E J`: coefficients on the entries and a target. `Form.Holds`.
  `Ledger E J`: a list of forms: the claims in the order in which they were added. `Ledger.Holds`.
  `Aff E J` (this file's): an affine form. `Aff.claim`: the claim that it is 0. `Aff.hid`,
    `Aff.vrow`: that model's two kinds of term.
  `Ledger.batch L θ`: the one form: the sum of θ^c times claim c. `Ledger.batch_holds`.
  `Ledger.cnt_batch`: if some claim fails, at most length - 1 elements θ make the batch hold.
  `batch_knowAt`: the draw of θ as a block with `KnowAt`, from "every claim of the ledger holds" to
    "the one form holds", with the error n - 1, on the statements whose ledger has at most n claims.

Limits: nothing on an honest prover or on zero knowledge; "hidden" and "mask" are names. That a
ledger, or a term, is the model's or the programs' own at any sub-proof is not said here.

-/
import Cb.G6.Join
import Cb.G6.Johnson.Layers.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb IOR Johnson.L5.Layers Finset

/-- Coefficients on the entries, and a target. -/
structure Form (E J : Type) where
  co : J → E
  tg : E

/-- The claims of a sub-proof, in the order in which they were added. -/
abbrev Ledger (E J : Type) := List (Form E J)

/-- An affine form in the entries. -/
structure Aff (E J : Type) where
  co : J → E
  c0 : E

section
variable {E J : Type} [Field E] [Fintype J]

/-- The form at the entries m, less its target. -/
def Form.gap (f : Form E J) (m : J → E) : E := ∑ j, f.co j * m j - f.tg
/-- The form meets its target at the entries m. -/
def Form.Holds (f : Form E J) (m : J → E) : Prop := f.gap m = 0
/-- Every claim of the ledger holds. -/
def Ledger.Holds (L : Ledger E J) (m : J → E) : Prop := ∀ f ∈ L, f.Holds m

/-- The value of an affine form at the entries m. -/
def Aff.val (a : Aff E J) (m : J → E) : E := ∑ j, a.co j * m j + a.c0
/-- The claim that the affine form is 0. -/
def Aff.claim (a : Aff E J) : Form E J := ⟨a.co, -a.c0⟩
theorem Aff.claim_holds (a : Aff E J) (m : J → E) : a.claim.Holds m ↔ a.val m = 0 := by
  unfold Aff.claim Form.Holds Form.gap Aff.val
  rw [sub_neg_eq_add]

/-- The one form: the sum of the claims, claim number c under the weight θ^c. -/
def Ledger.batch (L : Ledger E J) (θ : E) : Form E J :=
  ⟨fun j => ∑ c : Fin L.length, θ ^ (c : ℕ) * (L.get c).co j,
    ∑ c : Fin L.length, θ ^ (c : ℕ) * (L.get c).tg⟩

theorem Ledger.batch_gap (L : Ledger E J) (θ : E) (m : J → E) :
    (L.batch θ).gap m = ∑ c : Fin L.length, θ ^ (c : ℕ) * (L.get c).gap m := by
  have h1 : ∑ j, (∑ c : Fin L.length, θ ^ (c : ℕ) * (L.get c).co j) * m j =
      ∑ c : Fin L.length, θ ^ (c : ℕ) * ∑ j, (L.get c).co j * m j := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring
  show ∑ j, (∑ c : Fin L.length, θ ^ (c : ℕ) * (L.get c).co j) * m j -
      ∑ c : Fin L.length, θ ^ (c : ℕ) * (L.get c).tg =
    ∑ c : Fin L.length, θ ^ (c : ℕ) * (∑ j, (L.get c).co j * m j - (L.get c).tg)
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1]

theorem Ledger.batch_holds (L : Ledger E J) (θ : E) (m : J → E) (h : L.Holds m) :
    (L.batch θ).Holds m := by
  show (L.batch θ).gap m = 0
  rw [L.batch_gap]
  exact Finset.sum_eq_zero fun c _ => by
    have : (L.get c).gap m = 0 := h _ (List.get_mem L c)
    rw [this, mul_zero]

theorem Ledger.cnt_batch [Fintype E] (L : Ledger E J) (m : J → E) (h : ¬ L.Holds m) :
    cnt (fun θ => (L.batch θ).Holds m) ≤ L.length - 1 := by
  have ha : (fun c : Fin L.length => (L.get c).gap m) ≠ 0 := by
    intro h0
    apply h
    intro f hf
    obtain ⟨c, rfl⟩ := List.mem_iff_get.1 hf
    exact congrFun h0 c
  refine le_trans (cnt_mono fun θ hθ => ?_) (cnt_badPow fun c : Fin L.length => (L.get c).gap m)
  exact ⟨ha, by rw [← L.batch_gap]; exact hθ⟩

end

/-! ### The model's two kinds of term -/

section Terms
variable {E C S : Type} [Field E]

/-- The hidden value under slot j: what was shown, less the public factor times entry j of the mask
row. -/
def Aff.hid [DecidableEq S] (vp mf : S → E) (j : S) : Aff E (C ⊕ S) :=
  ⟨fun i => match i with | .inl _ => 0 | .inr s => if s = j then -mf j else 0, vp j⟩

/-- An entry of a virtual row: a public combination of cells. -/
def Aff.vrow (w : C → E) : Aff E (C ⊕ S) :=
  ⟨fun i => match i with | .inl c => w c | .inr _ => 0, 0⟩

theorem Aff.hid_val [DecidableEq S] [Fintype C] [Fintype S] (vp mf : S → E) (j : S)
    (m : C ⊕ S → E) :
    (Aff.hid (C := C) vp mf j).val m = vp j - mf j * m (.inr j) := by
  unfold Aff.hid Aff.val
  rw [Fintype.sum_sum_type]
  simp [Finset.sum_ite_eq', sub_eq_add_neg, add_comm]

theorem Aff.vrow_val [Fintype C] [Fintype S] (w : C → E) (m : C ⊕ S → E) :
    (Aff.vrow (S := S) w).val m = ∑ c, w c * m (.inl c) := by
  unfold Aff.vrow Aff.val
  rw [Fintype.sum_sum_type]
  simp

end Terms

/-! ### The batching draw as a block -/

section Block
variable {E J : Type} [Field E] [Fintype E] [Fintype J]

/-- The joint "every claim of the ledger holds", on the statements with at most n claims. P:
whatever public data rides along. -/
def ledIn {K M Wp P : Type} (Ex : ExtSpec) (n : ℕ) (msg : M → J → E) (core : M × Wp → K) :
    Rels K (P × Ledger E J) Ex (M × Wp) :=
  ⟨fun x _ w => x.2.Holds (msg w.1), fun a w => a.1.2.Holds (msg w.1), fun a => a.1.2.length ≤ n,
    core⟩

/-- The joint "the one form holds". -/
def ledOut {K M Wp P : Type} (Ex : ExtSpec) (msg : M → J → E) (core : M × Wp → K) :
    Rels K ((P × E) × Form E J) Ex (M × Wp) :=
  ⟨fun x _ w => x.2.Holds (msg w.1), fun a w => a.1.2.Holds (msg w.1), fun _ => True, core⟩

/-- The new statement: the element drawn is kept, the ledger becomes its batch. -/
def ledNx {P : Type} (x : P × Ledger E J) (θ : E) : (P × E) × Form E J := ((x.1, θ), x.2.batch θ)

/-- The draw that batches a ledger, as a block. -/
theorem batch_knowAt {K M Wp P : Type} (Ex : ExtSpec) (n : ℕ) (msg : M → J → E)
    (core : M × Wp → K) :
    KnowAt (IOR.draw E (ledNx (J := J) (P := P)) Ex) (ledIn Ex n msg core) (ledOut Ex msg core)
      (fun _ _ _ wp => wp) (Nums.draw K E (ledNx (J := J) (P := P)) Ex (n - 1)).err :=
  knowAt_draw _ _ _ (n - 1) (fun _ _ _ _ => trivial) fun x _ m hx => by
    by_cases h : x.2.Holds (msg m)
    · rw [cnt_false fun θ hθ => by
        obtain ⟨_, _, h2⟩ := hθ
        exact h2 h]
      exact Nat.zero_le _
    · refine le_trans (cnt_mono fun θ hθ => ?_)
        (le_trans (x.2.cnt_batch (msg m) h) (Nat.sub_le_sub_right hx 1))
      obtain ⟨_, h1, _⟩ := hθ
      exact h1

end Block

end TWhole
