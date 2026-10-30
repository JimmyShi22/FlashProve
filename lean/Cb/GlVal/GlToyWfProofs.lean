-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyWfProofs.lean: proofs that the data of the small test instance of the preamble of
weights-formedness in Cb/GlVal/GlToyWf.lean meet the laws of such data (`LdWfP.Laws`) and further
conditions on keys and places that the preamble's theorems take as hypotheses: above all, that the
lookup, over the extension field E, describes the index set, over the base field F.

Statements and proofs on the data of Cb/GlVal/GlToyWf.lean. A guard; no parameter of a protocol. A
guard is a proved statement that stands beside a theorem or a notion: most often an instance that
meets all hypotheses of the theorem.
F = the integers modulo p = 2^64 - 2^32 + 1; E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toy has
one lookup with two keys and the table (5, 7) (`Valid n T w W key t M`, Cb/Ld/LdLkpMult.lean, at n,
T, w, W = 1, 1, 1, 2: 2^n keys, 2^T table entries, 2^w bit positions for each, 0 from W on).
The analogue of Cb/Ld/LdWfToyProofs.lean for two different fields; that toy is over the field with
101 elements, with one field in the place of both. The conditions are `LdWfP.Laws`
(Cb/Ld/LdWf.lean), `LdWfP.LinKeys` (Cb/Ld/LdWfKeys.lean), `LdOWf.Tie` (Cb/Obj/LdObjectWf.lean),
`LdWfP.OwnPlaces` (Cb/Ld/LdWfOwn.lean), and what three clauses of `LdWfP.Lks.OK`
(Cb/Ld/LdWfBlocks.lean) rest on (`places`, `adm`, `rows`); `deg` and `zOK` are clauses of
`LdWfE.Rest2` (Cb/Ld/LdWfEnd.lean).
(Forests, batching: `LdWfP`, Cb/Ld/LdWf.lean.)

Main names:
  `held_iff`, `inT_iff`, `describes`: a message (over F) holds an index if and only if the keys
    (over E) lie in the table (over E): the clause `describes` of `LdWfP.Laws`.
  `tie`, `lin`: the matrix of the index is the index matrix in the layout of the encoded index,
    embedded (`LdOWf.Tie`: `W.P.mat U (r, fun i => c (W.e i)) = W.O.D.mat (W.Cf.upM U) r c`; by
    definition); the key maps are affine in one column of it (`LdWfP.LinKeys rv o co`, here with the
    constant functions 0, 0, 1 for `rv`, `o` (offsets), `co` (coefficients): by definition).
  `multOf`: for a forest f ≤ `P.n` whose keys lie in the table, the honest bits write the
    multiplicities.
  `own`: the batching's own places; `places`: all places of the lookup are named entries other than
    these; `adm`: the lookup's numbers against p; `rows`: `P.nR f` is the lookup's number of rows
    (`nRows`); `deg`: 2 ≤ `P.deg`; `zOK`: the batching's evader has `Evader.OK`.
  `key_eq`, `key_57`, `row_eq`, `valid_of`, `laws`: see their doc comments.

Nothing enumerates a field: every "decide" is on ℕ, Bool or Fin (the rule: the head of
Cb/GlVal/GlToyBase.lean; why: "A trap" in the head of Cb/GlVal/GlToyConf.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyWf
import Cb.Gen.BatEvaderProofs
import Cb.Ld.LdWfKeys

set_option autoImplicit false

namespace Cb.Gl
namespace Wf8
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

theorem tie (Ln : ToyLn) : (W Ln).Tie := fun _ _ _ => rfl

theorem lin : P.LinKeys (fun _ => 0) (fun _ _ => 0) (fun _ _ _ => 1) where
  v := fun _ _ => rfl
  key := fun _ _ _ _ _ => rfl
  off := fun _ _ _ => rfl
  gOf := fun _ _ _ _ => rfl
  cOf := fun _ _ _ _ => rfl

theorem deg : 2 ≤ P.deg := le_refl 2

theorem zOK : P.Z.OK := ok_powers E (0 + 1)

theorem btAt_inj : Function.Injective btAt := fun _ _ h =>
  Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))

theorem bit_ne (x : Ix) (i : WBt) : (Sum.inl x : Nm) ≠ btAt i := fun h => by cases h
theorem mk_ne (x : LkpToyE.Mk E) (i : WBt) : mkAt x ≠ btAt i := fun h => by cases h
theorem idle_ne (i : WBt) : idle ≠ btAt i := fun h => by cases h

theorem own : P.OwnPlaces (fun _ => True) where
  inj := btAt_inj
  own := fun _ => trivial
  mat := fun _ => trivial
  rdC := fun _ _ _ => trivial
  off := fun _ i h => h.elim fun x e => mk_ne x i e.symm

theorem places (l : ℕ) :
    (Kl.asm l).PlacesIn (fun j => ∃ n', j = Sum.inr n' ∧ ∀ i, n' ≠ btAt i) where
  bAt := fun _ _ => ⟨_, rfl, bit_ne _⟩
  wS := fun _ => ⟨_, rfl, mk_ne _⟩
  cS := fun _ => ⟨_, rfl, mk_ne _⟩
  wAt := fun l i => by cases l with
    | zero => exact ⟨_, rfl, mk_ne _⟩
    | succ l => exact ⟨_, rfl, idle_ne⟩
  cAt := fun l b => by cases l with
    | zero => exact ⟨_, rfl, mk_ne _⟩
    | succ l => exact ⟨_, rfl, idle_ne⟩
  wK := fun l i => by cases l with
    | zero => exact ⟨_, rfl, mk_ne _⟩
    | succ l => exact ⟨_, rfl, idle_ne⟩
  cK := fun l b => by cases l with
    | zero => exact ⟨_, rfl, mk_ne _⟩
    | succ l => exact ⟨_, rfl, idle_ne⟩
  wT := fun l i => by cases l with
    | zero => exact ⟨_, rfl, mk_ne _⟩
    | succ l => exact ⟨_, rfl, idle_ne⟩
  cT := fun l b => by cases l with
    | zero => exact ⟨_, rfl, mk_ne _⟩
    | succ l => exact ⟨_, rfl, idle_ne⟩
  wE := fun _ => ⟨_, rfl, mk_ne _⟩
  wB := fun _ => ⟨_, rfl, mk_ne _⟩
  cB := ⟨_, rfl, mk_ne _⟩

theorem oneHot_inj {α : Type} [DecidableEq α] :
    Function.Injective fun (i j : α) => decide (j = i) := fun a b h => by
  have e := congrFun h a
  simp only [decide_true] at e
  exact of_decide_eq_true e.symm

theorem adm (f : ℕ) : (Kl.asm f).H.lkb.Adm p :=
  ⟨(by decide : 2 ≤ 2 ^ 1),
    (by decide : 2 ^ 1 < 2 ^ 2),
    (small (by norm_num) : 2 ^ 1 * (2 ^ 2 - 1) < p)⟩

theorem rows (f : ℕ) : P.nR f = (Kl.asm f).nRows := rfl

/-! ### The keys, the index set, the multiplicities -/

/-- A key is an entry of the index message, embedded. -/
theorem key_eq (U : Cf.conf.Msg) (b : ℕ) :
    key U b = algebraMap F E (U (Alg.bits 1 (b % 2), Sum.inl ())) := by
  show 0 + ∑ r : Unit, 1 * algebraMap F E (U (Alg.bits 1 (b % 2 ^ 1), Sum.inl ())) = _
  simp

/-- "The key is 5 or 7 in E" is "the entry is 5 or 7 in F". -/
theorem key_57 (U : Cf.conf.Msg) (b : ℕ) :
    (key U b = 5 ∨ key U b = 7) ↔
    (U (Alg.bits 1 (b % 2), Sum.inl ()) = 5 ∨ U (Alg.bits 1 (b % 2), Sum.inl ()) = 7) := by
  rw [key_eq, up_eq_ofNat 5, up_eq_ofNat 7]

/-- Each of the two code rows `c` is the column with a number: `Alg.bits 1 (b % 2)`, b = 0 or 1. -/
theorem row_eq (c : Fin 1 → Bool) : c = Alg.bits 1 ((if c 0 then 1 else 0) % 2) := by
  funext v
  obtain rfl : v = 0 := Subsingleton.elim _ _
  cases h : c 0 <;> simp [Alg.bits]

theorem held_iff (U : Cf.conf.Msg) :
    (Cf.conf.held U).isSome ↔
    ∀ n : (Fin 1 → Bool) × Unit, U (n.1, Sum.inl n.2) = 5 ∨ U (n.1, Sum.inl n.2) = 7 := by
  show (ToyMo8.two.heldB fun n => U (n.1, Sum.inl n.2)).isSome ↔ _
  by_cases h : ∀ n : (Fin 1 → Bool) × Unit, U (n.1, Sum.inl n.2) = 5 ∨ U (n.1, Sum.inl n.2) = 7
  · have e : ToyMo8.two.heldB (fun n => U (n.1, Sum.inl n.2)) =
        some ⟨fun n => U (n.1, Sum.inl n.2), h⟩ := dif_pos h
    rw [e]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · have e : ToyMo8.two.heldB (fun n => U (n.1, Sum.inl n.2)) = none := dif_neg h
    rw [e]
    exact ⟨fun e => Bool.noConfusion e, fun e => absurd e h⟩

theorem inT_iff (U : Cf.conf.Msg) :
    InTable 1 1 (key U) tab ↔ (key U 0 = 5 ∨ key U 0 = 7) ∧ (key U 1 = 5 ∨ key U 1 = 7) := by
  constructor
  · intro h
    have t : ∀ b, b < 2 → key U b = 5 ∨ key U b = 7 := fun b hb => by
      obtain ⟨u, hu, e⟩ := h b hb
      have hu' : u < 2 := hu
      interval_cases u
      · exact Or.inl e
      · exact Or.inr e
    exact ⟨t 0 (by decide), t 1 (by decide)⟩
  · rintro ⟨h0, h1⟩ b hb
    have hb' : b < 2 := hb
    interval_cases b
    · exact h0.elim (fun e => ⟨0, by decide, e⟩) fun e => ⟨1, by decide, e⟩
    · exact h1.elim (fun e => ⟨0, by decide, e⟩) fun e => ⟨1, by decide, e⟩

/-- The lookup (over E) describes the index set (over F): a message U holds an index if and only if,
for every forest f ≤ `P.n`, the keys lie in the table (`P.InT f U`). -/
theorem describes (U : Cf.conf.Msg) : (Cf.conf.held U).isSome ↔ ∀ f, f ≤ P.n → P.InT f U := by
  rw [held_iff]
  constructor
  · intro h f _
    exact (inT_iff U).2 ⟨(key_57 U 0).2 (h (_, ())), (key_57 U 1).2 (h (_, ()))⟩
  · intro h n
    obtain ⟨h0, h1⟩ := (inT_iff U).1 (h 0 (le_refl 0))
    rw [key_57] at h0 h1
    obtain ⟨c, ⟨⟩⟩ := n
    show U (c, Sum.inl ()) = 5 ∨ U (c, Sum.inl ()) = 7
    rw [row_eq c]
    cases c 0
    · exact h0
    · exact h1

/-- What "valid" says at the toy's numbers, for bits given as four values (`h00` to `h11`), the two
keys named k0, k1 (`hk0`, `hk1`): if each of the four is 0 or 1 (`hb`), and at every x the
multiplicities that they write at the table entries equal to x add up to the number of keys equal to
x (`hs`), then `Valid 1 1 1 2 ky tab M`. -/
theorem valid_of (ky : ℕ → E) (M : ℕ → ℕ → E) (k0 k1 b00 b01 b10 b11 : E) (hk0 : ky 0 = k0)
    (hk1 : ky 1 = k1) (h00 : M 0 0 = b00) (h01 : M 0 1 = b01) (h10 : M 1 0 = b10)
    (h11 : M 1 1 = b11)
    (hb : b00 * (b00 - 1) = 0 ∧ b01 * (b01 - 1) = 0 ∧ b10 * (b10 - 1) = 0 ∧ b11 * (b11 - 1) = 0)
    (hs : ∀ x : E,
      (if (5 : E) = x then (if b00 = 1 then 1 else 0) + (if b01 = 1 then 2 else 0) else 0) +
          (if (7 : E) = x then (if b10 = 1 then 1 else 0) + (if b11 = 1 then 2 else 0) else 0) =
        (if k0 = x then 1 else 0) + (if k1 = x then 1 else 0)) : Valid 1 1 1 2 ky tab M := by
  classical
  refine ⟨?_, ?_, fun x => ?_⟩
  · intro u hu j hj
    have hu' : u < 2 := hu
    have hj' : j < 2 := hj
    interval_cases u <;> interval_cases j
    · rw [h00]; exact hb.1
    · rw [h01]; exact hb.2.1
    · rw [h10]; exact hb.2.2.1
    · rw [h11]; exact hb.2.2.2
  · intro u _ j h1 h2
    have h2' : j < 2 := h2
    omega
  · have e1 : (Finset.range (2 ^ 1)) = Finset.range 2 := rfl
    rw [e1, Finset.sum_filter, Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, hk0, hk1]
    have m0 : multOf 2 M 0 = (if b00 = 1 then 1 else 0) + (if b01 = 1 then 2 else 0) := by
      unfold multOf Alg.Lookup.mult
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      beta_reduce
      rw [h00, h01]
      by_cases a : b00 = 1 <;> by_cases c : b01 = 1 <;> simp [a, c]
    have m1 : multOf 2 M 1 = (if b10 = 1 then 1 else 0) + (if b11 = 1 then 2 else 0) := by
      unfold multOf Alg.Lookup.mult
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      beta_reduce
      rw [h10, h11]
      by_cases a : b10 = 1 <;> by_cases c : b11 = 1 <;> simp [a, c]
    rw [m0, m1, show tab 0 = 5 from rfl, show tab 1 = 7 from rfl]
    have := hs x
    by_cases h5 : (5 : E) = x <;> by_cases h7 : (7 : E) = x <;> by_cases g0 : k0 = x
      <;> by_cases g1 : k1 = x
      <;> simp only [h5, h7, g0, g1, if_true, if_false, Nat.zero_add] at this ⊢ <;> exact this

theorem multOf (U : Cf.conf.Msg) (f : ℕ) (_ : f ≤ P.n) (h : P.InT f U) :
    P.mult f U (P.bodyOf U) := by
  obtain ⟨h0, h1⟩ := (inT_iff U).1 h
  have n57 : (5 : E) ≠ 7 := n57E
  have n75 : (7 : E) ≠ 5 := n57E.symm
  show Valid 1 1 1 2 (key U) tab (bitOf (bodyOf U))
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · refine valid_of _ _ 5 5 0 1 0 0 h0 h1 ?_ ?_ ?_ ?_ (by simp) fun x => ?_
    · simp [bitOf, bodyOf, cntK, h0, h1]
    · simp [bitOf, bodyOf, cntK, h0, h1]
      decide
    · simp [bitOf, bodyOf, cntK, h0, h1, n57]
    · simp [bitOf, bodyOf, cntK, h0, h1, n57]
    · by_cases h : (5 : E) = x <;> simp [h]
  · refine valid_of _ _ 5 7 1 0 1 0 h0 h1 ?_ ?_ ?_ ?_ (by simp) fun x => ?_
    · simp [bitOf, bodyOf, cntK, h0, h1, n75]
    · simp [bitOf, bodyOf, cntK, h0, h1, n75]
      decide
    · simp [bitOf, bodyOf, cntK, h0, h1, n57]
    · simp [bitOf, bodyOf, cntK, h0, h1, n57]
      decide
    · simp
  · refine valid_of _ _ 7 5 1 0 1 0 h0 h1 ?_ ?_ ?_ ?_ (by simp) fun x => ?_
    · simp [bitOf, bodyOf, cntK, h0, h1, n75]
    · simp [bitOf, bodyOf, cntK, h0, h1, n75]
      decide
    · simp [bitOf, bodyOf, cntK, h0, h1, n57]
    · simp [bitOf, bodyOf, cntK, h0, h1, n57]
      decide
    · exact add_comm _ _
  · refine valid_of _ _ 7 7 0 0 0 1 h0 h1 ?_ ?_ ?_ ?_ (by simp) fun x => ?_
    · simp [bitOf, bodyOf, cntK, h0, h1, n75]
    · simp [bitOf, bodyOf, cntK, h0, h1, n75]
    · simp [bitOf, bodyOf, cntK, h0, h1]
    · simp [bitOf, bodyOf, cntK, h0, h1]
      decide
    · by_cases h : (7 : E) = x <;> simp [h]

/-- The laws of the data. -/
theorem laws : P.Laws where
  describes := describes
  held_hold := ldCf_held_hold F E Cf ToyMo8.two.held
  dcd_enc := ldCf_dcd_enc F E Cf dist8 (by show 1 < C8.d; rw [d8]; norm_num)
  multOf := multOf
  keyLin := ldWfK_keyLin E Cf.conf P _ _ _ lin

end Wf8
end Cb.Gl
