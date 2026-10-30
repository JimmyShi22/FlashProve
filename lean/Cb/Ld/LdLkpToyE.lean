-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpToyE.lean: the toy lookup over any finite field of characteristic above 6: the assembled
lookup at a small instance, all its hypotheses met together,
nothing assumed beyond the hypotheses of the statements; its errors written out in the number q of
elements.
This file is an example: the lookup argument for two keys and a table of two entries, over any
finite field of characteristic above 6.

Statement (`Cb.Spec.ldLkp_toyE`) and proof. A guard against empty theorems; no parameter of a
protocol.
It is Cb/Ld/LdLkpToy.lean (the field with 101 elements) re-stated with the field as a parameter, so
that the same guard stands over every field of characteristic above 6 in which a protocol's lookups
live, an extension field among them. What that file proves by evaluating elements of the field with
101 elements is proved here from the field's laws and 2 ≠ 0.

The claim. Over E: two keys, known to the prover alone, are entries of the public table (5, 7).
The numbers. v' = 0 (two keys), d = 1 (two table entries), n = 1 (multiplicities below 4: two bit
positions count), w = 1. The conditions on numbers: 2 ≤ 2, 2 < 4, 2 · 3 < p, p the characteristic.
The entries. 43: the 2 keys; the 4 bits of the multiplicities; 35 own masks (for each of the six
sumchecks the coefficients of its hiding polynomial and its inner masks: 2 + 2, 4 + 2, 3 + 2, 5 + 2,
5 (in the closing no map is revealed (`PscPar.core`, Cb/Ld/LdPsc.lean): no inner mask), 7 + 1); one
idle entry, which the levels that are never played name; one further entry that nothing names (for a
pad).
The oracle messages are a parameter: any signature S over E and any reading msg of the 43 entries
off its messages. (Codes, samples and sendings are an instance's.)

Main names: `Spec.ldLkp_toyE` states, for every p with `CharP E p` and 6 < p (the body, at a number
p: `Spec.ldLkp_toyAt E p`):
  the conditions on numbers; all places that are played are pairwise different, and none is the idle
  entry or the further one; the named entries (bits, masks, idle) are named once, and hold all
  places that the data name;
  two honest witnesses with different keys; a tuple of keys that is not in the table;
  and so, for every S, msg, beside every riding joint (`R0`; `rideJ`, Cb/Ld/LdLkp.lean): the lookup
  with rows and mask form on the named entries only meets the interface of the sub-protocol
  (`SubR.OK`, Cb/Ld/LdLkp.lean; by Cb/Ld/LdLkpAsm2Pull.lean);
  26 rounds; 8 rows at every transcript with an output; the errors and the numbers of values of the
  verifier messages, in order, in q = |E|; every error is below its number of values; the formats
  (`IdxStep`, `withheld`, `bud`, of `(toyA E).sub`; Cb/Ld/LdLkpAsm2Fmt.lean).

Limits: no security.
This file says nothing on zero knowledge: the item "masked messages" is not here.
It says nothing on any oracle message or any sending.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2PullProofs
import Cb.Ld.LdLkpAsm2Fmt
import Cb.Ld.LdLkpAsm2ErrProofs

set_option autoImplicit false

namespace Cb
namespace LkpToyE
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

noncomputable section
variable (E : Type) [Field E] [Fintype E]

/-- The names of the coefficients of the six hiding polynomials. -/
abbrev WS : Type := PIdx (([] : List (PFmt E)) ++ [pDummy E 1])
abbrev WA : Type := PIdx (([] : List (PFmt E)) ++ [pDummy E 3])
abbrev WK0 : Type := PIdx (List.replicate (0 + 0) (pfCube E 2) ++ [pDummy E 2])
abbrev WT0 : Type := PIdx (List.replicate (1 + 0) (pfCube E 2) ++ [pDummy E 2])
abbrev WE : Type := PIdx (List.replicate (1 + 1) (pfCube E 2))
abbrev WB : Type := PIdx (List.replicate (1 + 1) (pfCube E 2) ++ [pDummy E 2])

/-- The own masks. -/
abbrev Mk : Type :=
  ((WS E ⊕ Bool) ⊕ (WA E ⊕ Bool)) ⊕ (((WK0 E ⊕ Bool) ⊕ (WT0 E ⊕ Bool)) ⊕ (WE E ⊕ (WB E ⊕ Unit)))
/-- The entries proper: two keys, four bits; the masks, an idle entry. -/
abbrev J0 : Type := (Bool ⊕ (Bool × Bool)) ⊕ (Mk E ⊕ Unit)
/-- All entries: the entries proper, and one that nothing names. -/
abbrev Rw : Type := J0 E ⊕ Unit

instance decJ0 : DecidableEq (J0 E) := Classical.decEq _
instance decRw : DecidableEq (Rw E) := Classical.decEq _

variable {E}
def kAt (b : Bool) : Rw E := .inl (.inl (.inl b))
def bitAt (u j : Bool) : Rw E := .inl (.inl (.inr (u, j)))
def mAt (i : Mk E) : Rw E := .inl (.inr (.inl i))
def idle : Rw E := .inl (.inr (.inr ()))
variable (E)

/-- The data. -/
def toyA : LkAsm2 E where
  St := Unit
  J := Rw E
  v' := 0
  d := 1
  w := 1
  n := 1
  key := fun _ m i => m (kAt (decide (i = 1)))
  tab := fun _ u => if u = 0 then 5 else 7
  bAt := fun u j => bitAt (decide (u = 1)) (decide (j = 1))
  wS := fun i => mAt (.inl (.inl (.inl i)))
  cS := fun b => mAt (.inl (.inl (.inr b)))
  wAt := fun l => match l with
    | 0 => fun i => mAt (.inl (.inr (.inl i)))
    | _ + 1 => fun _ => idle
  cAt := fun l => match l with
    | 0 => fun b => mAt (.inl (.inr (.inr b)))
    | _ + 1 => fun _ => idle
  wK := fun l => match l with
    | 0 => fun i => mAt (.inr (.inl (.inl (.inl i))))
    | _ + 1 => fun _ => idle
  cK := fun l => match l with
    | 0 => fun b => mAt (.inr (.inl (.inl (.inr b))))
    | _ + 1 => fun _ => idle
  wT := fun l => match l with
    | 0 => fun i => mAt (.inr (.inl (.inr (.inl i))))
    | _ + 1 => fun _ => idle
  cT := fun l => match l with
    | 0 => fun b => mAt (.inr (.inl (.inr (.inr b))))
    | _ + 1 => fun _ => idle
  wE := fun i => mAt (.inr (.inr (.inl i)))
  wB := fun i => mAt (.inr (.inr (.inr (.inl i))))
  cB := mAt (.inr (.inr (.inr (.inr ()))))

/-- All places that are played: bits and masks through the fields of the data; the keys by `kAt`. -/
def plAt : (Bool ⊕ (Bool × Bool)) ⊕ Mk E → (toyA E).J
  | .inl (.inl b) => kAt b
  | .inl (.inr ub) => (toyA E).bAt ub.1.toNat ub.2.toNat
  | .inr (.inl (.inl (.inl i))) => (toyA E).wS i
  | .inr (.inl (.inl (.inr b))) => (toyA E).cS b
  | .inr (.inl (.inr (.inl i))) => (toyA E).wAt 0 i
  | .inr (.inl (.inr (.inr b))) => (toyA E).cAt 0 b
  | .inr (.inr (.inl (.inl (.inl i)))) => (toyA E).wK 0 i
  | .inr (.inr (.inl (.inl (.inr b)))) => (toyA E).cK 0 b
  | .inr (.inr (.inl (.inr (.inl i)))) => (toyA E).wT 0 i
  | .inr (.inr (.inl (.inr (.inr b)))) => (toyA E).cT 0 b
  | .inr (.inr (.inr (.inl i))) => (toyA E).wE i
  | .inr (.inr (.inr (.inr (.inl i)))) => (toyA E).wB i
  | .inr (.inr (.inr (.inr (.inr _)))) => (toyA E).cB

/-- The named entries: bits, masks, the idle entry; not the keys, not the further entry. -/
abbrev Nm : Type := (Bool × Bool) ⊕ (Mk E ⊕ Unit)
def iN : Nm E → (toyA E).J
  | .inl ub => bitAt ub.1 ub.2
  | .inr x => .inl (.inr x)

/-- A tuple of entries: the keys, the bits; all masks 0. -/
def wit (k : Bool → E) (b : Bool × Bool → E) : (toyA E).J → E
  | .inl (.inl (.inl c)) => k c
  | .inl (.inl (.inr ub)) => b ub
  | _ => 0

/-- The keys (5, 7), each entry of the table once; the keys (5, 5), the first entry twice; the keys
(5, 6). -/
def w57 : (toyA E).J → E := wit E (fun c => if c then 7 else 5) fun ub => if ub.2 then 0 else 1
def w55 : (toyA E).J → E := wit E (fun _ => 5) fun ub => if ub.1 then 0 else if ub.2 then 1 else 0
def w56 : (toyA E).J → E := wit E (fun c => if c then 6 else 5) fun _ => 0

/-- The errors and the numbers of values, in q. -/
def errsQ (q : ℕ) : List ℕ :=
  [1, 1, 1, 0, 1, 3, 0, 1, 1, 2, 0, 1, 1, 2, 2, 0, 1, 1, 2, 2, 2 * q, 1, 2, 2, 2, 0]
def valsQ (q : ℕ) : List ℕ :=
  [q, q, q - 1, 1, q, q - 1, 1, q, q, q - 1, 1, q, q, q, q - 1, 1, q, q, q, q,
    q ^ 2, q, q, q, q - 1, 1]

end
end LkpToyE

namespace Spec
open Iop LkpToyE IOR Cb.LdLkp

/-- What is said, at the number p. A condition with parameters, used inside other statements; it is
not itself a claim.

A condition with parameters, which other statements and theorems use; it is not itself a claim. -/
def ldLkp_toyAt (E : Type) [Field E] [Fintype E] (p : ℕ) : Prop :=
  (toyA E).H.lkb.Adm p ∧
  (Function.Injective (plAt E) ∧ ∀ x, plAt E x ≠ idle ∧ plAt E x ≠ .inr ()) ∧
  Function.Injective (iN E) ∧
  (toyA E).PlacesIn (fun j => j ∈ Set.range (iN E)) ∧
  ((toyA E).lk.inP (toyA E).ValidMu () (w57 E) ∧
    (toyA E).lk.inP (toyA E).ValidMu () (w55 E) ∧
    (toyA E).key () (w57 E) 1 ≠ (toyA E).key () (w55 E) 1 ∧
    ¬ (toyA E).lk.inR () (w56 E)) ∧
  (∀ (S : Sig E) (msg : S.Msg → (toyA E).J → E) (E₀ : ExtSpec)
        (Kc Wp : Type) (R0 : Rels Kc Unit E₀ (S.Msg × Wp)),
      ((toyA E).subN (iN E) S E₀ Kc Wp msg).OK
        ⟨1, 1, fun st ym => (toyA E).key st (msg ym.2), (toyA E).tab, fun _ _ => True⟩
        (fun st ym => (toyA E).ValidMu st (msg ym.2)) R0
        fun ym => (toyA E).entN (iN E) (msg ym.2)) ∧
  ∀ (S : Sig E) (msg : S.Msg → (toyA E).J → E) (E₀ : ExtSpec) (Kc Wp : Type),
    ((toyA E).subN (iN E) S E₀ Kc Wp msg).R.shape.length = 26 ∧
    (∀ x y τ xo,
      ((toyA E).subN (iN E) S E₀ Kc Wp msg).R.out x y τ = some xo → xo.1.2.2.length = 8) ∧
    ((toyA E).subN (iN E) S E₀ Kc Wp msg).P.err.toList = errsQ (Fintype.card E) ∧
    ((toyA E).subN (iN E) S E₀ Kc Wp msg).R.shape.chalList = valsQ (Fintype.card E) ∧
    ((toyA E).subN (iN E) S E₀ Kc Wp msg).P.err.Small ∧
    ((toyA E).sub S E₀ Kc Wp msg).R.IdxStep ∧
    (∀ w x, ((toyA E).sub S E₀ Kc Wp msg).H.withheld w x = ∅) ∧
    ∀ ρ T, ((toyA E).sub S E₀ Kc Wp msg).P.bud ρ T

/-- The guard, over every finite field of characteristic above 6. -/
def ldLkp_toyE (E : Type) [Field E] [Fintype E] : Prop :=
  ∀ (p : ℕ) [CharP E p], 6 < p → ldLkp_toyAt E p

end Spec

namespace LkpToyE
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp Finset
variable (E : Type) [Field E] [Fintype E]

theorem adm (p : ℕ) (hp : 6 < p) : (toyA E).H.lkb.Adm p := by
  refine ⟨(show 2 ≤ 2 ^ 1 from by decide), (show 2 ^ 1 < 2 ^ 2 from by decide), ?_⟩
  show 2 * 3 < p
  omega

theorem plAt_eq (x : (Bool ⊕ (Bool × Bool)) ⊕ Mk E) :
    plAt E x = Sum.inl (Sum.map id Sum.inl x) := by
  rcases x with (b | ⟨u, j⟩) | (((i | b) | (i | b)) | (((i | b) | (i | b)) | (i | (i | ⟨⟩))))
  all_goals first
    | rfl
    | (cases u <;> cases j <;> rfl)

theorem plAt_inj : Function.Injective (plAt E) := fun x y h => by
  rw [plAt_eq, plAt_eq] at h
  exact Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩ (Sum.inl_injective h)

theorem plAt_ne (x : (Bool ⊕ (Bool × Bool)) ⊕ Mk E) : plAt E x ≠ idle ∧ plAt E x ≠ .inr () := by
  rw [plAt_eq]
  refine ⟨fun h => ?_, fun h => Sum.inl_ne_inr h⟩
  have h1 : Sum.map id Sum.inl x = (Sum.inr (Sum.inr ()) : J0 E) := Sum.inl_injective h
  rcases x with x | i
  · exact Sum.inl_ne_inr h1
  · exact Sum.inl_ne_inr (Sum.inr_injective h1)

theorem iN_inj : Function.Injective (iN E) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Sum.inr_injective (Sum.inl_injective (Sum.inl_injective h)))
  · exact absurd (Sum.inl_injective h) Sum.inl_ne_inr
  · exact absurd (Sum.inl_injective h) Sum.inr_ne_inl
  · exact congrArg Sum.inr (Sum.inr_injective (Sum.inl_injective h))

theorem places : (toyA E).PlacesIn (fun j => j ∈ Set.range (iN E)) where
  bAt := fun u j => ⟨.inl (decide (u = 1), decide (j = 1)), rfl⟩
  wS := fun _ => ⟨.inr (.inl _), rfl⟩
  cS := fun _ => ⟨.inr (.inl _), rfl⟩
  wAt := fun l i => by cases l with
    | zero => exact ⟨.inr (.inl _), rfl⟩
    | succ l => exact ⟨.inr (.inr ()), rfl⟩
  cAt := fun l b => by cases l with
    | zero => exact ⟨.inr (.inl _), rfl⟩
    | succ l => exact ⟨.inr (.inr ()), rfl⟩
  wK := fun l i => by cases l with
    | zero => exact ⟨.inr (.inl _), rfl⟩
    | succ l => exact ⟨.inr (.inr ()), rfl⟩
  cK := fun l b => by cases l with
    | zero => exact ⟨.inr (.inl _), rfl⟩
    | succ l => exact ⟨.inr (.inr ()), rfl⟩
  wT := fun l i => by cases l with
    | zero => exact ⟨.inr (.inl _), rfl⟩
    | succ l => exact ⟨.inr (.inr ()), rfl⟩
  cT := fun l b => by cases l with
    | zero => exact ⟨.inr (.inl _), rfl⟩
    | succ l => exact ⟨.inr (.inr ()), rfl⟩
  wE := fun _ => ⟨.inr (.inl _), rfl⟩
  wB := fun _ => ⟨.inr (.inl _), rfl⟩
  cB := ⟨.inr (.inl _), rfl⟩

open Classical in
/-- What is enough for "valid" at the toy's numbers, for bits given as four values. -/
theorem valid_of (m : (toyA E).J → E) (k0 k1 b00 b01 b10 b11 : E) (hk0 : (toyA E).key () m 0 = k0)
    (hk1 : (toyA E).key () m 1 = k1) (h00 : (toyA E).H.bit m 0 0 = b00)
    (h01 : (toyA E).H.bit m 0 1 = b01) (h10 : (toyA E).H.bit m 1 0 = b10)
    (h11 : (toyA E).H.bit m 1 1 = b11)
    (hb : b00 * (b00 - 1) = 0 ∧ b01 * (b01 - 1) = 0 ∧ b10 * (b10 - 1) = 0 ∧ b11 * (b11 - 1) = 0)
    (hs : ∀ x : E,
      (if (5 : E) = x then (if b00 = 1 then 1 else 0) + (if b01 = 1 then 2 else 0) else 0) +
          (if (7 : E) = x then (if b10 = 1 then 1 else 0) + (if b11 = 1 then 2 else 0) else 0) =
        (if k0 = x then 1 else 0) + (if k1 = x then 1 else 0)) : (toyA E).ValidMu () m := by
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
    have h1' : 2 ≤ j := h1
    have h2' : j < 2 := h2
    omega
  · have e1 : (range (2 ^ (toyA E).d)) = range 2 := rfl
    have e2 : (range (2 ^ ((toyA E).v' + 1))) = range 2 := rfl
    rw [e1, e2, Finset.sum_filter, Finset.card_filter, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, hk0, hk1]
    have m0 : multOf ((toyA E).n + 1) ((toyA E).H.bit m) 0 =
        (if b00 = 1 then 1 else 0) + (if b01 = 1 then 2 else 0) := by
      unfold multOf Alg.Lookup.mult
      rw [show (toyA E).n + 1 = 2 from rfl, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      beta_reduce
      rw [h00, h01]
      by_cases a : b00 = 1 <;> by_cases c : b01 = 1 <;> simp [a, c]
    have m1 : multOf ((toyA E).n + 1) ((toyA E).H.bit m) 1 =
        (if b10 = 1 then 1 else 0) + (if b11 = 1 then 2 else 0) := by
      unfold multOf Alg.Lookup.mult
      rw [show (toyA E).n + 1 = 2 from rfl, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      beta_reduce
      rw [h10, h11]
      by_cases a : b10 = 1 <;> by_cases c : b11 = 1 <;> simp [a, c]
    rw [m0, m1, show (toyA E).tab () 0 = 5 from rfl, show (toyA E).tab () 1 = 7 from rfl]
    have := hs x
    by_cases h5 : (5 : E) = x <;> by_cases h7 : (7 : E) = x <;> by_cases g0 : k0 = x
      <;> by_cases g1 : k1 = x
      <;> simp only [h5, h7, g0, g1, if_true, if_false, Nat.zero_add] at this ⊢ <;> exact this

theorem in57 : (toyA E).lk.inP (toyA E).ValidMu () (w57 E) := by
  refine ⟨⟨fun b hb => ?_, trivial⟩,
    valid_of E (w57 E) 5 7 1 0 1 0 rfl rfl rfl rfl rfl rfl (by simp) fun x => ?_⟩
  · have hb' : b < 2 := hb
    interval_cases b
    · exact ⟨0, (show 0 < 2 ^ 1 from by decide), rfl⟩
    · exact ⟨1, (show 1 < 2 ^ 1 from by decide), rfl⟩
  · simp

theorem in55 : (toyA E).lk.inP (toyA E).ValidMu () (w55 E) := by
  refine ⟨⟨fun b hb => ?_, trivial⟩,
    valid_of E (w55 E) 5 5 0 1 0 0 rfl rfl rfl rfl rfl rfl (by simp) fun x => ?_⟩
  · have hb' : b < 2 := hb
    interval_cases b
    · exact ⟨0, (show 0 < 2 ^ 1 from by decide), rfl⟩
    · exact ⟨0, (show 0 < 2 ^ 1 from by decide), rfl⟩
  · by_cases h : (5 : E) = x <;> simp [h]

omit [Fintype E] in
theorem ne65 : (6 : E) ≠ 5 := fun h => one_ne_zero (α := E) (by linear_combination h)
omit [Fintype E] in
theorem ne67 : (6 : E) ≠ 7 := fun h => one_ne_zero (α := E) (by linear_combination (-1 : E) * h)
omit [Fintype E] in
theorem ne75 (p : ℕ) [CharP E p] (hp : 6 < p) : (7 : E) ≠ 5 := fun h => by
  have h2 : ((2 : ℕ) : E) = 0 := by
    push_cast
    linear_combination h
  have := Nat.le_of_dvd (by decide) ((CharP.cast_eq_zero_iff E p 2).1 h2)
  omega

theorem out56 : ¬ (toyA E).lk.inR () (w56 E) := by
  rintro ⟨h, -⟩
  obtain ⟨u, hu, he⟩ := h 1 (show 1 < 2 ^ 1 from by decide)
  have hu' : u < 2 := hu
  have he' : (6 : E) = if u = 0 then 5 else 7 := he
  interval_cases u
  · exact ne65 E he'
  · exact ne67 E he'

/-- The field has at least as many elements as its characteristic. -/
theorem card_ge (p : ℕ) [CharP E p] : p ≤ Fintype.card E := by
  obtain ⟨n, _, hq⟩ := FiniteField.card E p
  rw [hq]
  exact Nat.le_self_pow n.ne_zero p

section
variable (S : Sig E) (msg : S.Msg → (toyA E).J → E) (E₀ : ExtSpec) (Kc Wp : Type)

theorem errs : ((toyA E).subN (iN E) S E₀ Kc Wp msg).P.err.toList = errsQ (Fintype.card E) := by
  rw [((ldLkpAsm2E_sub E).1 (toyA E) (Nm E) (iN E) S E₀ Kc Wp msg).1]
  show [1, 1, 1, 0, 1, 3, 0, 1 * Fintype.card E ^ (1 - 1), 1, 2, 0, 1, 1, 2, 2, 0, 1, 1, 2, 2,
      (1 + 1) * Fintype.card E ^ (1 + 1 - 1), 1, 2, 2, 2, 0] = _
  simp [errsQ]

theorem chals :
    ((toyA E).subN (iN E) S E₀ Kc Wp msg).R.shape.chalList = valsQ (Fintype.card E) := by
  rw [((ldLkpAsm2E_sub E).1 (toyA E) (Nm E) (iN E) S E₀ Kc Wp msg).2]
  show [Fintype.card E, Fintype.card E, Fintype.card E - 1, 1, Fintype.card E, Fintype.card E - 1,
      1, Fintype.card E ^ 1, Fintype.card E, Fintype.card E - 1, 1, Fintype.card E, Fintype.card E,
      Fintype.card E, Fintype.card E - 1, 1, Fintype.card E, Fintype.card E, Fintype.card E,
      Fintype.card E, Fintype.card E ^ (1 + 1), Fintype.card E, Fintype.card E, Fintype.card E,
      Fintype.card E - 1, 1] = _
  simp [valsQ]

theorem small (p : ℕ) [CharP E p] (hp : 6 < p) :
    ((toyA E).subN (iN E) S E₀ Kc Wp msg).P.err.Small := by
  have hq := card_ge E p
  rw [chainErr_small, errs, chals]
  have h2 : 2 * Fintype.card E < Fintype.card E ^ 2 := by nlinarith
  simp only [errsQ, valsQ, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
  omega

theorem rounds : ((toyA E).subN (iN E) S E₀ Kc Wp msg).R.shape.length = 26 :=
  (ldLkpAsm2_rounds E (toyA E) E₀ S.Msg Wp Kc msg).trans
    (show 1 + 3 * (1 + 1) + 1 +
        (∑ l ∈ range (0 + 1), (0 + l + 3 + 1) + ∑ l ∈ range 1, (1 + l + 3 + 1)) +
        (1 + 1 + 1) + (1 + (1 + 1 + 3)) = 26 from by decide)

theorem nrows (x y τ xo) (h : ((toyA E).subN (iN E) S E₀ Kc Wp msg).R.out x y τ = some xo) :
    xo.1.2.2.length = 8 := by
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ldLkpAsm2N_len E (toyA E) (Nm E) (iN E) E₀ S.Msg Wp Kc msg _ _ _ _ hx'

end
end LkpToyE

open LkpToyE in
theorem ldLkp_toyE (E : Type) [Field E] [Fintype E] : Spec.ldLkp_toyE E := by
  intro p _ hp
  exact ⟨adm E p hp,
    ⟨plAt_inj E, plAt_ne E⟩,
    iN_inj E, places E,
    ⟨in57 E, in55 E, ne75 E p hp, out56 E⟩,
    fun S msg E₀ Kc Wp R0 =>
      ldLkpAsm2N_ok E p (toyA E) (Nm E) (iN E) (toyA E).ValidMu S E₀ Kc Wp R0 msg (iN_inj E)
        (places E) (adm E p hp) (ldLkpAsm2_muValid E (toyA E) (adm E p hp).1),
    fun S msg E₀ Kc Wp =>
      ⟨rounds E S msg E₀ Kc Wp,
        nrows E S msg E₀ Kc Wp,
        errs E S msg E₀ Kc Wp,
        chals E S msg E₀ Kc Wp,
        small E S msg E₀ Kc Wp p hp,
        ldLkpFmt2_idx E (toyA E) S E₀ Kc Wp msg,
        ldLkpFmt2_free E (toyA E) S E₀ Kc Wp msg,
        ldLkpFmt2_bud E (toyA E) S E₀ Kc Wp msg⟩⟩

end Cb
