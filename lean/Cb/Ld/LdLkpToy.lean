-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpToy.lean: a toy lookup: the assembled lookup at a small instance, all its hypotheses met
together, nothing assumed beyond the hypotheses of `Spec.ldLkp_toy`; its errors written out.
This file is an example: the lookup argument for two keys and a table of two entries, over the field
with 101 elements.

Statement (`Cb.Spec.ldLkp_toy`) and proof. A guard against empty theorems; no parameter of a
protocol.

The claim. Over the field with 101 elements: two keys, known to the prover alone, are entries of the
public table (5, 7). (So the statement does not determine the witness: the keys (5, 7) and the keys
(5, 5) are both honest.)
The numbers. v' = 0 (two keys), d = 1 (two table entries), n = 1 (multiplicities below 4: two bit
positions count), w = 1 (two bit positions). The conditions on numbers: 2 ≤ 2, 2 < 4, 2 · 3 < 101.
The oracle message. One, under the code of Cb/Ld/LdRelToy.lean (Reed-Solomon, five points, one
message symbol and one symbol of randomness a row, distance 4, radius 2: beyond unique decoding), 43
rows: the 2 keys; the 4 bits of the multiplicities; 35 own masks; one idle entry; the pad of the
sample.
The masks: for each of the six sumchecks (the steps in order: Cb/Ld/LdLkpAsm2.lean) the coefficients
of its hiding polynomial and its inner masks: the tie's two (2 + 2, 4 + 2), the keys' level (3 + 2),
the forest's level (5 + 2), the closing (5: no map is revealed (`PscPar.core`, Cb/Ld/LdPsc.lean), so
no inner mask), the bit test (7 + 1).
The data of Cb/Ld/LdLkpAsm2.lean name places for all levels l; the levels that are never played
(l ≥ 1) name the idle entry.
The sample. The row with a pad of Cb/Gen/OodDecPad.lean, as in Cb/Ld/LdSendPscToy.lean.

Main names: `Spec.ldLkp_toy` states:
  the conditions on numbers; all places that are played are pairwise different, and none is the idle
  entry or the pad (`plAt`); the named entries (bits, masks, idle) are named once, and hold all
  places that the data name;
  two honest witnesses with different keys; a tuple of keys that is not in the table (so the claim
  can fail);
  the laws of the code, lists of at most 2, the sample evades;
  and so, beside every riding joint (`R0`; `rideJ`, Cb/Ld/LdLkp.lean): the lookup over this
  signature, with rows and mask form on the named entries only, meets the interface of the
  sub-protocol (`SubR.OK`, Cb/Ld/LdLkp.lean; by Cb/Ld/LdLkpAsm2Pull.lean);
  26 rounds; 8 rows at every transcript with an output; the errors, in order, and the numbers of
  values of the verifier messages, in order; every error is below its number of values;
  the formats: the further oracles are not read, not tied, copied; nothing is withheld; every budget
  is borne (Cb/Ld/LdLkpAsm2Fmt.lean, for the form with all entries).
The errors. λ: 1 of 101. Each sumcheck: 1 of 101 (the coefficient), then the degree of each variable
(2 of 101 on the cube; the dummy variable's degree of 100), then 0 of 1 (the values; no verifier
message); the closing has neither a dummy variable nor values. A line step: 1 of 101. The point for
the table's products: 1 of 101. The zerocheck's point: 202 of 10201.

Limits: this file says nothing on real parameters: these errors are no security.
It says nothing on zero knowledge: the item "masked messages" is not here.
The sending of the oracle message is not here (Cb/Ld/LdSendPscToy.lean has one).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2PullProofs
import Cb.Ld.LdLkpAsm2Fmt
import Cb.Ld.LdSendPscToy
import Ior.KnowCollRulesChainErr

set_option autoImplicit false

namespace Cb
namespace LkpToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy Cb.LdLkp Cb.Lkp

noncomputable section

/-- The names of the coefficients of the six hiding polynomials. -/
abbrev WS : Type := PIdx (([] : List (PFmt K)) ++ [pDummy K 1])
abbrev WA : Type := PIdx (([] : List (PFmt K)) ++ [pDummy K 3])
abbrev WK0 : Type := PIdx (List.replicate (0 + 0) (pfCube K 2) ++ [pDummy K 2])
abbrev WT0 : Type := PIdx (List.replicate (1 + 0) (pfCube K 2) ++ [pDummy K 2])
abbrev WE : Type := PIdx (List.replicate (1 + 1) (pfCube K 2))
abbrev WB : Type := PIdx (List.replicate (1 + 1) (pfCube K 2) ++ [pDummy K 2])

/-- The own masks. -/
abbrev Mk : Type :=
  ((WS ⊕ Bool) ⊕ (WA ⊕ Bool)) ⊕ (((WK0 ⊕ Bool) ⊕ (WT0 ⊕ Bool)) ⊕ (WE ⊕ (WB ⊕ Unit)))
/-- The entries proper: two keys, four bits; the masks, an idle entry. -/
abbrev J0 : Type := (Bool ⊕ (Bool × Bool)) ⊕ (Mk ⊕ Unit)
/-- The rows: the entries proper, and the pad. -/
abbrev Rw : Type := J0 ⊕ Unit

instance decJ0 : DecidableEq J0 := Classical.decEq _
instance decRw : DecidableEq Rw := Classical.decEq _

def kAt (b : Bool) : Rw := .inl (.inl (.inl b))
def bitAt (u j : Bool) : Rw := .inl (.inl (.inr (u, j)))
def mAt (i : Mk) : Rw := .inl (.inr (.inl i))
def idle : Rw := .inl (.inr (.inr ()))

/-- The data. -/
def toyA : LkAsm2 K where
  St := Unit
  J := Rw
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
def plAt : (Bool ⊕ (Bool × Bool)) ⊕ Mk → toyA.J
  | .inl (.inl b) => kAt b
  | .inl (.inr ub) => toyA.bAt ub.1.toNat ub.2.toNat
  | .inr (.inl (.inl (.inl i))) => toyA.wS i
  | .inr (.inl (.inl (.inr b))) => toyA.cS b
  | .inr (.inl (.inr (.inl i))) => toyA.wAt 0 i
  | .inr (.inl (.inr (.inr b))) => toyA.cAt 0 b
  | .inr (.inr (.inl (.inl (.inl i)))) => toyA.wK 0 i
  | .inr (.inr (.inl (.inl (.inr b)))) => toyA.cK 0 b
  | .inr (.inr (.inl (.inr (.inl i)))) => toyA.wT 0 i
  | .inr (.inr (.inl (.inr (.inr b)))) => toyA.cT 0 b
  | .inr (.inr (.inr (.inl i))) => toyA.wE i
  | .inr (.inr (.inr (.inr (.inl i)))) => toyA.wB i
  | .inr (.inr (.inr (.inr (.inr _)))) => toyA.cB

/-- The named entries: bits, masks, the idle entry; not the keys, not the pad. -/
abbrev Nm : Type := (Bool × Bool) ⊕ (Mk ⊕ Unit)
def iN : Nm → toyA.J
  | .inl ub => bitAt ub.1 ub.2
  | .inr x => .inl (.inr x)

/-- The entries of a message are the rows. -/
def nuR : (toyLd Rw).J ≃ Rw where
  toFun j := j.2.1
  invFun r := ⟨(), (r, (0 : Fin 1))⟩
  left_inv := by
    rintro ⟨⟨⟩, b, i⟩
    have h : i.val < 1 := i.isLt
    have hi : i = (0 : Fin 1) := Fin.ext (show i.val = 0 from Nat.lt_one_iff.1 h)
    subst hi
    rfl
  right_inv := fun _ => rfl

/-- Each entry proper has a corner of the cube of its own (`pl` of `Sample.pad`,
Cb/Gen/OodDecPad.lean). -/
def plR : J0 → J0 → Bool := fun j i => decide (i = j)

/-- The sample, the oracle message, the signature, the reading of the entries. -/
@[reducible] def padR : Sample K (J0 ⊕ Unit) :=
  Sample.pad K J0 J0 Unit Bn plR (fun _ => 1) fun β => β.1
@[reducible] def toyM : OMsg K := OMsg.plain (toyLd Rw) (padR.comap nuR) 2 fun _ => 0
abbrev Sg : Sig K := Sig.one toyM
def toyMsg : Sg.Msg → toyA.J → K := fun m j => m () (nuR.symm j)

/-- A tuple of entries: the keys, the bits; all masks 0. -/
def wit (k : Bool → K) (b : Bool × Bool → K) : toyA.J → K
  | .inl (.inl (.inl c)) => k c
  | .inl (.inl (.inr ub)) => b ub
  | _ => 0

/-- The keys (5, 7), each entry of the table once; the keys (5, 5), the first entry twice; the keys
(5, 6) -/
def w57 : toyA.J → K := wit (fun c => if c then 7 else 5) fun ub => if ub.2 then 0 else 1
def w55 : toyA.J → K := wit (fun _ => 5) fun ub => if ub.1 then 0 else if ub.2 then 1 else 0
def w56 : toyA.J → K := wit (fun c => if c then 6 else 5) fun _ => 0

end
end LkpToy

namespace Spec
open Iop LdToy LkpToy IOR Cb.LdLkp

def ldLkp_toy : Prop :=
  toyA.H.lkb.Adm 101 ∧
  (Function.Injective plAt ∧ ∀ p, plAt p ≠ idle ∧ plAt p ≠ .inr ()) ∧
  Function.Injective iN ∧
  toyA.PlacesIn (fun j => j ∈ Set.range iN) ∧
  (toyA.lk.inP toyA.ValidMu () w57 ∧
    toyA.lk.inP toyA.ValidMu () w55 ∧
    toyA.key () w57 1 ≠ toyA.key () w55 1 ∧
    ¬ toyA.lk.inR () w56) ∧
  toyM.C.Laws ∧ toyM.ListLE 2 ∧ toyM.Evades ∧
  (∀ (E₀ : ExtSpec) (Kc Wp : Type) (R0 : Rels Kc Unit E₀ (Sg.Msg × Wp)),
    (toyA.subN iN Sg E₀ Kc Wp toyMsg).OK
      ⟨1, 1, fun st ym => toyA.key st (toyMsg ym.2), toyA.tab, fun _ _ => True⟩
      (fun st ym => toyA.ValidMu st (toyMsg ym.2)) R0 fun ym => toyA.entN iN (toyMsg ym.2)) ∧
  ∀ (E₀ : ExtSpec) (Kc Wp : Type),
    (toyA.subN iN Sg E₀ Kc Wp toyMsg).R.shape.length = 26 ∧
    (∀ x y τ xo, (toyA.subN iN Sg E₀ Kc Wp toyMsg).R.out x y τ = some xo → xo.1.2.2.length = 8) ∧
    (toyA.subN iN Sg E₀ Kc Wp toyMsg).P.err.toList =
      [1, 1, 1, 0, 1, 3, 0, 1, 1, 2, 0, 1, 1, 2, 2, 0, 1, 1, 2, 2, 202, 1, 2, 2, 2, 0] ∧
    (toyA.subN iN Sg E₀ Kc Wp toyMsg).R.shape.chalList =
      [101, 101, 100, 1, 101, 100, 1, 101, 101, 100, 1, 101, 101, 101, 100, 1, 101, 101, 101, 101,
        10201, 101, 101, 101, 100, 1] ∧
    (toyA.subN iN Sg E₀ Kc Wp toyMsg).P.err.Small ∧
    (toyA.sub Sg E₀ Kc Wp toyMsg).R.IdxStep ∧
    (∀ w x, (toyA.sub Sg E₀ Kc Wp toyMsg).H.withheld w x = ∅) ∧
    ∀ ρ T, (toyA.sub Sg E₀ Kc Wp toyMsg).P.bud ρ T

end Spec

namespace LkpToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy Cb.LdLkp Cb.Lkp Finset

theorem adm : toyA.H.lkb.Adm 101 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem plAt_eq (p : (Bool ⊕ (Bool × Bool)) ⊕ Mk) : plAt p = Sum.inl (Sum.map id Sum.inl p) := by
  rcases p with (b | ⟨u, j⟩) | (((i | b) | (i | b)) | (((i | b) | (i | b)) | (i | (i | ⟨⟩))))
  all_goals first
    | rfl
    | (cases u <;> cases j <;> rfl)

theorem plAt_inj : Function.Injective plAt := fun p q h => by
  rw [plAt_eq, plAt_eq] at h
  exact Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩ (Sum.inl_injective h)

theorem plAt_ne (p : (Bool ⊕ (Bool × Bool)) ⊕ Mk) : plAt p ≠ idle ∧ plAt p ≠ .inr () := by
  rw [plAt_eq]
  refine ⟨fun h => ?_, fun h => Sum.inl_ne_inr h⟩
  have h1 : Sum.map id Sum.inl p = (Sum.inr (Sum.inr ()) : J0) := Sum.inl_injective h
  rcases p with x | i
  · exact Sum.inl_ne_inr h1
  · exact Sum.inl_ne_inr (Sum.inr_injective h1)

theorem iN_inj : Function.Injective iN := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Sum.inr_injective (Sum.inl_injective (Sum.inl_injective h)))
  · exact absurd (Sum.inl_injective h) Sum.inl_ne_inr
  · exact absurd (Sum.inl_injective h) Sum.inr_ne_inl
  · exact congrArg Sum.inr (Sum.inr_injective (Sum.inl_injective h))

theorem places : toyA.PlacesIn (fun j => j ∈ Set.range iN) where
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

/-- What is enough for "valid" at the toy's numbers, for bits given as four values. -/
theorem valid_of (m : toyA.J → K) (k0 k1 b00 b01 b10 b11 : K) (hk0 : toyA.key () m 0 = k0)
    (hk1 : toyA.key () m 1 = k1) (h00 : toyA.H.bit m 0 0 = b00) (h01 : toyA.H.bit m 0 1 = b01)
    (h10 : toyA.H.bit m 1 0 = b10) (h11 : toyA.H.bit m 1 1 = b11)
    (hb : b00 * (b00 - 1) = 0 ∧ b01 * (b01 - 1) = 0 ∧ b10 * (b10 - 1) = 0 ∧ b11 * (b11 - 1) = 0)
    (hs : ∀ x : K,
      (if (5 : K) = x then (if b00 = 1 then 1 else 0) + (if b01 = 1 then 2 else 0) else 0) +
          (if (7 : K) = x then (if b10 = 1 then 1 else 0) + (if b11 = 1 then 2 else 0) else 0) =
        (if k0 = x then 1 else 0) + (if k1 = x then 1 else 0)) : toyA.ValidMu () m := by
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
  · have e1 : (range (2 ^ toyA.d)) = range 2 := rfl
    have e2 : (range (2 ^ (toyA.v' + 1))) = range 2 := rfl
    rw [e1, e2, Finset.sum_filter, Finset.card_filter, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, hk0, hk1]
    have m0 : multOf (toyA.n + 1) (toyA.H.bit m) 0 =
        (if b00 = 1 then 1 else 0) + (if b01 = 1 then 2 else 0) := by
      unfold multOf Alg.Lookup.mult
      rw [show toyA.n + 1 = 2 from rfl, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      beta_reduce
      rw [h00, h01]
      by_cases a : b00 = 1 <;> by_cases c : b01 = 1 <;> simp [a, c]
    have m1 : multOf (toyA.n + 1) (toyA.H.bit m) 1 =
        (if b10 = 1 then 1 else 0) + (if b11 = 1 then 2 else 0) := by
      unfold multOf Alg.Lookup.mult
      rw [show toyA.n + 1 = 2 from rfl, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      beta_reduce
      rw [h10, h11]
      by_cases a : b10 = 1 <;> by_cases c : b11 = 1 <;> simp [a, c]
    rw [m0, m1, show toyA.tab () 0 = 5 from rfl, show toyA.tab () 1 = 7 from rfl]
    have := hs x
    by_cases h5 : (5 : K) = x <;> by_cases h7 : (7 : K) = x <;> by_cases g0 : k0 = x
      <;> by_cases g1 : k1 = x
      <;> simp only [h5, h7, g0, g1, if_true, if_false, Nat.zero_add] at this ⊢ <;> exact this

theorem in57 : toyA.lk.inP toyA.ValidMu () w57 := by
  refine ⟨⟨fun b hb => ?_, trivial⟩,
    valid_of w57 5 7 1 0 1 0 rfl rfl rfl rfl rfl rfl (by decide) fun x => ?_⟩
  · have hb' : b < 2 := hb
    interval_cases b
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
  · simp

theorem in55 : toyA.lk.inP toyA.ValidMu () w55 := by
  refine ⟨⟨fun b hb => ?_, trivial⟩,
    valid_of w55 5 5 0 1 0 0 rfl rfl rfl rfl rfl rfl (by decide) fun x => ?_⟩
  · have hb' : b < 2 := hb
    interval_cases b
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
  · by_cases h : (5 : K) = x <;> simp [h]

theorem out56 : ¬ toyA.lk.inR () w56 := by
  rintro ⟨h, -⟩
  obtain ⟨u, hu, he⟩ := h 1 (by decide)
  have hu' : u < 2 := hu
  have he' : (6 : K) = if u = 0 then 5 else 7 := he
  interval_cases u
  · exact absurd he' (by decide)
  · exact absurd he' (by decide)

theorem plR_inj : Function.Injective plR := fun j j' h => by
  have h1 : plR j j = plR j' j := congrFun h j
  have h2 : plR j j = true := decide_eq_true rfl
  rw [h2] at h1
  exact of_decide_eq_true h1.symm

theorem padR_okOn : padR.OKOn (PadInF K) :=
  ood_okOn_pad K K J0 J0 Unit Bn _ _ _ plR_inj (fun _ _ h => Subtype.ext h) padBasis.1

theorem toyM_evades : toyM.Evades :=
  sig_evades_of_okOn K toyM _
    (ood_okOn_comap K (J0 ⊕ Unit) (toyLd Rw).J padR nuR (PadInF K) padR_okOn)
    fun _ _ _ _ _ _ => ⟨_, rfl⟩

theorem card_any {α : Type} (i j : Fintype α) : @Fintype.card α i = @Fintype.card α j := by
  congr
  exact Subsingleton.elim _ _

theorem cardK (i : Fintype K) : @Fintype.card K i = 101 := (card_any i _).trans (ZMod.card 101)
theorem cardD (n : ℕ) (i : Fintype (pDummy K n).Ch) : @Fintype.card _ i = 100 := by
  classical
  have h : ∀ (E : Type) [Field E] [Fintype E] (j : Fintype {x : E // x ≠ 0}),
      @Fintype.card _ j = Fintype.card E - 1 := fun E _ _ j => by
    rw [card_any j inferInstance, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  exact (h K i).trans (by rw [ZMod.card])
theorem cardU (i : Fintype Unit) : @Fintype.card _ i = 1 := (card_any i _).trans Fintype.card_unit
theorem cardF (g : ℕ) (i : Fintype (Fin g → K)) : @Fintype.card _ i = 101 ^ g := by
  rw [card_any i Pi.instFintype, Fintype.card_fun, ZMod.card, Fintype.card_fin]
theorem cardP (g : ℕ) (i : Fintype (Unit × (Fin g → K))) : @Fintype.card _ i = 101 ^ g := by
  rw [card_any i (instFintypeProd Unit (Fin g → K)), Fintype.card_prod,
    Fintype.card_unit, one_mul, cardF]

section
variable (E₀ : ExtSpec) (Kc Wp : Type)

set_option maxRecDepth 100000 in
theorem errs : (toyA.subN iN Sg E₀ Kc Wp toyMsg).P.err.toList =
    [1, 1, 1, 0, 1, 3, 0, 1, 1, 2, 0, 1, 1, 2, 2, 0, 1, 1, 2, 2, 202, 1, 2, 2, 2, 0] := by
  have h : (toyA.subN iN Sg E₀ Kc Wp toyMsg).P.err.toList =
      [1, 1, 1, 0, 1, 3, 0,
        Fintype.card (Fin (1 + 0)) * Fintype.card K ^ (Fintype.card (Fin (1 + 0)) - 1), 1, 2, 0, 1,
        1, 2, 2, 0, 1, 1, 2, 2,
        Fintype.card (Fin (1 + 1)) * Fintype.card K ^ (Fintype.card (Fin (1 + 1)) - 1), 1, 2, 2, 2,
        0] := rfl
  rw [h]
  simp [ZMod.card]

set_option maxRecDepth 100000 in
theorem chals :
    (toyA.subN iN Sg E₀ Kc Wp toyMsg).R.shape.chalList =
      [101, 101, 100, 1, 101, 100, 1, 101, 101, 100, 1, 101, 101, 101, 100, 1, 101, 101, 101, 101,
        10201, 101, 101, 101, 100, 1] := by
  refine (show (toyA.subN iN Sg E₀ Kc Wp toyMsg).R.shape.chalList =
    [@Fintype.card K _, @Fintype.card K _, @Fintype.card (pDummy K 1).Ch _, @Fintype.card Unit _,
      @Fintype.card K _, @Fintype.card (pDummy K 3).Ch _, @Fintype.card Unit _,
      @Fintype.card (Fin (1 + 0) → K) _, @Fintype.card K _, @Fintype.card (pDummy K 2).Ch _,
      @Fintype.card Unit _, @Fintype.card K _, @Fintype.card K _, @Fintype.card K _,
      @Fintype.card (pDummy K 2).Ch _, @Fintype.card Unit _, @Fintype.card K _,
      @Fintype.card K _, @Fintype.card K _, @Fintype.card K _,
      @Fintype.card (Unit × (Fin (1 + 1) → K)) _, @Fintype.card K _, @Fintype.card K _,
      @Fintype.card K _, @Fintype.card (pDummy K 2).Ch _, @Fintype.card Unit _] from rfl).trans ?_
  simp only [cardK, cardD, cardU, cardF, cardP]
  norm_num

theorem small : (toyA.subN iN Sg E₀ Kc Wp toyMsg).P.err.Small := by
  rw [chainErr_small, errs, chals]
  decide

theorem rounds : (toyA.subN iN Sg E₀ Kc Wp toyMsg).R.shape.length = 26 :=
  (ldLkpAsm2_rounds K toyA E₀ Sg.Msg Wp Kc toyMsg).trans (by decide)

theorem nrows (x y τ xo) (h : (toyA.subN iN Sg E₀ Kc Wp toyMsg).R.out x y τ = some xo) :
    xo.1.2.2.length = 8 := by
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ldLkpAsm2N_len K toyA Nm iN E₀ Sg.Msg Wp Kc toyMsg _ _ _ _ hx'

end
end LkpToy

open LdToy LkpToy in
theorem ldLkp_toy : Spec.ldLkp_toy := by
  have hT := ld_toy Rw
  exact ⟨adm, ⟨plAt_inj, plAt_ne⟩, iN_inj, places,
    ⟨in57, in55, by decide, out56⟩,
    hT.1,
    sig_list_of_code K toyM 2 hT.2.2.2.1,
    toyM_evades,
    fun E₀ Kc Wp R0 =>
      ldLkpAsm2N_ok K 101 toyA Nm iN toyA.ValidMu Sg E₀ Kc Wp R0 toyMsg iN_inj places
        adm (ldLkpAsm2_muValid K toyA adm.1),
    fun E₀ Kc Wp =>
      ⟨rounds E₀ Kc Wp, nrows E₀ Kc Wp, errs E₀ Kc Wp, chals E₀ Kc Wp, small E₀ Kc Wp,
        ldLkpFmt2_idx K toyA Sg E₀ Kc Wp toyMsg, ldLkpFmt2_free K toyA Sg E₀ Kc Wp toyMsg,
        ldLkpFmt2_bud K toyA Sg E₀ Kc Wp toyMsg⟩⟩

end Cb
