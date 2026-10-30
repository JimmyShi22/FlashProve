-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Digits/DatQ.lean: the numbering of the keys and rows of the lookup on the digits of a
smallness test, as a record of plain data with its laws; what the laws give for the lookup's claim
at its start and for the claim on its keys at its end. Definitions, statements and proofs.

A smallness test cuts each combination into a low and a high digit. One lookup with two calls is to
show that every low digit is below q and every high digit below H. The keys of all calls lie in one
joint vector of 2^v places, of which some are padding and hold 0. The rows of all tables lie in one
joint table of 2^d rows, in which a short table may stand several times. A drawn shift θ, times the
call's tag, is added to keys and rows alike (Cb/Pv/Lookup/Shift/ShiftQ.lean).

Main names:
  `DatQ I J`: the record. I: the names of the digits of one kind; J: the names of the entries of
    the committed messages. Every field is a number, a map on numbers or a place.
  `DatQ.DatOK q H pp`: its laws: statements on numbers, each bounded. pp: the characteristic.
  `DatQ.key`, `DatQ.tab`, `DatQ.tagE`, `DatQ.sh`: the joint keys as a term in the entries, the joint
    table and the tags, before the shift; the shift's data at them.
  `dgQ_in`: UNDER `DatOK`: each key is in the rows of its call if and only if every low digit is
    below q and every high digit below H (`Cb.Rng.InTab`, Cb/Gen/RngAlg.lean).
  `dgQ_tags`: under `DatOK`, in characteristic pp: the tags tell the calls apart.
  `dgQ_sum`, `dgQ_keys`, `dgQ_form`, with `DatQ.formK`, `DatQ.constK`: under `DatOK`: the
    multilinear extension of the shifted joint keys at a point is a linear form in the digits, plus
    θ times a public constant.
  `DatQ.rowH`, `DatQ.hbits`: the honest side's rows and planes of counts. Definitions alone.

Limits: no numbering with `DatOK` is given here. `DatOK` does not ask q ≤ pp or H ≤ pp: above the
characteristic "below q" is met by every element of the prime field. Nothing is proved here of the
honest side's planes. No protocol occurs. No definition here is noncomputable.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Lookup.Shift.ShiftQ
import Cb.Pv.Lookup.Alg.PadAlg
import Cb.Ld.LdRngProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CbQ
open Finset Blocks Cb Cb.Lkp Cb.LdLkp Cb.Rng Cb.RngPk

/-- The numbering of the keys and rows of the lookup on the digits. `false`: the low digits;
`true`: the high digits. -/
structure DatQ (I J : Type) where
  /-- the places of the digits among the entries -/
  lo    : I → J
  hi    : I → J
  /-- 2^v joint keys, 2^d joint rows, nc calls -/
  v     : ℕ
  d     : ℕ
  nc    : ℕ
  /-- the call of a kind of digits -/
  call  : Bool → ℕ
  /-- the joint key's number of a digit; its inverse (none: a padding place) -/
  pos   : Bool × I → ℕ
  digAt : ℕ → Option (Bool × I)
  /-- the call of a joint key; of a joint row; the number that a row holds before the shift; the
  number that is a call's tag -/
  fK    : ℕ → ℕ
  fT    : ℕ → ℕ
  rowV  : ℕ → ℕ
  tag   : ℕ → ℕ
  /-- one rule for the honest side: the joint row at which a key of call c with the value a is
  counted; the row of a call's padding key -/
  rowOf : ℕ → ℕ → ℕ
  zRow  : ℕ → ℕ
  /-- the planes' places: (joint row, plane) -/
  bAt   : ℕ → ℕ → J
  /-- the public padding: (joint row, how many padding keys hold it) -/
  pads  : List (ℕ × ℕ)

namespace DatQ
variable {I J : Type} (Q : DatQ I J)

/-- the place of a digit -/
def plc (p : Bool × I) : J := if p.1 then Q.hi p.2 else Q.lo p.2

/-- is the joint key X a padding place? -/
def padB (X : ℕ) : Bool := (Q.digAt X).isNone

/-- The laws. q, H: the sizes of the two tables; pp: the characteristic. -/
structure DatOK (q H pp : ℕ) : Prop where
  posLt  : ∀ p, Q.pos p < 2 ^ Q.v
  inv    : ∀ p, Q.digAt (Q.pos p) = some p
  inv'   : ∀ X < 2 ^ Q.v, ∀ p, Q.digAt X = some p → Q.pos p = X
  callK  : ∀ p, Q.fK (Q.pos p) = Q.call p.1
  kLt    : ∀ X < 2 ^ Q.v, Q.fK X < Q.nc
  tLt    : ∀ Y < 2 ^ Q.d, Q.fT Y < Q.nc
  rowLo  : ∀ Y < 2 ^ Q.d, Q.fT Y = Q.call false → Q.rowV Y < q
  rowHi  : ∀ Y < 2 ^ Q.d, Q.fT Y = Q.call true → Q.rowV Y < H
  ofLo   : ∀ a < q, Q.rowOf (Q.call false) a < 2 ^ Q.d ∧
             Q.fT (Q.rowOf (Q.call false) a) = Q.call false ∧
             Q.rowV (Q.rowOf (Q.call false) a) = a
  ofHi   : ∀ a < H, Q.rowOf (Q.call true) a < 2 ^ Q.d ∧
             Q.fT (Q.rowOf (Q.call true) a) = Q.call true ∧
             Q.rowV (Q.rowOf (Q.call true) a) = a
  zero   : ∀ c < Q.nc, Q.zRow c < 2 ^ Q.d ∧ Q.fT (Q.zRow c) = c ∧ Q.rowV (Q.zRow c) = 0
  tagLt  : ∀ c < Q.nc, Q.tag c < pp
  tagInj : ∀ c < Q.nc, ∀ c' < Q.nc, Q.tag c = Q.tag c' → c = c'
  pads   : padsOK Q.v Q.d Q.pads = true
  laid   : ∀ u < 2 ^ Q.d, padCnt Q.pads u =
             (((range (2 ^ Q.v)).filter fun X => Q.padB X = true).filter
               fun X => Q.zRow (Q.fK X) = u).card

variable {E : Type} [Field E]

/-- the joint keys before the shift -/
def key (μ : J → E) : ℕ → E := fun X =>
  match Q.digAt X with
  | some p => μ (Q.plc p)
  | none => 0

/-- the joint table before the shift; the tags -/
def tab : ℕ → E := fun Y => ((Q.rowV Y : ℕ) : E)
def tagE : ℕ → E := fun c => ((Q.tag c : ℕ) : E)

/-- The data of the shift over maps (`ShiftQ`, Cb/Pv/Lookup/Shift/ShiftQ.lean) at these vectors. -/
def sh (St : Type) : ShiftQ E St (J → E) :=
  ⟨Q.v, Q.d, Q.fK, Q.fT, fun _ μ => Q.key μ, fun _ => Q.tab, Q.tagE⟩

/-- The form on the digits in the claim on the keys at a point; the constant that goes with the
shift θ. -/
def formK [Fintype I] [DecidableEq J] (pt : ℕ → E) : J → E := fun n =>
  placed Q.lo (fun i => eqN Q.v 0 pt (Q.pos (false, i))) n +
    placed Q.hi (fun i => eqN Q.v 0 pt (Q.pos (true, i))) n
def constK (pt : ℕ → E) : E := ∑ X ∈ range (2 ^ Q.v), eqN Q.v 0 pt X * Q.tagE (Q.fK X)

/-- The honest side. `nat`: how the prover reads a digit as a number (an argument). The row at which
the key X is counted or, at a padding place, lies. -/
def rowH (nat : E → ℕ) (μ : J → E) : ℕ → ℕ := fun X =>
  match Q.digAt X with
  | some p => Q.rowOf (Q.call p.1) (nat (μ (Q.plc p)))
  | none => Q.zRow (Q.fK X)

/-- The honest planes of counts: `hbitP` (Cb/Pv/Lookup/Alg/PadAlg.lean), padding not counted. -/
def hbits (W : ℕ) (nat : E → ℕ) (μ : J → E) : ℕ → ℕ → E := hbitP Q.v W Q.padB (Q.rowH nat μ)

theorem key_pos {q H pp : ℕ} (h : Q.DatOK q H pp) (μ : J → E) (p : Bool × I) :
    Q.key μ (Q.pos p) = μ (Q.plc p) := by
  unfold key
  rw [h.inv p]

theorem key_none (μ : J → E) {X : ℕ} (hX : Q.digAt X = none) : Q.key μ X = 0 := by
  unfold key
  rw [hX]

theorem pos_inj {q H pp : ℕ} (h : Q.DatOK q H pp) : Function.Injective Q.pos := fun p p' e =>
  Option.some.inj ((h.inv p).symm.trans ((congrArg Q.digAt e).trans (h.inv p')))

end DatQ

section
variable {I J E : Type} [Field E] (Q : DatQ I J) {q H pp : ℕ}

/-- Each key is in the rows of its call if and only if every low digit is below q and every high
digit below H. -/
theorem dgQ_in (h : Q.DatOK q H pp) (μ : J → E) :
    AllInQ Q.v Q.d Q.fK Q.fT (Q.key μ) (Q.tab (E := E)) ↔
      (∀ i, InTab q (μ (Q.lo i))) ∧ ∀ i, InTab H (μ (Q.hi i)) := by
  constructor
  · intro hA
    refine ⟨fun i => ?_, fun i => ?_⟩
    · obtain ⟨Y, hY, hf, he⟩ := hA _ (h.posLt (false, i))
      rw [h.callK] at hf
      rw [Q.key_pos h] at he
      exact ⟨Q.rowV Y, h.rowLo Y hY hf, he⟩
    · obtain ⟨Y, hY, hf, he⟩ := hA _ (h.posLt (true, i))
      rw [h.callK] at hf
      rw [Q.key_pos h] at he
      exact ⟨Q.rowV Y, h.rowHi Y hY hf, he⟩
  · rintro ⟨hl, hh⟩ X hX
    cases hd : Q.digAt X with
    | none =>
      obtain ⟨z1, z2, z3⟩ := h.zero _ (h.kLt X hX)
      refine ⟨_, z1, z2, ?_⟩
      rw [Q.key_none μ hd]
      unfold DatQ.tab
      rw [z3]
      simp
    | some p =>
      have hp := h.inv' X hX p hd
      subst hp
      rw [Q.key_pos h, h.callK]
      obtain ⟨b, i⟩ := p
      cases b with
      | false =>
        obtain ⟨a, ha, he⟩ := hl i
        obtain ⟨o1, o2, o3⟩ := h.ofLo a ha
        refine ⟨_, o1, o2, ?_⟩
        unfold DatQ.tab
        rw [o3]
        exact he
      | true =>
        obtain ⟨a, ha, he⟩ := hh i
        obtain ⟨o1, o2, o3⟩ := h.ofHi a ha
        refine ⟨_, o1, o2, ?_⟩
        unfold DatQ.tab
        rw [o3]
        exact he

/-- The tags tell the calls apart (`ShiftQ.Tags`). -/
theorem dgQ_tags [CharP E pp] (h : Q.DatOK q H pp) (St : Type) : (Q.sh (E := E) St).Tags := fun _ =>
  tagsQ_of_lt E Q.v Q.d Q.nc Q.fK Q.fT _ _ h.kLt h.tLt fun c hc c' hc' e => by
    have h1 : Q.tag c % pp = Q.tag c' % pp := (CharP.natCast_eq_natCast E pp).1 e
    rw [Nat.mod_eq_of_lt (h.tagLt c hc), Nat.mod_eq_of_lt (h.tagLt c' hc')] at h1
    exact h.tagInj c hc c' hc' h1

/-- a weighted sum over the joint keys is a sum over the digits -/
theorem dgQ_sum [Fintype I] (h : Q.DatOK q H pp) (μ : J → E) (c : ℕ → E) :
    ∑ X ∈ range (2 ^ Q.v), c X * Q.key μ X =
      ∑ i, c (Q.pos (false, i)) * μ (Q.lo i) + ∑ i, c (Q.pos (true, i)) * μ (Q.hi i) := by
  classical
  have hsub : (univ : Finset (Bool × I)).image Q.pos ⊆ range (2 ^ Q.v) := fun X hX => by
    obtain ⟨p, _, rfl⟩ := mem_image.1 hX
    exact mem_range.2 (h.posLt p)
  rw [← sum_subset hsub fun X hX hn => by
    cases hd : Q.digAt X with
    | none => rw [Q.key_none μ hd, mul_zero]
    | some p =>
      exact absurd (mem_image.2 ⟨p, mem_univ _, h.inv' X (mem_range.1 hX) p hd⟩) hn]
  rw [sum_image fun p _ p' _ e => Q.pos_inj h e, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  congr 1 <;> exact sum_congr rfl fun i _ => by rw [Q.key_pos h]; rfl

/-- the extension of the shifted joint keys at a point -/
theorem dgQ_keys [Fintype I] (h : Q.DatOK q H pp) (μ : J → E) (θ : E) (pt : ℕ → E) :
    ext Q.v (shKeyQ Q.fK (Q.key μ) Q.tagE θ) pt =
      ∑ i, eqN Q.v 0 pt (Q.pos (false, i)) * μ (Q.lo i) +
          ∑ i, eqN Q.v 0 pt (Q.pos (true, i)) * μ (Q.hi i) +
        θ * Q.constK pt := by
  rw [← dgQ_sum Q h μ fun X => eqN Q.v 0 pt X]
  unfold Blocks.ext shKeyQ DatQ.constK
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun X _ => by ring

/-- the same through the form -/
theorem dgQ_form [Fintype I] [Fintype J] [DecidableEq J] (h : Q.DatOK q H pp) (μ : J → E) (θ : E)
    (pt : ℕ → E) :
    ext Q.v (shKeyQ Q.fK (Q.key μ) Q.tagE θ) pt = ∑ n, Q.formK pt n * μ n + θ * Q.constK pt := by
  rw [dgQ_keys Q h]
  congr 1
  unfold DatQ.formK
  simp only [add_mul, sum_add_distrib]
  rw [ldRng_placed I J E Q.lo _ μ, ldRng_placed I J E Q.hi _ μ]

end

#print axioms CbQ.dgQ_in
#print axioms CbQ.dgQ_tags
#print axioms CbQ.dgQ_keys
#print axioms CbQ.dgQ_form

end CbQ
