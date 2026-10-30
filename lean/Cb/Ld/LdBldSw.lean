-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldSw.lean: this file builds the data of a code switch (`LdSwD`, Cb/Obj/LdObjectTower.lean)
from numbers; a code switch is a step of the proximity test from one code to a new code whose
message has as its coordinates the old message, the old encoding randomness and a pad.

The parts of a code switch, built from numbers: the pad with filler entries, the placing, the sample
(a row with a pad that also reads the filler entries), the zero-evader of the batching (equality
weights); the form "row with a pad and filler entries" as a predicate on data.

Definitions and statements; the proofs are in Cb/Ld/LdBldSwProofs.lean. Generic: any finite field;
no code of a particular kind; nothing assumed beyond the hypotheses of the statements and whatever
the arguments hold as proofs.
`Z.OK` says of a sample map (`Sample E J`, Cb/Gen/OodDec.lean) or a zero-evader (`Evader E J`,
Cb/Gen/BatEvader.lean) that a vector other than 0 has all answers 0 (is annihilated) at no more than
`Z.err` seeds. The equality weight of a point z at a corner b of the cube is ∏ v, (z v if b v, else
1 - z v) (`Alg.eqk`, Alg/Mle.lean).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: a code switch (Cb/Ld/LdSwitch.lean; as data after a fold: `LdSwD`, Cb/Obj/LdObjectTower.lean)
names the coordinates of the new code's message by an equivalence "place" from (old message ⊕ old
encoding randomness) ⊕ pad. In a tower the new code is the next stage's input code: main rows beside
mask rows, whose sizes are products with powers of two. This protocol's technical report
(lean/CREDITS.md) lets the folded main message fill the next main rows, and lays into the next mask
rows: the two folded mask messages, the randomness of the three encodings, folded, then uniform
entries up to the rows' size, and the pad of the sample. So the switch's pad Qo has to hold filler
entries beside the one entry that masks the sample's answer.

Main names:
  `Z.PadFillForm`: Z, a sample map on J₀ ⊕ Qo, is the row with a pad (`Sample.pad`,
    Cb/Gen/OodDecPad.lean) on (J₀ ⊕ Fl) ⊕ P, re-bracketed: entries proper and filler entries at
    different corners of a cube, with equality weights; the pad entries P with weights b(β) w_i,
    (w_i) a basis of E over E (so one entry); b injective, never 0.
  `Spec.bldSw_fill`: `Z.PadFillForm` → `Z.OK` ∧ `Z.PrivateSim E` (a zero-evader on all vectors,
    filler entries included; private with a simulator, error 0, over uniform filler entries and
    pad).
The parts (namespace `Cb.Bld`), each a term of its own, on plain types (J₀: old message ⊕ old
randomness; Fl: the filler entries; Jn: the coordinates of the new message; R: the rows that are
batched):
  `swZo E place mv cor`: the sample: one answer; a seed is a point of E^mv and a unit β of E; an
    entry proper or filler entry n has the equality weight of the point at the corner cor (place n)
    of its place in the new message; the pad has the weight β.
  `swZb E gb num`: the zero-evader: a seed is a point of E^gb; the row x has the equality weight of
    the point at the corner num x.
  `sw Y Cnew Fl place mv cor ts gb num`: the data of a switch after the fold Y (`LdSwD`) from these
    parts; ts: the number of long positions of the input that the verifier reads (`LdSw.t`,
    Cb/Ld/LdSwitch.lean); the fold's long positions P are not empty.
  `Spec.bldSw_zo`, `Spec.bldSw_zb`: cor injective → `PadFillForm`; num injective → the evader is of
    one of the forms of zero-evaders that have a theorem in this library (`Evader.Form`,
    Cb/Req1/LdReqJohnEvForm.lean).
  `Spec.bldSw_nums`, `Spec.bldSw_frac`: the four numbers; as fractions.
  `Spec.bldSw_fix`: at every seed, for every value of the entries proper and the filler entries, pad
    ↦ answer is a bijection of E.
  `Spec.bldSw_sw`: long positions P not empty, cor, num injective → at every radius the switch's
    sample is a zero-evader and private with a simulator, its evader evades; both are of their
    forms.

Limits: this file says nothing on codes, lists, radii. It does not say that the numbers are small
against q = |E|. It does not say that any equation between cardinalities holds, but for those in
`Spec.bldSw_pad_one` (for `Z.PadForm E`), `Spec.bldSw_nums`, `Spec.bldSw_frac` (for 2 ≤ mv; for
1 ≤ gb): so not those that the placing needs (`hM`, `hR` of `swPlaceN`), nor the like equations
between numbers, `main` and `rest` of `SwEqP` (Cb/Ld/LdBldSwOrd.lean).
A sample here has one answer; this file says nothing on samples with more.
It does not say that the filler entries serve any purpose but to fill: they are uniform, read by the
sample, by nothing else here. Privacy is over uniform filler entries and pad together (the library's
notion draws all of Qo); by `Spec.bldSw_fix` the pad alone does it: for every value of all other
entries the map pad ↦ answer is a bijection.
Declared. (1) `swPlaceN`, `swCor` take an enumeration of a finite type (`Fintype.equivFin`,
`Fintype.equivOfCardEq`: by choice): which coordinate stands where within the main rows and within
the mask rows is not fixed by them; the report fixes an order. Whoever wants an order puts it
in through `swPlace`, cor, num (so `pPlace`, `pCor`, `pNum`, Cb/Ld/LdBldSwOrd.lean): every statement
here is for all of them. (2) The pad's weight is a unit β drawn with the point, not an equality
weight.
The form `Z.PadForm E` (Cb/Req1/LdReqJohnEvRec.lean) asks that the pad's weights be a basis of E
over E: the pad then has exactly one entry (`Spec.bldSw_pad_one`), and "place" forces |new message|
= |old message| + |old randomness| + 1: that number is not of the shape (power of two) · m + (power
of two) · m' at the report's reference numbers. The records that ask properties of the sample
(`Z.OK`, `Z.PrivateSim E`) are not touched by this; the records that ask `Z.PadForm E` of a switch's
sample cannot be met at those numbers. No record of this library asks `Z.PadForm E` of a switch's
sample: Cb/Gl/GlFinalEv.lean asks `PadFillForm`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqJohnEvRec
import Cb.Gen.OodDecSend
import Cb.Obj.LdObjectTower
import Alg.Mle
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood

namespace Ood

/-- The re-bracketing: the filler entries go to the entries proper. -/
def fillBr {J₀ Qo Fl P : Type} (σ : Qo ≃ Fl ⊕ P) : J₀ ⊕ Qo ≃ (J₀ ⊕ Fl) ⊕ P :=
  (Equiv.sumCongr (Equiv.refl J₀) σ).trans (Equiv.sumAssoc J₀ Fl P).symm

/-- The sample map is the row with a pad that also reads the filler entries. -/
def Sample.PadFillForm {E J₀ Qo : Type} [Field E] [Fintype E] (Z : Sample E (J₀ ⊕ Qo)) : Prop :=
  ∃ (Fl P μ B : Type) (_ : Fintype P) (_ : Fintype μ) (_ : DecidableEq μ) (_ : Fintype B)
      (_ : Nonempty B) (σ : Qo ≃ Fl ⊕ P) (pl : J₀ ⊕ Fl → μ → Bool) (w : P → E) (b : B → E),
    Z = (Sample.pad E μ (J₀ ⊕ Fl) P B pl w b).comap (fillBr σ) ∧ Function.Injective pl ∧
    Function.Injective b ∧ PadBasis E w ∧ ∀ β, b β ≠ 0

end Ood

namespace Bld

/-- entries proper and filler entries, among all entries of the new message -/
def swIn {J₀ Fl : Type} : J₀ ⊕ Fl → J₀ ⊕ (Fl ⊕ Unit) :=
  Sum.elim Sum.inl fun f => Sum.inr (Sum.inl f)

open Classical in
/-- The sample. -/
def swZo (E : Type) [Field E] [Fintype E] {J₀ Fl Jn : Type}
    (place : J₀ ⊕ (Fl ⊕ Unit) ≃ Jn) (mv : ℕ) (cor : Jn → Fin mv → Bool) :
    Sample E (J₀ ⊕ (Fl ⊕ Unit)) :=
  (Sample.pad E (Fin mv) (J₀ ⊕ Fl) Unit Eˣ (fun n => cor (place (swIn n)))
      (fun _ => 1) Units.val).comap
    (fillBr (Equiv.refl (Fl ⊕ Unit)))

/-- The zero-evader of the batching. -/
@[reducible] def swZb (E : Type) [Field E] [Fintype E] {R : Type}
    (gb : ℕ) (num : R → Fin gb → Bool) : Evader E R :=
  (Evader.eqPt E (Fin gb)).comap num

/-- a corner for each coordinate (for each row), from an enumeration -/
def swCor (J : Type) [Fintype J] (mv : ℕ) : J → Fin mv → Bool := fun j =>
  Alg.bits mv (Fintype.equivFin J j).val

/-- the old main message apart; the old masks' messages, all old randomness and the pad together -/
def swBr (C Zs Q Pd : Type) : ((C ⊕ Zs) ⊕ Q) ⊕ Pd ≃ C ⊕ ((Zs ⊕ Q) ⊕ Pd) :=
  (Equiv.sumCongr (Equiv.sumAssoc C Zs Q) (Equiv.refl Pd)).trans (Equiv.sumAssoc C (Zs ⊕ Q) Pd)

/-- The placing into main rows beside mask rows. -/
def swPlace {C Zs Q Pd A B : Type} (eM : C ≃ A) (eR : (Zs ⊕ Q) ⊕ Pd ≃ B) :
    ((C ⊕ Zs) ⊕ Q) ⊕ Pd ≃ A ⊕ B :=
  (swBr C Zs Q Pd).trans (Equiv.sumCongr eM eR)

/-- the same from two equations between cardinalities -/
def swPlaceN {C Zs Q Pd A B : Type} [Fintype C] [Fintype Zs] [Fintype Q] [Fintype Pd]
    [Fintype A] [Fintype B] (hM : Fintype.card C = Fintype.card A)
    (hR : Fintype.card ((Zs ⊕ Q) ⊕ Pd) = Fintype.card B) : ((C ⊕ Zs) ⊕ Q) ⊕ Pd ≃ A ⊕ B :=
  swPlace (Fintype.equivOfCardEq hM) (Fintype.equivOfCardEq hR)

/-- The data of a switch after the fold Y. -/
def sw {E P P' : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P)
    [Fintype Y.Cout.Aa] (Cnew : LdCode E P') (Fl : Type) [Fintype Fl] [DecidableEq Fl]
    (place : (Y.Cout.J ⊕ Y.Cout.Q) ⊕ (Fl ⊕ Unit) ≃ Cnew.J) (mv : ℕ) (cor : Cnew.J → Fin mv → Bool)
    (ts gb : ℕ) (num : LdRow Unit ts Y.Cout.Aa → Fin gb → Bool) : LdSwD Y P' where
  Cnew := Cnew
  Qo := Fl ⊕ Unit
  place := place
  Zo := swZo E place mv cor
  ts := ts
  Zb := swZb E gb num

end Bld

namespace Spec
open Cb.Bld

/-- A sample map with `Z.PadForm E` has a pad of exactly one entry. -/
def bldSw_pad_one : Prop :=
  ∀ (E J₀ P : Type) [Field E] [Fintype E] [Fintype P] (Z : Sample E (J₀ ⊕ P)),
    Z.PadForm E → Fintype.card P = 1

/-- `Z.PadForm E` is a case of `Z.PadFillForm`; in the proof: the case without a filler entry
(Fl := `Empty`, Cb/Ld/LdBldSwProofs.lean). -/
def bldSw_of_pad : Prop :=
  ∀ (E J₀ P : Type) [Field E] [Fintype E] [Fintype P] (Z : Sample E (J₀ ⊕ P)),
    Z.PadForm E → Z.PadFillForm

/-- A sample map of the form is a zero-evader on all vectors, and private with a simulator. -/
def bldSw_fill : Prop :=
  ∀ (E J₀ Qo : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype Qo] (Z : Sample E (J₀ ⊕ Qo)),
    Z.PadFillForm → Z.OK ∧ Z.PrivateSim E

def bldSw_zo : Prop :=
  ∀ (E J₀ Fl Jn : Type) [Field E] [Fintype E] (place : J₀ ⊕ (Fl ⊕ Unit) ≃ Jn)
      (mv : ℕ) (cor : Jn → Fin mv → Bool),
    Function.Injective cor → (swZo E place mv cor).PadFillForm

def bldSw_zb : Prop :=
  ∀ (E R : Type) [Field E] [Fintype E] (gb : ℕ) (num : R → Fin gb → Bool),
    Function.Injective num → (swZb E gb num).Form

/-- The four numbers, q = |E|: the sample: the larger of mv q^(mv-1) (q-1) and q^mv, of q^mv (q-1)
seeds; the evader: gb q^(gb-1) of q^gb seeds. -/
def bldSw_nums : Prop :=
  ∀ (E J₀ Fl Jn R : Type) [Field E] [Fintype E] (place : J₀ ⊕ (Fl ⊕ Unit) ≃ Jn) (mv : ℕ)
      (cor : Jn → Fin mv → Bool) (gb : ℕ) (num : R → Fin gb → Bool),
    (swZo E place mv cor).err =
      max (mv * Fintype.card E ^ (mv - 1) * (Fintype.card E - 1)) (Fintype.card E ^ mv) ∧
    Fintype.card (swZo E place mv cor).D = Fintype.card E ^ mv * (Fintype.card E - 1) ∧
    (swZb E gb num).err = gb * Fintype.card E ^ (gb - 1) ∧
    Fintype.card (swZb E gb num).D = Fintype.card E ^ gb

/-- As fractions: mv of |E| for 2 ≤ mv; gb of |E| for 1 ≤ gb. -/
def bldSw_frac : Prop :=
  ∀ (E J₀ Fl Jn R : Type) [Field E] [Fintype E] (place : J₀ ⊕ (Fl ⊕ Unit) ≃ Jn) (mv : ℕ)
      (cor : Jn → Fin mv → Bool) (gb : ℕ) (num : R → Fin gb → Bool),
    (2 ≤ mv →
      (swZo E place mv cor).err * Fintype.card E = mv * Fintype.card (swZo E place mv cor).D) ∧
    (1 ≤ gb → (swZb E gb num).err * Fintype.card E = gb * Fintype.card (swZb E gb num).D)

def bldSw_cor : Prop :=
  ∀ (J : Type) [Fintype J] (mv : ℕ), Fintype.card J ≤ 2 ^ mv → Function.Injective (swCor J mv)

/-- The pad alone makes the answer uniform: at every seed, for every value of the entries proper and
the filler entries, pad ↦ answer is a bijection of E. -/
def bldSw_fix : Prop :=
  ∀ (E J₀ Fl Jn : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype Fl]
      (place : J₀ ⊕ (Fl ⊕ Unit) ≃ Jn) (mv : ℕ) (cor : Jn → Fin mv → Bool)
      (ρ : (swZo E place mv cor).D) (a : J₀ → E) (x : Fl → E),
    Function.Bijective fun c : E =>
      (swZo E place mv cor).val ρ (Sum.elim a (Sum.elim x fun _ => c)) ()

/-- The switch from these parts: what the records of a tower require of its two maps (`LdSw.Hyp`,
Cb/Ld/LdTower.lean: okO, okB, priv; the two forms: Cb/Gl/GlFinalEv.lean). -/
def bldSw_sw : Prop :=
  ∀ (E P P' : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P)
      [Fintype Y.Cout.Aa] (Cnew : LdCode E P') (Fl : Type) [Fintype Fl] [DecidableEq Fl]
      (place : (Y.Cout.J ⊕ Y.Cout.Q) ⊕ (Fl ⊕ Unit) ≃ Cnew.J) (mv : ℕ) (cor : Cnew.J → Fin mv → Bool)
      (ts gb : ℕ) (num : LdRow Unit ts Y.Cout.Aa → Fin gb → Bool),
    Function.Injective cor → Function.Injective num →
    ∀ e : ℕ,
      ((sw Y Cnew Fl place mv cor ts gb num).D e).Zo.OK ∧
      ((sw Y Cnew Fl place mv cor ts gb num).D e).Zb.OK ∧
      ((sw Y Cnew Fl place mv cor ts gb num).D e).Zo.PrivateSim E ∧
      ((sw Y Cnew Fl place mv cor ts gb num).D e).Zo.PadFillForm ∧
      ((sw Y Cnew Fl place mv cor ts gb num).D e).Zb.Form

end Spec
end Cb
