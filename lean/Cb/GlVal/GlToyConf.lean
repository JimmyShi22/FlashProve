-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyConf.lean: a small test instance of a configuration: a Reed-Solomon code of length 8
with its encoder, the format of the encoded index, and a model whose index set is a parameter, over
the field with p = 2^64 - 2^32 + 1 elements and its cubic extension. Conditions that theorems within
a third of the distance put on a configuration are proved for it.

Definitions, statements (`Cb.Gl.Spec.toyCf8_third` and its like) and proofs. A guard against empty
theorems; no parameter of a protocol.
A configuration is a value of the structure `LdCf F E` (Cb/Obj/LdObjectConf.lean). F is the integers
modulo p; it has the entries of index messages and of the model, and is the code's own field. E =
F[x] / (x^3 - 2) is the field over which the encoded index is read. The analogue over one field with
101 elements is in Cb/Obj/LdObjectToyConf7.lean (there: seven points, distance 5).

The configuration (`toyCf8 Mo`). Its code is `C8` (Cb/GlVal/GlToyBase.lean): Reed-Solomon on the
subgroup of order 8, of dimension 3, with one message symbol and two symbols of randomness; distance
6. It has two rows; one entry a row, which is the layout; no pad; no sample (one seed, no answer);
radius of decoding 1: 3 · 1 < 6.
The index set is a parameter (`ToyMo8`: the indices, the entries that an index has, which tables of
entries hold an index; the law: the entries of an index hold it), with entries in F. The relation
pair, the trace and the cells are trivial.

Main names; the `Spec` statements are for every Mo:
  `Spec.toyCf8_third`: `toyCf8 Mo` has `LdCf.Third` (Cb/Obj/LdObjectThirdTests.lean): the code's
    `Enc.Core`, its distance, 3 · eM < d, the sample map's condition, the model's conditions.
  `Spec.toyCf8_ok`: it has `LdCf.OK` at 1 (Cb/Obj/LdObjectConf.lean: the named conditions on code,
    format and model; 1 bounds the lists at the radius of decoding).



  `Spec.toyCf8_gl`: seven clauses: the code `rs 3 2 1 2 1 2`, four inequalities, sample map, model.
  `Spec.toyCf8_code`: distance at least 6 over both fields (`HasDist`), the code's own number d = 6,
    radius 1, two hidden positions (in this sense: the code's own number b = 2, the number of
    positions in `Enc.Core.hides`), lists of at most 1 at every radius up to 1, at most 2
    exceptional coefficients of a fold at the radius 1.
  `ToyMo8.all`, `ToyMo8.two`, `toyMo8_two_proper`, `plcK8` (injective: `plcK8_inj`): see their doc
    comments.

Of these seven clauses none needs F = E: all statements above are proved as they stand
over the two fields.
A trap: a "show" or "rfl" that makes Lean compare two numbers in which `Fintype.card E` occurs
(here: card E ^ (1 - 1)) lets it enumerate the field: no error, all memory. Rewrite the exponent
first (`Nat.sub_self`, `pow_zero`), as the proof of `toyCf8_code` does.

Limits: this file has no protocol, prover, verifier or error: no level of security is said; on zero
knowledge: `LdCf.Third` and `LdCf.OK`, which `Spec.toyCf8_third` and `Spec.toyCf8_ok` conclude,
have, nested in their fields, `hides` (`Enc.Core`, Cb/Gen/CodeList.lean), at the toy code `C8`:
conclusions. The encoded index is read at the radius 1 (eM = 1, d = 6: 3 · eM < d).
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyBase
import Cb.Gl.GlOff
import Cb.Obj.LdObjectConfMore
import Cb.Obj.LdObjectThirdTestsProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Gl
open Iop Prob Hiop Blocks Cb.Ood

/-- The one entry of a row's message part. -/
def plE8 : Unit ⊕ Empty ≃ Fin C8.msg where
  toFun _ := (⟨0, Nat.one_pos⟩ : Fin 1)
  invFun _ := Sum.inl ()
  left_inv := by rintro (⟨⟩ | e) <;> [rfl; exact e.elim]
  right_inv := fun i => Fin.ext (by
    have h : i.val < 1 := i.2
    show 0 = i.val
    omega)

/-- The index set of the toy: the data. Entries in F. -/
structure ToyMo8 where
  I     : Type
  body  : I → (Fin 1 → Bool) × Unit → F
  heldB : ((Fin 1 → Bool) × Unit → F) → Option I
  held  : ∀ i, heldB (body i) = some i

/-- Every table holds an index. -/
def ToyMo8.all : ToyMo8 := ⟨(Fin 1 → Bool) × Unit → F, fun i => i, fun a => some a, fun _ => rfl⟩

open Classical in
/-- A proper index set: the tables all of whose entries are 5 or 7. -/
def ToyMo8.two : ToyMo8 where
  I := {a : (Fin 1 → Bool) × Unit → F // ∀ n, a n = 5 ∨ a n = 7}
  body := fun i => i.1
  heldB := fun a => if h : ∀ n, a n = 5 ∨ a n = 7 then some ⟨a, h⟩ else none
  held := fun i => dif_pos i.2

/-- The toy configuration. -/
def toyCf8 (Mo : ToyMo8) : LdCf F E where
  C₀ := C8
  hp := (by norm_num : (1 : ℕ) ≤ 2 + 1)
  v := 1
  J₀ := Unit
  Pd := Empty
  Lay := Unit
  lay := fun _ => ()
  plE := plE8
  Z := Sample.nil E (Unit ⊕ Empty)
  eM := 1
  rank := fun _ => 0
  I := Mo.I
  Xm := Unit
  Cells := Unit
  Ryes := fun _ _ _ => True
  Rno := fun _ _ _ => True
  trace := fun _ _ => ()
  cells0 := ()
  body := Mo.body
  heldB := Mo.heldB

instance neN8 (Mo : ToyMo8) : Nonempty (Fin (toyCf8 Mo).C₀.n) := ⟨(⟨0, by norm_num⟩ : Fin (2 ^ 3))⟩

/-- Each of the three entries of a full message has a corner of a square of its own. -/
def plcK8 : Fin C8.k → Fin 2 → Bool := fun i j => decide (i.val = j.val + 1)

theorem plcK8_inj : Function.Injective plcK8 := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  revert h0 h1
  have ha : a.val < 3 := a.2
  have hb : b.val < 3 := b.2
  simp only [plcK8, Fin.val_zero, Fin.val_one, decide_eq_decide]
  intro h0 h1
  exact Fin.ext (by omega)

theorem distC8 (Mo : ToyMo8) : HasDist (toyCf8 Mo).C₀.G (toyCf8 Mo).C₀.d := dist8

theorem smp8 (Mo : ToyMo8) : (toyCf8 Mo).Z.OKOn (PadInF F) := fun _ _ _ =>
  le_trans (cnt_le_card _) (le_of_eq (Fintype.card_unit))

theorem model8 (Mo : ToyMo8) : (toyCf8 Mo).ModelOK :=
  ⟨fun _ _ _ h => h, fun _ _ _ h => h, Mo.held,
    fun _ _ h => congrArg Mo.heldB (funext fun n => h n.1 n.2)⟩

namespace Spec

def toyCf8_third : Prop := ∀ Mo, (toyCf8 Mo).Third

def toyCf8_ok : Prop := ∀ Mo, (toyCf8 Mo).OK 1

/-- Seven clauses at `toyCf8 Mo`: the code, four inequalities, the sample map, the model. -/
def toyCf8_gl : Prop :=
  ∀ Mo, (toyCf8 Mo).C₀ = rs 3 2 1 2 1 2 ∧ 3 ≤ 32 ∧ 2 < 2 ^ 3 ∧ 1 + 2 ≤ 2 + 1 ∧
    3 * (toyCf8 Mo).eM < 2 ^ 3 - 2 ∧ (toyCf8 Mo).Z.OKOn (PadInF F) ∧ (toyCf8 Mo).ModelOK

def toyCf8_code : Prop :=
  ∀ Mo,
    HasDist (toyCf8 Mo).C₀.G 6 ∧
    HasDist (toyCf8 Mo).X.G 6 ∧
    (toyCf8 Mo).eM = 1 ∧
    (toyCf8 Mo).C₀.d = 6 ∧
    (toyCf8 Mo).C₀.b = 2 ∧
    (∀ e', e' ≤ 1 →
      ∀ f : (toyCf8 Mo).X.Row → Fin (toyCf8 Mo).C₀.n → E,
        ListLE (DecodesTo (toyCf8 Mo).X.G e' f) 1) ∧
    (toyCf8 Mo).X.MCAeq 1 2

end Spec

theorem toyCf8_third : Spec.toyCf8_third := fun Mo =>
  ⟨core8, distC8 Mo, (by norm_num : 3 * 1 < 6), smp8 Mo, model8 Mo⟩

theorem toyCf8_ok : Spec.toyCf8_ok := fun Mo => ldT3_conf F E (toyCf8 Mo) (toyCf8_third Mo)

theorem toyCf8_gl : Spec.toyCf8_gl := fun Mo =>
  ⟨rfl, by norm_num, by norm_num, by norm_num,
    (by norm_num : 3 * 1 < 2 ^ 3 - 2), smp8 Mo, model8 Mo⟩

theorem toyCf8_code : Spec.toyCf8_code := by
  intro Mo
  refine ⟨distC8 Mo, ldCm_dist F E (toyCf8 Mo) (distC8 Mo), rfl, rfl, rfl,
    fun e' he =>
      ldCm_list_le F E (toyCf8 Mo) 1 e'
        (ldCm_list_unique F E (toyCf8 Mo) (distC8 Mo) (by norm_num : 2 * 1 < 6)) he, ?_⟩
  have h := ldCm_mca_third F E (toyCf8 Mo) 1 (distC8 Mo) (by norm_num : 3 * 1 < 6)
  have hv : (toyCf8 Mo).v = 1 := rfl
  have e : (toyCf8 Mo).v * (1 + 1) * Fintype.card E ^ ((toyCf8 Mo).v - 1) = 2 := by
    rw [hv, Nat.sub_self, pow_zero]
    rfl
  rwa [e] at h

/-- At the proper index set there is a table that holds no index. -/
theorem toyMo8_two_proper : ToyMo8.two.heldB (fun _ => 6) = none := by
  have hn : ¬ ∀ n : (Fin 1 → Bool) × Unit, (6 : F) = 5 ∨ (6 : F) = 7 := fun h => by
    rcases h (fun _ => false, ()) with h | h
    · exact n65F h
    · exact n67F h
  unfold ToyMo8.two
  dsimp only
  exact dif_neg hn

end Cb.Gl
