-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectToyConf7.lean: the toy's index set (`ToyMo`) and its places over the seven-point
code.

Definitions and proofs. No parameter of a protocol.







Main names:

  The code is that of
    Cb/Ld/LdRelToy7.lean: Reed-Solomon over the field with 101 elements, seven points, dimension 3
    (one message symbol, two symbols of randomness), distance 5.



  `LdToy7.ToyMo`: the index set, as data.

  `ToyMo.all`: every table holds an index: weights-formedness then has nothing to check.







Limits: no security.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectConfMore
import Cb.Ld.LdRelToy7

set_option autoImplicit false

namespace Cb
namespace LdToy7
open Iop Prob Hiop Blocks Cb.Ood LdToy

/-- the one entry of a row's message part -/
def plE7 : Unit ⊕ Empty ≃ Fin C7.msg where
  toFun _ := ⟨0, by decide⟩
  invFun _ := Sum.inl ()
  left_inv := by rintro (⟨⟩ | e) <;> [rfl; exact e.elim]
  right_inv := fun i => Fin.ext (by
    have h : i.val < 1 := i.2
    show 0 = i.val
    omega)

/-- The index set of the toy, as data: the indices, the entries that an index has, which tables of
entries hold an index; the law `held`: the entries of an index hold it. -/
structure ToyMo where
  I     : Type
  body  : I → (Fin 1 → Bool) × Unit → K
  heldB : ((Fin 1 → Bool) × Unit → K) → Option I
  held  : ∀ i, heldB (body i) = some i

/-- every table holds an index -/
def ToyMo.all : ToyMo := ⟨(Fin 1 → Bool) × Unit → K, fun i => i, fun a => some a, fun _ => rfl⟩

/-- a proper index set: the tables all of whose entries are 5 or 7 -/
def ToyMo.two : ToyMo where
  I := {a : (Fin 1 → Bool) × Unit → K // ∀ n, a n = 5 ∨ a n = 7}
  body := fun i => i.1
  heldB := fun a => if h : ∀ n, a n = 5 ∨ a n = 7 then some ⟨a, h⟩ else none
  held := fun i => dif_pos i.2

/-- each of the three entries of a full message has a corner of a square of its own -/
def plcK : Fin C7.k → Fin 2 → Bool := fun i j => decide (i.val = j.val + 1)

theorem plcK_inj : Function.Injective plcK := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  revert h0 h1
  have ha : a.val < 3 := a.2
  have hb : b.val < 3 := b.2
  simp only [plcK, Fin.val_zero, Fin.val_one, decide_eq_decide]
  intro h0 h1
  exact Fin.ext (by omega)

end LdToy7

open Iop Prob Hiop Blocks Cb.Ood LdToy LdToy7

/-- at the proper index set there is a message that holds no index -/
theorem toyMo_two_proper : ToyMo.two.heldB (fun _ => 0) = none := by
  have hn : ¬ ∀ n : (Fin 1 → Bool) × Unit, (0 : K) = 5 ∨ (0 : K) = 7 := fun h => by
    rcases h (fun _ => false, ()) with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  show (if h : ∀ n : (Fin 1 → Bool) × Unit,
      (0 : K) = 5 ∨ (0 : K) = 7 then some (⟨fun _ => 0, h⟩ : ToyMo.two.I) else none) = none
  exact dif_neg hn

end Cb
