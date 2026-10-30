-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyChalTie.lean: the verifier message of the toy of Run/ToyQ.lean (`Run.Toy1`: this library's
own, not the programs') is the format's draw (section 6 of the page, in an edition that is not the
one that ships), by proof.

Statements (each a `Prop` in the namespace `Run.Spec`) and proofs. Nothing is defined but these
statements.
Run/ToyQ.lean wires the toy's one round with a verifier message by two lines of its own (a position:
the low four bits of word i of the one block), and lists the drawn positions by a filter over the
sixteen positions. Run/ToyChal.lean makes the same map out of the functions of Fmt/Rules6.lean. Here
the two are shown equal.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `Spec.toy1_chal`: the wire's map from blocks to the verifier message, `Toy1.w1.chal`, is
    `Run.toyChal` at one block: so (`chalPoss_draw`, Run/ToyChal.lean) its three values are what the
    format's `drawPoss 4 3` gives on the row of words of that block (R6.1, R6.6).
  `Spec.toy1_list`: the toy's list of the drawn positions (`Toy1.listOf`), as numbers, is the
    format's list (`Fmt.listOf`) of the draws: the set of the draws, increasing (R6.6).

Limits: this file says nothing on the law of the map on a uniform block. Nothing on the other wires.

Terms: lean/GLOSSARY.md.
-/
import Run.ToyQ
import Run.ToyChal
import Fmt.Rules6Laws

set_option autoImplicit false

namespace Run
open Iop

/-- States that the wire's map, `Toy1.w1.chal`, is `toyChal` at one block. -/
def Spec.toy1_chal : Prop := Toy1.w1.chal = toyChal (K := 1)

/-- States that the toy's list is the format's list of the draws, for every verifier message. -/
def Spec.toy1_list : Prop :=
  ∀ c : Fin 3 → Fin 16,
    (Toy1.listOf c).map Fin.val = _root_.Fmt.listOf (List.ofFn fun i => (c i).val)

theorem toy1_chal : Spec.toy1_chal := by
  funext u i
  apply Fin.ext
  show (_root_.Fmt.wordAt (digToBytes (u 0)) (8 * i.val)).toNat % 16 =
    (rowOfDigs u i.val).toNat % 2 ^ 4
  have hi : i.val < 3 := i.isLt
  have e : rowOfDigs u i.val = _root_.Fmt.wordAt (digToBytes (u 0)) (8 * i.val) := by
    show _root_.Fmt.wordAt
        ((Array.ofFn fun j : Fin 1 => digToBytes (u j)).getD (i.val / 4) ByteArray.empty)
        (8 * (i.val % 4)) = _
    rw [show i.val / 4 = 0 by omega, show i.val % 4 = i.val by omega]
    rfl
  rw [e]
  rfl

theorem toy1_list : Spec.toy1_list := by
  intro c
  have h1 : ((Toy1.listOf c).map Fin.val).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact ((List.pairwise_lt_finRange 16).filter _).imp fun h => h
  have h2 := _root_.Fmt.listOf_incr (List.ofFn fun i => (c i).val)
  refine List.Perm.eq_of_pairwise
    (le := (· < ·)) (fun a b _ _ hab hba => absurd hab (Nat.lt_asymm hba)) h1 h2 ?_
  refine (List.perm_ext_iff_of_nodup
      (h1.imp fun h => Nat.ne_of_lt h) (h2.imp fun h => Nat.ne_of_lt h)).2 fun x => ?_
  rw [_root_.Fmt.listOf_mem, List.mem_map, List.mem_ofFn]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := of_decide_eq_true (List.mem_filter.1 hy).2
    exact ⟨i, congrArg Fin.val hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨c i, List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true ⟨i, rfl⟩⟩, rfl⟩

end Run
