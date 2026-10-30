-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/NAtReaders.lean: SIX READERS OF THE TABLE's NUMBERS AT THE CLOSED VALUES (`At.N Zp
cF`, Johnson/P5J/LettersAt.lean) ARE THOSE OF THE PLAN's SEATS ALONE: laying the rows' numbers and
what each sub-protocol tells over `numbersOf (pseats Zp)` leaves sent, keptOf, group, index,
inside and w. Twelve theorems, by unfolding.
Why. Closed facts by Lean's kernel on these readers stand at a WRITTEN list of the plan's seats;
the laws' conditions stand at `At.N`. With these equations, and one equation "the plan's seats are
the written list", such a fact speaks at the closed constant.
  `N_sent`, `N_keptOf`, `N_group`, `N_index`, `N_inside`, `N_w`: the reader of `At.N Zp cF` is
    that of `P5T.numbersOf (At.pseats Zp)`.
  `N_sent_of`, … `N_w_of`: so, where `At.pseats Zp = W`, it is that of `P5T.numbersOf W`: general
    in the list W.
Limits: unfoldings. That the plan's seats are any written list is not shown here. NOT AMONG THE
SIX, SINCE THE LAYINGS TURN THEM: rowsAt, treesAt, msgsAt, indexNo. No soundness is claimed.

-/
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)

variable (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl)

theorem N_sent (l k : ℕ) : (N Zp cF).sent l k = (P5T.numbersOf (pseats Zp)).sent l k := rfl

theorem N_sent_of {W : List P5T.PSeat} (h : pseats Zp = W) (l k : ℕ) :
    (N Zp cF).sent l k = (P5T.numbersOf W).sent l k := by
  rw [N_sent, h]

theorem N_keptOf (l : ℕ) : (N Zp cF).keptOf l = (P5T.numbersOf (pseats Zp)).keptOf l := rfl

theorem N_keptOf_of {W : List P5T.PSeat} (h : pseats Zp = W) (l : ℕ) :
    (N Zp cF).keptOf l = (P5T.numbersOf W).keptOf l := by
  rw [N_keptOf, h]

theorem N_group (l : ℕ) : (N Zp cF).group l = (P5T.numbersOf (pseats Zp)).group l := rfl

theorem N_group_of {W : List P5T.PSeat} (h : pseats Zp = W) (l : ℕ) :
    (N Zp cF).group l = (P5T.numbersOf W).group l := by
  rw [N_group, h]

theorem N_index : (N Zp cF).index = (P5T.numbersOf (pseats Zp)).index := rfl

theorem N_index_of {W : List P5T.PSeat} (h : pseats Zp = W) :
    (N Zp cF).index = (P5T.numbersOf W).index := by
  rw [N_index, h]

theorem N_inside : (N Zp cF).inside = (P5T.numbersOf (pseats Zp)).inside := rfl

theorem N_inside_of {W : List P5T.PSeat} (h : pseats Zp = W) :
    (N Zp cF).inside = (P5T.numbersOf W).inside := by
  rw [N_inside, h]

theorem N_w : (N Zp cF).w = (P5T.numbersOf (pseats Zp)).w := rfl

theorem N_w_of {W : List P5T.PSeat} (h : pseats Zp = W) :
    (N Zp cF).w = (P5T.numbersOf W).w := by
  rw [N_w, h]

end P5J.At

#print axioms P5J.At.N_sent_of
#print axioms P5J.At.N_keptOf_of
#print axioms P5J.At.N_group_of
#print axioms P5J.At.N_index_of
#print axioms P5J.At.N_inside_of
#print axioms P5J.At.N_w_of
