-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/BaseNums.lean: THE PIECES' BASES AS NUMBERS, AND «THE PINNED TREES LIE BELOW THE PIECES' BASES» AS A TEST ON NUMBERS ALONE: a light file, over the data's type alone (OnBytes/Maker/Whole.lean): so that THE VERY Bool can be evaluated in any build.
Main names.
  `treesOf ds`: the trees that rounds' data send. `baseN base ds rs n`: the base of the n-th piece, off the list rs of the blocks' numbers of declared rounds: each block but the last takes so many rounds off the front; the base grows by the trees that they send.
  `basesOkN at_ pin₁ pinS pinE pin₃ rs₁ rs₂ rs₃ D`: the test: pin₁ n: the messages whose pin is open at the first chain's border n · pinS | pinE | pin₃: those open at the first seam, behind the shared chain, at the last chain's border 1.
  `basesAllN at_ pin₁ pin₂ pin₃ rs₁ rs₂ rs₃ D`: the same at every border of the three chains.
  `seatsApartN at_ l`: no two of the listed messages have one seat: a consequence of the tables' tie `ArrOk` (`seatsApart_of_arrOk`, BasesOk.lean).
That this is `basesOk` | `basesAll` (BasesOk.lean) at a description's blocks and our tables' lists: `basesOk_eq` | `basesAll_eq`, there.
Nothing on soundness.

-/
import OnBytes.Maker.Whole

set_option autoImplicit false

namespace LPFD
open OnBytes.Maker

/-- The trees that rounds' data send. -/
def treesOf (ds : List RDT) : Nat := (ds.map (·.trees.length)).sum

/-- The n-th piece's base, off the blocks' numbers of declared rounds. -/
def baseN : Nat → List RDT → List Nat → Nat → Nat
  | base, _, [], _ => base
  | base, _, [_], _ => base
  | base, _, _ :: _ :: _, 0 => base
  | base, ds, r :: r' :: rs, n + 1 => baseN (base + treesOf (ds.take r)) (ds.drop r) (r' :: rs) n

/-- **The pinned trees lie below the pieces' bases: on numbers alone.** -/
def basesOkN (at_ : Nat → Nat × Nat) (pin₁ : Nat → List Nat) (pinS pinE pin₃ : List Nat) (rs₁ rs₂ rs₃ : List Nat) (D : WholeD) : Bool :=
  ((List.range rs₁.length).all fun n => (pin₁ n).all fun j => decide ((at_ j).1 < baseN 0 D.ds₁ rs₁ n)) &&
  (pinS.all fun j => decide ((at_ j).1 < baseN D.t₁ D.ds₂ rs₂ 0)) &&
  (pinE.all fun j => decide ((at_ j).1 < baseN D.t₁ D.ds₂ rs₂ 11)) &&
  (pin₃.all fun j => decide ((at_ j).1 < baseN (D.t₁ + D.t₂) D.ds₃ rs₃ 1))

/-- **The same at EVERY border of the three chains** (the first test, basesOkN, asks the shared chain's pins at two borders and the last chain's at one: the places where a law of ours lay: a ride showed that it is not tight at the messages that the shared chain sends). pinⱼ n: the messages whose pin is open at chain j's border n. -/
def basesAllN (at_ : Nat → Nat × Nat) (pin₁ pin₂ pin₃ : Nat → List Nat) (rs₁ rs₂ rs₃ : List Nat) (D : WholeD) : Bool :=
  ((List.range rs₁.length).all fun n => (pin₁ n).all fun j => decide ((at_ j).1 < baseN 0 D.ds₁ rs₁ n)) &&
  ((List.range rs₂.length).all fun n => (pin₂ n).all fun j => decide ((at_ j).1 < baseN D.t₁ D.ds₂ rs₂ n)) &&
  ((List.range rs₃.length).all fun n => (pin₃ n).all fun j => decide ((at_ j).1 < baseN (D.t₁ + D.t₂) D.ds₃ rs₃ n))

/-- **No two of the listed messages have one seat.** (It is what refuses a message's seat moved onto its neighbour's, where one block sends both trees and no test on bases can part them.) -/
def seatsApartN (at_ : Nat → Nat × Nat) (l : List Nat) : Bool := decide (l.map at_).Nodup

end LPFD
