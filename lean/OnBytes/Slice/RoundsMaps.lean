-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RoundsMaps.lean: one drawn element, and a list of drawn positions, as verifier
messages of the library.

OnBytes/Slice/CorePeel.lean and RoundsOf.lean read the typed values of a written round as n elements
(`gVec`), as a seed (`gSeed`), as two lists of positions (`gLoc`), as elements and positions
(`gMix`). This file adds the two readings that the rounds of the proximity test use most, and says
how each reading is made from what the decision reads of the round (`rvOf`,
OnBytes/Slice/Stage.lean).

Main definitions.
 `gOne`   the first drawn element.
 `gPos`   t drawn positions.
Main theorems.
 `gOne_inj`, `SendsDraws.gOne_inj`, `SendsDraws.gPos_inj`
          the typed values are determined by these readings, if nothing else is drawn.
 `gVec_rvOf`, `gOne_rvOf`, `gOne_of_els`, `SendsDraws.gPos_val`
          the readings, from the elements and the positions that the decision reads.

Not claimed. Nothing on how the values are distributed. `gPos` takes a drawn position modulo 2^a:
that it is the position itself holds for rounds whose positions have a bits
(`SendsDraws.gPos_val`).
-/
import OnBytes.Slice.RoundsOf

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The first drawn element; 0 if none is drawn. -/
def gOne (ds : List Fmt.Draw) (v : Vals .two ds) : GE := (elemsV ds v).getD 0 0

/-- The first t drawn positions, each taken modulo 2^a; 0 where none is drawn. -/
def gPos (a t : ℕ) (ds : List Fmt.Draw) (v : Vals .two ds) : Fin t → Fin (2 ^ a) :=
  (gLoc a t 0 ds v).1

/-- The first drawn element is the coordinate of the reading as one element. -/
theorem gOne_eq (ds : List Fmt.Draw) (v : Vals .two ds) : gOne ds v = gVec 1 ds v 0 := rfl

/-- The drawn positions are the second part of the reading as elements and positions. -/
theorem gPos_eq (n a t : ℕ) (ds : List Fmt.Draw) (v : Vals .two ds) :
    gPos a t ds v = (gMix n a t ds v).2 := rfl

/-- Typed values that consist of one element are determined by it. -/
theorem gOne_inj (ds : List Fmt.Draw) (hp : PlainDraws ds) (hE : nE ds = 1) (hP : nP ds = 0) :
    Function.Injective (gOne ds) := fun v w h =>
  gVec_inj 1 ds hp hE hP (funext fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h)

/-- At a round that draws one element and nothing else the typed values are determined by it. -/
theorem SendsDraws.gOne_inj {d : PQ.RD} {ns a : ℕ} (h : SendsDraws d ns 1 0 a) :
    Function.Injective (gOne (Fmt.dsOf d.entry d.kind)) :=
  OnBytes.Slice.gOne_inj _ h.plain h.els h.poss

/-- At a round that draws positions alone the typed values are determined by them. -/
theorem SendsDraws.gPos_inj {d : PQ.RD} {ns np a : ℕ} (h : SendsDraws d ns 0 np a) :
    Function.Injective (gPos a np (Fmt.dsOf d.entry d.kind)) := fun _ _ hvw =>
  h.gMix_inj (Prod.ext (funext fun i => i.elim0) hvw)

section
variable (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal)

/-- The reading as n elements is the list of elements that the decision reads, as a point. -/
theorem gVec_rvOf (n : ℕ) : gVec n _ (valsOf d c) = ptL n (rvOf d m c).els := by
  funext i
  show (elemsV _ (valsOf d c)).getD i.val 0 = toE ((rvOf d m c).els.getD i.val Fmt.Fld.zeroE)
  rw [← rvOf_els d m c, ← toE_zeroE, List.getD_map]

/-- The first drawn element is the first that the decision reads. -/
theorem gOne_rvOf : gOne _ (valsOf d c) = toE ((rvOf d m c).els.getD 0 Fmt.Fld.zeroE) :=
  congrFun (gVec_rvOf d m c 1) 0

/-- If the decision reads one drawn element, that is the first drawn element. -/
theorem gOne_of_els {x : Fmt.M1.E} (h : (rvOf d m c).els = [x]) : gOne _ (valsOf d c) = toE x := by
  rw [gOne_rvOf d m c, h]
  rfl

end

/-- The drawn positions are those that the decision reads. -/
theorem SendsDraws.gPos_val {d : PQ.RD} {ns ne np a : ℕ} (h : SendsDraws d ns ne np a)
    (m : (wRound d).Msg) (c : (wRound d).Chal) (i : Fin np) :
    (gPos a np _ (valsOf d c) i).val = (rvOf d m c).poss.getD i.val 0 := by
  show (possV _ (valsOf d c)).getD i.val 0 % 2 ^ a = _
  rw [Nat.mod_eq_of_lt (getD_lt a _ h.allPos _ _), rvOf_poss]

end OnBytes.Slice

#print axioms OnBytes.Slice.gOne_eq
#print axioms OnBytes.Slice.gPos_eq
#print axioms OnBytes.Slice.gOne_inj
#print axioms OnBytes.Slice.SendsDraws.gOne_inj
#print axioms OnBytes.Slice.SendsDraws.gPos_inj
#print axioms OnBytes.Slice.gVec_rvOf
#print axioms OnBytes.Slice.gOne_rvOf
#print axioms OnBytes.Slice.gOne_of_els
#print axioms OnBytes.Slice.SendsDraws.gPos_val
