-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwTraceOf.lean.
What the last state of an assembled lookup's chain holds, as plain data: definitions.

Definitions alone, no proof. They stand in theorems alone (`rows16_eq`,
Cb/Pv/Lookup/Out/TwRows16.lean; `rows_eq`, OnBytes/Tie/Pv/Lookup/Out/TwRowsEq.lean; `state_eq`,
Cb/Pv/Lookup/Out/TwStateR.lean): no code is asked of them.

Main names:
  `tieSh`, `tieN D l`: the order of the shown values of a tie's step; the tie's steps below l, read
    down the nest (D.lv (l + 1)).T.St = (D.lv l).T.par.Out, the newest first.
  `lvN D l`: a tree's levels below l, each with its line's draw, read down the nest (D.lv (l +
    1)).T.St = (D.lv l).T.par.Out × E, the newest first.
  `traceOf A o`: the whole: a TwV.Trace E off the chain's last state o : A.XB.
  `tiePl`, `numsOf A st kAt`: the public numbers and places of A as a TwV.Nums A.J E. st: the
    caller's state, which A.tab reads. kAt: the reading of the keys (an entry or a constant).
Limits: two fields of the trace are read off free components of the state: kT is the first component
of A.X4, and join is the point in the table tree's root state. That on a run they are what their
names say is not stated here (it follows from `state_eq`, Cb/Pv/Lookup/Out/TwStateR.lean).
kAt is the caller's: nothing here ties it to A.key. The closing shows no value, so the field sh of
ledE is a filler; `TwV.rowsOfTrace` does not read it.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Asm.AsmH
import Cb.Pv.Lookup.Alg.TwGen

set_option autoImplicit false

namespace Tw3
open TwV Cb Cb.Tw Cb.LdLkp

noncomputable section
variable {E : Type} [Field E] [Fintype E]

/-- the order of the shown values of a tie's step, in the names of Cb/Pv/Lookup/Blocks/TieF.lean:
step 0: PK, Q_1, PT_0; step l + 1: Q_(l+2), PT_(l+1) -/
def tieSh (D : TieF E) : (l : ℕ) → List (D.lv l).T.par.A
  | 0 => [(none : Option Bool), some false, some true]
  | _ + 1 => [false, true]

def tieN (D : TieF E) : (l : ℕ) → (D.lv l).T.St → List (Sc E)
  | 0, _ => []
  | l + 1, o => scOf (D.lv l).T.par (tieSh D l) o :: tieN D l o.st

def lvN (D : TreeP E) : (l : ℕ) → (D.lv l).T.St → List (Sc E × E)
  | 0, _ => []
  | l + 1, s => (scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] s.1, s.2) :: lvN D l
      s.1.st

def traceOf (A : LkAsmH E) (o : A.XB) : Trace E where
  lam := (A.b2 (A.oR (A.o4 (A.oldT o)))).2
  tie := (tieN A.H.tie (A.n + 1) (A.oR (A.o4 (A.oldT o))).2).reverse
  join := List.ofFn (A.D.root A.d (A.outE o).st).2
  keys := (lvN (A.IK.setV (A.v' + 1)).DK (A.v' + 1) (A.oldT o).2).reverse
  kT := (A.oldT o).1
  tabl := (lvN A.D A.d (A.outE o).st).reverse
  cls := scMid A.En.par (A.outE o)
  zero := List.ofFn o.st.2.2
  bits := scOf A.Bt.zc.next.par [()] o

/-- the places of the masks of a tie's step's shown values, in tieSh's order -/
def tiePl (A : LkAsmH E) (l a : ℕ) : A.J :=
  if l = 0 then (if a = 0 then A.cZ else A.cAt 0 (decide (a ≠ 1))) else A.cAt l (decide (a ≠ 0))

def numsOf (A : LkAsmH E) (st : A.St) (kAt : ℕ → A.J ⊕ E) : Nums A.J E where
  v' := A.v'
  d := A.d
  w := A.w
  n := A.n
  tab := A.tab st
  pads := A.pads
  oK := fun l => List.ofFn fun j : Fin (0 + l) => ((A.oK l j : Fin (0 + l)) : ℕ)
  oT := fun l => List.ofFn fun j : Fin (A.w + l) => ((A.oT l j : Fin (A.w + l)) : ℕ)
  oE := List.ofFn fun j : Fin (A.w + A.d) => ((A.oE j : Fin (A.w + A.d)) : ℕ)
  oB := List.ofFn fun j : Fin (A.w + A.d) => ((A.oB j : Fin (A.w + A.d)) : ℕ)
  kAt := fun b => (kAt b).getLeft?
  kC := fun b => Sum.elim (fun _ => 0) id (kAt b)
  bAt := A.bAt
  ledTie := fun l => ledOf _ (A.wAt l) (tiePl A l)
  ledK := fun l => ledOf _ (A.wK l) fun a => A.cK l (decide (a ≠ 0))
  ledT := fun l => ledOf _ (A.wT l) fun a => A.cT l (decide (a ≠ 0))
  ledE := ledOf _ A.wE fun _ => A.cB
  ledB := ledOf _ A.wB fun _ => A.cB

end
end Tw3
