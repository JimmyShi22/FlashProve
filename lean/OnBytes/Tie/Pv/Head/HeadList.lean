-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Head/HeadList.lean: lists of rounds, written here after the typed blocks of
Cb/Pv/Head/, fit the entries that the planner adds for the output head's own rounds; for the merge,
the block's own rounds.

The head's sub-proof has, behind its lookup: a point; the sums of limb products and a batching
element; a sumcheck and the point of a line; the row products and a batching element; three token
sumchecks. Behind its smallness test: a batching element and the merge's sumcheck; then the last
batching element. The typed blocks for these lie in Cb/Pv/Head/. Here only their rounds are read.

Definitions. ownShape, endShape: the rounds, as lists, for any parameters of the five sumchecks.
Statements.
  own_fits   the rounds ownShape fit, one by one and in order (Fits,
             OnBytes/Tie/Pv/Head/Fits.lean), the entries headOwnList w x
             (OnBytes/Tie/Pv/Head/PlanList.lean), for every record x of the head's numbers and
             every work w.
  end_fits   the rounds endShape fit the entries headEndList w x.
  merge_fits the rounds of the merge's block (Cb/Pv/Head/Merge.lean) fit the entries
             hBatWeights w ++ hMerge w x.
By headOwn_adds and headEnd_adds these entries are just what the planner's own routines add.

Under: for each sumcheck, that its variables are the stated number of cube variables of degree 2
and the further variable of the stated degree, and the number of its end values.

Not claimed: what Fits does not read (an entry's name, work, rows, logN); anything that a plan does
not know. own_fits and end_fits speak of the lists ownShape and endShape, which are typed in this
file over free parameters. That the rounds of the row's block (rowR, Cb/Pv/Head/HeadRow.lean) are
ownShape at the blocks' parameters is not proved in this file.

-/
import OnBytes.Tie.Pv.Head.Fits
import OnBytes.Tie.Pv.Head.PlanList
import Cb.Pv.Head.Merge
import Cb.Pv.Head.Batch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Head
open Iop Prob Cb Johnson.L5.Layers Cb.Pv.Head.Bat

variable {E : Type} [Field E] [Fintype E]

/-- The rounds behind the lookup. -/
def ownShape (x : OnBytes.Params.HeadRounds) (Sq V N H : PscPar E) : Shape :=
  [IOR.drawRound (Fin x.lt → E)] ++ [batRound E x.sums] ++ (shapeS Sq ++ [IOR.drawRound E]) ++
    [batRound E x.products] ++ shapeR V ++ shapeR N ++ shapeR H

/-- The rounds behind the smallness test. -/
def endShape (Mg : PscPar E) : Shape := [IOR.drawRound E] ++ shapeS Mg ++ [IOR.drawRound E]

omit [Fintype E] in
theorem one_fits {r : Round} {e : Fmt.Entry} (h : Fits E r e) : List.Forall₂ (Fits E) [r] [e] :=
  List.Forall₂.cons h List.Forall₂.nil

theorem own_fits (w : ℕ) (x : OnBytes.Params.HeadRounds) (Sq V N H : PscPar E)
    (hSq : Sq.fmt = ldPartFmt E (x.lPd + x.lt) (fun _ => 2) ++ [pDummy E 2])
    (cSq : Fintype.card Sq.A = 2)
    (hV : V.fmt = ldPartFmt E x.lt (fun _ => 2) ++ [pDummy E 2])
    (cV : Fintype.card V.A = x.rowValues)
    (hN : N.fmt = ldPartFmt E x.lt (fun _ => 2) ++ [pDummy E 2]) (cN : Fintype.card N.A = 2)
    (hH : H.fmt = ldPartFmt E (x.lt + x.lPd) (fun _ => 2) ++ [pDummy E 2])
    (cH : Fintype.card H.A = 2) :
    List.Forall₂ (Fits E) (ownShape x Sq V N H) (headOwnList w x) :=
  List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append
    (List.rel_append (one_fits (fits_point "ZERO" w x.lt))
      (one_fits (fits_scalars (batRound E x.sums) w x.sums x.sums rfl rfl
        (inferInstanceAs (IsEmpty Empty)))))
    (List.rel_append (fits_psc Sq w (x.lPd + x.lt) 2 2 hSq cSq) (one_fits (fits_draw "LINE" w))))
    (one_fits (fits_scalars (batRound E x.products) w x.products x.products rfl rfl
      (inferInstanceAs (IsEmpty Empty)))))
    (fits_pscRide V w x.lt 2 x.rowValues hV cV)) (fits_pscRide N w x.lt 2 2 hN cN))
    (fits_pscRide H w (x.lt + x.lPd) 2 2 hH cH)

theorem end_fits (w : ℕ) (x : OnBytes.Params.HeadRounds) (Mg : PscPar E)
    (hM : Mg.fmt = ldPartFmt E x.lkW (fun _ => 2) ++ [pDummy E 1]) (cM : Fintype.card Mg.A = 1) :
    List.Forall₂ (Fits E) (endShape Mg) (headEndList w x) :=
  List.rel_append (List.rel_append (one_fits (fits_bat w 1)) (fits_psc Mg w x.lkW 1 1 hM cM))
    (one_fits (fits_bat w x.rows))

section
open Cb.Pv.Head.Merge
variable {St J M Wp Kc : Type} [Fintype J] {Ex : ExtSpec}

theorem merge_fits (w : ℕ) (x : OnBytes.Params.HeadRounds)
    (a : MergeAt E St J M Wp Kc Ex x.lkW) :
    List.Forall₂ (Fits E) a.R.shape (hBatWeights w ++ hMerge w x) :=
  List.Forall₂.cons (fits_bat w 1) (fits_psc a.Y w x.lkW 1 1 rfl Fintype.card_unit)

end

end OnBytes.Tie.Pv.Head

#print axioms OnBytes.Tie.Pv.Head.own_fits
#print axioms OnBytes.Tie.Pv.Head.end_fits
#print axioms OnBytes.Tie.Pv.Head.merge_fits
