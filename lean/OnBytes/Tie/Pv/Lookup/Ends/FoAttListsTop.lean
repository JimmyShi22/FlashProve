-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttListsTop.lean.
All claims that the check of the attention sub-proof adds before those of its smallness test, as one
written list.

`Attention.claims` (OnBytes/Model/Attention.lean) adds the rows of the lookup of the sub-proof's
calls, the claims 3, 4 and 5, the join, the claims 6, 7 and 8, and the lookup's three claims on the
planes.

Main names:
 * `attT P h K`: these claims, in this order, as a list of forms: a written function of the plan P,
   of the heard record h and of K, the number of columns of the array of tables. Its parts stand in
   OnBytes/Tie/Pv/Lookup/Ends/FoAttLists1.lean and OnBytes/Tie/Pv/Lookup/Ends/FoAttLists2.lean;
   `planeFormsT` in OnBytes/Tie/Pv/Lookup/Ends/FoRdPlanes.lean. `attJoinsT P h`: the joins behind
   claim 5, of which the join's form is made.
 * `ad_claims`: `Attention.claims P h` adds just `attT P h K`, in the sense of `Ad`
   (OnBytes/Tie/Pv/Lookup/Ends/FoRd.lean).
 * `att_walkT`: in plain words: every run of `Attention.claims P h` that returns, from a state F
   with one coefficient for each slot, ends in a state that comes from F by adding the forms of
   `attT P h (colsOf F h.iU3)` one after the other (`Adds`, OnBytes/Tie/Pv/Led/LedAdds.lean).

What is lost against the routines: the values and the lists here are total. They do not say where a
routine refuses: `xlT` is the empty form where `xl` refuses, and `unitKFDT` is empty where `unitKFD`
does. Off a run that returns, a list means nothing. Nothing says that a routine returns. The lists
are tied to a run by `Adds` (OnBytes/Tie/Pv/Led/LedAdds.lean): the forms are added one after the
other, in the list's order; `Added` (OnBytes/Tie/Pv/Lookup/Ends/FoAdded.lean) is not concluded here.

The heard record h holds what the check has drawn and heard up to the tables, so `attT` is no
function of the public files alone.

OnBytes/Tie/Pv/Lookup/Ends/FoBaseD.lean has the same claims as three terms `attA`, `attB`, `attC`
that are not written out. That `attT` is their list is not shown.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed what the forms are worth.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttLists2
import OnBytes.Tie.Pv.Lookup.Ends.FoRdPlanes

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

variable {t K : ℕ}

/-- `allJoined` is a test: if it returns, it leaves the state. -/
theorem rd_allJoined (j : Joins) : Rd t K (allJoined j) () := Rd.unit _

/-- `Attention.paddingLaid` is two tests: if it returns, it leaves the state. -/
theorem rd_paddingLaidA (S : Shape) (g : Forest.Heard) : Rd t K (Attention.paddingLaid S g) () := by
  unfold Attention.paddingLaid
  refine Rd.bind (Rd.unit _) ?_
  cases laidPadding S g.shape with
  | error e => exact Rd.never (refuse_never _) _
  | ok laid => exact Rd.unit _

/-- The joins behind claim 5. -/
def attJoinsT (P : Plan) (h : Attention.Heard) : Joins :=
  claim5V h (claim4V h (claim3V h (Joins.empty P.NC)))

/-- **The claims that Attention.claims adds, written out.** K: the number of columns of the array of
tables. -/
def attT (P : Plan) (h : Attention.Heard) (K : ℕ) : List Aff :=
  h.g.rows.toList ++ (claim3T h K ++ (claim4T h K ++ (claim5T h K ++
    ([joinForm h.g (attJoinsT P h).kf] ++ (claim6T h K ++ (claim7T h K ++ (claim8T h K ++
      (planeFormsT h.g h.S.cf.lmb
        (fun e col => u3Form h.iU3 K ((if e == 0 then h.t.tBit0 else h.t.tBit1) + col))
        (fun col => u3Form h.iU3 K (h.t.tPin + col))).toList)))))))

/-- **`Attention.claims`, if it returns, has added the written list.** -/
theorem ad_claims (P : Plan) (h : Attention.Heard) (K : ℕ) :
    Ad h.iU3 K (Attention.claims P h) (attT P h K) := by
  unfold Attention.claims attT attJoinsT
  refine Ad.seq (ad_objects h.g) ?_
  refine Ad.bindV (adV_claim3 h _) ?_
  refine Ad.bindV (adV_claim4 h _) ?_
  refine Ad.bindV (adV_claim5 h _) ?_
  refine Ad.after (rd_allJoined _) ?_
  refine Ad.after (rd_paddingLaidA h.S h.g) ?_
  refine Ad.bindV (l₁ := []) (adV_join h.g _) ?_
  refine Ad.seq (Ad.lin _) ?_
  refine Ad.seq (ad_claim6 h) (Ad.seq (ad_claim7 h) (Ad.seq (ad_claim8 h) ?_))
  exact ad_planeLins h.g h.S.cf.lmb (fun e col => rd_u3at h _ col) (fun col => rd_u3at h _ col)

/-- **Every run of Attention.claims that returns has added just the written list**, one form after
the other, at the first state's number of columns. -/
theorem att_walkT (P : Plan) (h : Attention.Heard) {F G : Fork} {c c' : Ctx}
    (hr : Attention.claims P h F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) :
    OnBytes.Road.Rows.Adds F (attT P h (colsOf F h.iU3)) G ∧
      colsOf G h.iU3 = colsOf F h.iU3 ∧ G.LS.size = G.ns :=
  Ad.run (ad_claims P h) hr hs

end Fo
