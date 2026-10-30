-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/SumShown.lean: WHAT THE MASKED SUMCHECK's PART SHOWS, AS
VALUES: where the call passes `shapeFair` (ShapeFair.lean) and the challenges are as many as the
part has moves, the items of `sumOut`'s rounds (Out.lean of this folder) are, message by message,
`msgsK` (SumMap.lean) at the coins' readings, each value laid as its three words below the prime.
Definitions that the statements need, and statements with their proofs.
Main names:
  `gotsOf`, `rvSaid_vals`: values as a view shows them; a round in which scalars were said.
  `zip_wOf`, `varOut_vals`: the variables' rounds.
  `endList`, `endsN`, `sumMsgs`, `uOf`, `mOf`: the letters of `msgsK` at a job, a front and
    challenges; the two stretches of coins, read, by number.
  `firstRun_count`, `endRun_count`: both stretches, laid as lists, have their counts by the coins'
    type: so `uOf` and `mOf` meet no default below these. (That the part's own cutting and filling
    of these lists fills nothing is stated by no lemma of its own. What is stated, each without a
    premise: the first stretch has `ownRun` members; that is the lead's count and one for each slot
    of the sumcheck's own (`ownRun_eq`, Counts.lean); the call's variables have as many slots as the
    shape's (`slots_all`, SumBij.lean); the second stretch has as many members as there are end
    values.)
  `first_read`, `ends_read`, `sumOut_vals`: the first and the last message; **all rounds.**

Limits. The call passes `shapeFair` (ShapeFair.lean), and the challenges are as many as the part has
moves: premises. THE JOB's OWN LISTS STAND HERE AS THE PART CUTS OR FILLS THEM (FitsAt.lean): in
`sumMsgs` the lead's values and the end values are cut or filled with 0 to the shape's counts; the
job's points are taken as the part takes them (`withPoints`, Honest/Sum.lean: points beyond the
shape's are dropped; where none is left the shape's own stands); a coefficient that the job's
polynomial lacks counts as 0; one from the variable's number of coefficients on is never read, nor
is the one that is left out of the message (number 1 at a plain sum, 0 at a point: `sentIdx`,
SumMap.lean). No distribution occurs. No property of a protocol is stated.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.SumMapReads
import Johnson.Desc.ProofFile.Honest.SumLaw.Counts
import Johnson.Desc.ProofFile.Honest.SumLaw.ShapeFair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Slice (GE ofE toE)
open VerifiableInference.Desc.Part.MaskedSum

variable {W X : Type}

/-- Values as a view shows them: each as its three words below the prime. -/
def gotsOf (l : List GE) : List Fmt.ItemValue := l.map fun g => .e (ofE g)

/-- The items of a round in which scalars were said. -/
theorem rvSaid_vals (l : List E) (d : Fmt.Drawn) :
    (rvSaid l d).vals = gotsOf (l.map Reading.gl.val) := by
  unfold rvSaid sayE gotsOf
  simp only [List.map_map]
  rfl

/-- The first variable's share apart. -/
theorem zip_wOf (v : Var) (vs : List Var) (U : List E) :
    ∃ w, (v :: vs).zip (wOf (v :: vs) U) = (v, w) :: vs.zip (wOf vs (U.drop (v.d - 1))) := by
  cases vs with
  | nil => exact ⟨padTo v.d U, rfl⟩
  | cons v' vs => exact ⟨zeroE :: padTo (v.d - 1) U, rfl⟩

/-- **The variables' rounds, as values.** f: the coins' readings by number, from i on. -/
theorem varOut_vals (eps : E) (poly : List E → List E) : ∀ (vs : List Var) (U : List E)
    (f : Nat → GE) (i : Nat) (a : E) (past : List E) (ds : List Fmt.Drawn),
    (∀ v ∈ vs, 2 ≤ v.d) →
    (∀ j, j < slots (vs.map (toK Reading.gl)) → Reading.gl.val (U.getD j zeroE) = f (i + j)) →
    vs.length = ds.length →
    (varOut eps poly (vs.zip (wOf vs U)) a past ds).map (·.vals) =
      (outK (fun p t => Reading.gl.val ((poly p).getD t zeroE)) (Reading.gl.val eps)
        (vs.map (toK Reading.gl)) f i past (ds.map elemOf)).map gotsOf
  | [], _, _, _, _, _, [], _, _, _ => by
    rw [varOut_nil]
    rfl
  | v :: vs, U, f, i, a, past, d :: ds, h2, h, hl => by
    obtain ⟨w, hw⟩ := zip_wOf v vs U
    have hs := slots_cons (toK Reading.gl v) (vs.map (toK Reading.gl))
    rw [toK_snd] at hs
    have ih := varOut_vals eps poly vs (U.drop (v.d - 1)) f (i + (v.d - 1))
      (addE (mulE a (psiAt v (elemOf d))) (valueAt w (elemOf d))) (past ++ [elemOf d]) ds
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
      (fun j hj => by
        rw [getD_drop, h (v.d - 1 + j) (by rw [List.map_cons, hs]; omega)]
        congr 1
        omega)
      (by simp only [List.length_cons] at hl; omega)
    rw [hw, varOut_cons, List.map_cons, ih, ← hw, rvSaid_vals,
      round_read Reading.gl v vs U f i a eps (poly past) h2 h]
    show _ = gotsOf (cutK (toK Reading.gl v) _) ::
      (outK _ _ (vs.map (toK Reading.gl)) f (i + ((toK Reading.gl v).2 - 1)) (past ++ [elemOf d])
        (ds.map elemOf)).map gotsOf
    rw [toK_snd]
  | [], _, _, _, _, _, _ :: _, _, _, hl => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | _ :: _, _, _, _, _, _, [], _, _, hl => by
    simp only [List.length_cons, List.length_nil] at hl
    omega

/-! ## All rounds -/

/-- Values by number, laid as the program's elements: as `coinsE` lays coins. -/
def endList (m : Nat → GE) (n : Nat) : List E := (List.range n).map fun j => E.ofTriple (ofE (m j))

/-- How many end values a shape has; 0 without ends. -/
def endsN (k : Call) : Nat := (k.ends.map (·.n)).getD 0

/-- **The letters of `msgsK` at a job, an input, a front and challenges.** eps: the first challenge.
rs: those of all variables, Y's last. beta: the factor of the end values' mask entries. -/
def sumMsgs (J : SumJob W X) (w : W) (fr : Front X) (eps : E) (rs : List E) (beta : E)
    (u m : Nat → GE) : List (List GE) :=
  msgsK J.shape.lead
    (fun i => Reading.gl.val ((padTo J.shape.lead (J.lead w fr)).getD i zeroE))
    ((J.callAt w fr).all.map (toK Reading.gl))
    (fun m p t => Reading.gl.val ((jobPoly J w fr (endList m (endsN J.shape)) p).getD t zeroE))
    (Reading.gl.val eps) rs
    (J.shape.ends.map fun e =>
      (e.n, fun j => Reading.gl.val
        ((padTo e.n (J.ends w fr (rs.take J.shape.vs.length))).getD j zeroE), Reading.gl.val beta))
    u m

/-- The first stretch, read, by number. -/
def uOf {name endName : String} {J : SumJob W X} (c : SumCoins name endName J) : Nat → GE :=
  fun j => Reading.gl.val ((firstRun c).getD j zeroE)

/-- The second stretch, read, by number. -/
def mOf {name endName : String} {J : SumJob W X} (c : SumCoins name endName J) : Nat → GE :=
  fun j => Reading.gl.val ((endRun c).getD j zeroE)

/-- Coins laid as the program's elements are the list of their readings, laid. -/
theorem coinsE_endList {d : Due} (c : Cs d) :
    coinsE c = endList (fun j => Reading.gl.val ((coinsE c).getD j zeroE)) d.e := by
  unfold endList
  refine List.ext_getElem ?_ ?_
  · unfold coinsE
    rw [List.length_ofFn, List.length_map, List.length_range]
  · intro i h1 _
    have hi : i < d.e := by
      unfold coinsE at h1
      rwa [List.length_ofFn] at h1
    rw [List.getElem_map, List.getElem_range]
    show (coinsE c)[i] = E.ofTriple (ofE (Reading.gl.val ((coinsE c).getD i zeroE)))
    rw [coinsE_getD c i hi]
    unfold coinsE
    rw [List.getElem_ofFn]

/-- The like for the end values' coins. -/
theorem endCoins_endList (endName : String) : ∀ (o : Option Ends) (cs : CsAll (endRuns endName o)),
    endCoins endName o cs =
      endList (fun j => Reading.gl.val ((endCoins endName o cs).getD j zeroE))
        ((o.map (·.n)).getD 0)
  | none, _ => rfl
  | some _, cs => coinsE_endList cs.1

/-- The second stretch is the list of its readings, laid. -/
theorem endRun_endList {name endName : String} {J : SumJob W X} (c : SumCoins name endName J) :
    endRun c = endList (mOf c) (endsN J.shape) :=
  endCoins_endList endName J.shape.ends c.2.1.2

/-- **The first stretch, laid as the program's elements, has as many members as the part's first
block has coins** (`ownRun` of the shape; at a shape with end values the part is lent a second block
besides): so `uOf` reads a coin, and no default, at every number below that count. -/
theorem firstRun_count {name endName : String} {J : SumJob W X} (c : SumCoins name endName J) :
    (firstRun c).length = ownRun J.shape := by
  unfold firstRun coinsE
  rw [List.length_ofFn]

/-- **The like for the second stretch**: `mOf` reads a coin at every number below the number of end
values. -/
theorem endRun_count {name endName : String} {J : SumJob W X} (c : SumCoins name endName J) :
    (endRun c).length = endsN J.shape := by
  rw [endRun_endList c]
  unfold endList
  rw [List.length_map, List.length_range]

/-- The first message, read. -/
theorem first_read {name endName : String} (J : SumJob W X) (c : SumCoins name endName J) (w : W)
    (fr : Front X) (h2 : ∀ v ∈ (J.callAt w fr).all, 2 ≤ v.d) :
    (addL (padTo J.shape.lead (J.lead w fr)) ((firstRun c).take J.shape.lead) ++
        [tailSum (sharesOf J.shape.lead (J.callAt w fr).all (firstRun c))]).map Reading.gl.val =
      (List.range J.shape.lead).map (fun i =>
          Reading.gl.val ((padTo J.shape.lead (J.lead w fr)).getD i zeroE) + uOf c i) ++
        [tailK ((J.callAt w fr).all.map (toK Reading.gl)) (uOf c) J.shape.lead] := by
  rw [List.map_append, map_read, lead_length]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [addL_getD]
    congr 2
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi']
  · show [Reading.gl.val (tailSum ((J.callAt w fr).all.zip
      (wOf (J.callAt w fr).all ((firstRun c).drop J.shape.lead))))] = _
    rw [tail_read Reading.gl (J.callAt w fr).all ((firstRun c).drop J.shape.lead) (uOf c)
      J.shape.lead h2 fun j _ => by rw [getD_drop]; rfl]

/-- The end values' message, read. -/
theorem ends_read (n : Nat) (A m : List E) (beta : E) :
    (addL (padTo n A) (scaleL beta (padTo n m))).map Reading.gl.val =
      (List.range n).map fun j => Reading.gl.val ((padTo n A).getD j zeroE) +
        Reading.gl.val beta * Reading.gl.val (m.getD j zeroE) := by
  have hl : (addL (padTo n A) (scaleL beta (padTo n m))).length = n := by
    rw [addL_length, padTo_length]
    show max n ((padTo n m).map _).length = n
    rw [List.length_map, padTo_length, Nat.max_self]
  rw [map_read, hl]
  refine List.map_congr_left fun j hj => ?_
  rw [addL_getD, scaleL_getD, padTo_getD n m, if_pos (List.mem_range.1 hj)]

/-- **All rounds of the part, as values.** dv: the variables' challenges, Y's last. dl: the last
round's challenge, where the shape has ends. -/
theorem sumOut_vals {name endName : String} (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn)
    (hs : shapeFair (J.callAt t.input (frontOf t seen)) = true)
    (hv : dv.length = (J.callAt t.input (frontOf t seen)).all.length)
    (hl : dl.length = if J.shape.ends.isSome then 1 else 0) :
    (sumOut J c t seen (d0 :: (dv ++ dl))).map (·.vals) =
      (sumMsgs J t.input (frontOf t seen) (elemOf d0) (dv.map elemOf)
        ((drawnE (d0 :: dv)).getLastD zeroE) (uOf c) (mOf c)).map gotsOf := by
  have htake : (dv ++ dl).take (J.callAt t.input (frontOf t seen)).all.length = dv := by
    rw [← hv, List.take_left]
  have hdrop : (dv ++ dl).drop (J.callAt t.input (frontOf t seen)).all.length = dl := by
    rw [← hv, List.drop_left]
  have h2 := fair_all_two hs
  have hvars := varOut_vals (elemOf d0) (jobPoly J t.input (frontOf t seen) (endRun c))
    (J.callAt t.input (frontOf t seen)).all ((firstRun c).drop J.shape.lead) (uOf c) J.shape.lead
    zeroE [] dv h2 (fun j _ => by rw [getD_drop]; rfl) hv.symm
  simp only [sumOut]
  rw [htake, hdrop, saidFirst_eq, List.map_cons, List.map_append, rvSaid_vals,
    first_read J c t.input (frontOf t seen) h2]
  have hsh : sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c) =
      (J.callAt t.input (frontOf t seen)).all.zip
        (wOf (J.callAt t.input (frontOf t seen)).all ((firstRun c).drop J.shape.lead)) := rfl
  rw [hsh, hvars]
  unfold sumMsgs msgsK
  beta_reduce
  rw [List.map_cons, List.map_append, ← endRun_endList c]
  congr 2
  cases he : J.shape.ends with
  | none => rfl
  | some e =>
    rw [he] at hl
    match dl, hl with
    | [d], _ =>
      show [(rvSaid (saidEnds J e _ _ _ _ _ _) d).vals] = [gotsOf _]
      rw [rvSaid_vals]
      show [gotsOf ((addL (padTo e.n _) (scaleL _ (padTo e.n (endRun c)))).map _)] = _
      rw [ends_read]
      rfl

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.rvSaid_vals
#print axioms ProofFile.Honest.SumLaw.zip_wOf
#print axioms ProofFile.Honest.SumLaw.varOut_vals
#print axioms ProofFile.Honest.SumLaw.coinsE_endList
#print axioms ProofFile.Honest.SumLaw.endCoins_endList
#print axioms ProofFile.Honest.SumLaw.endRun_endList
#print axioms ProofFile.Honest.SumLaw.firstRun_count
#print axioms ProofFile.Honest.SumLaw.endRun_count
#print axioms ProofFile.Honest.SumLaw.first_read
#print axioms ProofFile.Honest.SumLaw.ends_read
#print axioms ProofFile.Honest.SumLaw.sumOut_vals
#print axioms ProofFile.Honest.SumLaw.gotsOf
#print axioms ProofFile.Honest.SumLaw.endList
#print axioms ProofFile.Honest.SumLaw.endsN
#print axioms ProofFile.Honest.SumLaw.sumMsgs
#print axioms ProofFile.Honest.SumLaw.uOf
#print axioms ProofFile.Honest.SumLaw.mOf
