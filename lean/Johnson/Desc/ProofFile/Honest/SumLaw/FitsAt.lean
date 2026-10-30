-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/FitsAt.lean: THE FRAME's NAMED TESTS ON A CALLER's LISTS
(`SumJob.fitsAt`, `challengesFit`, Honest/SumFits.lean) BESIDE THE SEVEN STATEMENTS OF THIS FOLDER.
Definitions that the statements need, and statements with their proofs.

Why. The masked sumcheck's part never rejects: a list of the caller's that is too short is filled
with 0, one that is too long is cut. The seven statements (Statement.lean) bind the job freely and
speak of the lists as the part fills or cuts them: they hold at lists that do not fit too, and none
of them takes the test as a premise. The test serves a caller of the seven: under it what they say
of filled and cut lists is said of the caller's own lists.
Main names:
  `fitsAt_iff`: the test, clause by clause.
  `varsOf_length`, `vars_take_length`, `endRun_length`, `fitsAt_of_parts`: two clauses are paid by
    what the seven take already (the challenges fit the call; the coins' type); what is left for a
    caller to show. `shapeOk_callAt`, `fitsShapeAt_of_parts`: the library's test on the shape is the
    same at the shape and at the call in a run; so the like for `SumJob.fitsShapeAt`.
  `pointsOf`, `withPoints_points`, `callAt_points`: under the test every point of the job stands in
    the call, in order, and no placeholder of the shape's is left.
  `lead_member`, `ends_member`: under the test the values that `SumFirst`, `SumLast` and `SumEnds`
    read by number are members of the job's lists.
  `polyOf_noneCut`, `rawMoves`, `polyMoves_raw`, `sumsTo_unpadded`: where nothing but zeros is cut,
    a list as the part fills or cuts it is the polynomial of the list itself; so, WHERE EVERY
    VARIABLE HAS AT LEAST ONE COEFFICIENT AND THE CHALLENGES ARE AS MANY AS THE VARIABLES, `SumsTo`
    is the library's `Chain` at the polynomials of the lists as they are. `natDegree_noneCut`: the
    clause on the degree in `Chain` is given by the test.
  `fits_noneCut`, `sumsTo_job`: **the same at a job that passes the test**, under the same two
    premises: the first is not given by `fitsAt`; it follows from `shapeOk` (`all_two`, Reads.lean);
    the second is `varsOf_length` at the challenges at which the seven ask `SumsTo`.
  `challengesFit_of_drawsOk`: challenges that fit the call (`drawsOk`, Terms.lean) pass
    `challengesFit`.

Limits. IT IS NOWHERE A TEST ON PUBLIC DATA ALONE: every function of the job reads the prover's
input (Honest/SumFits.lean's own Limits say so). The test is at one input, one front, one list of
challenges AND, AT A CALL WITH END VALUES, ONE LIST OF COINS: its clause on Y reads the job's
polynomial in Y at the second stretch's members. A caller that carries it as a premise into a
statement over a distribution of coins has to have it at all inputs, fronts, challenges and coins of
which that statement speaks, or its premise picks among them.
`sumsTo_unpadded` serves callers of `Chain` alone: nothing is typed on `sumOf` or `valueAt` at a
list that is not filled or cut. `noneCut` compares with the program's zero: a member that reads as 0
and is not that element counts as cut. `fitsAt` passes at a call without a variable and without
ends: the library's `shapeOk` tests that (`SumJob.fitsShapeAt` has both). Nothing on any
distribution. No property of a protocol is stated.
-/
import Johnson.Desc.ProofFile.Honest.SumFits
import Johnson.Desc.ProofFile.Honest.SumLaw.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum
open OnBytes.Desc.First.P1 (Chain)
open Polynomial

variable {W X : Type}

/-! ## 1 The test, clause by clause -/

/-- A test at every member of a list with its number. -/
theorem all_zipIdx {α : Type} (f : α × Nat → Bool) : ∀ (l : List α) (n : Nat),
    (l.zipIdx n).all f = true ↔ ∀ i (h : i < l.length), f (l[i], n + i) = true
  | [], _ => by simp
  | x :: l, n => by
    rw [List.zipIdx_cons, List.all_cons, Bool.and_eq_true, all_zipIdx f l (n + 1)]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0
      | succ j =>
        have := h1 j (by simp only [List.length_cons] at hi; omega)
        rw [show n + 1 + j = n + (j + 1) by omega] at this
        exact this
    · intro h
      refine ⟨h 0 (by simp only [List.length_cons]; omega), fun i hi => ?_⟩
      have := h (i + 1) (by simp only [List.length_cons]; omega)
      rw [show n + (i + 1) = n + 1 + i by omega] at this
      exact this

/-- **The test, clause by clause.** -/
theorem fitsAt_iff (J : SumJob W X) (w : W) (fr : Front X) (rs m : List E) :
    J.fitsAt w fr rs m = true ↔
      (J.points w fr).length = pointsIn J.shape.vs ∧ (J.lead w fr).length = J.shape.lead ∧
        rs.length = J.shape.vs.length ∧
        (∀ i (h : i < J.shape.vs.length),
          noneCut J.shape.vs[i].d (J.round w fr (rs.take i)) = true) ∧
        ∀ e, J.shape.ends = some e → noneCut (e.dY + 1) (J.inY w fr rs m) = true ∧
          (J.ends w fr rs).length = e.n ∧ m.length = e.n := by
  unfold SumJob.fitsAt
  cases he : J.shape.ends with
  | none =>
    simp only [he, Bool.and_eq_true, beq_iff_eq, all_zipIdx, Nat.zero_add, and_true, reduceCtorEq,
      false_imp_iff, implies_true, and_assoc]
  | some e =>
    simp only [he, Bool.and_eq_true, beq_iff_eq, all_zipIdx, Nat.zero_add, Option.some.injEq,
      forall_eq', and_assoc]

/-! ## 2 Two clauses are paid already -/

/-- Challenges that fit a call are as many as its entries. -/
theorem drawsOk_length (k : Call) (ds : List Fmt.Drawn) (h : drawsOk k ds = true) :
    ds.length = (entries k).length := by
  have := congrArg List.length (beq_iff_eq.1 h)
  rwa [List.length_map, List.length_map] at this

/-- How many variables the call in a run has, Y among them. -/
theorem all_length (J : SumJob W X) (w : W) (fr : Front X) :
    (J.callAt w fr).all.length =
      J.shape.vs.length + (match J.shape.ends with
        | none => 0
        | some _ => 1) := by
  cases he : J.shape.ends with
  | none => rw [all_none J w fr he, withPoints_length]; rfl
  | some e => rw [all_some J w fr e he, List.length_append, withPoints_length]; rfl

/-- **Where the challenges fit the call, the variables' challenges are as many as the shape's
variables.** -/
theorem vars_take_length (J : SumJob W X) (w : W) (fr : Front X) (ds : List Fmt.Drawn)
    (h : drawsOk (J.callAt w fr) ds = true) :
    ((varsOf (J.callAt w fr) ds).take J.shape.vs.length).length = J.shape.vs.length := by
  have h1 := drawsOk_length _ ds h
  rw [entries_count] at h1
  have h2 : (J.callAt w fr).vs.length = J.shape.vs.length := withPoints_length _ _
  have h3 := all_length J w fr
  have h4 : (ownOf ds).length = ds.length := List.length_map _
  have h5 : (J.callAt w fr).ends = J.shape.ends := rfl
  unfold varsOf
  rw [List.length_take, List.length_take, List.length_drop, h4, h1, h2, h3, h5]
  cases J.shape.ends <;> simp only <;> omega

/-- How many variables a call has, Y among them. -/
theorem call_all_length (k : Call) :
    k.all.length = k.vs.length + (match k.ends with
      | none => 0
      | some _ => 1) := by
  unfold Call.all
  cases k.ends with
  | none => rfl
  | some e => exact List.length_append

/-- **Where the challenges fit a call, `varsOf` has one challenge for each variable, Y among them.**
-/
theorem varsOf_length (k : Call) (ds : List Fmt.Drawn) (h : drawsOk k ds = true) :
    (varsOf k ds).length = k.all.length := by
  have h1 := drawsOk_length k ds h
  rw [entries_count] at h1
  have h3 := call_all_length k
  have h4 : (ownOf ds).length = ds.length := List.length_map _
  unfold varsOf
  rw [List.length_take, List.length_drop, h4, h1, h3]
  cases k.ends <;> simp only <;> omega

/-- The end values' coins are as many as the end values. -/
theorem endCoins_length (endName : String) : ∀ (o : Option Ends) (e : Ends), o = some e →
    ∀ cs : CsAll (endRuns endName o), (endCoins endName o cs).length = e.n
  | _, e, rfl, cs => by
    show (coinsE cs.1).length = e.n
    unfold coinsE
    rw [List.length_ofFn]

/-- **The second stretch has as many members as there are end values**: by the coins' type. -/
theorem endRun_length {name endName : String} {J : SumJob W X} (c : SumCoins name endName J)
    (e : Ends) (he : J.shape.ends = some e) : (endRun c).length = e.n :=
  endCoins_length endName J.shape.ends e he c.2.1.2

/-- **What is left for a caller to show**, at the challenges and the coins of a run of the part. -/
theorem fitsAt_of_parts {name endName : String} (J : SumJob W X) (c : SumCoins name endName J)
    (w : W) (fr : Front X) (ds : List Fmt.Drawn) (hd : drawsOk (J.callAt w fr) ds = true)
    (hp : (J.points w fr).length = pointsIn J.shape.vs)
    (hl : (J.lead w fr).length = J.shape.lead)
    (hr : ∀ i (h : i < J.shape.vs.length), noneCut J.shape.vs[i].d
      (J.round w fr (((varsOf (J.callAt w fr) ds).take J.shape.vs.length).take i)) = true)
    (he : ∀ e, J.shape.ends = some e →
      noneCut (e.dY + 1)
          (J.inY w fr ((varsOf (J.callAt w fr) ds).take J.shape.vs.length) (endRun c)) = true ∧
        (J.ends w fr ((varsOf (J.callAt w fr) ds).take J.shape.vs.length)).length = e.n) :
    J.fitsAt w fr ((varsOf (J.callAt w fr) ds).take J.shape.vs.length) (endRun c) = true :=
  (fitsAt_iff J w fr _ _).2 ⟨hp, hl, vars_take_length J w fr ds hd, hr,
    fun e h => ⟨(he e h).1, (he e h).2, endRun_length c e h⟩⟩

/-- The run's points leave a list of variables empty or not as it was. -/
theorem withPoints_isEmpty : ∀ (vs : List Var) (zs : List E),
    (withPoints vs zs).isEmpty = vs.isEmpty
  | [], _ => rfl
  | .plain _ :: _, _ => rfl
  | .point _ _ :: _, _ :: _ => rfl
  | .point _ _ :: _, [] => rfl

/-- **The library's test on the shape reads no point: it is the same at the call in a run, where the
seven take it, and at the job's shape, where `SumJob.fitsShapeAt` takes it.** -/
theorem shapeOk_callAt (J : SumJob W X) (w : W) (fr : Front X) :
    shapeOk (J.callAt w fr) = shapeOk J.shape := by
  have e : ∀ l : List Var, (l.all fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) =
      (l.map Var.d).all fun d => decide (2 ≤ d) && decide (d ≤ 65) := by
    intro l
    rw [List.all_map]
    rfl
  show ((withPoints J.shape.vs (J.points w fr)).all
      (fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) &&
    (match J.shape.ends with
     | none => !(withPoints J.shape.vs (J.points w fr)).isEmpty
     | some e => decide (1 ≤ e.dY) && decide (1 ≤ e.n))) = shapeOk J.shape
  rw [e, withPoints_ds, ← e, withPoints_isEmpty]
  rfl

/-- **What is left for a caller to show for both names**: the seven's own premise on the shape, and
what `fitsAt_of_parts` asks. -/
theorem fitsShapeAt_of_parts {name endName : String} (J : SumJob W X)
    (c : SumCoins name endName J) (w : W) (fr : Front X) (ds : List Fmt.Drawn)
    (hs : shapeOk (J.callAt w fr) = true) (hd : drawsOk (J.callAt w fr) ds = true)
    (hp : (J.points w fr).length = pointsIn J.shape.vs)
    (hl : (J.lead w fr).length = J.shape.lead)
    (hr : ∀ i (h : i < J.shape.vs.length), noneCut J.shape.vs[i].d
      (J.round w fr (((varsOf (J.callAt w fr) ds).take J.shape.vs.length).take i)) = true)
    (he : ∀ e, J.shape.ends = some e →
      noneCut (e.dY + 1)
          (J.inY w fr ((varsOf (J.callAt w fr) ds).take J.shape.vs.length) (endRun c)) = true ∧
        (J.ends w fr ((varsOf (J.callAt w fr) ds).take J.shape.vs.length)).length = e.n) :
    J.fitsShapeAt w fr ((varsOf (J.callAt w fr) ds).take J.shape.vs.length) (endRun c) = true := by
  unfold SumJob.fitsShapeAt
  rw [← shapeOk_callAt J w fr, hs, fitsAt_of_parts J c w fr ds hd hp hl hr he]
  rfl

/-! ## 3 Under the test: the points, the lead's values, the end values -/

/-- The points at which variables are summed, in order. -/
def pointsOf : List Var → List E
  | [] => []
  | .plain _ :: vs => pointsOf vs
  | .point z _ :: vs => z :: pointsOf vs

/-- Points that are as many as the variables summed at a point all stand in the shape, in order. -/
theorem withPoints_points : ∀ (vs : List Var) (zs : List E), zs.length = pointsIn vs →
    pointsOf (withPoints vs zs) = zs
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | .plain _ :: vs, zs, h => withPoints_points vs zs h
  | .point _ _ :: vs, z :: zs, h => by
    show z :: pointsOf (withPoints vs zs) = z :: zs
    rw [withPoints_points vs zs (Nat.succ.inj h)]
  | .point _ _ :: _, [], h => by cases h

/-- **Under the test every point of the job stands in the call, in order, and no placeholder of the
shape's is left.** -/
theorem callAt_points (J : SumJob W X) (w : W) (fr : Front X) (rs m : List E)
    (h : J.fitsAt w fr rs m = true) : pointsOf (J.callAt w fr).vs = J.points w fr :=
  withPoints_points _ _ ((fitsAt_iff J w fr rs m).1 h).1

/-- Below a list's length the member by number with a default is a member. -/
theorem getD_member (l : List E) (i : Nat) (h : i < l.length) :
    l[i]? = some (l.getD i zeroE) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- Under the test the lead's value number i, which `SumFirst` reads, is a member of the job's list.
-/
theorem lead_member (J : SumJob W X) (w : W) (fr : Front X) (rs m : List E)
    (h : J.fitsAt w fr rs m = true) (i : Nat) (hi : i < J.shape.lead) :
    (J.lead w fr)[i]? = some ((J.lead w fr).getD i zeroE) :=
  getD_member _ i (by rw [((fitsAt_iff J w fr rs m).1 h).2.1]; exact hi)

/-- Under the test the end value number j, which `SumLast` and `SumEnds` read, is a member of the
job's list. -/
theorem ends_member (J : SumJob W X) (w : W) (fr : Front X) (rs m : List E)
    (h : J.fitsAt w fr rs m = true) (e : Ends) (he : J.shape.ends = some e) (j : Nat)
    (hj : j < e.n) : (J.ends w fr rs)[j]? = some ((J.ends w fr rs).getD j zeroE) :=
  getD_member _ j (by rw [(((fitsAt_iff J w fr rs m).1 h).2.2.2.2 e he).2.1]; exact hj)

/-! ## 4 Where nothing but zeros is cut -/

/-- Where nothing but zeros is cut, the members from d on are the program's zero. -/
theorem noneCut_getD (d : Nat) (g : List E) (h : noneCut d g = true) (i : Nat) (hi : d ≤ i) :
    g.getD i zeroE = zeroE := by
  by_cases hl : i < g.length
  · have hm : g[i] ∈ g.drop d := by
      rw [List.mem_iff_getElem]
      refine ⟨i - d, by rw [List.length_drop]; omega, ?_⟩
      rw [List.getElem_drop]
      congr 1
      omega
    have := List.all_eq_true.1 h _ hm
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    exact beq_iff_eq.1 this
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- **Where nothing but zeros is cut, the list as the part fills or cuts it is the polynomial of the
list itself.** -/
theorem polyOf_noneCut {K : Type} [Field K] (ρ : Reading K) (d : Nat) (g : List E)
    (h : noneCut d g = true) : polyOf ρ (padTo d g) = polyOf ρ g := by
  refine polyOf_congr ρ _ _ fun i => ?_
  rw [padTo_getD]
  by_cases hi : i < d
  · rw [if_pos hi]
  · rw [if_neg hi, noneCut_getD d g h i (by omega)]

/-- Where nothing but zeros is cut at d, and d is at least 1, the list's polynomial has a degree
below d: the clause on the degree in the library's `Chain`. -/
theorem natDegree_noneCut {K : Type} [Field K] (ρ : Reading K) (d : Nat) (g : List E)
    (h : noneCut d g = true) (hd : 1 ≤ d) : (polyOf ρ g).natDegree < d := by
  have := polyOf_natDegree_lt ρ (padTo d g) (by rw [padTo_length]; omega)
  rwa [padTo_length, polyOf_noneCut ρ d g h] at this

/-- The job's lists as they are, as polynomials, with the challenges read. -/
noncomputable def rawMoves {K : Type} [Field K] (ρ : Reading K) (poly : List E → List E) :
    List E → List E → List (K[X] × K)
  | past, r :: rs => (polyOf ρ (poly past), ρ.val r) :: rawMoves ρ poly (past ++ [r]) rs
  | _, [] => []

/-- Where nothing but zeros is cut in any round, `polyMoves` (More.lean) are these. -/
theorem polyMoves_raw {K : Type} [Field K] (ρ : Reading K) (poly : List E → List E) :
    ∀ (vs : List Var) (past rs : List E), vs.length = rs.length →
      (∀ i (h : i < vs.length), noneCut vs[i].d (poly (past ++ rs.take i)) = true) →
      polyMoves ρ vs poly past rs = rawMoves ρ poly past rs
  | [], _, [], _, _ => rfl
  | v :: vs, past, r :: rs, hl, h => by
    have h0 : noneCut v.d (poly past) = true := by
      have := h 0 (by simp only [List.length_cons]; omega)
      rwa [List.take_zero, List.append_nil] at this
    show (polyOf ρ (padTo v.d (poly past)), ρ.val r) :: polyMoves ρ vs poly (past ++ [r]) rs =
      (polyOf ρ (poly past), ρ.val r) :: rawMoves ρ poly (past ++ [r]) rs
    rw [polyOf_noneCut ρ _ _ h0, polyMoves_raw ρ poly vs (past ++ [r]) rs
      (by simp only [List.length_cons] at hl; omega) fun i hi => by
        have := h (i + 1) (by simp only [List.length_cons]; omega)
        have e : past ++ (r :: rs).take (i + 1) = past ++ [r] ++ rs.take i := by
          rw [List.take_succ_cons, List.append_assoc]
          rfl
        rw [e] at this
        exact this]
  | [], _, _ :: _, hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, [], hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega

/-- **Where nothing but zeros is cut, every variable has at least one coefficient and the challenges
are as many as the variables, `SumsTo` is the library's `Chain` at the polynomials of the lists as
they are.** -/
theorem sumsTo_unpadded {K : Type} [Field K] (ρ : Reading K) (poly : List E → List E)
    (vs : List Var) (past rs : List E) (c c' : K) (h1 : ∀ v ∈ vs, 1 ≤ v.d)
    (hl : vs.length = rs.length)
    (hn : ∀ i (h : i < vs.length), noneCut vs[i].d (poly (past ++ rs.take i)) = true) :
    SumsTo ρ vs poly past rs c c' ↔ Chain (vs.map (Var.wt ρ)) (rawMoves ρ poly past rs) c c' := by
  rw [sumsTo_iff_chain ρ poly vs past rs c c' h1 hl, polyMoves_raw ρ poly vs past rs hl hn]

/-! ## 5 At a job that passes the test -/

/-- A variable of the call in a run has the shape's number of coefficients. -/
theorem all_d_var (J : SumJob W X) (w : W) (fr : Front X) (i : Nat)
    (hv : i < J.shape.vs.length) (h : i < (J.callAt w fr).all.length) :
    (J.callAt w fr).all[i].d = J.shape.vs[i].d := by
  have h1 : ((J.callAt w fr).all.map Var.d)[i]? = (J.shape.vs.map Var.d)[i]? := by
    cases he : J.shape.ends with
    | none => rw [all_none J w fr he, withPoints_ds]
    | some e =>
      rw [all_some J w fr e he, List.map_append, withPoints_ds,
        List.getElem?_append_left (by rw [List.length_map]; exact hv)]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem hv] at h1
  exact Option.some.inj h1

/-- The variable Y of the call in a run has dY + 1 coefficients. -/
theorem all_d_Y (J : SumJob W X) (w : W) (fr : Front X) (e : Ends) (he : J.shape.ends = some e)
    (h : J.shape.vs.length < (J.callAt w fr).all.length) :
    (J.callAt w fr).all[J.shape.vs.length].d = e.dY + 1 := by
  have h1 : (J.callAt w fr).all[J.shape.vs.length]? = some (.point zeroE (e.dY + 1)) := by
    rw [all_some J w fr e he, List.getElem?_append_right (by rw [withPoints_length]),
      withPoints_length, Nat.sub_self]
    rfl
  rw [List.getElem?_eq_getElem h] at h1
  rw [Option.some.inj h1]
  rfl

/-- **At a job that passes the test nothing but zeros is cut in any round**, Y's among them. r: the
challenges of all variables, Y's last. -/
theorem fits_noneCut (J : SumJob W X) (w : W) (fr : Front X) (r m : List E)
    (hr : r.length = (J.callAt w fr).all.length)
    (hf : J.fitsAt w fr (r.take J.shape.vs.length) m = true) :
    ∀ i (h : i < (J.callAt w fr).all.length),
      noneCut (J.callAt w fr).all[i].d (jobPoly J w fr m ([] ++ r.take i)) = true := by
  obtain ⟨-, -, -, h4, h5⟩ := (fitsAt_iff J w fr _ m).1 hf
  intro i hi
  have hal := all_length J w fr
  rw [List.nil_append]
  have hlen : (r.take i).length = i := by
    rw [List.length_take]
    omega
  by_cases hv : i < J.shape.vs.length
  · have e1 : jobPoly J w fr m (r.take i) = J.round w fr (r.take i) := by
      unfold jobPoly
      rw [if_pos (by rw [hlen]; exact hv)]
    have e2 : (r.take J.shape.vs.length).take i = r.take i := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hv)]
    rw [e1, all_d_var J w fr i hv hi, ← e2]
    exact h4 i hv
  · cases he : J.shape.ends with
    | none =>
      rw [he] at hal
      simp only at hal
      omega
    | some e =>
      have hi' : i = J.shape.vs.length := by
        rw [he] at hal
        simp only at hal
        omega
      subst hi'
      have e1 : jobPoly J w fr m (r.take J.shape.vs.length) =
          J.inY w fr (r.take J.shape.vs.length) m := by
        unfold jobPoly
        rw [if_neg (by rw [hlen]; omega)]
      rw [e1, all_d_Y J w fr e he hi]
      exact (h5 e he).1

/-- **At a job that passes the test, where every variable of the call has at least one coefficient
(h1: not given by the test; from `shapeOk` by `all_two`, Reads.lean) and the challenges are as many
as the variables (hr: `varsOf_length`), `SumsTo`, as `SumClaim` and `SumLeft` take it, is the
library's `Chain` at the polynomials of the job's own lists.** -/
theorem sumsTo_job {K : Type} [Field K] (ρ : Reading K) (J : SumJob W X) (w : W) (fr : Front X)
    (r m : List E) (c c' : K) (h1 : ∀ v ∈ (J.callAt w fr).all, 1 ≤ v.d)
    (hr : r.length = (J.callAt w fr).all.length)
    (hf : J.fitsAt w fr (r.take J.shape.vs.length) m = true) :
    SumsTo ρ (J.callAt w fr).all (jobPoly J w fr m) [] r c c' ↔
      Chain ((J.callAt w fr).all.map (Var.wt ρ)) (rawMoves ρ (jobPoly J w fr m) [] r) c c' :=
  sumsTo_unpadded ρ _ _ [] r c c' h1 hr.symm (fits_noneCut J w fr r m hr hf)

/-! ## 6 The challenges -/

/-- How many elements each round of a call samples. -/
theorem entries_drawE (k : Call) :
    (entries k).map (·.drawE) =
      (1 :: k.vs.map fun _ => 1) ++ (match k.ends with
        | none => []
        | some _ => [1, 0]) := by
  unfold entries
  cases k.ends with
  | none =>
    rw [List.map_append, List.map_append, List.map_map]
    rfl
  | some e =>
    rw [List.map_append, List.map_append, List.map_map]
    rfl

/-- If each challenge of a list has just one element, none is without an element. -/
theorem all_hold (l : List Fmt.Drawn) (h : ∀ n ∈ l.map (·.elems.length), n = 1) :
    (l.all fun d => !d.elems.isEmpty) = true := by
  rw [List.all_eq_true]
  intro d hd
  have := h _ (List.mem_map_of_mem hd)
  cases he : d.elems with
  | nil =>
    rw [he] at this
    cases this
  | cons _ _ => rfl

/-- **Challenges that fit the call pass `challengesFit`.** -/
theorem challengesFit_of_drawsOk (k : Call) (ds : List Fmt.Drawn) (h : drawsOk k ds = true) :
    challengesFit k ds = true := by
  have hL : ds.map (·.elems.length) = (entries k).map (·.drawE) := beq_iff_eq.1 h
  rw [entries_drawE] at hL
  have hn := drawsOk_length k ds h
  rw [entries_count] at hn
  have h1 : ∀ n ∈ (1 :: k.vs.map fun _ => 1), n = 1 := by
    intro n hn'
    rcases List.mem_cons.1 hn' with rfl | hn'
    · rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hn'
      rfl
  unfold challengesFit scalarsOf
  rw [Bool.and_eq_true]
  cases he : k.ends with
  | none =>
    rw [he] at hL hn
    refine ⟨beq_iff_eq.2 ?_, ?_⟩
    · rw [hn, List.length_append, List.length_append, List.length_map]
      show k.vs.length + 1 = 1 + k.vs.length + 0
      omega
    · show (ds.all fun d => !d.elems.isEmpty) = true
      refine all_hold ds ?_
      rw [hL, List.append_nil]
      exact h1
  | some e =>
    rw [he] at hL hn
    refine ⟨beq_iff_eq.2 ?_, ?_⟩
    · rw [hn, List.length_append, List.length_append, List.length_map]
      show k.vs.length + 3 = 1 + k.vs.length + 2
      omega
    · show (ds.dropLast.all fun d => !d.elems.isEmpty) = true
      refine all_hold ds.dropLast ?_
      have e1 : ((1 :: k.vs.map fun _ => 1) ++ [1, 0] : List Nat) =
          ((1 :: k.vs.map fun _ => 1) ++ [1]) ++ [0] := by
        rw [List.append_assoc]
        rfl
      rw [List.map_dropLast, hL, e1, List.dropLast_concat]
      intro n hn'
      rcases List.mem_append.1 hn' with hn' | hn'
      · exact h1 n hn'
      · exact List.mem_singleton.1 hn'

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.all_zipIdx
#print axioms ProofFile.Honest.SumLaw.fitsAt_iff
#print axioms ProofFile.Honest.SumLaw.drawsOk_length
#print axioms ProofFile.Honest.SumLaw.all_length
#print axioms ProofFile.Honest.SumLaw.vars_take_length
#print axioms ProofFile.Honest.SumLaw.call_all_length
#print axioms ProofFile.Honest.SumLaw.varsOf_length
#print axioms ProofFile.Honest.SumLaw.endCoins_length
#print axioms ProofFile.Honest.SumLaw.endRun_length
#print axioms ProofFile.Honest.SumLaw.fitsAt_of_parts
#print axioms ProofFile.Honest.SumLaw.withPoints_isEmpty
#print axioms ProofFile.Honest.SumLaw.shapeOk_callAt
#print axioms ProofFile.Honest.SumLaw.fitsShapeAt_of_parts
#print axioms ProofFile.Honest.SumLaw.withPoints_points
#print axioms ProofFile.Honest.SumLaw.callAt_points
#print axioms ProofFile.Honest.SumLaw.getD_member
#print axioms ProofFile.Honest.SumLaw.lead_member
#print axioms ProofFile.Honest.SumLaw.ends_member
#print axioms ProofFile.Honest.SumLaw.noneCut_getD
#print axioms ProofFile.Honest.SumLaw.polyOf_noneCut
#print axioms ProofFile.Honest.SumLaw.natDegree_noneCut
#print axioms ProofFile.Honest.SumLaw.polyMoves_raw
#print axioms ProofFile.Honest.SumLaw.sumsTo_unpadded
#print axioms ProofFile.Honest.SumLaw.all_d_var
#print axioms ProofFile.Honest.SumLaw.all_d_Y
#print axioms ProofFile.Honest.SumLaw.fits_noneCut
#print axioms ProofFile.Honest.SumLaw.sumsTo_job
#print axioms ProofFile.Honest.SumLaw.entries_drawE
#print axioms ProofFile.Honest.SumLaw.all_hold
#print axioms ProofFile.Honest.SumLaw.challengesFit_of_drawsOk
