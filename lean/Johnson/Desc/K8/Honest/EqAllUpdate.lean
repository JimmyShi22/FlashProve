-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/EqAllUpdate.lean: THE SMALLNESS TEST: THE WHOLE RUN OF EQUATIONS
("K8.equations": eqAll, Johnson/Desc/First/TailClaims/Equations.lean) IN THE FORM "ONE Bool AND ONE
UPDATE ON SHAPES": THE UPDATE, AND THE LAW. General laws: nothing is evaluated.

  eqTail_cut, eqAll_cut   a return of the tail, and of the whole list, cut at its parts.
  sums_join, weightsU_join   the weights' step's update keeps one number.
  eqAll_record    FROM A RETURN ALONE: the record's shape behind the list is the weights' step's
                  update (Johnson/Desc/First/TailClaims/EqWeightsShape.lean) of the shape in front,
                  with one number laid in front of it and three fields behind it: these four are
                  read off the returned record itself.
  allRecU, allLedU, allClaimsU   THE UPDATE: on the record's shape; on the ledger's; the shapes of
                  the claims that are added, but for the reads'.
  ties_sh         the ties' shapes, in order.
  **eqAll_shape**   where the Bool accepts at the shapes (allB,
                  Johnson/Desc/K8/Honest/EqAllShape.lean) and the three tests on values pass, the
                  whole list returns, and the shapes behind are the updates of the shapes in front.

Limits. OF THE READS' CLAIMS THE NUMBER ALONE IS SAID, not their shapes: the law that this file
stands on (eqAll_returns, Johnson/Desc/K8/Honest/EqAllProofs.lean) says of a read's claim "there is
an array's number tU such that ...", and ties tU to nothing. eqTail_cut and eqAll_cut leave states
under "there is" that nothing ties to the run's own (see their docstrings). One direction alone.
Nothing on the tests on values. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K8.Honest.EqAllShape
import Johnson.Desc.K8.Honest.EqShapes
import Johnson.Desc.First.TailClaims.EqWeightsShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret eqTail eqRest eq_bind_ok eq_pure_ok)
open VerifiableInference.Desc.First.Shape
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf)

/-- A return of the tail, cut at the weights' step: the record behind is what that step returned,
but for three fields. THE STATES s1, s2 AT WHICH THAT STEP RAN ARE UNDER "THERE IS" AND TIED TO
NEITHER s NOR s': enough for a law on shapes that holds at all states; of values only what holds of
such a return at every state follows. -/
theorem eqTail_cut {before : Nat} {tl out : HTailF2} {funs : Array HFun} {front : Nat} {s s' : St}
    (h : eqTail before tl funs front s = .ok (out, s')) :
    ∃ tl' s1 s2 a b c, eqWeights tl front s1 = .ok (tl', s2) ∧
      out = { tl' with tieObj := a, tiesOn := b, nX4Laid := c } := by
  unfold eqTail at h
  simp only [eq_bind_ok, eq_pure_ok] at h
  obtain ⟨_, _, _, _, _, _, tl', s2, hw, h⟩ := h
  iterate 11 obtain ⟨_, _, _, h⟩ := h
  obtain ⟨rfl, _⟩ := h
  exact ⟨tl', _, s2, _, _, _, hw, rfl⟩

/-- The weights' step's update keeps the number of the claim on the key vectors. -/
theorem sums_join : ∀ (l : List Nat) (x : TailSh),
    (l.foldl (fun x mu => Law.sumU mu x) x).joinObj9 = x.joinObj9
  | [], _ => rfl
  | mu :: l, x => by
    rw [List.foldl_cons, sums_join l]
    rfl

theorem weightsU_join (t : TailSh) : (Law.weightsU t).joinObj9 = t.joinObj9 := by
  unfold Law.weightsU
  rw [sums_join]
  rfl

/-- A return of the whole list, cut at its three parts. The first part's state s0 and the number
"before" are under "there is" and tied to neither s nor front; from s0 the states chain on to s'. -/
theorem eqAll_cut {tl out : HTailF2} {funs : Array HFun} {front : Nat} {s s' : St}
    (h : eqAll tl funs front s = .ok (out, s')) :
    ∃ tla tlb before s0 s1 s2, eqKeys tl front s0 = .ok (tla, s1) ∧
      eqCounts tla front s1 = .ok (tlb, s2) ∧ eqTail before tlb funs front s2 = .ok (out, s') := by
  rw [Law.eqAll_split] at h
  unfold eqRest at h
  simp only [eq_bind_ok] at h
  iterate 6 obtain ⟨_, _, _, h⟩ := h
  obtain ⟨before, s0, _, tla, s1, hk, tlb, s2, hc, ht⟩ := h
  exact ⟨tla, tlb, before, s0, s1, s2, hk, hc, ht⟩

/-- **The record's shape behind the whole list, from a return**: the weights' step's update of the
shape in front with the number of the claim on the key vectors laid; and three fields. That number
and the three fields are read off "out" itself on the right side: of these four the law says
nothing. -/
theorem eqAll_record {tl out : HTailF2} {funs : Array HFun} {front : Nat} {s s' : St}
    (h : eqAll tl funs front s = .ok (out, s')) :
    tailSh out = { Law.weightsU { tailSh tl with joinObj9 := out.joinObj9 } with
      tieObj := out.tieObj, tiesOn := out.tiesOn, nX4Laid := out.nX4Laid } := by
  obtain ⟨tla, tlb, before, s0, s1, s2, hk, hc, ht⟩ := eqAll_cut h
  obtain ⟨tl', s3, s4, a, b, c, hw, rfl⟩ := eqTail_cut ht
  have e1 := Law.eqKeys_spec _ _ _ _ _ hk
  have e2 := Law.eqCounts_spec _ _ _ _ _ hc
  obtain ⟨e3, -⟩ := Law.eqWeights_shape hw
  have eb : tailSh tlb = { tailSh tl with joinObj9 := tla.joinObj9 } := by
    rw [e2, e1]
    rfl
  have ej : tl'.joinObj9 = tla.joinObj9 := by
    have := congrArg TailSh.joinObj9 e3
    rw [eb, weightsU_join] at this
    exact this
  show { tailSh tl' with tieObj := a, tiesOn := b, nX4Laid := c } = _
  rw [e3, eb]
  show _ = { Law.weightsU { tailSh tl with joinObj9 := tl'.joinObj9 } with
    tieObj := a, tiesOn := b, nX4Laid := c }
  rw [ej]

/-! ## The update -/

/-- **THE UPDATE OF THE WHOLE LIST, on the record's shape.** n: the number of claims on the list so
far. -/
def allRecU (front n : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) : TailSh :=
  { Law.weightsU { t with joinObj9 := some (front + n) } with
    tieObj := numbersFrom (front + (n + 4)) t.NM
    tiesOn := tiesOnOf t.blank L.trees.length
    nX4Laid := (readsList t.blank (fs.map FunSh.blank).toArray).length }

/-- **On the ledger's shape**: two owed marks paid, the leaves' sumcheck's own slots filled. The
first setOwed is overwritten by the last. -/
def allLedU (g : HeardAll) (L : LedSh) : LedSh :=
  ((L.setOwed (paidB L.owed g.owedJoin)).setGot
    (fillB L.got g.leaves.first (takenSh g.leaves.degrees))).setOwed
      (paidB (paidB L.owed g.owedJoin) g.owedPlanes)

/-- **The shapes of the claims that the list adds**, but for the reads' (it takes no list of
claims): the claim on the key vectors, the three on the planes, one tie for each matrix. t': the
record's shape behind. -/
def allClaimsU (t t' : TailSh) (g : HeardAll) : List ClaimSh :=
  Law.keysClaimSh t.narrow g.narrow :: Law.countsClaimsSh t.narrow g.narrow ++
    (List.range t.NM).map (tieSh t'.blank)

theorem ties_sh {tl' : HTailF2} : ∀ (q : Nat) (l : List Nat) (ties : List Claim),
    LaidBy (fun _ mu c => TieClaim tl' mu c) q l ties → ties.map claimSh = l.map (tieSh tl')
  | _, [], [], _ => rfl
  | q, mu :: l, c :: cs, h => by
    rw [List.map_cons, List.map_cons, tieClaim_sh h.1, ties_sh (q + 1) l cs h.2]
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

/-- **Where the Bool accepts at the shapes and the three tests on values pass, the whole list
returns, and the shapes behind are the updates of the shapes in front**; of the reads' claims the
number alone is said. -/
theorem eqAll_shape {front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {cs : Array Claim}
    (h : allB front (tailSh tl) (funs.toList.map funSh) (ledSh F) cs.size = true)
    (v1 : tl.funsHeld funs = true) (v2 : (F.LS.extract tl.slotA tl.slotB).all isZeroE = true)
    (v3 : LiveCols tl funs F.theta) :
    Ret (eqAll tl funs) front (F, cs) fun out s' =>
      tailSh out = allRecU front cs.size (tailSh tl) (funs.toList.map funSh) (ledSh F) ∧
      ∃ g, tl.heard = some g ∧ ledSh s'.1 = allLedU (heardAll g) (ledSh F) ∧
        ∃ reads : List ClaimSh, reads.length = out.nX4Laid ∧
          s'.2.toList.map claimSh = cs.toList.map claimSh ++
            (allClaimsU (tailSh tl) (tailSh out) (heardAll g) ++ reads) := by
  obtain ⟨g, rd, s1, s3, hA⟩ := allReady_of_shape h
  refine ((eqAll_returns front tl funs F cs g rd s1 s3 hA v1 v2 v3).also
    (P := fun out s' => tailSh out = { Law.weightsU { tailSh tl with joinObj9 := out.joinObj9 } with
      tieObj := out.tieObj, tiesOn := out.tiesOn, nX4Laid := out.nX4Laid })
    fun out s' e => eqAll_record e).mono ?_
  rintro out s' ⟨⟨bf, tl', four, ties, reads, hL, rfl, -, hLed, hcs, h4, hT, hR⟩, hrec⟩
  have ej : tl'.joinObj9 = some (front + cs.size) := congrArg HTailF2.joinObj9 hL.rest
  have el : (readsList (tailSh tl).blank ((funs.toList.map funSh).map FunSh.blank).toArray).length =
      (readsList tl funs).length := by
    show (readsList tl (eFs funs)).length = _
    rw [readsList_e, List.length_map]
  have et : (ledSh F).trees.length = F.trees.size := by
    show (F.trees.toList.map treeSh).length = _
    rw [List.length_map, Array.length_toList]
  refine ⟨?_, g, hA.heard, ?_, reads.map claimSh, ?_, ?_⟩
  · rw [hrec]
    unfold allRecU
    rw [el, et]
    dsimp only
    rw [ej]
    rfl
  · rw [hLed, ledSh_paid, ← taken_sh]
    rfl
  · rw [List.length_map]
    exact laidBy_length _ _ _ _ hR
  · rw [hcs]
    unfold allClaimsU
    rw [heard_narrow, tail_narrow, ← Law.keysClaim_sh, ← Law.countsClaims_sh]
    simp only [Array.toList_append, List.map_append, h4, ties_sh 0 _ _ hT, List.append_assoc,
      List.cons_append]
    rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqTail_cut
#print axioms VerifiableInference.Desc.First.K8.Honest.sums_join
#print axioms VerifiableInference.Desc.First.K8.Honest.weightsU_join
#print axioms VerifiableInference.Desc.First.K8.Honest.eqAll_cut
#print axioms VerifiableInference.Desc.First.K8.Honest.eqAll_record
#print axioms VerifiableInference.Desc.First.K8.Honest.ties_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.eqAll_shape
#print axioms VerifiableInference.Desc.First.K8.Honest.allRecU
#print axioms VerifiableInference.Desc.First.K8.Honest.allLedU
#print axioms VerifiableInference.Desc.First.K8.Honest.allClaimsU
