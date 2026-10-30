-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/EqAllReads.lean: THE SMALLNESS TEST: THE WHOLE RUN OF EQUATIONS
("K8.equations") ON SHAPES: THE READS' CLAIMS' SHAPES, which
Johnson/Desc/K8/Honest/EqAllUpdate.lean leaves as a number. General laws: nothing is evaluated.

  readsSh         the shapes of the reads' claims, in order, from number q on: none where a read's
                  vector has no array in the plan.
  reads_sh        what the law says of the reads' claims (ReadLaid,
                  Johnson/Desc/K8/Honest/EqUnitReturns.lean: the array's number is tied to the
                  plan's) gives these shapes.
  readSh_blank, readsSh_blank   they are read off the shapes: their value at the records is their
                  value at the blank records of the shapes.
  readsSh_three   the three fields that the tail lays last are not read.
  Ret_all         what a "returns" law says holds of every return.
  **eqAll_claims**   under the premises of eqAll_shape: the shapes of all claims behind the list are
                  a function of the shapes: those in front, then the claim on the key vectors, the
                  three on the planes, one tie a matrix, one claim a read.

Limits. One direction alone. Nothing on the tests on values. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.K8.Honest.EqAllUpdate
import Johnson.Desc.K8.Honest.EqUnitProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret)
open VerifiableInference.Desc.First.Shape
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- The shapes of the reads' claims, in order, from number q on. tl: the record in front; tl':
behind the weights' step; F: the ledger behind. IT IS TYPED ON RECORDS: "on shapes" is
readsSh_blank's doing. eqAll_claims calls it at the blank of the record behind the WHOLE list:
readsSh_three bridges that. -/
def readsSh (tl tl' : HTailF2) (F : Fork) : Nat → List (HFun × Nat) → Option (List ClaimSh)
  | _, [] => some []
  | q, x :: l =>
    (tl.ix.U.getD x.1.tree none).bind fun tU =>
      (readsSh tl tl' F (q + 1) l).map fun r => readSh tl' F x.1 x.2 q tU :: r

theorem reads_sh {tl tl' : HTailF2} {F : Fork} : ∀ (q : Nat) (l : List (HFun × Nat))
    (reads : List Claim), LaidBy (ReadLaid tl tl' F) q l reads →
      readsSh tl tl' F q l = some (reads.map claimSh)
  | _, [], [], _ => rfl
  | q, x :: l, c :: cs, h => by
    obtain ⟨⟨tU, hU, hc⟩, hr⟩ := h
    unfold readsSh
    rw [hU, reads_sh (q + 1) l cs hr, List.map_cons, readClaim_sh hc]
    rfl
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

theorem readSh_blank (tl' : HTailF2) (F : Fork) (Fn : HFun) (sg q tU : Nat) :
    readSh (tailSh tl').blank (ledBlank (ledSh F)) (eF Fn) sg q tU = readSh tl' F Fn sg q tU := by
  unfold readSh
  rw [led_cols, eF_size]
  rfl

theorem readsSh_blank (tl tl' : HTailF2) (F : Fork) : ∀ (q : Nat) (l : List (HFun × Nat)),
    readsSh (tailSh tl).blank (tailSh tl').blank (ledBlank (ledSh F)) q
      (l.map fun x => (eF x.1, x.2)) = readsSh tl tl' F q l
  | _, [] => rfl
  | q, x :: l => by
    rw [List.map_cons]
    unfold readsSh
    rw [readsSh_blank tl tl' F (q + 1) l]
    show (tl.ix.U.getD x.1.tree none).bind _ = _
    congr 1
    funext tU
    rw [readSh_blank]

/-- The three fields that the tail lays last are not read. -/
theorem readsSh_three (tl tl' : HTailF2) (F : Fork) (a b : Array Nat) (c : Nat) :
    ∀ (q : Nat) (l : List (HFun × Nat)),
      readsSh tl { tl' with tieObj := a, tiesOn := b, nX4Laid := c } F q l = readsSh tl tl' F q l
  | _, [] => rfl
  | q, x :: l => by
    unfold readsSh
    rw [readsSh_three tl tl' F a b c (q + 1) l]
    rfl

/-- What a "returns" law says holds of every return. -/
theorem Ret_all {α : Type} {x : EqM α} {front : Nat} {s : St} {Q : α → St → Prop}
    (h : Ret x front s Q) : ∀ a s', x front s = .ok (a, s') → Q a s' := by
  obtain ⟨a, s', e, q⟩ := h
  intro a' s'' e'
  rw [e] at e'
  cases e'
  exact q

/-- **The shapes of all claims behind the list are a function of the shapes.** -/
theorem eqAll_claims {front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {cs : Array Claim}
    (h : allB front (tailSh tl) (funs.toList.map funSh) (ledSh F) cs.size = true)
    (v1 : tl.funsHeld funs = true) (v2 : (F.LS.extract tl.slotA tl.slotB).all isZeroE = true)
    (v3 : LiveCols tl funs F.theta) :
    Ret (eqAll tl funs) front (F, cs) fun out s' =>
      tailSh out = allRecU front cs.size (tailSh tl) (funs.toList.map funSh) (ledSh F) ∧
      ∃ g, tl.heard = some g ∧ ledSh s'.1 = allLedU (heardAll g) (ledSh F) ∧
        ∃ reads : List ClaimSh,
          readsSh (tailSh tl).blank (tailSh out).blank (ledBlank (ledSh s'.1)) 0
            (readsList (tailSh tl).blank (eFs funs)) = some reads ∧
          s'.2.toList.map claimSh = cs.toList.map claimSh ++
            (allClaimsU (tailSh tl) (tailSh out) (heardAll g) ++ reads) := by
  obtain ⟨g, rd, s1, s3, hA⟩ := allReady_of_shape h
  refine ((eqAll_shape h v1 v2 v3).also
    (Ret_all (eqAll_returns_unit front tl funs F cs g rd s1 s3 hA v1 v2 v3))).mono ?_
  rintro out s' ⟨⟨hrec, g', hg', hled, -⟩,
    bf, tl', four, ties, reads, hL, rfl, -, -, hcs, h4, hT, hR⟩
  obtain rfl : g = g' := by
    have := hA.heard
    rw [hg'] at this
    exact (Option.some.inj this).symm
  refine ⟨hrec, g, hg', hled, reads.map claimSh, ?_, ?_⟩
  · show readsSh (tailSh tl).blank _ _ 0 (readsList tl (eFs funs)) = _
    rw [readsList_e, readsSh_blank, readsSh_three]
    exact reads_sh 0 _ _ hR
  · rw [hcs]
    unfold allClaimsU
    rw [heard_narrow, tail_narrow, ← Law.keysClaim_sh, ← Law.countsClaims_sh]
    simp only [Array.toList_append, List.map_append, h4, ties_sh 0 _ _ hT, List.append_assoc,
      List.cons_append]
    rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.reads_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.readSh_blank
#print axioms VerifiableInference.Desc.First.K8.Honest.readsSh_blank
#print axioms VerifiableInference.Desc.First.K8.Honest.readsSh_three
#print axioms VerifiableInference.Desc.First.K8.Honest.Ret_all
#print axioms VerifiableInference.Desc.First.K8.Honest.eqAll_claims
#print axioms VerifiableInference.Desc.First.K8.Honest.readsSh
