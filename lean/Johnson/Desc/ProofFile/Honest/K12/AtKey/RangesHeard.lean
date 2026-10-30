-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesHeard.lean: the job of the key file's test on the
ranges (rangesTestJob, E2E/KeyRangesJob.lean) places its member's rows at the first row of both tables, at
every input and front, in scope. So its first stage's tables read of a front nothing at all, and
its rows₀ reads the heard alone (RowsOfHeard, K12/TablesAtFront.lean), though the state on entry
that it is made with reads the rounds shown.

  shape15_of_fold   wherever the replay of the first fifteen sub-protocols returns, from the
                    chain's first state, over any rounds, with anything left over, the state has
                    the written shape T15 (E2E/KeyShapeAtFull.lean)
  firstRowZero      a closed test on a shape: the group holds its member 0 at the first row of the
                    main table and of the mask table, or there is no such group
  first_row_of_shape   that test at a state's shape gives oM and oZ at 0 for the state
  first_row_T15, first_row_T0   the test is true at the two shapes: by the kernel
  first_row_rec     at every input and front the state on entry has oM and oZ at 0, in scope
  rows_heard_rng    RowsOfHeard at the job, in scope

By what. reach_of_fold (Johnson/Top/H0/Walk/Reach.lean), shape_reach, run_front
(Honest/Thread/Shape.lean), carries_whole₁ (E2E/KeyShapeFirstWhole.lean), layoutS_eq
(Johnson/Desc/Ground/Shape/Ground.lean), layout_of_group (Johnson/Desc/Own/LayoutAgree.lean).

Limits.
- In scope; at the written sizes.
- The state on entry is recRanges: a function of the input and the rounds shown. What is said here
  of it is its shape alone, at rounds that may be no run's: where the replay refuses, the state is
  the one made of the chain's first state, and first_row_T0 speaks of that.
- first_row_T0 and first_row_T15 can be false: a group with a larger member in front of member 0
  would make them so.
- Nothing on what the rows hold. Nothing on completeness, soundness or hiding.
-/
import E2E.KeyRangesJob
import E2E.KeyRangesShape15
import Johnson.Desc.Own.LayoutAgree
import Johnson.Desc.ProofFile.Honest.K12.TablesAtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest AtPublicFiles.KeyLink
open H2K.Member (nKRFull)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **Wherever the replay of the first fifteen returns, the state has the written shape**, in
scope: at any rounds, and whatever is left over. -/
theorem shape15_of_fold (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription X N P).XiPub) {rs : List Fmt.RoundView}
    {y : FirstState × List Fmt.RoundView × List OpenedColumn}
    (hy : foldBlocks 0 ((keyFileDescription X N P).first.blocksInOrder.take 15) ((keyFileDescription X N P).start₁ x) rs [] =
      .ok y) :
    sh₁B (pubOf X) CF y.1 = T15 := by
  obtain ⟨hN, -, -, hlen, hsh0, -, hyes, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have h6 := six_sourced hs scope
  have hr : Reach 0 (keyFileDescription X N P).first.blocksInOrder (fun _ : Unit => (keyFileDescription X N P).start₁ x) 15
      ((), y.1) :=
    reach_of_fold 15 (Nat.le_trans (by decide : 15 ≤ 19) (Nat.le_of_eq hlen.symm)) y.1 rs y.2.1 []
      y.2.2 hy
  obtain ⟨e, hE⟩ := run_front (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true) T0 19 15
    (by decide) hyes
  have e1 := shape_reach (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true)
    (fun j => carries_whole₁ (pubOf X) CF X.Y.D.1 X.Y.told.1 N 0 _ bw hw he ha j) hr e
    (by
      have h0 := (start₁_shape (cs := CF) (N := N) (X := X) (P := P) (fun _ _ _ _ => true) x).trans
        hsh0
      show (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true).run 15
        ((Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true).sh
          ((keyFileDescription X N P).start₁ x)) = _
      rw [h0]
      exact hE)
  have h15 : (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true).run 15 T0 =
      .ok ((Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true).sh y.1) := by
    rw [hE, e1]
  subst hN
  have q0 := entries_six X nKRFull P hs.named.plan h6 0 (by decide)
  have q1 := entries_six X nKRFull P hs.named.plan h6 1 (by decide)
  exact Except.ok.inj (h15.symm.trans (run15_six h6 _ _ _ q0 q1))

end AtPublicFiles.AtFiles.Full

namespace ProofFile.Honest.K12.AtKey
open OnBytes.Means (layoutOf)
open VerifiableInference.Desc (foldBlocks)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.Ground.Sh (StSh stSh grpSh grp_get layoutS layoutS_eq)
open H2K.First (oM oZ)
open AtPublicFiles.AtFiles (KeySourced rangesState pubOf sh₁B Sh₁B CF)
open AtPublicFiles.AtFiles.Full (T0 T15 shape15_of_fold)
open AtPublicFiles.KeyThread (D recRanges rangesTestJob)
open OnBytes.Slice (GF)
open VerifierAndGoals (InScope)

/-- The group holds its member 0 at the first row of both tables, or there is no such group. -/
def firstRowZero (a : StSh) (g : Nat) : Bool :=
  (a.groups[g]?).all fun G => oM (layoutS a G) 0 == 0 && oZ (layoutS a G) 0 == 0

/-- **At a state whose shape passes the test, the member stands at the first row.** -/
theorem first_row_of_shape (t : T12) (a : StSh) (ha : stSh t.st = a)
    (h : firstRowZero a t.g = true) :
    oM (layoutAt t) 0 = 0 ∧ oZ (layoutAt t) 0 = 0 := by
  subst ha
  unfold layoutAt
  cases hG : t.st.groups[t.g]? with
  | none => exact ⟨rfl, rfl⟩
  | some G =>
    have e : (stSh t.st).groups[t.g]? = some (grpSh G) := by
      rw [grp_get, hG]
      rfl
    have l1 := OnBytes.Means.layout_eq t.st t.g G hG
    have l2 := VerifiableInference.Desc.Own.layout_of_group hG
    have hl : layoutOf t.st G = layoutS (stSh t.st) (grpSh G) := by
      rw [layoutS_eq]
      exact Option.some.inj (l1.symm.trans l2)
    unfold firstRowZero at h
    rw [e] at h
    have h' : (oM (layoutS (stSh t.st) (grpSh G)) 0 == 0 &&
        oZ (layoutS (stSh t.st) (grpSh G)) 0 == 0) = true := h
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h'
    show oM (layoutOf t.st G) 0 = 0 ∧ oZ (layoutOf t.st G) 0 = 0
    rw [hl]
    exact h'

set_option maxRecDepth 1000000 in
theorem first_row_T15 : firstRowZero T15.1.st T15.2.grp = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem first_row_T0 : firstRowZero T0.1.st T0.2.grp = true := by decide +kernel

/-- A state of a shape that passes: the structure made of it has its member at the first row. -/
theorem first_row_state {Q : AtPublicFiles.KeyShape.Pub1} (e : FirstState) (A : Sh₁B)
    (h : sh₁B Q CF e = A) (hz : firstRowZero A.1.st A.2.grp = true) :
    oM (layoutAt (rangesState e)) 0 = 0 ∧ oZ (layoutAt (rangesState e)) 0 = 0 := by
  have h1 : stSh e.d.st = A.1.st := congrArg (·.1.st) h
  have h2 : e.grp = A.2.grp := congrArg (·.2.grp) h
  refine first_row_of_shape (rangesState e) A.1.st h1 ?_
  show firstRowZero A.1.st e.grp = true
  rw [h2]
  exact hz

section
variable {W₀ Rc X' : Type} {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source}
  {N : H2U.PlaceNums} {Pl : VerifiableInference.Desc.Key.LaterPlaces}

/-- **At every input and front the member stands at the first row**, in scope. -/
theorem first_row_rec (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (w : Local W₀ Rc Xi Unit) (fr : Front X') :
    oM (layoutAt (recRanges (X' := X') Xs N Pl w fr)) 0 = 0 ∧
      oZ (layoutAt (recRanges (X' := X') Xs N Pl w fr)) 0 = 0 := by
  unfold recRanges
  cases h : foldBlocks 0 ((D Xs N Pl).first.blocksInOrder.take 15)
      ((D Xs N Pl).start₁ ((D Xs N Pl).pub w.x)) fr.seen.rounds [] with
  | ok y => exact first_row_state y.1 T15 (shape15_of_fold hsrc scope _ h) first_row_T15
  | error _ =>
    obtain ⟨-, -, -, -, hsh0, -⟩ := AtPublicFiles.AtFiles.Full.first_of_sourced hsrc scope fun _ _ _ _ => true
    have h0 : sh₁B (pubOf Xs) CF ((D Xs N Pl).start₁ ((D Xs N Pl).pub w.x)) = T0 :=
      (AtPublicFiles.AtFiles.start₁_shape (cs := CF) (N := N) (X := Xs) (P := Pl)
        (fun _ _ _ _ => true) ((D Xs N Pl).pub w.x)).trans hsh0
    exact first_row_state _ T0 h0 first_row_T0

/-- **The job's rows₀ reads the heard alone**, in scope: it reads nothing of a front. -/
theorem rows_heard_rng (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat))
    (first : Nat) (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    RowsOfHeard (rangesTestJob (X' := X') Xs N Pl entry groups first) := by
  intro w fr fr' mem _
  obtain ⟨a1, a2⟩ := first_row_rec (X' := X') hsrc scope w fr
  obtain ⟨b1, b2⟩ := first_row_rec (X' := X') hsrc scope w fr'
  show layOne _ (oM (layoutAt (recRanges Xs N Pl w fr)) 0)
      (oZ (layoutAt (recRanges Xs N Pl w fr)) 0) _ _ =
    layOne _ (oM (layoutAt (recRanges Xs N Pl w fr')) 0)
      (oZ (layoutAt (recRanges Xs N Pl w fr')) 0) _ _
  rw [a1, a2, b1, b2]

end

end ProofFile.Honest.K12.AtKey

#print axioms AtPublicFiles.AtFiles.Full.shape15_of_fold
#print axioms ProofFile.Honest.K12.AtKey.first_row_of_shape
#print axioms ProofFile.Honest.K12.AtKey.first_row_T15
#print axioms ProofFile.Honest.K12.AtKey.first_row_T0
#print axioms ProofFile.Honest.K12.AtKey.first_row_rec
#print axioms ProofFile.Honest.K12.AtKey.rows_heard_rng
