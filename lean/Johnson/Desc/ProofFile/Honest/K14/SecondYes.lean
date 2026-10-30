-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondYes.lean: kind K14: "K14, second part"
(Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean: batchLinearConstraintsSecondPart), at the place ⟨3, none, 0, .K14⟩, the first member of
a proof file's last chain: WHEN ITS decide FUNCTION RETURNS: one list of named tests with code on
the state in front, and: all true, so it returns; and only then. And so, UNDER TWO PREMISES,
Accepted at the member 0 of the last chain's thread (Honest/Thread/Last.lean), at every fall: hblk:
whatever stands at the number 0 of the letters' list declares no round and has batchLinearConstraintsSecondPart p's decide
function (LikeSecond, Honest/K14/SecondBehind.lean); hY: the list is all true wherever the thread
holds in front of the member. It is stated twice: from the thread's sentence Thr (Accepted), and
from the pair of Thr and what is said, ThrS (AcceptedS, Honest/Thread/PaysS.lean).
Definitions with code, and statements with their proofs.

  ok_append, ok_cons   all clauses of a joined list hold just where all of each part hold. (Two
                  lemmas of these names state the like in Johnson/Desc/K12/Law/ChainOf.lean, of
                  another definition ok, Johnson/Desc/K12/Law/PubOk.lean, whose body reads the same)
  adoptP_of_ok, elsewhereP_of_ok, joinP_of_ok   where all clauses of the library's own list hold,
                  the library's function returns: it has no other way to return nothing
  ok_of_adoptP, ok_of_elsewhereP, ok_of_joinP, ok_of_addRowP   the converses. (The library has two
                  of them as clauses of wider statements: ok_of_elsewhereP is the last clause of
                  elsewhereP_inv, Johnson/Desc/Third/Law/Later.lean; ok_of_addRowP the first clause
                  of addRowP_inv, Johnson/Desc/K15/GroundInv.lean)
  takeList S own o d   the tests of takeOver: six under the library's own names, and in the place of
                  its three calls the library's own lists of clauses, called (adoptL 5,
                  elsewhereL 7, joinL 8), each at the state that the call in front of it returns
  takeOver_of_list, list_of_takeOver   all true: takeOver returns; and only then
  secondList p s  **THE LIST**: the member's three own tests, takeList, that the row (Dot) can be
                  made, and the library's eight clauses on laying it (rowL)
  second_yes      **all true: (batchLinearConstraintsSecondPart p).decide s rs gs returns**, at all rounds and groups,
                  which it does not read
  second_only     **and only then**: where it returns, all are true: the list asks no more than the
                  member
  second_accepted, second_acceptedS   **Accepted, and AcceptedS at every Said, at the member 0, at
                  every fall, GENERAL IN THE LETTERS, UNDER hblk AND hY**: hblk: whatever stands at
                  the number 0 of the letters' list is LikeSecond: it declares no round and has
                  batchLinearConstraintsSecondPart p's decide function; hY: under all that AcceptedS itself hands out (for
                  Accepted: wherever the thread holds in front of the member) the list is all true

WHAT THE LIST READS. The state in front alone. In this file's two statements on Accepted the letters
are general: there the state in front of the member 0 is whatever the letter first allows
(Honest/K14/SecondDoor.lean: begun_of_thr). At the library's own description that state is what the
description's start of the last chain has returned of the two earlier chains' last states
(SecondDoor.lean: start_at_last): there, and not at other letters, hY is a sentence on these two
states and the plan. A later test is evaluated at the state that the library's own
functions return from the earlier ones: where an earlier function returns nothing the later tests
are left out, and an earlier test is false.

HOW MANY. Of the member's fourteen names ten stand in the list; the four names of calls ("Omega: its
tree comes in", "Omega: it is sampled there, under the same shape and codes", "Omega: it joins the
own group", "the row (Dot) is laid") are replaced by the twenty-eight clauses beneath them:
thirty-eight tests. SIX OF THEM SAY THAT SOMETHING IS THERE, AND ARE LISTED ONLY WHERE THEY ARE
FALSE: so the list's length is a function of the state: thirty-two where all is there. THE ORDER IS
NOT THE MEMBER's: the look-ups stand in front: for "all true" the order is nothing, but the first
false name of the list need not be the name under which the member rejects.

What is not claimed. That the list is all true at any state: a file that is not part of this tree
evaluates it at small synthetic states; two files above this one give it from shorter lists, which
are premises there (Honest/K14/SecondOwed.lean: owed_list; Honest/K14/SecondDoor.lean: door_owed).
That hblk holds at any letters (at the library's own description: SecondDoor.lean: like_at_last).
That the thread holds at any run. That the prover's side of the step is ever had at the member
(Plays): where it is not, Accepted holds for nothing. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondBehind
import Johnson.Desc.ProofFile.Honest.K14.FitsPaid
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Desc.Third.Law.Keeps
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linDotRow linLayOmega linLayW OracleNotice)
open Desc.Plain (DState)
open VerifiableInference.Desc (Block Place OpenedColumn named need step_iff)
open VerifiableInference.Desc.Ground (Clauses ok has adoptL adoptP elsewhereL elsewhereP joinL joinP
  rowL addRowP)
open VerifiableInference.Desc.Third (S₃ P₁₄ Loc₃ SharedOut batchLinearConstraintsSecondPart takeOver plainArm firstStepB)
open VerifiableInference.Desc.Third.Law (ok_of_bind some_of_named true_of_need)
open Desc.K14 (St)

/-! ## The library's three functions return where their own lists hold -/

/-- All clauses of two lists in a row hold just where all of each hold. -/
theorem ok_append (a b : Clauses) : ok (a ++ b) = (ok a && ok b) := by
  unfold ok
  rw [List.all_append]

/-- The like for one clause in front of a list. -/
theorem ok_cons (x : String × Bool) (l : Clauses) : ok (x :: l) = (x.2 && ok l) := rfl

variable {L : Type}

/-- Where all five clauses of adoptL hold, adoptP returns. -/
theorem adoptP_of_ok (d : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (h : ok (adoptL d.st d.book sent given) = true) : ∃ a, adoptP d sent given = some a := by
  unfold adoptP
  rw [if_pos h]
  simp only [ok, adoptL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, h5⟩ := h
  cases hl : VerifiableInference.Desc.Own.treesMade d.st.codes sent with
  | none => rw [hl] at h5; cases h5
  | some lay => exact ⟨_, rfl⟩

/-- Where all seven clauses of elsewhereL hold, elsewhereP returns. -/
theorem elsewhereP_of_ok (d : DState L) (mine : Nat) (other : OnBytes.Statement) (theirs : Nat)
    (h : ok (elsewhereL d.st mine other theirs) = true) :
    ∃ d', elsewhereP d mine other theirs = some d' := by
  unfold elsewhereP
  rw [if_pos h]
  simp only [ok, elsewhereL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, h2, -⟩ := h
  cases hy : other.oracles[theirs]? with
  | none => rw [hy] at h2; cases h2
  | some y => exact ⟨_, rfl⟩

/-- Where all eight clauses of joinL hold, joinP returns. -/
theorem joinP_of_ok (d : DState L) (g o : Nat) (kept : Bool)
    (h : ok (joinL d.st g o kept) = true) : ∃ d', joinP d g o kept = some d' := by
  unfold joinP
  rw [if_pos h]
  simp only [ok, joinL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  cases hG : d.st.groups[g]? with
  | none => rw [hG] at h1; cases h1
  | some G => exact ⟨_, rfl⟩

/-- And only there: where adoptP returns, all five clauses of adoptL hold. -/
theorem ok_of_adoptP (d : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (a : Array Nat × DState L) (h : adoptP d sent given = some a) :
    ok (adoptL d.st d.book sent given) = true := by
  unfold adoptP at h
  split at h
  · assumption
  · cases h

/-- Where elsewhereP returns, all seven clauses of elsewhereL hold. -/
theorem ok_of_elsewhereP (d d' : DState L) (mine : Nat) (other : OnBytes.Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') :
    ok (elsewhereL d.st mine other theirs) = true := by
  unfold elsewhereP at h
  split at h
  · assumption
  · cases h

/-- Where joinP returns, all eight clauses of joinL hold. -/
theorem ok_of_joinP (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : ok (joinL d.st g o kept) = true := by
  unfold joinP at h
  split at h
  · assumption
  · cases h

/-- Where addRowP returns, all eight clauses of rowL hold. -/
theorem ok_of_addRowP (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : ok (rowL d.st g row) = true := by
  unfold addRowP at h
  split at h
  · assumption
  · cases h

/-! ## The taking-over -/

/-- **The tests of takeOver**: six under the library's own names; in the place of its three calls,
whose names are not in the list, the library's own lists of clauses (adoptL, elsewhereL, joinL).
Where adoptP or elsewhereP returns nothing the later tests are left out (the two arms that give the
empty list): a clause of that function's own list is false there (adoptP_of_ok,
elsewhereP_of_ok). -/
def takeList (S : OnBytes.Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃) :
    Clauses :=
  match o.book.place[o.omega]? with
  | none => [("Omega: it has a place in the shared chain's book", false)]
  | some q =>
  match o.book.trees[q.1]? with
  | none => [("Omega: its tree is in the shared chain's book", false)]
  | some t =>
  match o.st.oracles[o.omega]? with
  | none => [("Omega: it is in the shared chain's statement", false)]
  | some y =>
    ("Omega: it has a tree to itself", t.parts.size == 1) ::
    ("Omega: it has the plan's shape", decide (y.shape = S.omega)) ::
    (adoptL d.st d.book #[{ shape := y.shape, leafClass := S.omegaLeafClass }]
      #[(t.number, t.src)] ++
    match adoptP d #[{ shape := y.shape, leafClass := S.omegaLeafClass }] #[(t.number, t.src)] with
    | none => []
    | some a =>
    match a.1[0]? with
    | none => [("Omega: its number here", false)]
    | some mine =>
      elsewhereL a.2.st mine o.st o.omega ++
      match elsewhereP a.2 mine o.st o.omega with
      | none => []
      | some d₁ => joinL d₁.st own mine false)

/-- All true: takeOver returns. -/
theorem takeOver_of_list (S : OnBytes.Params.LinShape) (own : Nat) (o : SharedOut)
    (d : DState Loc₃) (h : ok (takeList S own o d) = true) : ∃ r, takeOver S own o d = .ok r := by
  unfold takeList at h
  unfold takeOver
  cases hq : o.book.place[o.omega]? with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    dsimp only at h
    cases ht : o.book.trees[q.1]? with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      dsimp only at h
      cases hy : o.st.oracles[o.omega]? with
      | none => rw [hy] at h; cases h
      | some y =>
        rw [hy] at h
        dsimp only at h
        rw [ok_cons, ok_cons, ok_append, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true] at h
        obtain ⟨h3, h5, hA, h⟩ := h
        obtain ⟨a, ha⟩ := adoptP_of_ok d _ _ hA
        rw [ha] at h
        dsimp only at h
        cases hm : a.1[0]? with
        | none => rw [hm] at h; cases h
        | some mine =>
          rw [hm] at h
          dsimp only at h
          rw [ok_append, Bool.and_eq_true] at h
          obtain ⟨hE, h⟩ := h
          obtain ⟨d₁, hd₁⟩ := elsewhereP_of_ok a.2 mine o.st o.omega hE
          rw [hd₁] at h
          obtain ⟨d₂, hd₂⟩ := joinP_of_ok d₁ own mine false h
          have h3' : (t.parts.size == 1) = true := h3
          have h5' : decide (y.shape = S.omega) = true := h5
          refine ⟨(mine, d₂), ?_⟩
          simp [named, need, bind, Except.bind, pure, Except.pure, ht, h3', h5', ha, hm, hd₁, hd₂]

/-- And only then: where takeOver returns, all are true. -/
theorem list_of_takeOver (S : OnBytes.Params.LinShape) (own : Nat) (o : SharedOut)
    (d : DState Loc₃) (r : Nat × DState Loc₃) (h : takeOver S own o d = .ok r) :
    ok (takeList S own o d) = true := by
  unfold takeOver at h
  obtain ⟨q, hq, h⟩ := ok_of_bind h
  obtain ⟨t, ht, h⟩ := ok_of_bind h
  obtain ⟨_, h3, h⟩ := ok_of_bind h
  obtain ⟨y, hy, h⟩ := ok_of_bind h
  obtain ⟨_, h5, h⟩ := ok_of_bind h
  obtain ⟨a, ha, h⟩ := ok_of_bind h
  obtain ⟨mine, hm, h⟩ := ok_of_bind h
  obtain ⟨d₁, h1, h⟩ := ok_of_bind h
  obtain ⟨d₂, h2, -⟩ := ok_of_bind h
  unfold takeList
  rw [some_of_named hq]
  dsimp only
  rw [some_of_named ht]
  dsimp only
  rw [some_of_named hy]
  dsimp only
  rw [ok_cons, ok_cons, ok_append, some_of_named ha]
  dsimp only
  rw [some_of_named hm]
  dsimp only
  rw [ok_append, some_of_named h1, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true]
  exact ⟨true_of_need h3, true_of_need h5, ok_of_adoptP _ _ _ _ (some_of_named ha),
    ok_of_elsewhereP _ _ _ _ _ (some_of_named h1), ok_of_joinP _ _ _ _ _ (some_of_named h2)⟩

/-! ## The member -/

/-- **THE LIST**: the member's three own tests, takeList, that the row (Dot) can be made, and the
library's eight clauses on laying it (rowL). Where takeOver returns an error the later tests are
left out (the arm that gives the empty list): a test of takeList is false there
(takeOver_of_list). -/
def secondList (p : P₁₄) (s : S₃) : Clauses :=
  match s.loc.border with
  | none => [("the two ends are at hand", false)]
  | some x =>
    ("the shape does not split the row (Dot)", plainArm p.S) ::
    ("no root is received yet, and the first own tree's number counts just one tree more",
      firstStepB s.roots s.loc.firstTree s.book) ::
    (takeList p.S s.loc.own x.shared (s.withCols []) ++
    match takeOver p.S s.loc.own x.shared (s.withCols []) with
    | .error _ => []
    | .ok a =>
      match linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S) with
      | none => [("the row (Dot) can be made", false)]
      | some dot => rowL a.2.st s.loc.own dot)

/-- **All true: the member's decide function returns.** -/
theorem second_yes {Cl : Type} (p : P₁₄) (s : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : ok (secondList p s) = true) :
    ∃ s', (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s' := by
  unfold secondList at h
  cases hx : s.loc.border with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    dsimp only at h
    rw [ok_cons, ok_cons, ok_append, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h2, h3, hT, h⟩ := h
    obtain ⟨a, ha⟩ := takeOver_of_list _ _ _ _ hT
    rw [ha] at h
    dsimp only at h
    cases hd : linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
        (linLayW a.2.st.codes p.S) with
    | none => rw [hd] at h; cases h
    | some dot =>
      rw [hd] at h
      obtain ⟨b, hb⟩ : ∃ b, addRowP a.2 s.loc.own dot = some b := by
        unfold addRowP
        rw [if_pos h]
        exact ⟨_, rfl⟩
      have h2' : plainArm p.S = true := h2
      have h3' : firstStepB s.roots s.loc.firstTree s.book = true := h3
      refine ⟨{ st := b.st, book := b.book, roots := b.roots
                loc := { s.loc with border := none, omega := a.1 } }, ?_⟩
      simp [batchLinearConstraintsSecondPart, named, need, bind, Except.bind, pure, Except.pure, hx, h2', h3', ha, hd, hb]

/-- **And only then**: where it returns, all are true: the list asks no more than the member. -/
theorem second_only {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') : ok (secondList p s) = true := by
  simp only [batchLinearConstraintsSecondPart] at h
  obtain ⟨x, hx, h⟩ := ok_of_bind h
  obtain ⟨_, h2, h⟩ := ok_of_bind h
  obtain ⟨_, h3, h⟩ := ok_of_bind h
  obtain ⟨a, ha, h⟩ := ok_of_bind h
  obtain ⟨dot, hd, h⟩ := ok_of_bind h
  obtain ⟨b, hb, -⟩ := ok_of_bind h
  unfold secondList
  rw [some_of_named hx]
  dsimp only
  rw [ok_cons, ok_cons, ok_append, ha]
  dsimp only
  rw [some_of_named hd, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨true_of_need h2, true_of_need h3, list_of_takeOver _ _ _ _ _ ha,
    ok_of_addRowP _ _ _ _ (some_of_named hb)⟩

/-! ## Accepted -/

section accepted
variable {Bk : ProverCoinCounts} {S₂ Cl W₀ Rc Xi Tr X P₁ Wt : Type}
  (L : LastThread.Letters Bk S₂ S₃ Cl W₀ Rc Xi Tr X P₁ Wt) (p : P₁₄)

/-- **AcceptedS at the member 0, at every Said and every fall, general in the letters, under hblk
and hY.** hblk: whatever stands at the number 0 of the letters' list is LikeSecond: it declares no
round and has batchLinearConstraintsSecondPart p's decide function. hY: UNDER ALL THAT AcceptedS ITSELF HANDS OUT (the pair
in front of the member, challenges that fit, nothing of the member stops, the fall says nothing, the
prover's side of the step) the list is all true. -/
theorem second_acceptedS (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hY : ∀ blk, L.bs[0]? = some blk → ∀ k s m E ds y cols, ThrS L.thread Said 0 k s m E →
      drawsFit blk.rounds ds = true →
      chainStopAt (L.thread.φ.sees m.st.input) [blk] L.thread.hs m.loc ds = none →
      fall 0 s ds = none → L.thread.Moved blk k m E ds y cols → ok (secondList p s) = true) :
    AcceptedS L.thread Said fall 0 := by
  intro blk hb k s m E ds y cols hA hd hst hfl hMv
  have hfit := fitsAt_none (T := L.thread) (b := 0) (fun blk hb => (hblk blk hb).rounds) blk hb k
    m E ds y cols hd hMv
  obtain ⟨s', hs⟩ := second_yes (Cl := Cl) p s
    ((roundsOf y.1).map VerifiableInference.Desc.noDigest)
    (blk.shown L.thread.ft (roundsOf y.1) cols) (hY blk hb k s m E ds y cols hA hd hst hfl hMv)
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, (step_iff _ _ _ _ _ _ _).2 ⟨hfit, ?_, hw.symm⟩⟩
  rw [(hblk blk hb).decide]
  exact hs

/-- **Accepted at the member 0, at every fall, general in the letters, under hblk and hY.** hblk:
whatever stands at the number 0 of the letters' list is LikeSecond. hY: at every state at which the
thread holds in front of the member the list is all true. It is second_acceptedS where nothing is
said, with less handed to hY. -/
theorem second_accepted (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hY : ∀ k s m E, Thr L.thread 0 k s m E → ok (secondList p s) = true)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) : Accepted L.thread fall 0 :=
  fun blk hb k s m E ds y cols hA =>
    second_acceptedS L p (fun _ _ _ => True) fall hblk
      (fun _ _ k s m E _ _ _ h _ _ _ _ => hY k s m E h.1) blk hb k s m E ds y cols ⟨hA, trivial⟩

end accepted

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.ok_append
#print axioms ProofFile.Honest.K14.ok_cons
#print axioms ProofFile.Honest.K14.ok_of_adoptP
#print axioms ProofFile.Honest.K14.ok_of_elsewhereP
#print axioms ProofFile.Honest.K14.ok_of_joinP
#print axioms ProofFile.Honest.K14.ok_of_addRowP
#print axioms ProofFile.Honest.K14.list_of_takeOver
#print axioms ProofFile.Honest.K14.second_only
#print axioms ProofFile.Honest.K14.second_acceptedS
#print axioms ProofFile.Honest.K14.second_accepted
#print axioms ProofFile.Honest.K14.adoptP_of_ok
#print axioms ProofFile.Honest.K14.elsewhereP_of_ok
#print axioms ProofFile.Honest.K14.joinP_of_ok
#print axioms ProofFile.Honest.K14.takeOver_of_list
#print axioms ProofFile.Honest.K14.second_yes
