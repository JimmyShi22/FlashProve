-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorOpened.lean

What it proves. A state on entry to a proximity test that is made of the columns which the frame
hands a part (Seen.opened). At the state that midSharedAtW (Honest/MidW.lean) returns in front of a
part of the shared chain, the field opened holds a list of columns, and the description's own fold
over the blocks in front of the part's block returns at the rounds seen of these blocks and at these
columns, with nothing left over; the state's input and how many rounds it has seen are said beside
it, so that what a part's move lays can be held to the fold (fold_at_stand). So at a run of the
frame's walking prover, in front of a called part, the fold returns (fold_at_called); and at the
front that the test's second part lays (rest_front_at). Apart from these, door_of_opened: where such
a fold returns, the state function at the test on G_omega (doorOmegaF, DoorsByShape.lean) at the
reader colsOpened is what the seat's way in makes of the fold's state.

Names.
  colsOpened       the reader: the columns that a front holds; [] where it holds none.
  doorOf_of_fold   where the fold and the way in return, doorOf (JobShared.lean) is what the way in
      returned.
  fold_at_stand    the fold returns at the state that midSharedAtW returns.
  fold_at_called   the same at a run, in front of a called part.
  rest_front_at    the rounds and the columns of restFront (Sim/Row.lean) at such a state.
  door_of_opened   doorOmegaF at colsOpened against such a fold, with no description in it.

By what. live_field (LiveField.lean); walk_mid (Honest/Law/WalkMid.lean); walk_laid_length
(Honest/WalkHeard.lean); stretch_back (Honest/Law/OwedParts.lean); ready_ok (Honest/Law/Run.lean);
envOf_tree (Honest/Law/Cut.lean); exBind_ok, exMap_ok (Honest/Law/Play.lean); called_at_run
(CalledAtRun.lean); fold_like, peel_front (Johnson/Desc/K14/Honest/FlatSteps.lean).

Limits.
- fold_at_stand is a conditional: hm says that the walk is going on in front of the part: it holds
  because a walk that the verifier has stopped returns no state. Nothing here shows that ready or
  runC returns, or that a part is called.
- Of the walk (runC, midSharedAtW), not of play (run, midSharedAt): these hand no columns. Where a
  front holds none, colsOpened is []: a job's state on entry has no way to err (TestJob.rec₀,
  Test.lean); the frame's duty at none is kept around the part, by the guard (FieldGuard.lean), as
  halfO (AtProof/HalfO.lean) lays it. door_of_opened asks that the front holds the columns (ho).
- The stand is the state that midSharedAtW returns. That runC's own walk goes through it is not said
  here.
- door_of_opened: c, Q, sentU, bs, p and pre are free: no verifier stands in it; a caller's terms
  meet it by unfolding. No theorem here calls it at fold_at_stand: the two are not joined. The join
  owes five things: hpre, that the blocks in front are like the front block, bs and the test on G_u;
  that the description's start F.start₂ (F.pub x) is first Q.codes k, at k := P.key x; hk; hr; ho.
  fold_at_stand's clauses and rest_front_at pay the last three, once the caller has that i is the
  first part's number of rounds at the test's second part. That the state
  is the verifier's is not said: the statement is against the fold. Nor that it differs from
  the fall-back.
- The laws stand in front of a part, at the front that its first move lays or, for the test's
  second part, at restFront. Each later move lays its own front; that the rounds seen only grow and
  that the field stays within a sub-protocol is read off the code (MidW.lean).
- What may be said here on hiding, and no more (a rule of use for whoever builds on this file;
  no theorem): «The state on entry reads the key, the rounds shown, and ALL columns opened in front
  of this test, in the order of reading: the stored table's at "LOC"'s positions, computed from the
  index; and those that the test on G_u has read from trees that parts of the run have sent,
  computed from the index AND THE RUN's COINS. Never a word on a simulator at this place without
  «given the key, the rounds shown and all columns opened in front: "LOC"'s, and those that the test
  on G_u has read». The second kind no one can hand a simulator from outside: the simulators of the
  parts in front must have made them. That the field holds columns of the run's view, and that each
  tree's budget counts them, is typed by nobody.»
- The shared chain alone. The test on G_omega alone; the last chain's test has another form of
  front (doorOf's limit).
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorAnyRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St first frontBlock)
open Desc.K14.Honest (Like fold_like peel_front)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC
  midSharedAtW)

/-- **The columns that a front holds**: the reader of a state function that folds at what the frame
hands. [] where it holds none: see the file's limits. -/
def colsOpened {W X : Type} (_ : W) (fr : Front X) : List OpenedColumn := fr.seen.opened.getD []

/-- **Where the fold and the way in return, doorOf is what the way in returned.** -/
theorem doorOf_of_fold {S₀ W X : Type} (bs : List (Block S₀ Unit)) (s₀ : W → S₀)
    (enter : S₀ → Except String T12) (cols : W → Front X → List OpenedColumn) (fall : T12) (w : W)
    (fr : Front X) (x : S₀ × List Fmt.RoundView × List OpenedColumn) (t : T12)
    (h : foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) = .ok x) (he : enter x.1 = .ok t) :
    doorOf bs s₀ enter cols fall w fr = t := by
  unfold doorOf
  rw [h]
  show (enter x.1).toOption.getD fall = t
  rw [he]
  rfl

/-- **At the state that midSharedAtW returns in front of a part of the shared chain** (hm): the
field opened holds columns, and the description's own fold over the blocks in front of the part's
block, from the description's own start at the instance, returns with nothing left over at the
rounds seen of these blocks and at these columns. General in the description, the book, the prover
and the part (i: how many rounds of its block come before it). Beside it: the state's input, and
how many rounds it has seen. On the filling and the book: hR, S. On the run: hm alone: no run of
runC is asked for. -/
theorem fold_at_stand {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i : ℕ) (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    {m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀}
    (hm : midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m)) :
    ∃ (s : F.S₂) (cols : List OpenedColumn), m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧ m.opened = some cols ∧
      foldBlocks 0 pre (F.start₂ (F.pub x)) (m.seen.take (pre.flatMap (·.rounds)).length) cols =
        .ok (s, [], []) := by
  have hi : i < σ.block.rounds.length := by
    have h1 := S.le
    have h2 := S.pos
    omega
  obtain ⟨-, hN, -, -⟩ := ProofFile.Honest.stretch_back S.str S.pos S.fits
  obtain ⟨-, _tr, -, -, hcom, -, -, -⟩ := ProofFile.Honest.ready_ok hR
  unfold midSharedAtW at hm
  obtain ⟨R', hR', h0⟩ := ProofFile.Honest.exBind_ok hm
  rw [hR] at hR'
  cases hR'
  obtain ⟨a₂, ha₂, h1⟩ := ProofFile.Honest.exBind_ok h0
  unfold ProofFile.Honest.midInW at h1
  try simp only at h1
  split at h1
  · cases h1
  · obtain ⟨y, hy, e⟩ := ProofFile.Honest.exMap_ok h1
    rw [hN] at hy
    have hlen : (R.shared.take ((pre.flatMap (·.rounds)).length + i)).length =
        (pre.flatMap (·.rounds)).length + i := by
      rw [List.length_take]
      exact Nat.min_eq_left (by have h3 := S.fits; omega)
    rw [S.cut] at ha₂
    have hLo : ∀ ps, ProofFile.Honest.treeOwn ps =
        (ProofFile.Honest.envOf (P.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
      fun ps => ((ProofFile.Honest.envOf_tree (P.storedWords w₀ rc) ps [] []).1).symm
    obtain ⟨s, cols, -, -, -, -, ho, hf, -⟩ := live_field ⟨1, 0, P.storedWords w₀ rc,
      ProofFile.Honest.treeOwn⟩ hLo pre σ.block t i hi (R.start₂ P) (F.start₂ (F.pub x)) [] ha₂ hy hlen e
    have hw := ProofFile.Honest.walk_mid ha₂ hy e
    have hs : m.seen = ProofFile.Honest.roundsOf y.laid := hw.2.2
    have htake : m.seen.take (pre.flatMap (·.rounds)).length =
        ProofFile.Honest.roundsOf (y.laid.take (pre.flatMap (·.rounds)).length) := by
      rw [hs]
      unfold ProofFile.Honest.roundsOf
      rw [List.map_take]
    refine ⟨s, cols, hw.1.trans hcom, ?_, ?_, ?_⟩
    · rw [hs, ProofFile.Honest.roundsOf_length, ProofFile.Honest.walk_laid_length _ _ _ _ _ hy,
        ProofFile.Honest.start_laid ha₂, hlen]
      exact Nat.zero_add _
    · rw [ho, List.nil_append]
    · rw [htake]
      exact hf

/-- **At a run of the frame's walking prover, in front of a called part of the shared chain, the
fold returns at what the frame hands**: called_at_run for the state, fold_at_stand for the fold.
Public: hpl. On the filling and the book: hR, S. On the run: hrun, hc. Nothing on whether runC
returns or calls the part. -/
theorem fold_at_called {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i : ℕ) (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀) (s : F.S₂) (cols : List OpenedColumn),
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧ m.opened = some cols ∧
      foldBlocks 0 pre (F.start₂ (F.pub x)) (m.seen.take (pre.flatMap (·.rounds)).length) cols =
        .ok (s, [], []) := by
  obtain ⟨m, -, -, -, -, hm, -⟩ := called_at_run hpl hR σ u pre t i S hrun hc
  obtain ⟨s, cols, hin, hl, ho, hf⟩ := fold_at_stand hR σ u pre t i S hm
  exact ⟨m, s, cols, hm, hin, hl, ho, hf⟩

/-- **What the test's second part lays, at such a state**: where the state has seen the N rounds in
front of the test's block and the first part's rounds, restFront has the first N rounds seen, and
the field as it is. -/
theorem rest_front_at {W X : Type} (J : TestJob W X) (m : ProofFile.Honest.Mid W X) (N : ℕ)
    (hl : m.seen.length = N + firstLen J.p.nums.stages) :
    (restFront J m).seen.rounds = m.seen.take N ∧ (restFront J m).seen.opened = m.opened := by
  refine ⟨?_, rfl⟩
  show m.seen.take (m.seen.length - firstLen J.p.nums.stages) = _
  rw [hl, Nat.add_sub_cancel]

/-- **The state function at the test on G_omega, against such a fold, with no description in it.**
pre: blocks of the state St that are, member by member, like the shared chain's front block, the
blocks bs and the test on G_u at the numbers p. Where the fold over pre returns with nothing left
over at rs and cols, doorOmegaF at colsOpened gives what the seat's way in makes of its state, at
every input and front whose readers agree with k, rs and cols. It says nothing of whether that state
differs from the fall-back. -/
theorem door_of_opened {Cl V X : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (bs : List (Block St Unit)) (p : P12)
    (pre : List (Block St Cl))
    (hpre : List.Forall₂ Like pre (frontBlock c ::
      (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])))
    (k : TableKey) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s : St)
    (hfold : foldBlocks 0 pre (first Q.codes k) rs cols = .ok (s, [], []))
    (key : V → TableKey) (w : V) (fr : Front X) (hk : key w = k) (hr : fr.seen.rounds = rs)
    (ho : fr.seen.opened = some cols) :
    VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) s =
      .ok (doorOmegaF Q sentU bs p key colsOpened w fr) := by
  have gE := peel_front c 0 _ _ _ _ _ (fold_like 0 _ _ hpre _ _ _ _ hfold)
  have hx : foldBlocks 0 (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])
      (first Q.codes (key w)) fr.seen.rounds (colsOpened w fr) = .ok (s, [], []) := by
    have e : colsOpened w fr = cols := by
      show fr.seen.opened.getD [] = cols
      rw [ho]
      rfl
    rw [hk, hr, e]
    exact gE
  obtain ⟨t, ht⟩ : ∃ t, VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) s =
      (.ok t : Except String T12) := ⟨_, rfl⟩
  have e : doorOmegaF Q sentU bs p key colsOpened w fr = t :=
    doorOf_of_fold (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])
      (fun w => first Q.codes (key w))
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) colsOpened
      (fallOmega Q sentU p) w fr (s, [], []) t hx ht
  rw [ht, e]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.colsOpened
#print axioms ProofFile.Honest.K12.Light.doorOf_of_fold
#print axioms ProofFile.Honest.K12.Light.fold_at_stand
#print axioms ProofFile.Honest.K12.Light.fold_at_called
#print axioms ProofFile.Honest.K12.Light.rest_front_at
#print axioms ProofFile.Honest.K12.Light.door_of_opened
