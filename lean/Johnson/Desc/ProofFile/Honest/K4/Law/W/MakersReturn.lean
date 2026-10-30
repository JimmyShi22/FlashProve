-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MakersReturn.lean: CONDITIONAL. Statements with their proofs.

Not shown here. No property is claimed. THAT THE PREMISES CAN BE MET: no example is known. NOTHING
ON ANY VALUE: that a maker returns, and that what it returns has its call's public shape, hangs on
lengths alone; what the jobs hold is other statements' matter. HERE `K4Seated.fits` IS SPENT: at
shapes that do not fit these statements say nothing.

What is here: at a stand (`K4Stand`, Law/SlotsTrue.lean) of the layers' own rounds (the sub-protocol
K4) the honest side's makers for the second token sumcheck and for the batched sumcheck return, at
the run's own input and at the challenges heard in front of each; and the batched sumcheck's true
end values are made at its own challenges. These returns are hypotheses of the statements on the
honest words of the two sumchecks (Law/W/RightTermsOf.lean, Law/W/BackOfLed.lean);
Law/W/FootAtStand.lean calls them. They stand beside `tabs_at` (Law/W/ItemRightOf.lean) and
`makersNorms_at` (Law/W/MakersAt.lean), which have the like for four other sumchecks. Calls:
`terms_run` and `stack_run` (Law/SumAtRun2.lean: from the public test to the makers at a run);
`stack_ends_some` (Law/StackCube.lean); `stand_own_fits` (Law/OwnAtStand.lean), so that no
hypothesis on the challenges' shape is asked.

THE PREMISES: `K4Stand`, and `Thr`, the thread's own proposition on a stand
(Honest/Thread/Thr.lean): by it the seat's field `fits` gives the public test `k4Fits` at what the
lookup has sampled at the run and at the run's tokens.

  `stand_run`   what the two calls share: the public test at the run; the run's challenges cut at a
      round's number; the lookup's sampled values' lengths
  `termsJob_at`   **the second token sumcheck: what its two jobs share is made, the job is made,
      and it has its call's public shape**
  `termsJob_foot`   the first two, as `rightFoot_at` (Law/W/FootAtStand.lean) calls them
  `stackJob_at`   **the batched sumcheck: its data are made AT EVERY LIST OF SHOWN VALUES, the job
      of these data has its call's public shape, and its true end values are made at its own
      challenges**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.SumAtRun2
import Johnson.Desc.ProofFile.Honest.K4.Law.StackCube
import Johnson.Desc.ProofFile.Honest.K4.Law.StackPass
import Johnson.Desc.ProofFile.Honest.K4.Law.LookSkel
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightTermsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- What the two calls share, at a stand: the public test at the run; the run's challenges cut at a
round's number; the lookup's sampled values' lengths. -/
theorem stand_run
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) :
    k4Fits Q (look Q m.st.heard) (k4Wit Q cells weights tokens (look Q) m.st.input).tokv = true ∧
      (∀ n, n ≤ ds.length → ((m.st.heard ++ ds.take n).drop Q.r0).length = n) ∧
      ∀ n, LookSkel ((k4Wit Q cells weights tokens (look Q) m.st.input).look
        ((m.st.heard ++ ds.take n).take Q.r0)) (look Q m.st.heard) := by
  have Se := Z.seat
  have hh := k4_heard_front Se hT
  refine ⟨Se.fits m.st.heard m.st.input hT.2.1 hT.2.2.2.2.2.2, fun n hn => ?_, fun n => ?_⟩
  · rw [k4_own_drop Se hT, List.length_take]
    exact Nat.min_eq_left hn
  · have tk : (m.st.heard ++ ds.take n).take Q.r0 = m.st.heard := by
      rw [← hh]
      exact List.take_left
    rw [tk]
    exact lookSkel_refl _

/-- **THE SECOND TOKEN SUMCHECK's MAKERS RETURN AT A STAND**, at the run's input and the challenges
heard in front of the sumcheck; the job has its call's public shape. CONDITIONAL on the stand and on
Thr. -/
theorem termsJob_at
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) :
    ∃ (S : OnBytes.Desc.First.K4.Honest.Sides) (J : Job),
      OnBytes.Desc.First.K4.Honest.Sides.of Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (pts3 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) = some S ∧
      jobTermsOn S = some J ∧ k4JobFits ((k4Shapes Q).getD 2 ⟨0, [], none⟩) J = true := by
  obtain ⟨hk, ln, hL⟩ := stand_run Z hT
  have hr := stand_reach Z
  obtain ⟨_, _, e2, _, _, _, _⟩ := k4StartAt_eq Q
  have l2 : rJ3 Q.P Q.g ≤ ds.length := by
    rw [← e2]
    refine Nat.le_trans ?_ hr
    simp only [k4StartAt]
    omega
  have s2 : (starts Q).getD 2 0 = rJ3 Q.P Q.g := by rw [k4_starts]; rfl
  exact terms_run (k4Wit Q cells weights tokens (look Q) m.st.input) hk
    (m.st.heard ++ ds.take (rJ3 Q.P Q.g)) (stand_own_fits Z hT _) (by rw [ln _ l2, s2]) (hL _)

/-- The same without the shape, as `rightFoot_at` (Law/W/FootAtStand.lean) calls it. -/
theorem termsJob_foot
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) :
    ∃ (S : OnBytes.Desc.First.K4.Honest.Sides) (J : Job),
      OnBytes.Desc.First.K4.Honest.Sides.of Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (pts3 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) = some S ∧
      jobTermsOn S = some J := by
  obtain ⟨S, J, hS, hJ, _⟩ := termsJob_at Z hT
  exact ⟨S, J, hS, hJ⟩

/-- **THE BATCHED SUMCHECK's MAKER RETURNS AT A STAND**, at the run's input, the challenges heard in
front of the sumcheck and EVERY list sh of shown values; the job of these data has its call's public
shape; its true end values are made at the sumcheck's own challenges. CONDITIONAL on the stand and
on Thr. -/
theorem stackJob_at
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (sh : Array OnBytes.E) :
    ∃ (SD : StackData) (e : List OnBytes.E),
      stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) sh = some SD ∧
      SD.endsAt (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).toArray.reverse = some e ∧
      k4JobFits ((k4Shapes Q).getD 3 ⟨0, [], none⟩) (jobStackOn SD) = true := by
  obtain ⟨hk, ln, hL⟩ := stand_run Z hT
  have hr := stand_reach Z
  obtain ⟨_, _, _, e3, _, _, _⟩ := k4StartAt_eq Q
  have l4 : rJ4 Q.P Q.g + 1 + Q.hp.lamS ≤ ds.length := by
    rw [← e3]
    refine Nat.le_trans ?_ hr
    simp only [k4StartAt]
    omega
  have s3 : (starts Q).getD 3 0 = rJ4 Q.P Q.g := by rw [k4_starts]; rfl
  obtain ⟨SD, hD, hfit⟩ := stack_run (k4Wit Q cells weights tokens (look Q) m.st.input) hk
    (m.st.heard ++ ds.take (rJ4 Q.P Q.g)) (stand_own_fits Z hT _)
    (by rw [ln _ (by omega), s3]) (hL _) sh
  have hD' := hD
  unfold stackData at hD'
  obtain ⟨S, hS, hOn⟩ := Option.bind_eq_some_iff.mp hD'
  have eQ : SD.S.Q = Q := by rw [(stackDataOn_open hOn).1]; exact (sidesOf_pub hS).1
  have hfit' : k4JobFits (k4PlainShape SD.S.Q.hp.lamS 2
      (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0))) (jobStackOn SD) = true := by
    rw [eQ]
    exact hfit
  obtain ⟨e, he, _⟩ := stack_ends_some hfit' (by omega) (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS)
    (by
      rw [ownE_length _ _ _ l4]
      show Q.hp.lamS = SD.S.Q.hp.lamS
      rw [eQ])
  exact ⟨SD, e, hD, he, hfit⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.stand_run
#print axioms ProofFile.Honest.K4.W.termsJob_at
#print axioms ProofFile.Honest.K4.W.termsJob_foot
#print axioms ProofFile.Honest.K4.W.stackJob_at
