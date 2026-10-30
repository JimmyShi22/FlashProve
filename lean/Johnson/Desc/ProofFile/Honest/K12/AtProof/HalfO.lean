-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfO.lean: the prover's side of the proximity test on
G_omega of the proof file's shared chain, beside HalfU.lean's test on G_u. It is made of a public
part and of one thing that a filling of the honest prover (OnlineProverParts,
Johnson/Desc/ProofFile/Honest/AtPure.lean) holds already: its reader of the index. For the field
OnlineProverParts.shared. Definitions with code, and one statement on public letters.

  jobRealO       the job: jobAtOmega (JobShared.lean) at the public part's own letters: the
                 sendings' public data (sendPub, Members.lean), the two tests' numbers (four,
                 Places.lean), what goes out with o_u (sentOf, NearAtHead.lean), the kind K14's
                 eight sub-protocols (Desc.K14.blocks). Its state on entry is doorOmegaF
                 (DoorsByShape.lean) at the columns that the frame hands (colsOpened,
                 DoorOpened.lean). The vector of o_omega is the sending's own text at the challenges
                 heard (its last argument is none). Nothing where one of the public letters is not
                 made, and nothing where the plan has no test on G_omega
  realO, halfO   the job as a TestJob; its pair of parts at the test's place, behind the guard
                 (FieldGuard.lean in the folder above): at every move, where no columns are
                 handed, the error
  withHalfO      FOR A TOY ALONE: a filling with the pair behind its shared chain's other sides
                 (withShared, Doors.lean), without the arm (HalfOAtPure.lean)
  realO_bare     the job's place, members and word on the fresh table are the bare job's (bareO,
                 Bare.lean)
  jobAtOmega_rand   rand reaches no row of jobAtOmega, with no vector handed in: by uAtE_rand,
                 omegaAtE_rand, memOmega_rand

What parts from the test on G_u. The door's reader: at G_u it is colsLoc at the stored columns,
which is what the letter enc feeds; here the door reads what the run has opened. So jobRealO has the
letter wt alone, where jobRealU has wt and enc. randAt stands here as in jobRealU; rand reaches no
row of jobAtOmega (jobAtOmega_rand, with no vector handed in). The fresh table is the test's own.

Limits. Nothing is played here, and nothing says that a sub-protocol accepts what the pair sends.
The door has been evaluated at a small made-up plan alone (SmallRunO.lean, on no row): a test,
which pays nothing here.
The state on entry is doorOmegaF's: where its fold fails it falls back, without a warning, on
a state that is not shown to be the verifier's. That the fold returns at the walk's state is
fold_at_stand (DoorOpened.lean), and what the door then gives is door_of_opened; they are not called
here, and that the filling's blocks in front are like bs and the test on G_u is not shown here.
At a player that hands no columns (run, midAt, midSharedAt) the pair errs at its first round: the
frame's duty on Seen.opened, kept by the guard, since a job's state on entry has no way to err. No
law at these three may be drawn with halfO laid.
- What may be said here on hiding, and no more (a rule of use for whoever builds on this file;
  no theorem): «The state on entry reads the key, the rounds shown, and ALL columns opened in front
  of this test, in the order of reading: the stored table's at "LOC"'s positions, computed from the
  index; and those that the test on G_u has read from trees that parts of the run have sent,
  computed from the index AND THE RUN's COINS. Never a word on a simulator at this place without
  «given the key, the rounds shown and all columns opened in front: "LOC"'s, and those that the test
  on G_u has read». The second kind no one can hand a simulator from outside: the simulators of the
  parts in front must have made them. That the field holds columns of the run's view, and that each
  tree's budget counts them, is typed by nobody.»
withHalfO's reader wt is a free letter, as withHalfU's is: nothing holds it against the reader with
which the filling's other sides were made; with two readers the test's rows are not the sender's.
Where four, F.O, sendPub or Desc.K14.blocks gives nothing, halfO is the empty list and withHalfO
returns the filling's own sides, without a word; where the library's withU refuses, sentOf is the
empty array, without a word (it reaches the fall-back alone).
The test on G_omega alone. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfU
import Johnson.Desc.ProofFile.Honest.K12.DoorOpened
import Johnson.Desc.ProofFile.Honest.K12.FieldGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (TableKey)
open ProofFile.Honest.K12.Light (ManyJob jobAtOmega doorOmegaF colsOpened sentOf)

variable {W₀ Tr X : Type}

/-- **The job at the test on G_omega, at a public part.** wt: the reader of the index. Of the
randomness rc it reads randAt A.P w.rc, the pad and the tail of the plan's item, through askOf;
this reaches no row of this job (jobAtOmega_rand).
The last none is omega?: no vector is handed in: the sending's own text computes o_omega's at the
challenges heard. The job's field fresh is none (jobAtOmega): its first fold sends its own fresh
table, which stands in the tree of its own that jobAtOmega's list lays last. -/
def jobRealO (wt : W₀ → Weights) (Z : Pub) :
    Option (ManyJob (Common W₀ IndexCommitterCoins TableKey) Unit) :=
  (four Z).bind fun F => F.O.bind fun pO => (sendPub Z).bind fun A =>
    (Desc.K14.blocks A.P).map fun bs =>
      jobAtOmega A pO (doorOmegaF A.P (sentOf A.P.S) bs F.U (fun w => w.key) colsOpened)
        (fun w => wt w.w₀) (fun w => randAt A.P w.rc) none

/-- The same as a TestJob. -/
def realO (wt : W₀ → Weights) (Z : Pub) : Option (TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) :=
  (jobRealO wt Z).map (·.toRun.toTest)

/-- **The pair of parts at the test's place, behind the guard**; no side where the job is not
made. -/
def halfO (wt : W₀ → Weights) (Z : Pub) :
    List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit) :=
  (realO wt Z).toList.map fun J => (proverSideOfProximityTest J : Placed Empty _ Unit).needsField

/-- **A filling with the pair behind its shared chain's other sides. FOR A TOY ALONE**: it lays
without the arm (HalfOAtPure.lean: sharedWithUO is the term to lay). wt: a free letter. -/
def withHalfO (P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X) (wt : Pub → W₀ → Weights) : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X :=
  withShared P fun Z => halfO (wt Z) Z

/-- The shared sum reads its summands below n alone. -/
theorem sumE_below (n : ℕ) (f g : ℕ → OnBytes.E) (h : ∀ t < n, f t = g t) :
    Desc.K14.Law.sumE n f = Desc.K14.Law.sumE n g := by
  unfold Desc.K14.Law.sumE
  exact List.foldl_ext _ _ _ fun a b hb => by rw [h b (List.mem_range.1 hb)]

/-- At a place that holds the matrix the folded row reads no pad or tail of the index committer. -/
theorem uAtE_rand (S : OnBytes.Params.LinShape) (psi : List OnBytes.E) (w : Weights)
    (c c' : TableRand) (k : ℕ) (hk : k < S.matrixRows * 2 ^ S.kLo) :
    Desc.K14.Honest.uAtE S psi (ProofFile.Honest.K14.rowsOf S w c) k =
      Desc.K14.Honest.uAtE S psi (ProofFile.Honest.K14.rowsOf S w c') k := by
  unfold Desc.K14.Honest.uAtE Desc.K14.Honest.uHonE Desc.K14.Honest.foldRowsE
  split
  · refine sumE_below _ _ _ fun r _ => ?_
    have e : ProofFile.Honest.K14.rowsOf S w c r k = ProofFile.Honest.K14.rowsOf S w c' r k := by
      unfold ProofFile.Honest.K14.rowsOf
      rw [if_pos hk, if_pos hk]
    rw [e]
  · rfl

/-- **omega_col reads no pad or tail of the index committer.** -/
theorem omegaAtE_rand (S : OnBytes.Params.LinShape) (psi : List OnBytes.E) (w : Weights)
    (c c' : TableRand) :
    Desc.K14.Honest.omegaAtE S psi (ProofFile.Honest.K14.rowsOf S w c) =
      Desc.K14.Honest.omegaAtE S psi (ProofFile.Honest.K14.rowsOf S w c') := by
  funext j
  unfold Desc.K14.Honest.omegaAtE Desc.K14.Honest.omegaHonE
  split
  · rename_i hj
    refine sumE_below _ _ _ fun t ht => ?_
    have h1 : 2 ^ S.kLo * (j + 1) ≤ 2 ^ S.kLo * S.matrixRows := Nat.mul_le_mul_left _ hj
    rw [Nat.mul_add, Nat.mul_one] at h1
    have hk : t + 2 ^ S.kLo * j < S.matrixRows * 2 ^ S.kLo := by
      rw [Nat.mul_comm S.matrixRows]
      omega
    rw [uAtE_rand S _ w c c' _ hk]
  · rfl

/-- A member of the sending of o_omega and o_sp, at two readers of the committer's values, has one
reader of rows. -/
theorem memOmega_rand {W X : Type} (A : ProofFile.Honest.K14.SendPub) (wt : W → Weights)
    (r r' : W → TableRand) (a : ProofFile.Honest.Addr) (k : ℕ) (fs : Option ℕ × Option ℕ) :
    (ProofFile.Honest.K12.Light.memOfSending (ProofFile.Honest.K14.jobOmega A) a k fs
        (ProofFile.Honest.K12.Light.askOf A wt r) none : ProofFile.Honest.K12.Light.Mem W X).rows =
      (ProofFile.Honest.K12.Light.memOfSending (ProofFile.Honest.K14.jobOmega A) a k fs
        (ProofFile.Honest.K12.Light.askOf A wt r') none : ProofFile.Honest.K12.Light.Mem W X).rows := by
  funext w fr c
  have e : (ProofFile.Honest.K14.jobOmega A).data ⟨ProofFile.Honest.K12.Light.askOf A wt r w, fr.heard, ()⟩ k =
      (ProofFile.Honest.K14.jobOmega A).data ⟨ProofFile.Honest.K12.Light.askOf A wt r' w, fr.heard, ()⟩ k :=
    omegaAtE_rand A.P.S _ (wt w) (r w) (r' w)
  simp only [ProofFile.Honest.K12.Light.memOfSending, e]

/-- **rand reaches no row of jobAtOmega**: with no vector handed in, two readers of the committer's
values give one reader of rows at each member. wt is one. -/
theorem jobAtOmega_rand {W X : Type} (A : ProofFile.Honest.K14.SendPub)
    (p : VerifiableInference.Desc.K12.P12)
    (door : W → ProofFile.Honest.Front X → VerifiableInference.Desc.K12.T12) (wt : W → Weights)
    (r r' : W → TableRand) :
    (ProofFile.Honest.K12.Light.jobAtOmega A p door wt r none).mems.map (·.rows) =
      (ProofFile.Honest.K12.Light.jobAtOmega A p door wt r' none).mems.map (·.rows) := by
  show [(ProofFile.Honest.K12.Light.memOfSending (ProofFile.Honest.K14.jobOmega A) _ 0 _
        (ProofFile.Honest.K12.Light.askOf A wt r) none : ProofFile.Honest.K12.Light.Mem W X).rows,
      (ProofFile.Honest.K12.Light.memOfSending (ProofFile.Honest.K14.jobOmega A) _ 1 _
        (ProofFile.Honest.K12.Light.askOf A wt r) none : ProofFile.Honest.K12.Light.Mem W X).rows] =
    [(ProofFile.Honest.K12.Light.memOfSending (ProofFile.Honest.K14.jobOmega A) _ 0 _
        (ProofFile.Honest.K12.Light.askOf A wt r') none : ProofFile.Honest.K12.Light.Mem W X).rows,
      (ProofFile.Honest.K12.Light.memOfSending (ProofFile.Honest.K14.jobOmega A) _ 1 _
        (ProofFile.Honest.K12.Light.askOf A wt r') none : ProofFile.Honest.K12.Light.Mem W X).rows]
  rw [memOmega_rand A wt r r', memOmega_rand A wt r r']

/-- **The job's place, members and word on the fresh table are the bare job's.** -/
theorem realO_bare (wt : W₀ → Weights) (Z : Pub) (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit)
    (h : realO wt Z = some J) :
    ∃ J₀ : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit, bareO Z = some J₀ ∧ J.p = J₀.p ∧
      J.members = J₀.members ∧ J.fresh = J₀.fresh := by
  unfold realO jobRealO at h
  cases hF : four Z with
  | none => rw [hF] at h; cases h
  | some F =>
    cases hO : F.O with
    | none => rw [hF] at h; simp [hO] at h
    | some p =>
      cases hA : sendPub Z with
      | none => rw [hF] at h; simp [hA] at h
      | some A =>
        cases hb : Desc.K14.blocks A.P with
        | none => rw [hF] at h; simp [hA, hb] at h
        | some bs =>
          rw [hF] at h
          simp only [Option.bind_some, hO, hA, hb, Option.map_some, Option.some.injEq] at h
          subst h
          refine ⟨bareJob p (membersO A) freshO, ?_, rfl, rfl, rfl⟩
          unfold bareO
          simp only [hF, Option.bind_some, hO, hA, Option.map_some]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.jobRealO
#print axioms ProofFile.Honest.K12.AtProof.realO
#print axioms ProofFile.Honest.K12.AtProof.halfO
#print axioms ProofFile.Honest.K12.AtProof.withHalfO
#print axioms ProofFile.Honest.K12.AtProof.sumE_below
#print axioms ProofFile.Honest.K12.AtProof.uAtE_rand
#print axioms ProofFile.Honest.K12.AtProof.omegaAtE_rand
#print axioms ProofFile.Honest.K12.AtProof.memOmega_rand
#print axioms ProofFile.Honest.K12.AtProof.jobAtOmega_rand
#print axioms ProofFile.Honest.K12.AtProof.realO_bare
