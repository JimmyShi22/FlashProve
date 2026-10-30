-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesJob.lean: THE JOB OF THE KEY FILE's TEST ON THE RANGES: what a caller of the proximity
test's two parts owes (`TestJob`, Johnson/Desc/ProofFile/Honest/K12/Test.lean), at the first chain's
thread (`laid₁`, E2E/KeyRest.lean). The verifier's state that the test is entered with is made BY
REPLAY: the description's own first fifteen sub-protocols are run over the rounds shown so far; no
column is needed for that (E2E/KeyRangesFront.lean). The rows and the tree are made of the sending
of the multiplicities (`msgJob`, E2E/KeySendJobs.lean) by `jobOne`
(Johnson/Desc/ProofFile/Honest/K12/JobOne.lean). Definitions with code, statements and proofs.

  `recRanges`    THE STATE IN FRONT, of the input and the rounds shown
  **`rec_of_thr`**   in scope, where the thread stands at the border 15: that function's value IS
                 the structure that the test's seat makes of the verifier's state there
  `enter_passes`   where the seat's three tests on the state and its tests on the structure pass,
                 the seat's entering returns that structure
  **`enters_of_thr`**   THE CLAUSE "enters" of `K12At` and `K12Front`, from the thread and these two
  `sentRanges`, **`rangesTestJob`**   what is taken of the sending; THE JOB
  `jobRng_p`, `jobRng_fresh`, `jobRng_rows`   its place is the description's; its fresh table has
                 come earlier; its first stage's rows read the one member's stretch alone

Limits. `Enters` (E2E/KeyRangesSeat.lean) and "the seat's tests on the structure pass" are asked in
`enters_of_thr`; both are met at the thread in E2E/KeyRangesSeated.lean. NOTHING IS SHOWN OF THE
JOB's DATA HERE: the public clauses of `jobOne`'s laws (`OneFits`) are met at this place by
`front_data_KR` (Johnson/Desc/ProofFile/Honest/K12/FrontAtKey.lean), under hypotheses of its own,
among them that the state on entry has the written shape; that the open rows say true things of the
member's words is not touched. That the member's count of coins is the book's:
E2E/KeyRangesLends.lean. THE LETTER first IS READ BY NOTHING: `sentRanges` takes of the sending its
public data and its data, and neither reads it. groups is read in the public data's field of that
name alone; for the table that the frame's play sends it has to be the description's own list: not
said here. `sentRanges` takes the sending's data at an empty front: that data reads no front.
NO GUARD STANDS AT THIS PAIR: it reads no opened column, so it plays at run and midAt too, and
behind a refusal it speaks at recRanges' default. So a law at run or midAt on what this pair sends
speaks «at a state on entry that is made of the plan's public part, not shown to be the verifier's»
(said of the text; no theorem).
Nothing on completeness, on soundness or on what is hidden.

-/
import E2E.KeyRangesFront
import E2E.KeyRangesSeat
import E2E.KeyBookHeldK1Jobs
import E2E.KeyTestSizes
import Johnson.Desc.ProofFile.Honest.K12.JobOne
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place foldBlocks)
open VerifiableInference.Desc.K12 (T12 P12)
open VerifiableInference.Desc.Key (Xi FirstState Claim enterRanges leaveRanges enterAndAsk
  rangesParams asksOnRecord rangesRecord pieces)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription Enters enterRanges_passes rangesState)
open AtPublicFiles.Key (msgJob)
open AtPublicFiles.KeyBook (rideMsg)
open AtPublicFiles.KeyTest (sMsg)
open OnBytes.Slice (GF)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K12 (TestJob OneSent jobOne rows_one frontOf Stretch)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)

/-- **The verifier's state that the test is entered with**, by replay: the description's own first
fifteen sub-protocols over the rounds shown; where they do not return, the structure at the chain's
first state. -/
def recRanges (w : Local W₀ Rc Xi Unit) (fr : Front X') : T12 :=
  match foldBlocks 0 ((D Xs N Pl).first.blocksInOrder.take 15) ((D Xs N Pl).start₁ ((D Xs N Pl).pub w.x))
      fr.seen.rounds [] with
  | .ok x => rangesState x.1
  | .error _ => rangesState ((D Xs N Pl).start₁ ((D Xs N Pl).pub w.x))

variable (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **Where the thread stands at the border 15 the replay gives the seat's structure.** -/
theorem rec_of_thr (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl) {k : Coins Bk}
    {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E) :
    recRanges (X' := X') Xs N Pl m.st.input (frontOf m) = rangesState s := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, cols, hb, hc, hf⟩, -, -⟩ := hT
  rw [colsTo15 Xs N Pl L w₀ rc x hs tb scope h m E] at hc
  obtain rfl := Except.ok.inj hc
  have hb' : s₀ = (D Xs N Pl).start₁ ((D Xs N Pl).pub m.st.input.x) := hb
  subst hb'
  have hf' : foldBlocks 0 ((D Xs N Pl).first.blocksInOrder.take 15)
      ((D Xs N Pl).start₁ ((D Xs N Pl).pub m.st.input.x)) m.seen [] = .ok (s, [], []) := hf
  unfold recRanges
  show (match foldBlocks 0 ((D Xs N Pl).first.blocksInOrder.take 15)
      ((D Xs N Pl).start₁ ((D Xs N Pl).pub m.st.input.x)) m.seen [] with
    | .ok x => rangesState x.1
    | .error _ => _) = _
  rw [hf']

end

/-- The seat's entering returns the structure. -/
theorem enter_passes (one : OnBytes.Params.OneTime) (p : P12) (s : FirstState) (hE : Enters one s)
    (hA : asksOnRecord p (rangesState s) = .ok ()) :
    enterAndAsk (enterRanges one) p s = .ok (rangesState s) := by
  unfold enterAndAsk rangesRecord
  rw [enterRanges_passes one s hE]
  show (asksOnRecord p (rangesState s)).map (fun _ => rangesState s) = _
  rw [hA]
  rfl

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀)
  (rc : Rc) (x : Xi) (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **The clause "enters".** -/
theorem enters_of_thr (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl) {k : Coins Bk}
    {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E) (hE : Enters Xs.Y.k.oneTime s)
    (hA : asksOnRecord (rangesParams N) (rangesState s) = .ok ()) :
    enterAndAsk (enterRanges Xs.Y.k.oneTime) (rangesParams N) s =
      .ok (recRanges (X' := X') Xs N Pl m.st.input (frontOf m)) := by
  rw [rec_of_thr Xs N Pl L w₀ rc x hs tb scope h hT]
  exact enter_passes _ _ s hE hA

end

section Job
variable {W₀ Rc X' : Type} (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- What is taken of the sending of the multiplicities. Its data are read at the empty front, at
which no column is handed: `Seen.bare []`. -/
def sentRanges : OneSent (Local W₀ Rc Xi Unit) where
  P := (msgJob (X := Unit) entry Xs.Y.k.oneTime pieces groups first rideMsg).P
  ride := rideMsg
  data := fun w => (msgJob (X := Unit) entry Xs.Y.k.oneTime pieces groups first rideMsg).data w
    ⟨[], (), Seen.bare []⟩
  addr := sMsg

/-- **The job.** -/
def rangesTestJob : TestJob (Local W₀ Rc Xi Unit) X' :=
  jobOne (rangesParams N) (sentRanges Xs entry groups first) (recRanges Xs N Pl)

theorem jobRng_p : (rangesTestJob (X' := X') Xs N Pl entry groups first).p = rangesParams N := rfl

theorem jobRng_fresh : (rangesTestJob (X' := X') Xs N Pl entry groups first).fresh = some (sMsg, 1) := rfl

theorem jobRng_rows (w : Local W₀ Rc Xi Unit) (fr : Front X') (mem mem' : Nat → Stretch)
    (h : ∀ t, t < (rangesTestJob (X' := X') Xs N Pl entry groups first).members.length →
      mem t = mem' t) :
    (rangesTestJob (X' := X') Xs N Pl entry groups first).rows₀ w fr mem =
      (rangesTestJob (X' := X') Xs N Pl entry groups first).rows₀ w fr mem' :=
  rows_one _ _ _ w fr mem mem' h

end Job

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.rec_of_thr
#print axioms AtPublicFiles.KeyThread.enter_passes
#print axioms AtPublicFiles.KeyThread.enters_of_thr
#print axioms AtPublicFiles.KeyThread.jobRng_p
#print axioms AtPublicFiles.KeyThread.jobRng_fresh
#print axioms AtPublicFiles.KeyThread.jobRng_rows
