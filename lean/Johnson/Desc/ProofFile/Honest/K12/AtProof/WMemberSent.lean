-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/WMemberSent.lean: THE JOIN: W's member of the last chain's
test and the sender that K1's authors lay at M:4 (`wLotAt`, Honest/K1/Law/WSideAtFill.lean): one job
term, at `secondW`'s letters (HalfWAtPure.lean).
The AI review of hiding (its point 1): «(h1) IS MET AT W's MEMBER, BY LEMMAS, AT
widerFillAtCPUOWM», at X := Unit, at `LongLots.plain`, at that one filling; `hf`, `he`, `h` of
`wMember_mem_rows` are premises: the first is (h6), not (h1).

  `lettersW`    `secondW`'s letters in one place: the readers
  `wJobOf`      the job term that both sides hold, at a message
  `wMember_is_sent`   where `jobRealW` returns at `secondW`'s letters: its second member is
                 `memK1` of that job, and the lot's one half is `placeHalf` of that same job, at
                 the same input
  `secondW_letters`   `secondW` is `halfW` at these readers
  `placeJob_data_cut`   a job made by `placeJob` reads of what was heard, message by message, no
                 more than `heardAt` says
  `wMember_rows`   the member's rows at a carried stretch are the sender's at its purse, where
                 the purse agrees with the stretch on the message's coins and the two fronts agree
                 on what the message's data has heard
  `wMember_mem_rows`   the same at `memK1` of the job: what the member lays is `psOfRows` of the
                 sender's rows

What stays, as K1's authors' head has it. THAT `onlineProverFromPublicFiles` RETURNS AT THIS FILLING IS A PREMISE, and of
the filling beneath it nobody states it. `pile` is a letter of `OnlineProverArguments`: nothing is said of what it
yields. The two fronts' agreement and the purse's are premises here: that the run's stretch holds
the sender's coins is not here. o is free; for a join with `half_w_wM` o := OnBytes.secondHashFunction is the
case that matters. The same fence holds the other two members (SendersW.lean).

Limits.
- K1's authors' limits bear on the member: `RowData.readyAt` at a run's list is not named (K13/
  WPair.lean: «WHERE `RowData.readyAt` REJECTS AT THE LIST HEARD THE VALUE MEANS NOTHING»);
  `wDataAt` lays nothing where the pile
  has one row: W's place is another there; one named filling, at `LongLots.plain`.
- `wMember_is_sent` is at X := Unit, as `onlineProverPartsInUse` is.
- Nothing on what a half plays. No run is named.
- What may be said of this pair on hiding stands in the head of HalfW.lean in this folder.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.SendersW
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (FileDescription Place)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest.K12.Light (ManyJob)
open Johnson.Prover.Send (shapeAt)

variable {W₀ : Type}

/-- `secondW`'s readers. -/
def lettersW (I : WiderIn W₀) (Z : Pub) (w : Local W₀ IndexCommitterCoins Inst Cells) : Readers :=
  ⟨w.trace, I.weights Z w.w₀, w.rc⟩

/-- The job term that both sides hold, at a message. -/
def wJobOf {X : Type} (o : SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : Pub) (G : Ground)
    (msg : Array OnBytes.OracleNotice) : K1.SendJob (K1.PlaceIn Inst) X :=
  K1.wJobAt Z.first (K1.wGp Z) 4 msg (K1.lotNo o Z ⟨1, none, 4, .K1⟩) (K13.wDataAt O.pile Z G)

/-- **ONE JOB TERM.** Where `jobRealW` returns at `secondW`'s letters: its second member is `memK1`
of the job, and the lot's one half is `placeHalf` of that same job, at the same input. -/
theorem wMember_is_sent (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Fd : FileDescription Inst) (enter : Fd.S₃ → Except String T12) (Z : Pub) (G : Ground)
    {M : ManyJob (Local W₀ IndexCommitterCoins Inst Cells) Unit}
    (hM : jobRealW S Fd enter O.pile (K1.lotNo o Z) (lettersW I Z) (fun w => I.weights Z w.w₀)
      (fun P w => randAt P w.rc) Z G = some M) :
    ∃ msg fs, OnBytes.linMessageW Z.first.lin = some msg ∧
      M.mems[1]? = some (memK1 (wJobOf o O Z G msg) (inOf (lettersW I Z)) senderW 0 fs) ∧
      (wLotAt (X := Unit) I o O).halves Z G =
        [K1.placeHalf (inOf (lettersW I Z)) (wJobOf o O Z G msg)] := by
  unfold jobRealW at hM
  obtain ⟨F, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hM
  refine ⟨msg, _, hmsg, rfl, ?_⟩
  rw [wLotAt_halves, hmsg]
  rfl

/-- **`secondW` is `halfW` at these readers**, where the three are made. -/
theorem secondW_letters (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Z : Pub} (G : Ground) {six : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)}
    {N : H2U.Places4} {c : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    (h : nowSharedBy (I.weights Z) Z = .ok six) (hN : H2U.placesOfMade Z.made = .ok N)
    (hc : ProofFile.onlineFirstChainAt Z = .ok c) :
    (secondW I o S O Z G : List (Placed _ _ Unit)) =
      halfW S (P5J.F0T o Z N c) VerifiableInference.Desc.K12.Seat.enterOwn O.pile (K1.lotNo o Z)
        (lettersW I Z) (fun w => I.weights Z w.w₀) (fun P w => randAt P w.rc) Z G :=
  secondW_ok I o S O G h hN hc

/-- **A job made by `placeJob` reads of what was heard no more than `heardAt` says**: at two fronts
that agree there, its data is one. -/
theorem placeJob_data_cut {Xi X : Type} (P : VerifiableInference.Desc.K1.Par) (first : Nat)
    (fold : Option (Nat × OnBytes.FoldShape)) (D : RowDataOf Xi) (part : Nat)
    (v : K1.PlaceIn Xi) (fr fr' : Front X)
    (h : ∀ a, fr.heard.take ((D v.x).heardAt a) = fr'.heard.take ((D v.x).heardAt a)) :
    (K1.placeJob (X := X) P first fold D part).data v fr =
      (K1.placeJob (X := X) P first fold D part).data v fr' := by
  funext k r j
  show RowData.at_ _ _ _ _ _ _ = RowData.at_ _ _ _ _ _ _
  unfold RowData.at_
  rw [h]

/-- **THE MEMBER's ROWS ARE THE SENDER's**: at message k of the job, at a purse c that agrees with
the carried stretch on the message's own coins, and at two fronts that agree on what the data has
heard. -/
theorem wMember_rows {Xi X : Type} (P : VerifiableInference.Desc.K1.Par) (first : Nat)
    (fold : Option (Nat × OnBytes.FoldShape)) (D : RowDataOf Xi) (part : Nat)
    (v : K1.PlaceIn Xi) (fr fr' : Front X)
    (h : ∀ a, fr.heard.take ((D v.x).heardAt a) = fr'.heard.take ((D v.x).heardAt a))
    (k : Nat) (hk : k < P.sent.size) (St : Stretch) (c : Cs (K1.dueR P (K1.rideOf fold)))
    (hf : ∀ i, i < (K1.dueMsg P.codes (shapeAt P k) (K1.rideOf fold k)).f →
      K1.cf c ((K1.startR P (K1.rideOf fold) k).f + i) = St.f i)
    (he : ∀ i, i < (K1.dueMsg P.codes (shapeAt P k) (K1.rideOf fold k)).e →
      K1.ce c ((K1.startR P (K1.rideOf fold) k).e + i) = St.e i) :
    K1.rowsR P (K1.rideOf fold) ((K1.placeJob (X := X) P first fold D part).data v fr)
        (csAt _ (K1.startR P (K1.rideOf fold) k) St) k =
      K1.rowsR P (K1.rideOf fold) ((K1.placeJob (X := X) P first fold D part).data v fr') c k := by
  rw [placeJob_data_cut P first fold D part v fr fr' h]
  exact rowsR_csAt P _ _ k hk St c hf he

/-- **What the member lays is the sender's rows, as lists of words**: `wMember_rows` at `memK1` of a
job made by `placeJob`. lift: the input, of the test's. -/
theorem wMember_mem_rows {Xi W X : Type} (P : VerifiableInference.Desc.K1.Par) (first : Nat)
    (fold : Option (Nat × OnBytes.FoldShape)) (D : RowDataOf Xi) (part : Nat)
    (lift : W → K1.PlaceIn Xi) (at_ : Addr) (fs : Option Nat × Option Nat) (w : W)
    (fr fr' : Front X)
    (h : ∀ a, fr.heard.take ((D (lift w).x).heardAt a) = fr'.heard.take ((D (lift w).x).heardAt a))
    (k : Nat) (hk : k < P.sent.size) (St : Stretch) (c : Cs (K1.dueR P (K1.rideOf fold)))
    (hf : ∀ i, i < (K1.dueMsg P.codes (shapeAt P k) (K1.rideOf fold k)).f →
      K1.cf c ((K1.startR P (K1.rideOf fold) k).f + i) = St.f i)
    (he : ∀ i, i < (K1.dueMsg P.codes (shapeAt P k) (K1.rideOf fold k)).e →
      K1.ce c ((K1.startR P (K1.rideOf fold) k).e + i) = St.e i) :
    (memK1 (K1.placeJob (X := X) P first fold D part) lift at_ k fs).rows w fr St =
      psOfRows P k (K1.rowsR P (K1.rideOf fold)
        ((K1.placeJob (X := X) P first fold D part).data (lift w) fr') c k) := by
  show psOfRows P k (K1.rowsR P (K1.rideOf fold) _
    (csAt _ (K1.startR P (K1.rideOf fold) k) St) k) = _
  rw [wMember_rows P first fold D part (lift w) fr fr' h k hk St c hf he]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.lettersW
#print axioms ProofFile.Honest.K12.AtProof.wJobOf
#print axioms ProofFile.Honest.K12.AtProof.wMember_is_sent
#print axioms ProofFile.Honest.K12.AtProof.secondW_letters
#print axioms ProofFile.Honest.K12.AtProof.placeJob_data_cut
#print axioms ProofFile.Honest.K12.AtProof.wMember_rows
#print axioms ProofFile.Honest.K12.AtProof.wMember_mem_rows
