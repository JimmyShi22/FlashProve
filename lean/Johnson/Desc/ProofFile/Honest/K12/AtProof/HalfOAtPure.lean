-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfOAtPure.lean: the pair at the proximity test on
G_omega (halfO, HalfO.lean in this folder) at a filling of the honest prover (OnlineProverParts,
Johnson/Desc/ProofFile/Honest/AtPure.lean): what it lays, beside the pair at the test on G_u; the
frame's authors' filling widerFillOwnCP (Honest/AtPureWiderK12.lean) with the six and both pairs,
as widerFillOwnCPU (Honest/AtPureWiderK12U.lean) has the six and the one; and under the library's
head the job that is handed. Three definitions; fourteen theorems.

  withHalfO_shared, withHalfO_enc, shared_at_pure_O   what withHalfO lays, and what onlineProverFromPublicFiles's prover
                 then holds in the shared chain
  sharedWithUO   the shared chain's sides: the six, the pair on G_u, the pair on G_omega; no side at
                 all where the six are not made
  widerFillOwnCPUO, widerFillAtCPUO   widerFillOwnCPU and widerFillAtCPU with that field
  sharedWithUO_ok, sharedWithUO_error   the two arms
  sharedWithUO_withHalfO   where the six are made the field is that of withHalfO over withHalfU, at
                 this filling's reader
  widerFillOwnCPUO_shared, _lots, _second, _enc   the fields
  realO_at_head, halfO_at_head   under the head the real job is jobAtOmega at the head's letters,
                 and halfO is its pair behind the guard
  someO_at_head, halfO_made_at_head   under the head the planner gives a test on G_omega: so where
                 the eight are made the pair is there

Why the arm. As at the test on G_u (Honest/AtPureWiderK12U.lean, «Why the arm»): the maker of the
six rejects where the tests on the shape refuse; the pairs are laid only where the six are made. By
reading these texts; no lemma. JobShared.lean's head names these tests for both jobs, and its fault
in rowsOf reaches jobAtOmega through askOf too. withHalfO (HalfO.lean) lays without the arm:
sharedWithUO is the term to lay.

Limits.
- A SILENT DEFAULT: no side of the shared chain where nowSharedBy returns an error. A second: no
  pair at G_omega where four, F.O, sendPub or Desc.K14.blocks gives nothing.
- WHERE COLUMNS ARE HANDED THE TWO PARTS CANNOT REFUSE (Honest/K12/Parts.lean); at none they err,
  by the guard: having a side is no ground. That a part plays is not said here. door_omega_at_run
  (K12/DoorOmegaAtRun.lean) and atHandAtO_at_run (AtHandO.lean in this folder, which stands over
  this file) are what is had of its state on entry, at a run of the walk, under premises.
- At a player that hands no columns the pair errs: HalfO.lean's limits.
- wt is one reader at all places in sharedWithUO; in withHalfO it is a free letter.
- Over the frame's authors' text: the limits of Honest/AtPureWiderK12U.lean and of HalfO.lean hold,
  among them the lending of o_sp's values at three places, now with this pair laid: owed before
  any count. One does not carry over as it reads: its words on a simulator at the test on G_u name
  the stored columns that "LOC" opens: the words for this place stand below.
- realO_at_head and halfO_at_head take hO as a premise: someO_at_head pays it under the head.
- What may be said here on hiding, and no more (a rule of use for whoever builds on this file;
  no theorem): «The state on entry reads the key, the rounds shown, and ALL columns opened in front
  of this test, in the order of reading: the stored table's at "LOC"'s positions, computed from the
  index; and those that the test on G_u has read from trees that parts of the run have sent,
  computed from the index AND THE RUN's COINS. Never a word on a simulator at this place without
  «given the key, the rounds shown and all columns opened in front: "LOC"'s, and those that the test
  on G_u has read». The second kind no one can hand a simulator from outside: the simulators of the
  parts in front must have made them. That the field holds columns of the run's view, and that each
  tree's budget counts them, is typed by nobody.»
- That onlineProverFromPublicFiles returns at these fields, that ready does, that a part plays: none is stated here.
- Nothing is evaluated here. It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfO
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfAtPure
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12U

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)
open ProofFile.Honest.K12.Light (jobAtOmega doorOmegaF colsOpened sentOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

section
variable {W₀ Tr X : Type} {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}

/-- What withHalfO lays in the shared chain. -/
theorem withHalfO_shared (P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X) (wt : Pub → W₀ → Weights) (Z : Pub)
    (G : Ground) : (withHalfO P wt).shared Z G = P.shared Z G ++ halfO (wt Z) Z := rfl

/-- It leaves the columns as they are. -/
theorem withHalfO_enc (P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X) (wt : Pub → W₀ → Weights) :
    (withHalfO P wt).enc = P.enc := rfl

/-- **What onlineProverFromPublicFiles's prover holds in the shared chain at a filling with the pair.** -/
theorem shared_at_pure_O {P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X} {wt : Pub → W₀ → Weights}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Tr Unit X} (h : onlineProverFromPublicFiles o' pol lay KL (withHalfO P wt) = .ok A) :
    A.H.shared = P.shared A.Z A.G ++ halfO (wt A.Z) A.Z := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok h
  rw [hs]
  rfl

/-- **The shared chain's sides: the six, the pair on G_u, the pair on G_omega.** A SILENT DEFAULT:
no side at all where the six are not made. THE ARM IS LOAD-BEARING: NEVER LAY halfO WITHOUT IT (the
file's head); withHalfO is for a toy alone. One reader of the index at every place. WHERE COLUMNS
ARE HANDED THE TWO PARTS CANNOT REFUSE: having a side is no ground that they play. -/
def sharedWithUO (I : WiderIn W₀) (Z : Pub) :
    List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit) :=
  match nowSharedBy (I.weights Z) Z with
  | .ok six =>
    six ++ halfU (I.weights Z) (fun w => Bind.ForProver.encW Z (I.weights Z w)) Z ++
      halfO (I.weights Z) Z
  | .error _ => []

/-- **widerFillOwnCPU with the pair at the test on G_omega behind that on G_u.** The arguments are
widerFillOwn's. A TERM: BY ITSELF FOR NO FILLING OF RECORD. The honest prover's filling is built on
it by two further updates (widerFillOwnCPUOW: the field second; widerFillOwnCPUOWM: one lot more),
which leave the field shared as it is laid here. THE LENDING OF o_sp's VALUES IS NOT PAID HERE (the
head's Limits). AtFullSide/K12/LettersAtHead.lean states it under the head, at whatever book the
maker returns: one owner and one start, each entry by name (`one_coin_at_filling`), and one coin at
the three places (`osp_one_coin_at_filling`). -/
def widerFillOwnCPUO (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) : OnlineProverParts W₀ IndexCommitterCoins Cells Unit X :=
  { widerFillOwnCP own₀ L I o S O with shared := fun Z _ => sharedWithUO I Z }

/-- **widerFillAtCPU's sister with both pairs.** FOR NO FILLING OF RECORD: no other term is built
on it. -/
def widerFillAtCPUO (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts W₀ IndexCommitterCoins Cells Unit Unit :=
  widerFillOwnCPUO () (LongLots.plain o S O) I o S O

/-- **Where the six are made**: the field of widerFillOwnCPU, then the pair on G_omega. -/
theorem sharedWithUO_ok (I : WiderIn W₀) {Z : Pub}
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)}
    (h : nowSharedBy (I.weights Z) Z = .ok six) :
    sharedWithUO I Z = sharedWithU I Z ++ halfO (I.weights Z) Z := by
  rw [sharedWithU_ok I h]
  show (match nowSharedBy (I.weights Z) Z with
    | .ok six =>
      six ++ halfU (I.weights Z) (fun w => Bind.ForProver.encW Z (I.weights Z w)) Z ++
        halfO (I.weights Z) Z
    | .error _ => []) = _
  rw [h]

/-- **Where they are not made**: no side. -/
theorem sharedWithUO_error (I : WiderIn W₀) {Z : Pub} {e : String}
    (h : nowSharedBy (I.weights Z) Z = .error e) : sharedWithUO I Z = [] := by
  show (match nowSharedBy (I.weights Z) Z with
    | .ok six =>
      six ++ halfU (I.weights Z) (fun w => Bind.ForProver.encW Z (I.weights Z w)) Z ++
        halfO (I.weights Z) Z
    | .error _ => []) = _
  rw [h]

/-- **Where the six are made the field is that of withHalfO over withHalfU at this filling's
reader.** -/
theorem sharedWithUO_withHalfO (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Z : Pub} (G : Ground)
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)}
    (h : nowSharedBy (I.weights Z) Z = .ok six) :
    sharedWithUO I Z =
      (withHalfO (withHalfU (widerFillOwnCP own₀ L I o S O) I.weights) I.weights).shared Z G := by
  rw [sharedWithUO_ok I h, sharedWithU_withHalfU own₀ L I o S O G h]
  rfl

/-- The field shared. -/
theorem widerFillOwnCPUO_shared (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    (widerFillOwnCPUO own₀ L I o S O).shared Z G = sharedWithUO I Z := rfl

/-- The field lots is widerFillOwnCP's. -/
theorem widerFillOwnCPUO_lots (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnCPUO own₀ L I o S O).lots = (widerFillOwnCP own₀ L I o S O).lots := rfl

/-- The field second is widerFillOwnCP's. -/
theorem widerFillOwnCPUO_second (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnCPUO own₀ L I o S O).second = (widerFillOwnCP own₀ L I o S O).second := rfl

/-- The field enc. -/
theorem widerFillOwnCPUO_enc (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) :
    (widerFillOwnCPUO own₀ L I o S O).enc Z = fun w => Bind.ForProver.encW Z (I.weights Z w) := rfl

end

/-- **Under the head the real job is jobAtOmega at the head's letters**, at the numbers pO that the
planner gives the test. -/
theorem realO_at_head {W₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (wt : W₀ → Weights) {pO : P12} (hO : (fourOf Np).O = some pO) :
    realO wt Zp = some (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
        (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8]
          (fourOf Np).U (fun w : Common W₀ IndexCommitterCoins TableKey => w.key) colsOpened)
        (fun w => wt w.w₀) (fun w => randAt (K1.qAt Zp Np) w.rc) none).toRun.toTest := by
  unfold realO jobRealO
  rw [(Light.stages_at_head h).1, sendPub_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb]
  simp only [Option.bind_some, hO, hb, Option.map_some]

/-- So halfO is that job's pair, behind the guard. -/
theorem halfO_at_head {W₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (wt : W₀ → Weights) {pO : P12} (hO : (fourOf Np).O = some pO) :
    halfO wt Zp = [(proverSideOfProximityTest (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
                         (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8]
                           (fourOf Np).U (fun w : Common W₀ IndexCommitterCoins TableKey => w.key) colsOpened)
                         (fun w => wt w.w₀) (fun w => randAt (K1.qAt Zp Np) w.rc) none).toRun.toTest :
          Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit).needsField] := by
  unfold halfO
  rw [realO_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb wt hO]
  rfl

/-- **Under the head the planner gives a test on G_omega.** -/
theorem someO_at_head (h : P5J.AtMg o Z D r₀ Zp Np cF) : ∃ pO : P12, (fourOf Np).O = some pO := by
  obtain ⟨-, -, ⟨p, hp, -⟩, -⟩ := Light.stages_at_head h
  exact ⟨p, hp⟩

/-- **So under the head, where the eight are made, the pair is there**: halfO is no empty list. -/
theorem halfO_made_at_head {W₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (wt : W₀ → Weights) : halfO wt Zp ≠ [] := by
  obtain ⟨pO, hO⟩ := someO_at_head h
  rw [halfO_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb wt hO]
  exact List.cons_ne_nil _ _

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.withHalfO_shared
#print axioms ProofFile.Honest.K12.AtProof.withHalfO_enc
#print axioms ProofFile.Honest.K12.AtProof.shared_at_pure_O
#print axioms ProofFile.Honest.K12.AtProof.sharedWithUO
#print axioms ProofFile.Honest.K12.AtProof.widerFillOwnCPUO
#print axioms ProofFile.Honest.K12.AtProof.widerFillAtCPUO
#print axioms ProofFile.Honest.K12.AtProof.sharedWithUO_ok
#print axioms ProofFile.Honest.K12.AtProof.sharedWithUO_error
#print axioms ProofFile.Honest.K12.AtProof.sharedWithUO_withHalfO
#print axioms ProofFile.Honest.K12.AtProof.widerFillOwnCPUO_shared
#print axioms ProofFile.Honest.K12.AtProof.widerFillOwnCPUO_lots
#print axioms ProofFile.Honest.K12.AtProof.widerFillOwnCPUO_second
#print axioms ProofFile.Honest.K12.AtProof.widerFillOwnCPUO_enc
#print axioms ProofFile.Honest.K12.AtProof.realO_at_head
#print axioms ProofFile.Honest.K12.AtProof.halfO_at_head
#print axioms ProofFile.Honest.K12.AtProof.someO_at_head
#print axioms ProofFile.Honest.K12.AtProof.halfO_made_at_head
