-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/AtWiderAt.lean: CONDITIONAL.

What is here. THE STATEMENTS ON THE MEMBER OF THE LAYERS' OWN ROUNDS (kind K4) AT THE MAKER's
PROVER, AT ONE WRITTEN FILLING: `widerFillOwn` (Honest/AtPureWiderAt.lean), general in the type of
the index and in the sides' own state; `widerFillAt` (in that file too) is
that filling at chosen arguments. Its list of lots
holds K4's lot wrapped: `HLot.byPub I.weights fun wt => K4.k4HLot id wt fun _ _ => K4.k4LookAt`: the
reader of the index is a function of the public part. Here that membership is a statement
(`k4Lot_mem_widerOwn`); the wrapped lot's halves at a public part are those of K4's lot at that
part's reader, by unfolding (the frame's lemma `HLot.byPub_halves`, Honest/AtPureWiderLots.lean,
says so; no statement here calls it); and six statements in the form with hM and hE
(Law/SeatedAtBy.lean, Law/TopsAt.lean) are said again at that filling without the two, at cells :=
id and weights := I.weights A.Z and, in the three whose other form leaves it free, look := fun _ _
=> k4LookAt. What it is for: that the six fit that filling's own term is held by Lean here, and by
nothing else. Statements with their proofs: one call each.

  `k4Lot_mem_widerOwn`   **K4's wrapped lot is among the filling's lots**: the seventh of ten.
  `k4Seated_widerAt`, `k4Seated_ready_widerAt`, `k4Seated_run_widerAt`, `k4_plays_widerAt`,
  `k4_playsS_widerAt`, `k4_accepted_widerAt`   the six.

Limits. CONDITIONAL: the six on h · LaidK4 · hA · ho; `k4Seated_widerAt` besides on hVd; the two at
a run that is made ready on hR and hmark in its stead (hR: `ready` returns R; in
`k4Seated_run_widerAt` at the maker's own book: there it asks, at every place at which a half
stands, that the book's cut, rows and entries are the half's (`chainSteps`, Honest/Frame.lean); no
statement of this folder speaks of that book); `k4_accepted_widerAt` besides on hs (the list of
falls holds K4's own list: every longer list is the weaker way; K4's second fall is not in the
list). THAT THE FRAME's MAKER `onlineProverFromPublicFiles` (Honest/AtPure.lean) RETURNS AT THAT FILLING (hA) IS SHOWN
HERE OF NO FILES; no statement or test in that file or here runs the maker at it. ho (every other
lot of the filling has no half at a place of the kind K4, or K4's halves): shown here of none of the
nine. WHAT THAT FILLING LACKS, by its own files' heads: no prover's side for K1 at the place of the
message "W", nor for K9, K10 and K12; the second chain has none; the shared chain has none where
`nowSharedBy` returns an error; nothing compares `WiderIn.trace` with `WiderIn.weights`; the lists
in L are arguments (K1's too, where `LongLots` has that field: then the clause on K1 holds at
`LongLots.plain`, not at a free L). Three of the six (`Plays`, `PlaysS`, `AcceptedS`: each, like
`K4Seated`, the form of a hypothesis of the threads' rule: Honest/Thread/Pays.lean, PaysS.lean;
Law/Seated.lean) speak only where the thread stands in front of K4's member: how a run of that
filling's prover gets there is not said here. Of h together with hA · LaidK4 · ho · hVd · hR · hmark
· hs no example is known to us. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h
holds of any files is not shown here: the side library AtFullSide proves, with no hypothesis, that h
has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). The limits of the statements that are called are theirs here
too. If that filling's list turns, in its order or in K4's entry, this file no longer compiles.
IT IS A LAW, NOT A
PART: it rests on modules under Johnson/Goal/: no file that defines a part may build on it; it
states no goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedAtBy
import Johnson.Desc.ProofFile.Honest.K4.Law.TopsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {W₀ X : Type}

/-- **K4's wrapped lot is among the lots of `widerFillOwn`**: the seventh of ten. -/
theorem k4Lot_mem_widerOwn (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    HLot.byPub I.weights (fun wt => k4HLot (Rc := IndexCommitterCoins) (Tr := Cells) (X := X) id wt
      fun _ _ => k4LookAt) ∈ (widerFillOwn own₀ L I o S O).lots :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.head _))))))

variable {own₀ : X} {L : LongLots W₀ X} {I : WiderIn W₀} {o : SecondHashFunctionArgument}
  {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- CONDITIONAL: on h, hA, Lh, ho and hVd. **`K4Seated` AT THE MAKER's PROVER AT THAT FILLING.** -/
theorem k4Seated_widerAt {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hVd : Vd w₁ → reqFine Zp w₁.x.pub = true) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k id (I.weights A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_lookAt_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Lh id (I.weights A.Z)
    (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho hVd

/-- CONDITIONAL: on h, hA, Lh, ho, hR and hmark. **THE SAME AT THE INPUT OF A RUN THAT IS MADE
READY.** -/
theorem k4Seated_ready_widerAt {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G)
    {w₀ : W₀} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {kc : Coins Bk}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit X}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk A.H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k id (I.weights
      A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_ready_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp hA Lh id (I.weights A.Z)
    (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho hR hmark

/-- CONDITIONAL: on h, hA, Lh and ho. **`Plays` AT THE MAKER's PROVER AT THAT FILLING.** -/
theorem k4_plays_widerAt {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G) :
    Plays (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k :=
  k4_plays_by h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Lh id (I.weights A.Z)
    (fun _ _ => k4LookAt) (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho

/-- CONDITIONAL: on h, hA, Lh and ho. **`PlaysS` AT THE MAKER's PROVER AT THAT FILLING.** -/
theorem k4_playsS_widerAt {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) X → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k :=
  k4_playsS_by h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh id (I.weights A.Z)
    (fun _ _ => k4LookAt) (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho

/-- CONDITIONAL: on h, hA, Lh, ho and hs. **`AcceptedS` AT THE MAKER's PROVER AT THAT FILLING**, at
every list of falls that holds K4's own list. -/
theorem k4_accepted_widerAt {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) X → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G)
    {fs : List (Fall TS)} (hs : ∀ f ∈ k4LotFalls A.Z A.G, f ∈ fs) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said
      (fallsBy fs cF.blocksInOrder) k :=
  k4_accepted_falls_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh id (I.weights A.Z)
    (fun _ _ => k4LookAt) (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho hs

end

/-- CONDITIONAL: on h, hA, Lh, ho, hR and hmark. **`K4Seated` WITH hR AT WHAT THE MAKER RETURNS**:
its own description A.F, book A.B and prover A.H. No round is played: `ready` lays a run. -/
theorem k4Seated_run_widerAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
    (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G)
    {w₀ : W₀} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {kc : Coins A.B}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit X}
    (hR : ready A.F A.B A.H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k id (I.weights
      A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_run_at h hA Q test carryX item n₁ n₂ b₀ Vd Rd Kp Lh id (I.weights A.Z)
    (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho hR hmark

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Lot_mem_widerOwn
#print axioms ProofFile.Honest.K4.k4Seated_widerAt
#print axioms ProofFile.Honest.K4.k4Seated_ready_widerAt
#print axioms ProofFile.Honest.K4.k4_plays_widerAt
#print axioms ProofFile.Honest.K4.k4_playsS_widerAt
#print axioms ProofFile.Honest.K4.k4_accepted_widerAt
#print axioms ProofFile.Honest.K4.k4Seated_run_widerAt
