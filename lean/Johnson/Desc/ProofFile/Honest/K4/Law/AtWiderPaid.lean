-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/AtWiderPaid.lean: CONDITIONAL.

What is here. ho, THE HYPOTHESIS ON THE OTHER LOTS, IS PROVED AT `widerFillAt`
(Honest/AtPureWiderAt.lean). ho: each lot of the filling has no half at a place of the kind K4, or
has the halves of the lot of the layers' own rounds (kind K4). half: at the place of K4's member the
first chain of the prover that the frame's maker `onlineProverFromPublicFiles` returns holds K4's own half. `ho_widerAt`
(Law/AtWiderKinds.lean) has ho at that filling from `WiderKinds` (Honest/Thread/FirstFill.lean):
each lot's halves stand at places of its own kind. `FirstFill.widerKinds`
(Honest/Thread/FirstFillAll.lean) proves `WiderKinds` at every public part and ground, with no
hypothesis. So ho holds
there with no hypothesis; and half, and the nine statements of Law/AtWiderKindsTops.lean, no longer
ask it. Each of the nine here is that file's statement with the binder K struck; each proof is one
call at K := `FirstFill.widerKinds`. Statements with their proofs.

  `ho_widerAt_paid`   **ho at `widerFillAt`: no hypothesis.**
  `half_widerAt`   half at `widerFillAt`, from h, LaidK4 and hA.
  `k4Seated_widerPaid`, `k4Seated_ready_widerPaid`, `k4Seated_run_widerPaid`   `K4Seated`.
  `k4_plays_widerPaid`, `k4_playsS_widerPaid`   `Plays`, `PlaysS`.
  `k4_accepted_widerPaid`   `AcceptedS`.
  `k4_exchange_wo_widerPaid`, `k4_exchange_wo_parts_widerPaid`,
  `k4_exchange_wo_index_widerPaid`   `ExchangeAtS` at the pending row's item `Item.wo m`.

Limits. `ho_widerAt_paid` has no hypothesis and is general in the public part and the ground.
CONDITIONAL: all else on h · LaidK4 · hA (the maker returns at that filling: shown here of no
files), and each of the nine on what its source statement asks besides. AT `widerFillAt` ALONE: for
`widerFillOwn` with a free `LongLots` L, ho stays a hypothesis. All limits of
the source statements (Law/AtWiderAt.lean, Law/AtWiderAtWo.lean, Law/AtWiderKinds.lean) hold here:
they speak only where the thread stands in front of K4's member. Beneath `half_widerOwn`, on which
half and the nine stand, are comparisons by Lean's own kernel that no independent checker has
replayed (Law/HalfAtPure.lean's head names them). THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH
ALONE; that h holds of any files is not shown here: the side library AtFullSide proves, with no
hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with
LaidK4 · hA and a statement's own hypotheses (hVd · hR · hmark · hs · hZ · hEn · hI · K4MaskTieAt ·
K4IndexTieAt · K4WeightsTieK) no example is known to us. Honest/Thread/FirstFillAll.lean,
Honest/AtPureWiderAt.lean and the files beside the library that they import are no part of the
library yet. IT IS A LAW, NOT A PART: it rests on modules under Johnson/Goal/: no file that defines
a part may build on it; it states no goal. Nothing on soundness, on completeness or on any other
property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.K4.Law.AtWiderKindsTops

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading)
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}
  {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}

/-- **ho AT `widerFillAt`: NO HYPOTHESIS.** -/
theorem ho_widerAt_paid (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ M' ∈ (widerFillAt I o S O).lots, (∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) ∨
      M'.halves Zq G = (k4HLot id (I.weights Zq) (fun _ _ => k4LookAt)).halves Zq G :=
  ho_widerAt (FirstFill.widerKinds I o S O Zq G)

/-- CONDITIONAL: on h, Lh and hA. **half AT `widerFillAt`.** -/
theorem half_widerAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) :
    A.H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half id (I.weights A.Z) k4Tokens (k4LookAt) (k4PubAt cF k x)) :=
  half_widerKinds h Lh hA (FirstFill.widerKinds I o S O A.Z A.G)

/-- CONDITIONAL: on h, hA, Lh, hR and hmark. `k4Seated_run_widerAt` at `widerFillAt`, with ho paid.
-/
theorem k4Seated_run_widerPaid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
    (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {w₀ : W₀} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {kc : Coins A.B}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (hR : ready A.F A.B A.H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k id (I.weights
      A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_run_widerKinds h hA Q test carryX item n₁ n₂ b₀ Vd Rd Kp Lh (FirstFill.widerKinds I o S
    O A.Z A.G) hR hmark

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- CONDITIONAL: on h, hA, Lh and hVd. `k4Seated_widerAt` at `widerFillAt`, with ho proved. -/
theorem k4Seated_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (hVd : Vd w₁ → reqFine Zp w₁.x.pub = true) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k id (I.weights A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_widerKinds h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Lh (FirstFill.widerKinds I o S
    O A.Z A.G) hVd

/-- CONDITIONAL: on h, hA, Lh, hR and hmark. `k4Seated_ready_widerAt` at `widerFillAt`, with ho
proved. -/
theorem k4Seated_ready_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {w₀ : W₀} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {kc : Coins Bk}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk A.H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k id (I.weights
      A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_ready_widerKinds h Q test carryX item n₁ n₂ b₀ Vd Rd Kp hA Lh (FirstFill.widerKinds I o
    S O A.Z A.G) hR hmark

/-- CONDITIONAL: on h, hA and Lh. `k4_plays_widerAt` at `widerFillAt`, with ho proved. -/
theorem k4_plays_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    Plays (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k :=
  k4_plays_widerKinds h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Lh (FirstFill.widerKinds I o S
    O A.Z A.G)

/-- CONDITIONAL: on h, hA and Lh. `k4_playsS_widerAt` at `widerFillAt`, with ho proved. -/
theorem k4_playsS_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k :=
  k4_playsS_widerKinds h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh (FirstFill.widerKinds
    I o S O A.Z A.G)

/-- CONDITIONAL: on h, hA, Lh and hs. `k4_accepted_widerAt` at `widerFillAt`, with ho proved. -/
theorem k4_accepted_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {fs : List (Fall TS)} (hs : ∀ f ∈ k4LotFalls A.Z A.G, f ∈ fs) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said
      (fallsBy fs cF.blocksInOrder) k :=
  k4_accepted_widerKinds h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh
    (FirstFill.widerKinds I o S O A.Z A.G) hs

/-- CONDITIONAL: on h, hA, Lh, hMask, hIx and hWt. `k4_exchange_wo_widerAt` at `widerFillAt`, with
ho paid. -/
theorem k4_exchange_wo_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread id (I.weights
        A.Z)
        k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hIx : ∀ blk,
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∀ cc name endName (cp : SumCoins name endName (mergeSum (k4PubAt cF k x))),
        lendRow Bk
          (Bk.rowsOf (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place (k4PubAt cF k x))
          (k4Half (Rc := IndexCommitterCoins) (X := Unit) id (I.weights A.Z) k4Tokens k4LookAt (k4PubAt cF k
            x)).parts 0 =
            .ok cc →
        SumAt cc (k0 (k4PubAt cF k x).g + 15) name endName (mergeSum (k4PubAt cF k x)) cp →
        K4IndexTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)))
    (hWt : ∀ blk,
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      K4WeightsTieK (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.d1
        h.𝔇.rw13 c y.2 s'
        (wmOf (k4Wit (k4PubAt cF k x) id (I.weights A.Z) k4Tokens (k4LookAt (k4PubAt cF k x))
          mm.st.input).w)) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_widerKinds h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh
    (FirstFill.widerKinds I o S O A.Z A.G) hMask hIx hWt

/-- CONDITIONAL: on h, hA, Lh, hZ, hMask, hIx and hEn. `k4_exchange_wo_parts_widerAt` at
`widerFillAt`, with ho proved. -/
theorem k4_exchange_wo_parts_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hZ : Vd w₁ → K4IndexZeroFrom OnBytes.Flat.numsFull.rows (I.weights A.Z) w₁)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread id (I.weights
        A.Z)
        k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hIx : ∀ blk,
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∀ cc name endName (cp : SumCoins name endName (mergeSum (k4PubAt cF k x))),
        lendRow Bk
          (Bk.rowsOf (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place (k4PubAt cF k x))
          (k4Half (Rc := IndexCommitterCoins) (X := Unit) id (I.weights A.Z) k4Tokens k4LookAt (k4PubAt cF k
            x)).parts 0 =
            .ok cc →
        SumAt cc (k0 (k4PubAt cF k x).g + 15) name endName (mergeSum (k4PubAt cF k x)) cp →
        K4IndexTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)))
    (hEn : ∀ blk,
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      K4EntriesTieK (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
        y.2 s'
        (wmOf (k4Wit (k4PubAt cF k x) id (I.weights A.Z) k4Tokens (k4LookAt (k4PubAt cF k x))
          mm.st.input).w)) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_parts_widerKinds h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh
    (FirstFill.widerKinds I o S O A.Z A.G) hZ hMask hIx hEn

/-- CONDITIONAL: on h, hA, Lh, hI, hMask and hIx. `k4_exchange_wo_index_widerAt` at `widerFillAt`,
with ho proved. -/
theorem k4_exchange_wo_index_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hI : Vd w₁ → K4IndexIs Q (I.weights A.Z) w₁)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread id (I.weights
        A.Z)
        k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hIx : ∀ blk,
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∀ cc name endName (cp : SumCoins name endName (mergeSum (k4PubAt cF k x))),
        lendRow Bk
          (Bk.rowsOf (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place (k4PubAt cF k x))
          (k4Half (Rc := IndexCommitterCoins) (X := Unit) id (I.weights A.Z) k4Tokens k4LookAt (k4PubAt cF k
            x)).parts 0 =
            .ok cc →
        SumAt cc (k0 (k4PubAt cF k x).g + 15) name endName (mergeSum (k4PubAt cF k x)) cp →
        K4IndexTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE))) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_index_widerKinds h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh
    (FirstFill.widerKinds I o S O A.Z A.G) hI hMask hIx

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.ho_widerAt_paid
#print axioms ProofFile.Honest.K4.half_widerAt
#print axioms ProofFile.Honest.K4.k4Seated_widerPaid
#print axioms ProofFile.Honest.K4.k4Seated_ready_widerPaid
#print axioms ProofFile.Honest.K4.k4_plays_widerPaid
#print axioms ProofFile.Honest.K4.k4_playsS_widerPaid
#print axioms ProofFile.Honest.K4.k4_accepted_widerPaid
#print axioms ProofFile.Honest.K4.k4Seated_run_widerPaid
#print axioms ProofFile.Honest.K4.k4_exchange_wo_widerPaid
#print axioms ProofFile.Honest.K4.k4_exchange_wo_parts_widerPaid
#print axioms ProofFile.Honest.K4.k4_exchange_wo_index_widerPaid
