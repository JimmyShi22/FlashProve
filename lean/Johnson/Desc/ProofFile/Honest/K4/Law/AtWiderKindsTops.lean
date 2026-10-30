-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/AtWiderKindsTops.lean: CONDITIONAL.

What is here. THE SIX STATEMENTS OF Law/AtWiderAt.lean AND THE THREE OF Law/AtWiderAtWo.lean THAT
ASK ho, AT `widerFillAt` (Honest/AtPureWiderAt.lean), WITH `WiderKinds`
(Honest/Thread/FirstFill.lean) IN ho's STEAD. ho: each lot of the filling has no half at a place of
the kind K4, or has the halves of the lot of the layers' own rounds (kind K4). `ho_widerAt`
(Law/AtWiderKinds.lean) has ho at that filling from K : `WiderKinds`. Each statement here is the
source one with three things turned: ho for K, `widerFillOwn own₀ L I o S O` for `widerFillAt I o S
O`, the sides' own state X for `Unit`; each proof is one call of the source statement at ho :=
`ho_widerAt` K. What each source statement says: its own file. Nine statements with their proofs.

  `k4Seated_widerKinds`, `k4Seated_ready_widerKinds`, `k4Seated_run_widerKinds`   `K4Seated`.
  `k4_plays_widerKinds`, `k4_playsS_widerKinds`   `Plays`, `PlaysS`.
  `k4_accepted_widerKinds`   `AcceptedS`.
  `k4_exchange_wo_widerKinds`, `k4_exchange_wo_parts_widerKinds`,
  `k4_exchange_wo_index_widerKinds`   `ExchangeAtS` at the pending row's item `Item.wo m`.

Limits. CONDITIONAL: all nine on h · LaidK4 · hA (the maker returns at that filling: shown here of
no files) · K, and each on what its source statement asks too. ho IS MOVED ONTO K, NOT PROVED, IN
THIS FILE: K is a hypothesis here, and asks more than ho; Law/AtWiderPaid.lean has the nine without
K, since `FirstFill.widerKinds` (Honest/Thread/FirstFillAll.lean) proves it. AT `widerFillAt` ALONE.
All limits of the nine source statements hold here: they speak only where the thread stands in front
of K4's member. Beneath `half_widerOwn`, on which the nine stand, are comparisons by Lean's own
kernel that no independent checker has replayed (Law/HalfAtPure.lean's head names them). THE FULL
SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of any files is not shown here: the
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with LaidK4 · hA · K and a statement's own hypotheses (hVd · hR · hmark ·
hs · hZ · hEn · hI · K4MaskTieAt · K4IndexTieAt · K4WeightsTieK) no example is known to us.
Honest/Thread/FirstFill.lean, Honest/AtPureWiderAt.lean and those of their imports that lie beside
the library are no part of the library yet. IT IS A LAW, NOT A PART: it rests on modules under
Johnson/Goal/: no file that defines a part may build on it; it states no goal. Nothing on soundness,
on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.AtWiderKinds
import Johnson.Desc.ProofFile.Honest.K4.Law.AtWiderAtWo

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

/-- CONDITIONAL: on h, hA, Lh, K, hR and hmark. `k4Seated_run_widerAt` at `widerFillAt`, with K for
ho. -/
theorem k4Seated_run_widerKinds (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
    (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (K : WiderKinds I o S O A.Z A.G)
    {w₀ : W₀} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {kc : Coins A.B}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (hR : ready A.F A.B A.H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k id (I.weights
      A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_run_widerAt h hA Q test carryX item n₁ n₂ b₀ Vd Rd Kp Lh (ho_widerAt K) hR hmark

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- CONDITIONAL: on h, hA, Lh, K and hVd. `k4Seated_widerAt` at `widerFillAt`, with K for ho. -/
theorem k4Seated_widerKinds {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (K : WiderKinds I o S O A.Z A.G)
    (hVd : Vd w₁ → reqFine Zp w₁.x.pub = true) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k id (I.weights A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_widerAt h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Lh (ho_widerAt K) hVd

/-- CONDITIONAL: on h, hA, Lh, K, hR and hmark. `k4Seated_ready_widerAt` at `widerFillAt`, with K
for ho. -/
theorem k4Seated_ready_widerKinds {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (K : WiderKinds I o S O A.Z A.G)
    {w₀ : W₀} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {kc : Coins Bk}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk A.H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k id (I.weights
      A.Z)
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_ready_widerAt h Q test carryX item n₁ n₂ b₀ Vd Rd Kp hA Lh (ho_widerAt K) hR hmark

/-- CONDITIONAL: on h, hA, Lh, K. `k4_plays_widerAt` at `widerFillAt`, with K for ho. -/
theorem k4_plays_widerKinds {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (K : WiderKinds I o S O A.Z A.G) :
    Plays (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k :=
  k4_plays_widerAt h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Lh (ho_widerAt K)

/-- CONDITIONAL: on h, hA, Lh, K. `k4_playsS_widerAt` at `widerFillAt`, with K for ho. -/
theorem k4_playsS_widerKinds {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (K : WiderKinds I o S O A.Z A.G) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k :=
  k4_playsS_widerAt h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh (ho_widerAt K)

/-- CONDITIONAL: on h, hA, Lh, K and hs. `k4_accepted_widerAt` at `widerFillAt`, with K for ho. -/
theorem k4_accepted_widerKinds {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (K : WiderKinds I o S O A.Z A.G)
    {fs : List (Fall TS)} (hs : ∀ f ∈ k4LotFalls A.Z A.G, f ∈ fs) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said
      (fallsBy fs cF.blocksInOrder) k :=
  k4_accepted_widerAt h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh (ho_widerAt K) hs

/-- CONDITIONAL: on h, hA, Lh, K, hMask, hIx and hWt. `k4_exchange_wo_widerAt` at `widerFillAt`,
with K for ho. -/
theorem k4_exchange_wo_widerKinds {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (K : WiderKinds I o S O A.Z A.G)
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
  k4_exchange_wo_widerAt h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh (ho_widerAt K) hMask
    hIx hWt

/-- CONDITIONAL: on h, hA, Lh, K, hZ, hMask, hIx and hEn. `k4_exchange_wo_parts_widerAt` at
`widerFillAt`, with K for ho. -/
theorem k4_exchange_wo_parts_widerKinds {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (K : WiderKinds I o S O A.Z A.G)
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
  k4_exchange_wo_parts_widerAt h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh (ho_widerAt K)
    hZ hMask hIx hEn

/-- CONDITIONAL: on h, hA, Lh, K, hI, hMask, hIx. `k4_exchange_wo_index_widerAt` at `widerFillAt`,
with K for ho. -/
theorem k4_exchange_wo_index_widerKinds {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (K : WiderKinds I o S O A.Z A.G)
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
  k4_exchange_wo_index_widerAt h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh (ho_widerAt K)
    hI hMask hIx

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Seated_widerKinds
#print axioms ProofFile.Honest.K4.k4Seated_ready_widerKinds
#print axioms ProofFile.Honest.K4.k4_plays_widerKinds
#print axioms ProofFile.Honest.K4.k4_playsS_widerKinds
#print axioms ProofFile.Honest.K4.k4_accepted_widerKinds
#print axioms ProofFile.Honest.K4.k4Seated_run_widerKinds
#print axioms ProofFile.Honest.K4.k4_exchange_wo_widerKinds
#print axioms ProofFile.Honest.K4.k4_exchange_wo_parts_widerKinds
#print axioms ProofFile.Honest.K4.k4_exchange_wo_index_widerKinds
