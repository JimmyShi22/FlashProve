-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TopsAt.lean: CONDITIONAL.

What is here. FIVE STATEMENTS ON THE MEMBER OF THE LAYERS' OWN ROUNDS (kind K4) AT THE PROVER THAT
THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS, FOR A FILLING THAT NEED NOT HOLD K4's LOT ITSELF, BUT A LOT WITH
THE SAME HALVES. The elder forms (`k4_plays_atPure`, `k4_playsS_atPure`, Law/PlaysAtPure.lean;
`k4_accepted_falls`, `k4_accepted_lotFalls`, Law/FillFalls.lean; `k4_exchange_wo_lookAt_thr`,
Law/WoTopThr.lean) ask hL: `k4HLot cells weights look` is a member of the filling's list of lots. A
filling that hands each lot its reader of the index as a function of the public part lays a wrapped
lot there, and hL need hold of no one reader. Here hL is replaced by two hypotheses: hM: a lot M is
a member of the list; hE: at the maker's own public part and ground M has the halves of `k4HLot
cells weights look`. Every other hypothesis and each end stand as with hL. Two statements with hL
have no form here, since a form here asks less: `k4_accepted_fill`
(Law/HalfAtPure.lean) and `k4_exchange_wo_lookAt` (Law/WoTopAtPure.lean). On the names:
`k4_plays_at` is an elder statement's name (Law/Plays.lean), so the two on plays end in «_by»; in
Law/HalfAtPureBy.lean that ending marks another thing: the form from ∃ M ∈ P.lots. Where the words
are defined: `Fall`: Honest/Side.lean; `fallsBy`: Honest/Law/FallFree.lean; `Plays`:
Honest/Thread/Pays.lean; `PlaysS`, `AcceptedS`: Honest/Thread/PaysS.lean; `ExchangeAtS`:
Honest/Thread/SharesS.lean; `OnlineProverParts`, `onlineProverFromPublicFiles`: Honest/AtPure.lean; `HLot`: Honest/Frame.lean. Five
statements with their proofs: the fifth calls the fourth; each of the others is the statement from
half (Law/PlaysFive.lean, Law/LookJoinDear.lean, Law/WoTopThr.lean) at `half_atPure_at`
(Law/HalfAtPureBy.lean).

  `k4_plays_by`, `k4_playsS_by`   `Plays`, `PlaysS`.
  `k4_accepted_falls_at`   `AcceptedS` at every list of falls that holds K4's own list.
  `k4_accepted_lotFalls_at`   the same at K4's own list.
  `k4_exchange_wo_at`   `ExchangeAtS` at the pending row's item, at look := `k4LookAt`.

Limits. CONDITIONAL: all five on h · LaidK4 · hA (the maker returns) · hM · hE · ho (no other lot of
the filling has a half at a place of the kind K4, or it has the same halves); `k4_accepted_falls_at`
besides on hs (the list of falls holds K4's own list, `k4LotFalls`, Honest/K4/LotFalls.lean): «EVERY
LIST THAT HOLDS K4's» IS THE WEAKER WAY: `AcceptedS` asks that no fall at the place has spoken, so
each further fall at K4's place makes it say less; K4's SECOND FALL, on the free slots behind the
batching, IS NOT IN THE LIST; EACH FALL's SHARE IS A STATED NUMBER: no bound is shown, and nothing
is added up here; `k4_exchange_wo_at` besides on three named ties, each still a hypothesis:
`K4MaskTieAt` · `K4IndexTieAt` · `K4WeightsTieK`. `K4WeightsTieK` (Law/WoShareK.lean) holds, beside
the tie on the witness, a public inequality (the matrix's rows are at most 2 ^ kRow: not shown here)
and a sentence on the index alone (its reader is 0 from the row nR on), which only Vd can give. THAT
ANY FILLING HAS SUCH A LOT M IS NOT SHOWN HERE: no filling is imported; that hE holds at a wrapped
lot by unfolding is not held by this file. That `onlineProverFromPublicFiles` returns at any filling is not shown here.
Of h together with hA · LaidK4 · hM · hE · ho · hs · K4MaskTieAt · K4IndexTieAt · K4WeightsTieK no
example is known to us; all five speak only where the thread stands (`Thr`; four of them ask `ThrS`:
the thread, and what is said), `k4_exchange_wo_at` only where besides the member's step accepts. NOT
COMPLETENESS: the member's step tests no sent value (Law/Hears.lean); of a play nothing is said but
that it returns. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of any files
is not shown here: the side library AtFullSide proves, with no hypothesis, that h has a member at
one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits
say what it is worth). Beneath `half_atPure_at` and `fits_member` stand comparisons by Lean's own
kernel that no independent checker has replayed (Law/FitsMember.lean's head names them;
`k4_front_closed`, Law/FrontClosed.lean). IT IS A LAW, NOT A PART: it rests on modules under
Johnson/Goal/: no file that defines a part may build on it; it states no goal. Nothing on soundness,
on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPureBy
import Johnson.Desc.ProofFile.Honest.K4.Law.PlaysFive
import Johnson.Desc.ProofFile.Honest.K4.Law.FillFalls
import Johnson.Desc.ProofFile.Honest.K4.Law.LookJoinDear
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTopThr

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Forest.Heard)
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.W (lookFits_lookAt lookAt_isK3 lookBase_head)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X' : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hA, hM, hE and ho. **`Plays` AT THE MAKER's PROVER.** -/
theorem k4_plays_by {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) :
    Plays (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k :=
  k4_plays_half h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh
    (half_atPure_at h Lh hA cells weights look hM hE ho)

/-- CONDITIONAL: on h, Lh, hA, hM, hE and ho. **`PlaysS` AT THE MAKER's PROVER.** -/
theorem k4_playsS_by {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k :=
  k4_playsS_half h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
    (half_atPure_at h Lh hA cells weights look hM hE ho)

/-- CONDITIONAL: on h, Lh, hA, hM, hE, ho and hs. **`AcceptedS` AT THE MAKER's PROVER, AT EVERY LIST
OF FALLS THAT HOLDS K4's LIST.** -/
theorem k4_accepted_falls_at {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    {fs : List (Fall TS)} (hs : ∀ f ∈ k4LotFalls A.Z A.G, f ∈ fs) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said
      (fallsBy fs cF.blocksInOrder) k :=
  k4_accepted_last h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
    (half_atPure_at h Lh hA cells weights look hM hE ho)
    (hf_head Lh (hs _ (k4Fall_mem_atPure h Lh hA)))

/-- CONDITIONAL: on h, Lh, hA, hM, hE and ho. **THE SAME AT K4's OWN LIST OF FALLS.** -/
theorem k4_accepted_lotFalls_at {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said
      (fallsBy (k4LotFalls A.Z A.G) cF.blocksInOrder) k :=
  k4_accepted_falls_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh cells weights look hM
    hE ho fun _ hf => hf

/-- CONDITIONAL: on every hypothesis named. **`ExchangeAtS` AT THE PENDING ROW's ITEM, AT THE
MAKER's PROVER, AT look := `k4LookAt`.** hMask: `K4MaskTieAt`, Law/ScriptAt.lean. hIx, hWt: what
each says: Law/WoTopLot.lean. -/
theorem k4_exchange_wo_at {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
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
          (k4Half (Rc := Rc) (X := X') cells weights k4Tokens k4LookAt (k4PubAt cF k x)).parts 0 =
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
        (wmOf (k4Wit (k4PubAt cF k x) cells weights k4Tokens (k4LookAt (k4PubAt cF k x))
          mm.st.input).w)) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_seat_thr h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
    (half_atPure_at h Lh hA cells weights (fun _ _ => k4LookAt) hM hE ho)
    (fun fr _ => lookFits_lookAt h Lh fr) hMask
    (lookAt_isK3 h Lh w₁.x (lookBase_head h Lh)).2 hIx hWt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_plays_by
#print axioms ProofFile.Honest.K4.k4_playsS_by
#print axioms ProofFile.Honest.K4.k4_accepted_falls_at
#print axioms ProofFile.Honest.K4.k4_accepted_lotFalls_at
#print axioms ProofFile.Honest.K4.k4_exchange_wo_at
