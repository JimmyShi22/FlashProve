-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/AtWiderAtWo.lean: CONDITIONAL.

What is here. `ExchangeAtS` AT THE PENDING ROW's ITEM, FOR THE MEMBER OF THE LAYERS' OWN ROUNDS
(kind K4), AT THE MAKER's PROVER AT THE WRITTEN FILLING `widerFillOwn` (Honest/AtPureWiderAt.lean),
in three forms: with the tie on the weights whole (`k4_exchange_wo_at`, Law/TopsAt.lean), in its
parts and from `K4IndexIs` (`k4_exchange_wo_parts_at`, `k4_exchange_wo_index_at`,
Law/WoTopsAt.lean). Each is said again at that filling without hM and hE (`k4Lot_mem_widerOwn`,
Law/AtWiderAt.lean; hE by unfolding), at cells := id and weights := I.weights A.Z. What it is for:
that these statements, which bear the two readers inside their hypotheses, fit that filling's own
term is held by Lean here, and by nothing else. Three statements with their proofs: one call each.

  `k4_exchange_wo_widerAt`, `k4_exchange_wo_parts_widerAt`, `k4_exchange_wo_index_widerAt`

Limits. CONDITIONAL: all three on h · LaidK4 · hA · ho · `K4MaskTieAt` · `K4IndexTieAt`; the first
besides on `K4WeightsTieK`; the second on hZ (one clause under Vd: the reader of the index is 0 from
the table's number of rows on) and `K4EntriesTieK`; the third on hI (one clause under Vd:
`K4IndexIs`, Law/IndexIs.lean). Each tie is still a hypothesis. THAT THE FRAME's MAKER `onlineProverFromPublicFiles`
(Honest/AtPure.lean) RETURNS AT THAT FILLING (hA) IS SHOWN HERE OF NO FILES; no statement or test in
that file or here runs the maker at it. ho (every other lot of the filling has no half at a place of
the kind K4, or K4's halves): shown here of none of the nine. WHAT THAT FILLING LACKS, by its own
files' heads: no prover's side for K1 at the place of the message "W", nor for K9, K10 and K12; the
second chain has none; the shared chain has none where `nowSharedBy` returns an error; nothing
compares `WiderIn.trace` with `WiderIn.weights`; the lists in L are arguments (K1's too, where
`LongLots` has that field: then the clause on K1 holds at `LongLots.plain`, not at a free L). The
statements speak only where the thread stands in front of K4's member and the member's step accepts:
how a run of that filling's prover gets there is not said here. Of h together with hA · LaidK4 · ho
· K4MaskTieAt · K4IndexTieAt · K4WeightsTieK · hZ · hEn · hI no example is known to us. THE FULL
SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of any files is not shown here: the
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). The limits of the statements that are called are theirs here too. If that filling's list
turns, in its order or in K4's entry, this file no longer compiles. Honest/AtPureWiderAt.lean and
what it imports are no part of the library yet. IT IS A LAW, NOT A PART: it rests on modules under
Johnson/Goal/: no file that defines a part may build on it; it states no goal. Nothing on soundness,
on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.AtWiderAt
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTopsAt

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
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {W₀ X : Type}

variable {own₀ : X} {L : LongLots W₀ X} {I : WiderIn W₀} {o : SecondHashFunctionArgument}
  {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- CONDITIONAL: on every hypothesis named. **THE TIE ON THE WEIGHTS WHOLE.** hMask: `K4MaskTieAt`,
Law/ScriptAt.lean. hIx, hWt: what each says: Law/WoTopLot.lean. -/
theorem k4_exchange_wo_widerAt {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) X → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G)
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
          (k4Half (Rc := IndexCommitterCoins) (X := X) id (I.weights A.Z) k4Tokens k4LookAt (k4PubAt cF k
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
  k4_exchange_wo_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh id (I.weights A.Z)
    (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho hMask hIx hWt

/-- CONDITIONAL: on every hypothesis named. **THE TIE ON THE WEIGHTS IN ITS PARTS.** hZ, hEn: what
each says: Law/WoTopsAt.lean. -/
theorem k4_exchange_wo_parts_widerAt {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) X → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G)
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
          (k4Half (Rc := IndexCommitterCoins) (X := X) id (I.weights A.Z) k4Tokens k4LookAt (k4PubAt cF k
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
  k4_exchange_wo_parts_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh id (I.weights A.Z)
    (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho hZ hMask hIx hEn

/-- CONDITIONAL: on every hypothesis named. **FROM `K4IndexIs`.** hI: what it says:
Law/IndexIs.lean. -/
theorem k4_exchange_wo_index_widerAt {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) X → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G)
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
          (k4Half (Rc := IndexCommitterCoins) (X := X) id (I.weights A.Z) k4Tokens k4LookAt (k4PubAt cF k
            x)).parts 0 =
            .ok cc →
        SumAt cc (k0 (k4PubAt cF k x).g + 15) name endName (mergeSum (k4PubAt cF k x)) cp →
        K4IndexTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE))) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_index_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh id (I.weights A.Z)
    (k4Lot_mem_widerOwn own₀ L I o S O) rfl ho hI hMask hIx

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exchange_wo_widerAt
#print axioms ProofFile.Honest.K4.k4_exchange_wo_parts_widerAt
#print axioms ProofFile.Honest.K4.k4_exchange_wo_index_widerAt
