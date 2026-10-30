-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoTopsAt.lean: CONDITIONAL.

What is here. `k4_exchange_wo_parts` (Law/WoTopParts.lean) and `k4_exchange_wo_index`
(Law/WoTopIndex.lean): the threads' debt ExchangeAtS at the pending row's item `Item.wo m`, at the
member of the feed-forward layers' own rounds (sub-protocol K4), at the first chain's thread of the
honest prover that the frame's maker `onlineProverFromPublicFiles` returns: EACH WITH A WEAKER HYPOTHESIS ON THE
FILLING's LIST OF LOTS. There hL asks that K4's lot `k4HLot cells weights look` itself is a member
of the list. Here it is enough that a lot M of the list (hM) has, at the maker's own public part and
ground, the halves that K4's lot has there (hE). They are meant for a filling that wraps K4's lot,
for instance to hand it a reader of the index that is made of the public part: weights is then that
reader at the maker's public part. Each is `k4_exchange_wo_at` (Law/TopsAt.lean) with its hypothesis
on the weights replaced as above.

  `k4_exchange_wo_parts_at`   **the tie on the weights in its parts (hZ under Vd; hEn)**
  `k4_exchange_wo_index_at`   **the tie on the weights from one clause on Vd (hI: `K4IndexIs`)**

Limits. HYPOTHESES, ALL: h · `LaidK4` · hA (the maker returns) · hM, hE · ho (no other lot of the
filling has a half at a place of the kind K4) · on the weights: hZ (`K4IndexZeroFrom`, under Vd) and
hEn (`K4EntriesTieK`), or hI (`K4IndexIs`, under Vd) · TWO NAMED TIES ON THE THREAD's WITNESS:
`K4MaskTieAt` · `K4IndexTieAt`. Nothing shows one of these of any thread. THE TYPE OF AN INPUT GIVES
NEITHER hZ NOR hI. hI asks more than the pending row's item spends (a well-formed matrix; zeros from
the cells' number of columns on): the second statement has fewer names and a stronger hypothesis
than the first. That `onlineProverFromPublicFiles` returns at any such filling is not shown here. THAT ANY FILLING HAS
SUCH AN M: no filling is imported here; that hE holds at a wrapper by unfolding is not held by this
file. On h: the side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with Lh (`LaidK4`), hA, hM, hE, ho, hMask, hIx and hZ, hEn (the first
statement) or hI (the second) no example is known to us; the statements speak only where the thread
stands and the member's step accepts. THE FULL SIZE ALONE, and the format's second hash function
alone. Beneath `fits_member` stand comparisons by Lean's own kernel that no independent checker has
replayed (Law/FitsMember.lean's head names them). A LAW, NOT A PART: it rests on modules under
Johnson/Goal/: no file that defines a part of the proof file's description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TopsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.WoOfIndex

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

/-- **`ExchangeAtS` AT THE PENDING ROW's ITEM, AT THE MAKER's PROVER, AT A LOT THAT HAS K4's HALVES;
THE TIE ON THE WEIGHTS IN ITS PARTS.** hM, hE: a lot M of the filling has, at the maker's own public
part and ground, the halves of K4's lot. hZ: under Vd the index of the thread's own input is 0 from
the reader's number of rows on. hMask: in the witness's mask row of the segment the entry under the
member's slot number j is coin number j of those that the book lends the member's row, at every coin
but the last. hIx: the first end coin that the lent row hands the merge's part is the witness's mask
entry, in the index masks' message, at the entry that this message's ledger in the state behind the
step hands out next. hEn: inside its rows the witness's matrix is the matrix of the honest input's
weights. CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE (h). -/
theorem k4_exchange_wo_parts_at {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hZ : Vd w₁ → K4IndexZeroFrom OnBytes.Flat.numsFull.rows weights w₁)
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
    (hEn : ∀ blk,
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      K4EntriesTieK (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
        y.2 s'
        (wmOf (k4Wit (k4PubAt cF k x) cells weights k4Tokens (k4LookAt (k4PubAt cF k x))
          mm.st.input).w)) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh cells weights hM hE ho
    hMask hIx
    (k4_weightsTie_head h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said (tokens := k4Tokens)
      (look := k4LookAt) (Qp := k4PubAt cF k x) hZ hEn)

/-- **`ExchangeAtS` AT THE PENDING ROW's ITEM, AT THE MAKER's PROVER, AT A LOT THAT HAS K4's HALVES;
THE TIE ON THE WEIGHTS FROM ONE CLAUSE ON Vd.** hM, hE: a lot M of the filling has, at the maker's
own public part and ground, the halves of K4's lot. hI: under Vd the script's cells and the honest
side's reader are one index's matrix, at the thread's own input. hMask: in the witness's mask row of
the segment the entry under the member's slot number j is coin number j of those that the book lends
the member's row, at every coin but the last. hIx: the first end coin that the lent row hands the
merge's part is the witness's mask entry, in the index masks' message, at the entry that this
message's ledger in the state behind the step hands out next. CONDITIONAL: on every hypothesis
named. THE FULL SIZE ALONE (h). -/
theorem k4_exchange_wo_index_at {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hI : Vd w₁ → K4IndexIs Q weights w₁)
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
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE))) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh cells weights hM hE ho
    hMask hIx
    (k4_weightsTie_index h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said (cells := cells)
      (tokens := k4Tokens) (look := k4LookAt) (Qp := k4PubAt cF k x) hI)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exchange_wo_parts_at
#print axioms ProofFile.Honest.K4.k4_exchange_wo_index_at
