-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MsgLotsStatement.lean: WHAT THE KIND K11 ASKS OF THE
SCRIPT's MESSAGES, AS TWO LOTS OF ENTRIES IN THE FRAME's AUTHORS' FORM (`MsgLot`, `OwnMsgs`,
Honest/Thread/ScriptLots.lean): three definitions, and STATEMENTS: four definitions of propositions.
NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

  `k11Lent`        what the book lends the merge's row of parts, of a run's coins: the term that
                   `headMergeCoins` (SeatFieldsStatement.lean of this folder) matches on. It reads
                   the chain's number, the place and the coins; no Script, no input, no challenge
  `k11MaskLot`     entries ν₀ .. ν₀ + 2 lk + 1 of row 0 of the mask table of message number n: the
                   values of the first run that is lent. IT ANSWERS NOWHERE WHERE THE BOOK DOES NOT
                   LEND
  `k11IndexLot`    ONE entry (row, place) of the mask table of message number n: the value of the
                   head of the run "ends". It answers nowhere where the book does not lend
  `MaskLotAt`      where the book lends, the first lot answers at entry ν₀ + i, i < 2 lk + 2, with
                   entry i of the first run
  `IndexLotAt`     the like for the second
  `LotsOfLent`     two runs' coins to which the book lends alike give one text, at both lots
  `MaskTieOfOwn`   AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD: the base Bs · the prover's
                   half found at `IM.k11Place` · `OwnMsgs` at the first lot, at message number
                   `P5J.At.num Zp 24 0`, from entry 3531 on, at the thread's own Vd and N := 0:
                   `K11MaskTieF` (MaskBridgeStatement.lean of this folder: the field maskTie of
                   `K11ScriptMsg`) at the kind's own coins, at every letter claims

WHAT IT IS NOT. `OwnMsgs` STAYS A PREMISE: SHOWN AT NO SCRIPT. No lot of any sender's is here, and
NOTHING SAYS THAT THESE LOTS AGREE WITH THE SENDERS' (`LotsAgree`, ScriptLots.lean). `LotsOfLent`
speaks of what is lent, whole: which of a run's coins the lending reads is not said. The numbers n,
row and place of the second lot are letters. The field indexTie is not treated. The values are
called nothing but what the book lends. The head is a premise, at `OnBytes.secondHashFunction`, at the full
size.

NEAR. `MaskTieOfOn`, `MaskTieOfRoad` (MaskBridgeStatement.lean, MaskRoadStatement.lean): the same
end from other forms of the frame's authors', the second under twelve premises; `MaskTieOfAll`
(MaskBridgeAllStatement.lean) and `MaskTieOfTen` (MaskTenStatement.lean: ten: the pad and "free"
paid) end there too. `input_head` (Johnson/Desc/ProofFile/Honest/K4/Law/IndexIs.lean, another group
of authors', in no sealed library): where the thread stands the run's input is the thread's own and
Vd holds of it: its second half is two lines of the last proof here.

Limits. Definitions, and lemmas under premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskBridgeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatFieldsStatement
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading WsClaim)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest.SumLaw (SumCoins firstRun endRun)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- What the book lends the merge's row of parts, of a run's coins. ch: the chain's number. -/
def k11Lent (Bk : ProverCoinCounts) {W₀ Rc Xi Tr : Type} (X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (k : Coins Bk) :=
  lendRow Bk (Bk.rowsOf ch) (k.look ch) pl
    (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts 0

/-- **The kind's lot of entries of the segment's mask row.** n: the message's number in the witness.
ν₀: the first entry. -/
def k11MaskLot (Bk : ProverCoinCounts) {W₀ Rc Xi Tr : Type} (X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n ν₀ : Nat) :
    MsgLot Bk (Local W₀ Rc Xi Tr) where
  n := n
  fx := 0
  txt := fun k _ _ mask row place =>
    match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
    | .error _ => none
    | .ok c =>
      if mask = true ∧ row = 0 ∧ ν₀ ≤ place ∧ place < ν₀ + (2 * P.lay.lk + 2) then
        some (Reading.gl.val ((firstRun c.2.1).getD (place - ν₀) zeroE))
      else none

/-- **The kind's lot of one entry of the index masks' message.** n: the message's number in the
witness. r, p: the entry's row and place. -/
def k11IndexLot (Bk : ProverCoinCounts) {W₀ Rc Xi Tr : Type} (X : Type) (ch : Nat) (pl : Place)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (n r p : Nat) : MsgLot Bk (Local W₀ Rc Xi Tr) where
  n := n
  fx := 0
  txt := fun k _ _ mask row place =>
    match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
    | .error _ => none
    | .ok c =>
      if mask = true ∧ row = r ∧ place = p then
        some (Reading.gl.val ((endRun c.2.1).headD zeroE))
      else none

/-- The statement on where the first lot answers. Not proved here; a lemma's statement, none of the
library's goals. -/
def MaskLotAt : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n ν₀ : Nat)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) c,
    k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k = .ok c →
    ∀ i, i < 2 * P.lay.lk + 2 →
      (k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k w hd true 0
        (ν₀ + i) = some (Reading.gl.val ((firstRun c.2.1).getD i zeroE))

/-- The statement on where the second lot answers. Not proved here; a lemma's statement, none of
the library's goals. -/
def IndexLotAt : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n r p : Nat)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) c,
    k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k = .ok c →
      (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n r p).txt k w hd true r p =
        some (Reading.gl.val ((endRun c.2.1).headD zeroE))

/-- The statement on two runs' coins. Not proved here; a lemma's statement, none of the library's
goals. -/
def LotsOfLent : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n ν₀ n' r p : Nat)
    (k k' : Coins Bk),
    k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k =
      k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k' →
    (k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k =
        (k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k' ∧
      (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n' r p).txt k =
        (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n' r p).txt k'

/-- **The statement on the first join.** Not proved here; a lemma's statement, none of the library's
goals. -/
def MaskTieOfOwn : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g =>
      g.place == IM.k11Place) =
        some (headMergeHalf claims weights (_root_.K11.parOf Zp Bs.G₀)) →
    OwnMsgs Q Vd 0 (P5J.At.num Zp 24 0) 0
      (k11MaskLot Bk (Rc := Rc) (Tr := Tr) X
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain IM.k11Place
        (_root_.K11.parOf Zp Bs.G₀) claims weights (P5J.At.num Zp 24 0) 3531).txt →
    K11MaskTieF (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) claims weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24

end ProofFile.Honest.K11
