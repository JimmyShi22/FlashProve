-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/MsgFirstAtHead.lean: the honest side of the smallness test (K8):
"THE OWNER FORM" AT SEGMENT 0, UNDER THE LIBRARY's HEAD AND AN OPENING, AT THE JOINED SCRIPT OVER
THE TWO LISTS OF JOBS AT THE LOT's OWN DATA AT THE SIZES `Sz.ref`: the witness holds, in the message
with the plan's number of (segment 0, the array's message), at the layout's place of each element of
the array "M mu", mu below 9, the packed cells of the reader's cells of (0, mu). `msg_first_at_join`
(Johnson/Desc/ProofFile/Honest/K8/MsgFirstAtJoin.lean) WITH ALL ITS PUBLIC PREMISES MET. One
definition, a public test on written lists; five closed facts by Lean's kernel; one lemma; one
theorem.

IT NAMES THE SCRIPT's WITNESS AND, THROUGH THE LETTER wit, WHAT A READER YIELDS OF THE INPUT: AN
EQUATION ON THE SCRIPT: DATA AGAINST DATA. The run's coins k stand on the left, inside the witness;
on the right: none. No measure; no stop. NOT IN FRONT OF A LAW OVER COINS. hcoins
(`coinsB`) is asked: whoever quotes it at a free book names hasCoins at that book beside it.

  `symFirstAt dk dn mu`   THE TEST, at the written layout, request, opening's plan and seats: the
                    layout has the array "M mu" of segment 0; its message is there and has a sample;
                    the sizes' packed shape of (0, mu) is the array's size; the matrix has an array
                    of its own segment; and one of the opening's messages n has the seat (0, the
                    array's message) and, in the written list of all seats, a holder whose key is
                    (0, 0, that message). dk, dn: two bends for the controls: 0 in earnest
  `symFirst_all`     yes at each mu below 9
  `symFirst_key`, `symFirst_msg`, `symFirst_ninth`   CONTROLS THAT SAY NO: the key's message one
                    further: at each of the nine · the opening's message one further: at each of the
                    nine · at the number 9
  `symLen`           the written codes' lengths pass the library's test
  `any_some`         what the yes of a test on an option gives
  **`msg_owner_first_at_head`**   THE END, with, beside it: the number n of the opening's message,
                    that the place is no place of a pad at that message's shape, and that the plan's
                    number of the member's seat is the plan's number of (0, the array's message)
By, of other authors: `first_at_head` (Johnson/Desc/ProofFile/Honest/K2/Law/LightAtHead.lean) ·
`layout_at` (Johnson/P1K8R/FoldAtDraw.lean) · `lawful_at_head`
(Johnson/HB/LLHARD/Q38J/LawfulAtHead.lean) · `blank_first` · `msgFits_of_layoutOk`
(Johnson/Desc/ProofFile/Honest/K5/Law/WayBackFill.lean) · `labelNo_arrayLabel`, `cellsVals_size`
(Johnson/Desc/ProofFile/Honest/K5/Law/PackedVals.lean) · `eG_atAll`
(Johnson/Desc/K1/Law/TiesAtAll.lean) · `find_two`
(Johnson/Desc/ProofFile/Honest/K1/Law/K1NumApart.lean) · `arrOf_is_num`
(Johnson/P5T/NumOfPlan.lean).
What stays a hypothesis: the head, the opening, F (`JoinFit`), hcoins, a valid input (at any Vd), a
list of challenges no shorter than the rounds in front of the member 2; mu below 9; hA, hi, hc, hrp:
the layout has the array, the element lies in it and is laid at rp.
Two options are raised at the five closed facts (maxRecDepth, maxHeartbeats), one in the whole file
(maxHeartbeats), and one instance is taken away, as in the files beneath. No tactic that searches
but `decide` on one line, on two numbers; five lines are an evaluation each by Lean's kernel
(`decide +kernel`).
Limits. An implication. THE EQUATION COMES OF HOW THE JOINED SCRIPT IS BUILT: at the opening it is
built of a lot whose data are these packed cells of the reader's answers: what is proved is that the
witness agrees with the lots' own text, whichever reader is taken; nothing here rests on a run. NOT
SAID: that an honest prover's Script is the joined one; that the letter wit reads the trace of the
model; anything of the arrays of segments 1 to 24. At the message's first sending alone. The full
size alone; decided at one version of the written lists. It stands over files that are
on no row.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.MsgFirstAtJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.LightAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.WayBackFill
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedVals
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumApart
import Johnson.HB.LLHARD.Q38J.LawfulAtHead
import Johnson.P1K8R.FoldAtDraw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Params (ReqArray)
open OnBytes.HonestTrace (Sz packedCells)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull)
open ProofFile.Honest.FirstThread (Others joinQ JoinFit coinsB byNo)
open OnBytes.SendSim.Seat (wJobs)
open Johnson.Prover.Send (shapeAt)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA TS)
open P5T (seatsAllFull)

/-- The public test at the written lists. dk, dn: bends for the controls; 0 in earnest. -/
def symFirstAt (dk dn mu : ℕ) : Bool :=
  (arrayOf layoutFull 0 (Meaning.nameOf mu)).any fun a =>
    (Meaning.messageAt proofSizedFull.request 0 a.message).any fun M =>
      decide (M.shape.answers ≠ 0) && decide (Sz.ref.packedShape 0 mu = (a.sizeI, a.sizeC)) &&
      ((Sz.ref.matAt 0 mu).any fun y => (Sz.ref.arrayNo y.1 y.2).isSome) &&
      (List.range K1.parGF.sent.size).any fun n =>
        decide (K1.firstSeat proofSizedFull.request 0 ⟨K1.firstAddr, n + dn⟩ =
          some (0, a.message)) &&
        (seatsAllFull.find? fun p => p.j == (K1.seatOfMsg K1.parGF 0 n).1 &&
          p.t == (K1.seatOfMsg K1.parGF 0 n).2).any fun p =>
            decide (P5T.keyOf p = (0, 0, a.message + dk))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test says yes at each of the nine. -/
theorem symFirst_all : (List.range 9).all (symFirstAt 0 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: with the key's message one further it says no at each of the nine. -/
theorem symFirst_key : (List.range 9).any (symFirstAt 1 0) = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: with the opening's message one further it says no at each of the nine. -/
theorem symFirst_msg : (List.range 9).any (symFirstAt 0 1) = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at the number 9 the test says no. -/
theorem symFirst_ninth : symFirstAt 0 0 9 = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The written codes' lengths pass the library's test. -/
theorem symLen : proofSizedFull.codes.lengthsOk = true := by decide +kernel

/-- What the yes of a test on an option gives. -/
theorem any_some {α : Type} {o : Option α} {p : α → Bool} (h : o.any p = true) :
    ∃ a, o = some a ∧ p a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The owner form at segment 0, under the head, at the joined Script.** An equation on the
Script; no coin on its right. NOT IN FRONT OF A LAW OVER COINS. Whoever quotes it at
a free book names hasCoins at that book beside it. -/
theorem msg_owner_first_at_head {Bk : ProverCoinCounts} {Wl Cw Tok X : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Wl → Cw) (tokQ : Wl → Tok) (wit : Wl → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (O : Others Bk Wl) {seats : List (ℕ × ℕ)}
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) seats wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) O)
    (hcoins : coinsB Bk
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) = true)
    (Vd : Wl → Prop) {mu : ℕ} (hmu : mu < 9) {A : ReqArray}
    (hA : arrayOf (P5J.At.layout Zp) 0 (Meaning.nameOf mu) = some A) (k : Coins Bk) (w : Wl)
    (hw : Vd w) (hd : List Fmt.Drawn) (hN : roundsTo cF.blocksInOrder 2 ≤ hd.length) {i c : ℕ}
    (hi : i < A.sizeI) (hc : c < A.sizeC) {rp : ℕ × ℕ} (hrp : laidAt A i c = some rp) :
    ((joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) O).wit k w hd).msg
        (P5J.At.num Zp 0 A.message) false rp.1 rp.2 =
      algebraMap GF GE (packedCells Sz.ref (wit w).R.cells.cell 0 mu i c) ∧
    ∃ n, n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size ∧
      padB (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).codes
        (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n) false rp.1 rp.2 = false ∧
      P5J.At.arr Zp (K1.seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).1
        (K1.seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).2 =
          P5J.At.num Zp 0 A.message := by
  obtain ⟨fc, fs, fl⟩ := K2.Law.first_at_head h O₁
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := O₁.blank
  have eL : P5J.At.layout Zp = layoutFull := (P1K8T.layout_at hG).symm.trans fl
  have eG : K1.firstPar Bs.G₀.first (K1.gpOf Zp) = K1.parGF := K1.eG_atAll h O₁ (K1.pin1_atAll h)
  rw [eL] at hA
  have hW := List.all_eq_true.1 symFirst_all mu (List.mem_range.2 hmu)
  unfold symFirstAt at hW
  obtain ⟨a, ha, h1⟩ := any_some hW
  obtain rfl : A = a := Option.some.inj (hA.symm.trans ha)
  have h1' : (Meaning.messageAt proofSizedFull.request 0 A.message).any _ = true := h1
  obtain ⟨M, hM, h2⟩ := any_some h1'
  obtain ⟨h3, h4⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  obtain ⟨h5, h6⟩ := Eq.mp (Bool.and_eq_true _ _) h3
  obtain ⟨h7, h8⟩ := Eq.mp (Bool.and_eq_true _ _) h5
  have hans : M.shape.answers ≠ 0 := of_decide_eq_true h7
  have hsz : Sz.ref.packedShape 0 mu = (A.sizeI, A.sizeC) := of_decide_eq_true h8
  have h6' : (Sz.ref.matAt 0 mu).any _ = true := h6
  obtain ⟨y, hy, hyo⟩ := any_some h6'
  obtain ⟨n, hnR, h9⟩ := List.any_eq_true.1 h4
  obtain ⟨h10, h11⟩ := Eq.mp (Bool.and_eq_true _ _) h9
  have t1W : K1.firstSeat proofSizedFull.request 0 ⟨K1.firstAddr, n + 0⟩ = some (0, A.message) :=
    of_decide_eq_true h10
  have h11' : (seatsAllFull.find? fun p => p.j == (K1.seatOfMsg K1.parGF 0 n).1 &&
    p.t == (K1.seatOfMsg K1.parGF 0 n).2).any _ = true := h11
  obtain ⟨p, hp, hk⟩ := any_some h11'
  have hkey : P5T.keyOf p = (0, 0, A.message + 0) := of_decide_eq_true hk
  have hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size := by
    rw [eG]
    exact List.mem_range.1 hnR
  -- the array's name
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 hA
  have hb := List.find?_some hf
  have hname : A.name = Meaning.nameOf mu := beq_iff_eq.1 hb
  have hlab : K1.labelNo A.name = some mu := by
    rw [hname]
    exact K5.labelNo_arrayLabel (Nat.lt_of_lt_of_le hmu (by decide))
  have hmem : A ∈ (Bs.G₀.first.layout.link.getD 0 []).filter fun u => u.message == A.message := by
    rw [fl]
    refine List.mem_filter.2 ⟨?_, beq_self_eq_true _⟩
    rw [List.getD_eq_getElem?_getD, hl]
    exact List.mem_of_find?_eq_some hf
  have ok : reqLayoutOk Bs.G₀.first.codes Bs.G₀.first.shape Bs.G₀.first.layout = true := by
    rw [Meaning.K2.blank_first hG]
    exact Q38.lawful_at_head h
  have hfit : msgFits Bs.G₀.first.codes Bs.G₀.first.shape Bs.G₀.first.layout 0 A.message = true :=
    K5.msgFits_of_layoutOk ok (by rw [fl]; exact hA) (by rw [fs]; exact hM) hans
  have hz : (K1.cellsVals Sz.ref).size 0 A.name = some (Sz.ref.packedShape 0 mu) :=
    K5.cellsVals_size Sz.ref hlab (σ := y.1) (μ := y.2) hy hyo
  -- the number
  obtain ⟨p', f1, f2⟩ := K1.find_two h O₁ hn
  obtain rfl : p' = p := Option.some.inj (f2.symm.trans hp)
  have hnum : P5J.At.arr Zp
      (K1.seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).1
      (K1.seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).2 =
        P5J.At.num Zp 0 A.message := P5T.arrOf_is_num _ _ _ 0 A.message p' f1 hkey
  obtain ⟨e1, e2⟩ := msg_first_at_join cF.blocksInOrder cellsQ tokQ (P5J.At.arr Zp) wit own₀ _ O F hcoins
    (first_job_in_list h O₁ no Sz.ref Dd) Sz.ref Zp Bs.G₀ (K1.gpOf Zp) (no ⟨1, some 0, 1, .K1⟩) rfl
    (n := n) hn Vd k w hw hd (by rw [Nat.zero_add]; exact hN)
    (by rw [fc]; exact symLen) (a := A) (by rw [fs]; exact t1W) hfit hmem hrp hlab hz
    (by rw [hsz]; exact ⟨hi, hc⟩)
  refine ⟨?_, n, hn, e2, hnum⟩
  rw [← hnum]
  exact e1

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.symFirstAt
#print axioms ProofFile.Honest.K8.symFirst_all
#print axioms ProofFile.Honest.K8.symFirst_key
#print axioms ProofFile.Honest.K8.symFirst_msg
#print axioms ProofFile.Honest.K8.symFirst_ninth
#print axioms ProofFile.Honest.K8.symLen
#print axioms ProofFile.Honest.K8.any_some
#print axioms ProofFile.Honest.K8.msg_owner_first_at_head
