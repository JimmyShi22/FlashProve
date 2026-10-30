-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ReadsAtFirst.lean: the honest side of the smallness test (K8): AT
THE HEAD's LETTERS AND THE JOINED SCRIPT OVER THE TWO LISTS OF JOBS AT THE LOT's OWN DATA AT THE
SIZES `Sz.ref`: (1) hShape OF `hst_of_reads` AND `hsym_of_stand` IS MET, AT EVERY SCRIPT; (2) "THE
OWNER FORM" AT SEGMENT 0 HOLDS AT THE STAND OF EACH OF THE 25 DRAWS; (3) SO "THE READS' FORM" hrd
HOLDS AT SEGMENT 0. Three theorems; no definition.

(2) AND (3) NAME THE SCRIPT's WITNESS AND, THROUGH THE LETTER wit, WHAT A READER YIELDS OF THE
INPUT: EQUATIONS ON THE SCRIPT: DATA AGAINST DATA. Neither has a premise on the hidden input (wit is
one of F's letters, and inside F each input stands under a "for all"): the equations hold because
the joined Script's lot at the opening lays what that reader yields. The run's coins k stand on the
left, inside the witness; on the right: none. No measure; no stop. NOT IN FRONT OF A LAW OVER COINS.
hcoins (`coinsB`) is asked: whoever quotes them at a free book names hasCoins at
that book beside them.

  `shapes_at_stand`   hShape's very text at `Sz.ref`: by `shows_at_stand`
                    (Johnson/Desc/ProofFile/Honest/K8/ShowsAtStand.lean: the state's record has the
                    plan's count and list of matrices) and `shapesFit_plan`
                    (Johnson/Desc/ProofFile/Honest/K8/PlanAtHead.lean). The verifier's state and
                    public data alone
  **`owner_first_at_stand`**   at the pair at the draw's number of any segment l, at every
                    continuation e: the thread's witness holds, in the message with the plan's
                    number of (0, the array's message), at the layout's place of each element of an
                    array "M mu" of segment 0, mu below 9, the packed cells of (0, mu): by
                    `msg_owner_first_at_head`
                    (Johnson/Desc/ProofFile/Honest/K8/MsgFirstAtHead.lean); the length of what has
                    been heard by `drawsFit_length` and `roundsTo_mono`
  **`hrd_first`**      hrd's very text at l = 0: by `reads_of_owners_at_head`
                    (Johnson/Desc/ProofFile/Honest/K8/ReadsOfOwnersAtHead.lean) and `own_first`
What stays a hypothesis: the head, the opening, the built segment, hOk, hb (the draw's number is no
greater than the chain's length), and for (2) and (3) F (`JoinFit`) and hcoins.
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath.
Tactics that search: `omega` on two lines, on l.
Limits. Implications. (2) AND (3): THE EQUATION COMES OF HOW THE JOINED SCRIPT IS BUILT: at the
opening it is built of a lot whose data are these packed cells of the reader's answers: what is
proved is that the witness agrees with the lots' own text, whichever reader is taken; nothing here
rests on a run. NOT SAID: that an honest prover's Script is the joined one; that the letter wit
reads the trace of the model; that the thread stands at any of these numbers (the pair is a
premise); hrd at segments 1 to 24. At the opening's messages' first sending alone. The full size
alone. They stand over files of other houses that are on no row. Counted nowhere.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ShowsAtStand
import Johnson.Desc.ProofFile.Honest.K8.PlanAtHead
import Johnson.Desc.ProofFile.Honest.K8.MsgFirstAtHead
import Johnson.Desc.ProofFile.Honest.K8.ReadsOfOwnersAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Slice VerifiableInference.Desc
open OnBytes.Params (ReqArray)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz packedCells ShapesFit)
open VerifiableInference.Desc.Sound (MsgT readAt)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.FirstThread (Others joinQ JoinFit lettersHead WtF Script coinsB byNo)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)
open P1K8T (seatC)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **hShape is met**, at every Script: the verifier's state and public data alone. -/
theorem shapes_at_stand
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    (hb : 14 * l + (if l = 24 then 5 else 4) + 2 ≤ cF.blocksInOrder.length) :
    ∀ k s m E tl,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      s.tl? = some tl → ShapesFit tl Sz.ref l := by
  intro k s m E tl hA ht μ hμ
  obtain ⟨eN, eM, -⟩ := shows_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl hG e3 hb
    hA m.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input m.st.heard)
    tl ht
  rw [eM]
  exact shapesFit_plan h hl μ (by rw [← eN]; exact hμ)

/-- **The owner form at segment 0, at the stand of each draw.** An equation on the Script; no coin
on its right; no premise on the hidden input. NOT IN FRONT OF A LAW OVER COINS.
Whoever quotes it at a free book names hasCoins at that book beside it. -/
theorem owner_first_at_stand {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {Bs : ProofFile.PureBase} {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr)) {seats : List (ℕ × ℕ)}
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) seats wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) O)
    (hcoins : coinsB Bk (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
               wJobs (X := X) no Dd Zp Bs.G₀)) = true) (l : ℕ) :
    ∀ k s m E e,
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      ∀ (mu : ℕ) (B : ReqArray) (i c : ℕ) (rp : ℕ × ℕ), mu < 9 →
        arrayOf (P5J.At.layout Zp) 0 (Meaning.nameOf mu) = some B → i < B.sizeI → c < B.sizeC →
        laidAt B i c = some rp →
        ((lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
            (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                       wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.wit k m.st.input (m.st.heard ++ e)).msg
            (P5J.At.num Zp 0 B.message) false rp.1 rp.2 =
          algebraMap Cb.Gl.F Cb.Gl.E
            (packedCells Sz.ref (wit m.st.input).R.cells.cell 0 mu i c) := by
  intro k s m E e hA mu B i c rp hmu hB hi hc hrp
  have hLen : m.st.heard.length = roundsTo cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2) :=
    drawsFit_length _ _ hA.1.2.1
  have hN : roundsTo cF.blocksInOrder 2 ≤ (m.st.heard ++ e).length := by
    rw [List.length_append, hLen]
    exact Nat.le_trans (roundsTo_mono cF.blocksInOrder 2 _ (by omega)) (Nat.le_add_right _ _)
  exact (msg_owner_first_at_head h O₁ no Dd cellsQ tokQ wit own₀ O F hcoins
    (fun v => v = w ∧ Vd v) hmu hB k m.st.input hA.1.2.2.2.2.2.2 (m.st.heard ++ e) hN hi hc hrp).1

/-- **The reads' form hrd at segment 0.** An equation on the Script; no coin on its right; no
premise on the hidden input. NOT IN FRONT OF A LAW OVER COINS. Whoever quotes it at
a free book names hasCoins at that book beside it. -/
theorem hrd_first {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {Bs : ProofFile.PureBase} {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr)) {seats : List (ℕ × ℕ)}
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) seats wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) O)
    (hcoins : coinsB Bk (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
               wJobs (X := X) no Dd Zp Bs.G₀)) = true) :
    ∀ k s m E e,
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * 0 + (if 0 = 24 then 5 else 4) + 2) k s m E →
      ∀ (μ : Fin (Meaning.sizesOf (P5J.At.X Zp) 0).NM) (r c : ℕ),
        r < Alg.symRows ((Meaning.sizesOf (P5J.At.X Zp) 0).m μ) →
        c < (Meaning.sizesOf (P5J.At.X Zp) 0).k μ →
        readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 0
            ((lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
                (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                           wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
                w).thread.wit k m.st.input (m.st.heard ++ e))
            (seatC Zp 0 μ r c).1 false (seatC Zp 0 μ r c).2.1 (seatC Zp 0 μ r c).2.2 =
          algebraMap Cb.Gl.F Cb.Gl.E
            (packedCells Sz.ref (wit m.st.input).R.cells.cell 0 μ r c) := by
  intro k s m E e hA
  obtain ⟨e9, hown⟩ := own_first h
  refine reads_of_owners_at_head h (by omega : 0 < 25) _
    (fun μ r c => algebraMap Cb.Gl.F Cb.Gl.E
      (packedCells Sz.ref (wit m.st.input).R.cells.cell 0 μ r c)) ?_
  intro μ A y r c hA' _ _ hr hc hy
  have hμ : μ.val < 9 :=
    Nat.lt_of_lt_of_eq (show μ.val < (Meaning.tlAt (P5J.At.X Zp) 0).NM from μ.isLt) e9
  obtain ⟨o1, o2⟩ := hown μ.val hμ
  rw [o1, o2] at hA'
  rw [o1]
  exact owner_first_at_stand h H test carryX item n₁ n₂ b₀ Vd Rd Kp w O₁ no Dd cellsQ tokQ wit own₀
    O F hcoins 0 k s m E e hA μ.val A r c y hμ hA' hr hc hy

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.shapes_at_stand
#print axioms ProofFile.Honest.K8.owner_first_at_stand
#print axioms ProofFile.Honest.K8.hrd_first
