-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/SymAtTake.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6): THE
PREMISE hSym OF `k6_cellsOn_own_of_sym` (Honest/K6/Law/CellsOnOfSym.lean) FROM hO, hLend AND PUBLIC
FACTS: at the seats of the head's six own matrices off the plane the thread's witness holds the
image of the format's packing of the prover's own cells. NEVER "cellsOn is paid"; NEVER "hSym is
paid" WITHOUT hO, hLend AND THE REST. No definition; six theorems.

  `noWordW`                    a closed fact on public data: the switch's authors' test noWord
                               accepts at the sending of each place of their written list
  `k6_array_of_own`            a closed fact: each number below 6 is, at segment 24, the number of
                               a matrix of the head off the plane that has an array of its own
  `k6_filling_at_seat`         NO DEFAULT IS MET: at each of these seats the switches' own data
                               answers "some": the packing of the reader's cells. At every reader R
  `k6_sym_at_take`             THE TOP
  `k6_sym_at_withSwitchData`   the same where the filling is that data joined to another lot's
  `k6_sym_same_at_coins`       so the left side is one at any two runs' coins; never quoted toward
                               hiding

THE ROAD IS MOSTLY NOT OURS. The switch's authors': `msgTxt_main_f_of` (Honest/K2/Law/MainTxt.lean),
`msgTxt_answers_head` (Honest/K2/Law/LotsAnswerAtHead.lean), `with_own` (Honest/K2/OwnData.lean),
`servesW`, `roomyW`, `fitsW` (Honest/K2/Law/PublicAtWritten.lean), `atLink24_gives`, `noWord_yes`.
K5's authors': `laidData_at` (Honest/K5/Law/WayBackFill.lean), `cellsVals_size`,
`labelNo_arrayLabel`, `asE_inl` (Honest/K5/Law/PackedVals.lean). The library's `symAt_readAt`
(Johnson/P5J/HidBears.lean), `AtMg.placesOff`, `offC_ofHead`, `answers_of_shape`. Ours: the closed
test and the seat (Honest/K6/Cells/Link24Main.lean, SeatAtLink24.lean), where the seats lie
(SeatsInside.lean), the key's first lines (Honest/K6/Law/ReaderAtTake.lean), and the join.

What it is not.
  * NEVER "cellsOn is paid": hSmall and hStream stay.
  * NEVER QUOTED TOWARD HIDING.
  * AN EXCHANGE: hSym goes; hO, hLend, hN, hv come: the four of `k6_reader_at_link24`, to the sign;
    and hD (or a choice of the filling's letter) and hRd. Not one debt fewer.
  * hO: an equation on the Script's messages at the sender's number: shown of no Script here; no
    Script is laid. hLend: a public test on the book: shown at no book here.
  * THE LAW ON THE SWITCH's TEXT IS ON A TEXT: the tie to a Script is hO.
  * hD: the filling's rows at one address are the switches' own data's: that the filling which is
    run is such a one is not said. hRd: the readers' cells are the trace's: a choice of letters.
  * It speaks only of states at which the thread stands. THE PROVER H IS A FREE LETTER, tied to no
    return of the frame's maker. At the prover that this maker returns at its fillings of record (a
    written list of ten lots, with no side at the kinds K10 and K12), and at a Said that ties the
    rounds seen to that prover's own play, the thread stands at no state from number 13 on [argued
    by reading; not typed]: there these laws hold for nothing.
  * The two closed facts: by evaluation in Lean's kernel; replayed by no independent checker.
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Cells.SeatAtLink24
import Johnson.Desc.ProofFile.Honest.K6.Cells.SeatsInside
import Johnson.Desc.ProofFile.Honest.K6.Law.ReaderAtLink24
import Johnson.Desc.ProofFile.Honest.K6.Law.CellsOnOfSym
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswerAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.WayBackFill
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedVals
import Johnson.P5J.HidBearsAtMg
import Johnson.Top.H0.K2Ties.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales is no instance in this file: no statement here can take it
in silence. An instance is taken away, none is added. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes.HonestTrace (Sz Seg MatName planeOf planMats packedCells shapeNo_in_scope)
open VerifiableInference.Desc (Chain Place Strs arrayOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open P5T (seatsAllFull)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS Readers RowDataOf declsTo drawsFit
  drawsFit_length lendsPart lookDue K2.switchData K2.withSwitchData K2.switchSeat K2.asRow
  K2.with_own)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K2 (SwitchPlace switchSent switchMsgTxt lotClosingAt publicOk switchNumIn
  switchPlaces noWord noWord_yes)
open ProofFile.Honest.K2.Law (placesW segsW places_at_head segments_at_head atLink24W atLink24_gives
  role24W servesW roomyW fitsW msgTxt_answers_head msgTxt_main_f_of)
open ProofFile.Honest.K6 (atLink24MainW atLink24Main_gives)

set_option maxRecDepth 1000000 in
/-- A CLOSED FACT, ON PUBLIC DATA: the switch's authors' public test noWord (every message with a
main row is sampled) accepts at the sending of each place of their written list. By evaluation in
Lean's kernel. -/
theorem noWordW : (placesW.all fun p => noWord (switchSent p.sizes p.others)) = true := by
  decide +kernel

/-- A CLOSED FACT. Each number below 6 is the number, in the list of Sz.ref at segment 24, of a
matrix of the head that is not the plane and has an array of its own segment. -/
theorem k6_array_of_own {a : ℕ} (ha : a < 6) :
    ∃ μ, Sz.ref.matAt 24 a = some (.head, μ) ∧ μ ≠ planeOf .head ∧
      (Sz.ref.arrayNo .head μ).isSome = true := by
  interval_cases a
  · exact ⟨.hf 0, by decide, by decide, by decide⟩
  · exact ⟨.hf 1, by decide, by decide, by decide⟩
  · exact ⟨.hf 2, by decide, by decide, by decide⟩
  · exact ⟨.hf 3, by decide, by decide, by decide⟩
  · exact ⟨.hd, by decide, by decide, by decide⟩
  · exact ⟨.hr, by decide, by decide, by decide⟩

section Filling

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- CONDITIONAL: h; hG; hp; hlk. ON PUBLIC DATA AND A READER's LETTER R, UNDER "FOR ALL". **NO
DEFAULT IS MET: AT EACH SEAT OF THE HEAD's SIX OWN MATRICES OFF THE PLANE THE SWITCHES' OWN DATA
ANSWERS "some": THE FORMAT's PACKING OF THE READER's CELLS.** -/
theorem k6_filling_at_seat (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {p : SwitchPlace} (hp : p ∈ placesW)
    (hlk : p.link = 24) {a : ℕ} (ha : a < 6) (ha' : a < (Meaning.sizesOf (At.X Zp) 24).NM)
    {i c : ℕ} (hi : i < Alg.symRows ((Meaning.sizesOf (At.X Zp) 24).m a))
    (hc : c < (Meaning.sizesOf (At.X Zp) 24).k a) (R : Readers) :
    (K2.switchData Sz.ref Zp G).at_ R [] (p.ownAddr 0)
        (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i c).2.1
        (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i c).2.2 =
      some (.inl (packedCells Sz.ref R.cells.cell 24 a i c)) := by
  obtain ⟨A, hA, hm0, -, -, hat, -, -, -⟩ := k6_seats_inside h hp hlk ha ha' hi hc
  obtain ⟨μ, hμ, hpl, ho⟩ := k6_array_of_own ha
  have hSeat := k6_seat_at_link24 h hG hp hlk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have eG : G = Bs.G₀ := Option.some.inj (hG.symm.trans (IM.Open.blank O))
  have eF : G.first = Zp.first := by
    rw [eG]
    exact IM.Open.first O
  obtain ⟨Z', hZ', -, c2, c3⟩ := P5J.three_at_pure h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  rw [eZ] at c2 c3
  obtain ⟨-, -, f3, -, -, -⟩ :=
    (H2K5.Door.made_row_gives (H2K5.Door.pins_at_head h.toAtMg).1).1
  have hM : Meaning.messageAt Zp.first.shape 24 A.message =
      some ((proofSizedFull.request.link.getD 24 default).messages.getD 0 default) := by
    rw [hm0, f3]
    exact message24W
  have hs : ((proofSizedFull.request.link.getD 24 default).messages.getD 0
      default).shape.answers ≠ 0 := by
    have q := Meaning.answers_of_shape c2 hM
    omega
  have hname : A.name = Meaning.nameOf a := by
    obtain ⟨as, -, hf⟩ := Option.bind_eq_some_iff.1 hA
    simpa using List.find?_some hf
  have hn : ProofFile.Honest.K1.labelNo A.name = some a := by
    rw [hname]
    exact ProofFile.Honest.K5.labelNo_arrayLabel (by omega)
  have hz := ProofFile.Honest.K5.cellsVals_size Sz.ref hn hμ ho
  -- Sz.ref's shape of that matrix is the plan's rows of cells and columns
  obtain ⟨-, -, sm, sk⟩ := shapeNo_in_scope h.scope h.reads h.pubOne hμ hpl
  have ep : planMats (At.X Zp) 24 = (At.X Zp).H.tl.mats := by simp [planMats]
  have et : Meaning.tlAt (At.X Zp) 24 = (At.X Zp).H.tl := by
    unfold Meaning.tlAt
    simp
  have hm' : (Meaning.sizesOf (At.X Zp) 24).m a = (Sz.ref.shapeNo 24 a).1 := by
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD a {}).m = _
    rw [et, ← ep, sm]
  have hk' : (Meaning.sizesOf (At.X Zp) 24).k a = (Sz.ref.shapeNo 24 a).2 := by
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD a {}).k = _
    rw [et, ← ep, sk]
  have hi' : i < (Sz.ref.packedShape 24 a).1 := by
    show i < Alg.symRows (Sz.ref.shapeNo 24 a).1
    rw [← hm']
    exact hi
  have hc' : c < (Sz.ref.packedShape 24 a).2 := by
    show c < (Sz.ref.shapeNo 24 a).2
    rw [← hk']
    exact hc
  have hAd : K2.switchSeat Zp G (p.ownAddr 0) = some (24, A.message) := by
    rw [hm0]
    exact hSeat
  have L := ProofFile.Honest.K5.laidData_at c3 hA hat hM hs (fun _ => 0) hAd hz hi' hc' R []
  show (ProofFile.Honest.laidData G.first.codes G.first.shape G.first.layout (K2.switchSeat Zp G)
    (fun _ => 0) (ProofFile.Honest.K1.cellsVals Sz.ref)).at_ R [] (p.ownAddr 0) _ _ = _
  rw [eF]
  refine L.trans ?_
  simp only [ProofFile.Honest.K1.cellsVals, hn]

end Filling

section Take

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (Dd : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
  (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (N fx : Nat)
  (cells : Tr → ProofFile.Honest.Cells) {G : ProofFile.Ground}

/-- OFF THE PADS' PLACES, AT MOMENT 0, AT AN OWN MESSAGE, WHERE THE TEXT ANSWERS (the terms of the
law on the switch's text that is spent here). NEVER "cellsOn is paid"; NEVER "hSym is paid" WITHOUT
hO, hLend AND THE REST. CONDITIONAL: h; hG; hp; hlk; hLend; hN; hv; hO; hD; hRd. **AT THE SEATS OF
THE HEAD's SIX OWN MATRICES OFF THE PLANE THE THREAD's WITNESS HOLDS THE IMAGE OF THE FORMAT's
PACKING OF THE PROVER's OWN CELLS**: the premise hSym of k6_cellsOn_own_of_sym, to the sign. No
default is met: at each of these seats the filling answers "some" (laidData_at). The message has a
mask row: no pad lies in its main rows; the two fences of the law that is spent (the row below the
message's main rows, the place below its main code's length) fence the seats off the entries that
the sending does not lay from data: rows that are not sent, and the tail behind the message's
length. -/
theorem k6_sym_at_take (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hp : p ∈ placesW)
    (hlk : p.link = 24)
    (hLend : lendsPart Bk (Bk.rowsOf 0) (lookDue Bk 0) ⟨p.place, 0⟩ (takePart p) = true)
    (hN : N ≤ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
      declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341).length)
    (hv : publicOk Dd lay p (segsW.take p.link) w.x = true)
    (hO : OwnMsgs Q (fun v => v = w ∧ Vd v) N (switchNumIn seatsAllFull 24 2) fx
      (switchMsgTxt 0 Dd readers (lotClosingAt lay segsW) p 2))
    (hD : ∀ (R : Readers) (r j : ℕ), (Dd w.x).at_ R [] (p.ownAddr 0) r j =
      (K2.switchData Sz.ref Zp G).at_ R [] (p.ownAddr 0) r j)
    (hRd : (readers w).cells = cells w.trace) :
    ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E → ∀ ds (a : ℕ), a < 6 →
      ∀ (ha' : a < (Meaning.sizesOf (At.X Zp) 24).NM) i' c,
        Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
          (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
            (Q.wit k m.st.input (m.st.heard ++ ds))) ⟨a, ha'⟩ i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cells m.st.input.trace).cell 24 a
          i'.val c.val) := by
  intro k s m E hT ds a ha ha' i' c
  have hval : m.st.input = w ∧ Vd m.st.input := hT.1.2.2.2.2.2.2
  have hfit : drawsFit ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
      declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341)
      m.st.heard = true := hT.1.2.1
  have hlen : N ≤ (m.st.heard ++ ds).length := by
    have e := drawsFit_length _ _ hfit
    rw [List.length_append, e]
    exact Nat.le_trans hN (Nat.le_add_right _ _)
  have g := atLink24_gives (List.all_eq_true.1 atLink24W p hp) hlk
  obtain ⟨k1, -, -, d3, an⟩ := atLink24Main_gives (List.all_eq_true.1 atLink24MainW p hp) hlk
  obtain ⟨A, -, -, -, -, -, q1, q2, q3⟩ := k6_seats_inside h hp hlk ha ha' i'.isLt c.isLt
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp' : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  -- off the pads of the copies the symbols that the reader yields are the witness's own messages'
  refine (congrFun (congrFun (congrFun (P5J.symAt_readAt h.plan.hN h.plan.hG
    (h.toAtMg.placesOff (VerifiableInference.Desc.First.K2Ties.offC_ofHead h.toAtMg))
    (Q.wit k m.st.input (m.st.heard ++ ds)) 24) ⟨a, ha'⟩) i') c).trans ?_
  show Q.msg (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).1 k
    m.st.input ((m.st.heard ++ ds).take (Q.fixedMsg
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).1)) false
    (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.1
    (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.2 = _
  rw [q1]
  -- the text answers there
  obtain ⟨y, hy⟩ := msgTxt_answers_head h.toAtMg O 0 Dd readers lay hp' 2 k m.st.input
    ((m.st.heard ++ ds).take fx) false
    (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.1
    (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.2
    (handed_of_lends hLend k) (List.all_eq_true.1 servesW p hp) (List.all_eq_true.1 roomyW p hp)
    (by rw [segments_at_head h.toAtMg O, hval.1]; exact hv) (List.all_eq_true.1 fitsW p hp)
  rw [segments_at_head h.toAtMg O] at hy
  have hmsg := hO k m.st.input (m.st.heard ++ ds) hval hlen false _ _ y hy
  rw [num_at_take h hp hlk (by rw [g.2.1]; decide) role24W] at hmsg
  rw [hmsg]
  -- which element: the law on the switch's text at a main row's entry, at own message 0
  have e2 : 1 + p.sizes.kept.length + 0 = 2 := by omega
  have L := msgTxt_main_f_of 0 Dd readers (lotClosingAt lay segsW) p k m.st.input
    ((m.st.heard ++ ds).take fx) (noWord_yes (List.all_eq_true.1 noWordW p hp)) (m := 0)
    (r := (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.1)
    (j := (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.2) (y := y)
  rw [e2] at L
  -- the message has a mask row: the list of the pad's places in its main rows is empty
  have hm1 : (((switchSent p.sizes p.others).getD 2 default).shape.maskRows != 0) = true :=
    bne_iff_ne.2 (by rw [g.2.2.1]; exact Nat.one_ne_zero)
  have hc1 : (((switchSent p.sizes p.others).getD 2 default).shape.maskRows != 0 ||
      ((switchSent p.sizes p.others).getD 2 default).shape.mainRows == 0) = true := by
    rw [hm1, Bool.true_or]
  have hpad : ((seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.1,
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.2) ∉
      ProofFile.Honest.padInMain
        (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD 2 default).shape.code
          default).ell ((switchSent p.sizes p.others).getD 2 default).shape := by
    intro hm
    unfold ProofFile.Honest.padInMain at hm
    rw [if_pos hc1] at hm
    cases hm
  rw [L (by rw [g.2.1]; decide) (beq_eq_false_iff_ne.2 d3) q2 q3 an hpad hy]
  show algebraMap Cb.Gl.F Cb.Gl.E (K2.asRow _ ((Dd m.st.input.x).at_ (readers m.st.input) []
    (p.ownAddr 0) (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.1
    (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i'.val c.val).2.2)).c0 = _
  rw [hval.1, hD, k6_filling_at_seat h hG hp hlk ha ha' i'.isLt c.isLt (readers w)]
  show algebraMap Cb.Gl.F Cb.Gl.E (ProofFile.Honest.asE (some (.inl
          (packedCells Sz.ref (readers w).cells.cell 24 a i'.val c.val)))).c0 = _
  have e10 : (ProofFile.Honest.asE (some (.inl
            (packedCells Sz.ref (readers w).cells.cell 24 a i'.val c.val)))).c0 =
      packedCells Sz.ref (readers w).cells.cell 24 a i'.val c.val :=
    (congrArg Code.Cubic.c0 (ProofFile.Honest.K5.asE_inl _)).trans (Code.Cubic.algebraMap_c0 _)
  rw [e10, hRd]

/-- NEVER "cellsOn is paid"; NEVER "hSym is paid" WITHOUT hO, hLend AND THE REST. The same where the
filling is the switches' own data joined to another lot's: hD falls, by the switch's authors'
with_own at the seat of the head's own message. -/
theorem k6_sym_at_withSwitchData (D₀ : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hp : p ∈ placesW)
    (hlk : p.link = 24)
    (hLend : lendsPart Bk (Bk.rowsOf 0) (lookDue Bk 0) ⟨p.place, 0⟩ (takePart p) = true)
    (hN : N ≤ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
      declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341).length)
    (hv : publicOk (K2.withSwitchData Sz.ref D₀ Zp G) lay p (segsW.take p.link) w.x = true)
    (hO : OwnMsgs Q (fun v => v = w ∧ Vd v) N (switchNumIn seatsAllFull 24 2) fx
      (switchMsgTxt 0 (K2.withSwitchData Sz.ref D₀ Zp G) readers (lotClosingAt lay segsW) p 2))
    (hRd : (readers w).cells = cells w.trace) :
    ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E → ∀ ds (a : ℕ), a < 6 →
      ∀ (ha' : a < (Meaning.sizesOf (At.X Zp) 24).NM) i' c,
        Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
          (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
            (Q.wit k m.st.input (m.st.heard ++ ds))) ⟨a, ha'⟩ i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cells m.st.input.trace).cell 24 a
          i'.val c.val) :=
  k6_sym_at_take h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said (K2.withSwitchData Sz.ref D₀ Zp G)
    readers lay N fx cells hG hp hlk hLend hN hv hO
    (fun R r j => K2.with_own Sz.ref D₀ Zp G w.x R [] (p.ownAddr 0) r j
      (by rw [k6_seat_at_link24 h hG hp hlk]; rfl)) hRd

/-- NEVER "cellsOn is paid". NEVER QUOTED TOWARD HIDING. CONDITIONAL: as k6_sym_at_take. **AT THESE
SEATS THE WITNESS DOES NOT HANG ON THE RUN's COINS: so nothing here masks them: that is the sender's
law**: the left side is one at any two states at which the thread stands, whatever their coins and
continuations. -/
theorem k6_sym_same_at_coins (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hp : p ∈ placesW)
    (hlk : p.link = 24)
    (hLend : lendsPart Bk (Bk.rowsOf 0) (lookDue Bk 0) ⟨p.place, 0⟩ (takePart p) = true)
    (hN : N ≤ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
      declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341).length)
    (hv : publicOk Dd lay p (segsW.take p.link) w.x = true)
    (hO : OwnMsgs Q (fun v => v = w ∧ Vd v) N (switchNumIn seatsAllFull 24 2) fx
      (switchMsgTxt 0 Dd readers (lotClosingAt lay segsW) p 2))
    (hD : ∀ (R : Readers) (r j : ℕ), (Dd w.x).at_ R [] (p.ownAddr 0) r j =
      (K2.switchData Sz.ref Zp G).at_ R [] (p.ownAddr 0) r j)
    (hRd : (readers w).cells = cells w.trace) :
    ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E →
      ∀ k' s' m' E', ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k' s' m' E' → ∀ ds ds' (a : ℕ), a < 6 →
      ∀ (ha' : a < (Meaning.sizesOf (At.X Zp) 24).NM) i' c,
        Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
          (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
            (Q.wit k m.st.input (m.st.heard ++ ds))) ⟨a, ha'⟩ i' c =
        Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
          (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
            (Q.wit k' m'.st.input (m'.st.heard ++ ds'))) ⟨a, ha'⟩ i' c := by
  intro k s m E hT k' s' m' E' hT' ds ds' a ha ha' i' c
  rw [k6_sym_at_take h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Dd readers lay N fx cells hG
      hp hlk hLend hN hv hO hD hRd k s m E hT ds a ha ha' i' c,
    k6_sym_at_take h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Dd readers lay N fx cells hG
      hp hlk hLend hN hv hO hD hRd k' s' m' E' hT' ds' a ha ha' i' c,
    hT.1.2.2.2.2.2.2.1, hT'.1.2.2.2.2.2.2.1]

end Take

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.noWordW
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_array_of_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_filling_at_seat
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_sym_at_take
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_sym_at_withSwitchData
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_sym_same_at_coins
