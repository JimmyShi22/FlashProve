-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/StreamOfSymbols.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind
K6 of the online proof): THE TIE OF THE BORROWED STREAM's CELLS, EXCHANGED FOR A SENTENCE ON ITS
SYMBOLS. One closed fact and one theorem.

WHAT IT IS NOT. An exchange: nothing is paid. The new premise, that at the stream's seats the
thread's witness holds the packing of the input's cells, is shown of no Script here. The stream is a
matrix that the head borrows: its array is another segment's; of that array's message and of its
sender nothing is said. It speaks only of states at which the thread stands. Under the library's
hypothesis h: the full size and the format's second hash function alone. Nothing on soundness, on
completeness or on what a proof hides.

WHAT IT IS. The field cellsOn of K6HeadBelow (Honest/K6/Law/ScriptBelowFree.lean) asks, inside four
ranges, that the prover's cell is the integer which the head's law reads off the thread's witness.
For the three ranges of the head's own six matrices that follows from "the symbols at their seats
are the packing of the prover's cells" (k6_cellsOn_own_of_sym, Honest/K6/Law/CellsOnOfSym.lean).
Here the same is shown for the fourth range, the stream's: matrix number 7 of segment 24. That the
cells are small enough for the packing to have one unpacking comes from the trace: every cell of the
integer model's trace at the head's segment is below 129 in absolute value (k6_headMats_small,
Honest/K6/Law/SmallOfTheTrace.lean).

  streamHasAName                          a closed fact: number 7 is, in the reference sizes' list
                                          at segment 24, the stream's name at the head, not the
                                          plane
  streamIsTiedWhereItsSymbolsArePacked    the tie inside the stream's range
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.CellsOnOfSym
import Johnson.Desc.ProofFile.Honest.K6.Law.SmallOfTheTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open Inst.Model (ppref Instance)
open OnBytes.Model.Verify (borderOf)
open OnBytes.HonestTrace (Sz Seg MatName planeOf planMats packedCells pack3 pack3_eq_pack
  pack3_cast shapeNo_in_scope theTrace cellOf ServesAt)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS CellsTieOn)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headMats headWhereOf)

/-- A CLOSED FACT. Number 7 is, in the list of the reference sizes at segment 24, the name of the
stream at the head, which is not the plane. -/
theorem _root_.ProofFile.Honest.K6.Term.streamHasAName :
    Sz.ref.matAt 24 7 = some (.head, .xbL) ∧ MatName.xbL ≠ planeOf .head :=
  ⟨by decide, by decide⟩

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
  (cells : Tr → ProofFile.Honest.Cells) {G : ProofFile.Ground}

/-- AN EXCHANGE. CONDITIONAL on the library's hypothesis h, on "G is the blank ground of the public
part" and on two premises that stay: streamSymbolsAreThePacking (at the seats of matrix number 7 of
segment 24 the thread's witness holds the packing of the input's cells) and traceIsTheModels (the
valid input's trace, read by cells, is the library's reader by labels at the integer model's trace
at a served instance). **INSIDE THE RANGE OF THE STREAM THAT THE HEAD BORROWS, THE INPUT's CELL IS
THE INTEGER THAT THE HEAD's LAW READS OFF THE THREAD's WITNESS.** -/
theorem _root_.ProofFile.Honest.K6.Term.streamIsTiedWhereItsSymbolsArePacked
    (groundIsBlank : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (streamSymbolsAreThePacking : ∀ k s m E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
      ∀ ds (ha' : 7 < (Meaning.sizesOf (At.X Zp) 24).NM) i' c,
        Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
          (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
            (Q.wit k m.st.input (m.st.heard ++ ds))) ⟨7, ha'⟩ i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cells m.st.input.trace).cell 24 7
          i'.val c.val))
    (traceIsTheModels : Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref), ServesAt (At.X Zp) i xI ∧
      cells w.trace = ⟨cellOf (At.X Zp) (theTrace (At.X Zp) i xI)⟩) :
    CellsTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
      (fun _ => some ())
      (fun v a rr c =>
        (ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells v.trace) a rr c) : Int))
      (fun _ _ _ v a rr c => P5J.ownQ (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
        (P5J.At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (seatLay (At.X Zp) (At.layout Zp) (At.num Zp)) v 24 a rr c)
      (fun a rr c => InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y) a rr c ∧
        ¬ a ≠ (At.X Zp).hS.NHf + 3) := by
  intro k s m En hT u _ ds a rr c hboth
  obtain ⟨hin, hnot⟩ := hboth
  have hP := h.pubOne
  have hN4 : (At.X Zp).hS.NHf = 4 := (k6_sizes_own h).2.1
  obtain rfl : a = 7 := by
    have e : a = (At.X Zp).hS.NHf + 3 := Classical.not_not.1 hnot
    omega
  obtain ⟨g1, g2, g3⟩ := Came.inSizes_in_scope h.scope h.reads hP 7 rr c hin
  obtain ⟨hμ, hpl⟩ := ProofFile.Honest.K6.Term.streamHasAName
  -- the cells are small: they are the integer model's trace's
  have hval : m.st.input = w ∧ Vd m.st.input := hT.1.2.2.2.2.2.2
  obtain ⟨ew, hVd⟩ := hval
  rw [ew] at hVd
  obtain ⟨i₀, xI, Sv, hcell⟩ := traceIsTheModels hVd
  have small : ∀ i : ℕ, |(ZMod.valMinAbs
      (headMats (headWhereOf Zp G) (cells m.st.input.trace) 7 i c) : Int)| < 2 ^ 18 := by
    intro i
    rw [ew, hcell]
    exact lt_trans (k6_headMats_small h groundIsBlank Sv 7 i c) (by norm_num)
  -- the reference sizes' shape of that matrix is the plan's rows of cells and columns
  obtain ⟨-, -, sm, sk⟩ := shapeNo_in_scope h.scope h.reads hP hμ hpl
  have ep : planMats (At.X Zp) 24 = (At.X Zp).H.tl.mats := by simp [planMats]
  have et : Meaning.tlAt (At.X Zp) 24 = (At.X Zp).H.tl := by
    unfold Meaning.tlAt
    simp
  have eN : Sz.ref.shapeNo 24 7 = Sz.ref.shape .head .xbL := by
    unfold Sz.shapeNo
    rw [hμ]
  have hm' : (Meaning.sizesOf (At.X Zp) 24).m 7 = (Sz.ref.shape .head .xbL).1 := by
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD 7 {}).m = _
    rw [et, ← ep, sm, eN]
  have hk' : (Meaning.sizesOf (At.X Zp) 24).k 7 = (Sz.ref.shape .head .xbL).2 := by
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD 7 {}).k = _
    rw [et, ← ep, sk, eN]
  have hb17 : (Meaning.sizesOf (At.X Zp) 24).beta = 2 ^ 17 := rfl
  have hr20 : (Meaning.sizesOf (At.X Zp) 24).rad = 2 ^ 20 := rfl
  have key := ProofFile.Honest.Small.ownOf_of_column (s := Meaning.sizesOf (At.X Zp))
    (y := fun k' => Meaning.symAt (Meaning.sizesOf (At.X Zp) k')
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) k')
      (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) k'
        (Q.wit k m.st.input (m.st.heard ++ ds))))
    (k := 24) Cb.Gl.p (OnBytes.Tie.Pv.Tail.sizeOf_uniq (Meaning.tlAt (At.X Zp) 24)) ⟨7, g1⟩ ⟨c, g2⟩
    (a := fun i => (ZMod.valMinAbs
      ((cells m.st.input.trace).cell 24 MatName.xbL.label i.val c) : Int))
    (by
      intro i
      have hs := small i.val
      rw [k6_headMats_label h groundIsBlank hμ] at hs
      have e18 : (2 : Int) * (((Meaning.sizesOf (At.X Zp) 24).beta : ℕ) : Int) = 2 ^ 18 := by
        rw [hb17]
        norm_num
      rw [e18]
      exact hs)
    (by
      intro i'
      have e1 := streamSymbolsAreThePacking k s m En hT ds g1 i' ⟨c, g2⟩
      have hc2 : c < (Sz.ref.shape .head .xbL).2 := by
        rw [← hk']
        exact g2
      -- at every number j: i' itself lives in a type that names the size
      have e2 : ∀ j : ℕ, packedCells Sz.ref (cells m.st.input.trace).cell 24 7 j c =
          pack3 ((Meaning.sizesOf (At.X Zp) 24).m 7)
            (fun r => (cells m.st.input.trace).cell 24 MatName.xbL.label r c) j := by
        intro j
        unfold packedCells
        rw [hμ]
        show (if c < (Sz.ref.shape .head .xbL).2 then
          pack3 (Sz.ref.shape .head .xbL).1
            (fun r => (cells m.st.input.trace).cell 24 MatName.xbL.label r c) j else 0) = _
        rw [if_pos hc2, hm']
      have e3 : ∀ j : ℕ, pack3 ((Meaning.sizesOf (At.X Zp) 24).m 7)
            (fun r => (cells m.st.input.trace).cell 24 MatName.xbL.label r c) j =
          ((pack3 ((Meaning.sizesOf (At.X Zp) 24).m 7) (fun r =>
            (ZMod.valMinAbs ((cells m.st.input.trace).cell 24 MatName.xbL.label r c) : Int)) j :
              Int) : Cb.Gl.F) := by
        intro j
        rw [pack3_cast]
        simp only [ZMod.coe_valMinAbs]
      have erz : (((Meaning.sizesOf (At.X Zp) 24).rad : ℕ) : Int) = 2 ^ 20 := by
        rw [hr20]
        norm_num
      refine e1.trans ?_
      show algebraMap Cb.Gl.F Cb.Gl.E
        (packedCells Sz.ref (cells m.st.input.trace).cell 24 7 i'.val c) = _
      rw [e2 i'.val, e3 i'.val, map_intCast, pack3_eq_pack, erz])
    ⟨rr, g3⟩
  show (ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells m.st.input.trace) 7 rr c) : Int) =
    Meaning.ownOf (Meaning.sizesOf (At.X Zp)) (fun k' =>
      Meaning.symAt (Meaning.sizesOf (At.X Zp) k')
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) k')
      (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) k'
        (Q.wit k m.st.input (m.st.heard ++ ds)))) 24 7 rr c
  rw [k6_headMats_label h groundIsBlank hμ]
  exact key.symm

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms ProofFile.Honest.K6.Term.streamHasAName
#print axioms ProofFile.Honest.K6.Term.streamIsTiedWhereItsSymbolsArePacked
