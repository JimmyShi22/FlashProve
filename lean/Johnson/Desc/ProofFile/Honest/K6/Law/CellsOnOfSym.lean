-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/CellsOnOfSym.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6): THE
FIELD cellsOn OF `K6HeadBelow` (Honest/K6/Law/ScriptBelowFree.lean), EXCHANGED FOR THREE PREMISES.
NEVER "cellsOn is paid". No definition; three theorems.

  `k6_name_of_own`               a closed fact: each number below 6 is, in the list of `Sz.ref`
                                 at segment 24, the number of a matrix of the head, not the plane
  `k6_cellsOn_own_of_sym`        h, hG, hSym, hSmall: the field's text inside the three ranges of
                                 the head's own matrices (the wide one's four parts, the
                                 activations, the rows)
  `k6_cellsOn_of_sym_and_stream` with hStream: the field, to the sign

THE THREE PREMISES, EACH SHOWN BY NOBODY THAT WE KNOW.
  * hSym: at the seats of the six matrices the thread's witness holds the packing
    (`packedCells`, Johnson/HonestTrace/Packed.lean) of the prover's own cells. It is meant as the
    end of a statement that is not typed yet: from what it would follow is not said here.
  * hSmall: the prover's cells inside the three ranges are below 2^18 in absolute value: A PREMISE
    ON THE INPUT's TRACE.
  * hStream: the field's own text inside the fourth range: the stream, a matrix that the head
    borrows: its array is another segment's and reaches the head's link in a kept copy.

By. `ownOf_of_column` (Honest/Small/OwnOfColumn.lean); `k6_headMats_label`
(Honest/K6/Cells/HeadMatsLabels.lean); `k6_sizes_own` (Honest/K6/Cells/SizesAtHead.lean);
`cellsTieOn_of_two` (Honest/K6/Cells/TieOfTwo.lean); the library's `Came.inSizes_in_scope`,
`shapeNo_in_scope` (Johnson/Goal/HonestTrace/ShapesAtRefInScope.lean), `pack3_eq_pack`,
`pack3_cast`, `OnBytes.Tie.Pv.Tail.sizeOf_uniq`.

What it is not.
  * No Script is laid; no member of `K6HeadBelow` is built here.
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Small.OwnOfColumn
import Johnson.Desc.ProofFile.Honest.K6.Cells.HeadMatsLabels
import Johnson.Desc.ProofFile.Honest.K6.Cells.SizesAtHead
import Johnson.Desc.ProofFile.Honest.K6.Cells.TieOfTwo
import Johnson.Desc.ProofFile.Honest.K6.Law.ScriptBelowFree
import Johnson.Goal.HonestTrace.ShapesAtRefInScope
import OnBytes.Tie.Pv.Tail.SizeUniq

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes.Model.Verify (borderOf)
open OnBytes.HonestTrace (Sz Seg MatName planeOf planMats packedCells pack3 pack3_eq_pack
  pack3_cast shapeNo_in_scope)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS CellsTieOn)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headMats headWhereOf cellsTieOn_of_two)

/-- A CLOSED FACT. Each number below 6 is the number, in the list of Sz.ref at segment 24, of a
matrix of the head that is not the plane. -/
theorem k6_name_of_own {a : ℕ} (ha : a < 6) :
    ∃ μ, Sz.ref.matAt 24 a = some (.head, μ) ∧ μ ≠ planeOf .head := by
  interval_cases a
  · exact ⟨.hf 0, by decide, by decide⟩
  · exact ⟨.hf 1, by decide, by decide⟩
  · exact ⟨.hf 2, by decide, by decide⟩
  · exact ⟨.hf 3, by decide, by decide⟩
  · exact ⟨.hd, by decide, by decide⟩
  · exact ⟨.hr, by decide, by decide⟩

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

/-- NEVER "cellsOn is paid". CONDITIONAL: h; hG; hSym; hSmall. **THE TEXT OF THE FIELD cellsOn
INSIDE THE THREE RANGES OF THE HEAD's OWN MATRICES, FROM "the symbols at their seats are the packing
of the prover's own cells".** hSym is a premise, shown by nobody that we know. -/
theorem k6_cellsOn_own_of_sym (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hSym : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E → ∀ ds (a : ℕ), a < 6 →
      ∀ (ha' : a < (Meaning.sizesOf (At.X Zp) 24).NM) i' c,
        Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
          (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
            (Q.wit k m.st.input (m.st.heard ++ ds))) ⟨a, ha'⟩ i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cells m.st.input.trace).cell 24 a
          i'.val c.val))
    (hSmall : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E → ∀ a rr c,
      InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y) a rr c → a ≠ (At.X Zp).hS.NHf + 3 →
      |(ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells m.st.input.trace) a rr c) : Int)| <
        2 ^ 18) :
    CellsTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
      (fun _ => some ())
      (fun v a rr c =>
        (ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells v.trace) a rr c) : Int))
      (fun _ _ _ v a rr c => P5J.ownQ (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
        (P5J.At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (seatLay (At.X Zp) (At.layout Zp) (At.num Zp)) v 24 a rr c)
      (fun a rr c => InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y) a rr c ∧
        a ≠ (At.X Zp).hS.NHf + 3) := by
  intro k s m En hT u _ ds a rr c hboth
  obtain ⟨hin, hne⟩ := hboth
  have hP := h.pubOne
  obtain ⟨-, hN4, s0, s4, s5⟩ := k6_sizes_own h
  obtain ⟨g1, g2, g3⟩ := Came.inSizes_in_scope h.scope h.reads hP a rr c hin
  have ha6 : a < 6 := by
    rcases hin with ⟨q, -, -⟩ | ⟨q, -, -⟩ | ⟨q, -, -⟩ | ⟨q, -, -⟩ <;> omega
  obtain ⟨μ, hμ, hpl⟩ := k6_name_of_own ha6
  -- Sz.ref's shape of that matrix is the plan's rows of cells and columns
  obtain ⟨-, -, sm, sk⟩ := shapeNo_in_scope h.scope h.reads hP hμ hpl
  have ep : planMats (At.X Zp) 24 = (At.X Zp).H.tl.mats := by simp [planMats]
  have et : Meaning.tlAt (At.X Zp) 24 = (At.X Zp).H.tl := by
    unfold Meaning.tlAt
    simp
  have eN : Sz.ref.shapeNo 24 a = Sz.ref.shape .head μ := by
    unfold Sz.shapeNo
    rw [hμ]
  have hm' : (Meaning.sizesOf (At.X Zp) 24).m a = (Sz.ref.shape .head μ).1 := by
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD a {}).m = _
    rw [et, ← ep, sm, eN]
  have hk' : (Meaning.sizesOf (At.X Zp) 24).k a = (Sz.ref.shape .head μ).2 := by
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD a {}).k = _
    rw [et, ← ep, sk, eN]
  have hb17 : (Meaning.sizesOf (At.X Zp) 24).beta = 2 ^ 17 := rfl
  have hr20 : (Meaning.sizesOf (At.X Zp) 24).rad = 2 ^ 20 := rfl
  -- every row of cells below the size lies in the range
  have hrow : ∀ i, i < (Meaning.sizesOf (At.X Zp) 24).m a →
      InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y) a i c := by
    intro i hi
    have hc := g2
    have h3 : a < 4 ∨ a = 4 ∨ a = 5 := by omega
    rcases h3 with q | q | q
    · rw [(s0 a q).1] at hi
      rw [(s0 a q).2] at hc
      exact Or.inl ⟨by omega, hi, hc⟩
    · subst q
      rw [s4.1] at hi
      rw [s4.2] at hc
      exact Or.inr (Or.inl ⟨hN4.symm, hi, hc⟩)
    · subst q
      rw [s5.1] at hi
      rw [s5.2] at hc
      exact Or.inr (Or.inr (Or.inl ⟨by omega, hi, hc⟩))
  have key := ProofFile.Honest.Small.ownOf_of_column (s := Meaning.sizesOf (At.X Zp))
    (y := fun k' => Meaning.symAt (Meaning.sizesOf (At.X Zp) k')
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) k')
      (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) k'
        (Q.wit k m.st.input (m.st.heard ++ ds))))
    (k := 24) Cb.Gl.p (OnBytes.Tie.Pv.Tail.sizeOf_uniq (Meaning.tlAt (At.X Zp) 24)) ⟨a, g1⟩ ⟨c, g2⟩
    (a := fun i => (ZMod.valMinAbs ((cells m.st.input.trace).cell 24 μ.label i.val c) : Int))
    (by
      intro i
      have hs := hSmall k s m En hT a i.val c (hrow i.val i.isLt) hne
      rw [k6_headMats_label h hG hμ] at hs
      have e18 : (2 : Int) * (((Meaning.sizesOf (At.X Zp) 24).beta : ℕ) : Int) = 2 ^ 18 := by
        rw [hb17]
        norm_num
      rw [e18]
      exact hs)
    (by
      intro i'
      have e1 := hSym k s m En hT ds a ha6 g1 i' ⟨c, g2⟩
      have hc2 : c < (Sz.ref.shape .head μ).2 := by
        rw [← hk']
        exact g2
      -- at every number j: i' itself lives in a type that names the size
      have e2 : ∀ j : ℕ, packedCells Sz.ref (cells m.st.input.trace).cell 24 a j c =
          pack3 ((Meaning.sizesOf (At.X Zp) 24).m a)
            (fun r => (cells m.st.input.trace).cell 24 μ.label r c) j := by
        intro j
        unfold packedCells
        rw [hμ]
        show (if c < (Sz.ref.shape .head μ).2 then
          pack3 (Sz.ref.shape .head μ).1
            (fun r => (cells m.st.input.trace).cell 24 μ.label r c) j else 0) = _
        rw [if_pos hc2, hm']
      have e3 : ∀ j : ℕ, pack3 ((Meaning.sizesOf (At.X Zp) 24).m a)
            (fun r => (cells m.st.input.trace).cell 24 μ.label r c) j =
          ((pack3 ((Meaning.sizesOf (At.X Zp) 24).m a) (fun r =>
            (ZMod.valMinAbs ((cells m.st.input.trace).cell 24 μ.label r c) : Int)) j : Int) :
              Cb.Gl.F) := by
        intro j
        rw [pack3_cast]
        simp only [ZMod.coe_valMinAbs]
      have erz : (((Meaning.sizesOf (At.X Zp) 24).rad : ℕ) : Int) = 2 ^ 20 := by
        rw [hr20]
        norm_num
      refine e1.trans ?_
      show algebraMap Cb.Gl.F Cb.Gl.E
        (packedCells Sz.ref (cells m.st.input.trace).cell 24 a i'.val c) = _
      rw [e2 i'.val, e3 i'.val, map_intCast, pack3_eq_pack, erz])
    ⟨rr, g3⟩
  show (ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells m.st.input.trace) a rr c) : Int) =
    Meaning.ownOf (Meaning.sizesOf (At.X Zp)) (fun k' =>
      Meaning.symAt (Meaning.sizesOf (At.X Zp) k')
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) k')
      (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) k'
        (Q.wit k m.st.input (m.st.heard ++ ds)))) 24 a rr c
  rw [k6_headMats_label h hG hμ]
  exact key.symm

/-- NEVER "cellsOn is paid": AN EXCHANGE. CONDITIONAL: h; hG; hSym; hSmall; hStream. **THE FIELD
cellsOn, TO THE SIGN**, for these three premises; hStream is the field's own text inside the range
of the stream, which the head borrows: shown by nobody that we know. -/
theorem k6_cellsOn_of_sym_and_stream (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hSym : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E → ∀ ds (a : ℕ), a < 6 →
      ∀ (ha' : a < (Meaning.sizesOf (At.X Zp) 24).NM) i' c,
        Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
          (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
            (Q.wit k m.st.input (m.st.heard ++ ds))) ⟨a, ha'⟩ i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cells m.st.input.trace).cell 24 a
          i'.val c.val))
    (hSmall : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E → ∀ a rr c,
      InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y) a rr c → a ≠ (At.X Zp).hS.NHf + 3 →
      |(ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells m.st.input.trace) a rr c) : Int)| <
        2 ^ 18)
    (hStream : CellsTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
      (fun _ => some ())
      (fun v a rr c =>
        (ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells v.trace) a rr c) : Int))
      (fun _ _ _ v a rr c => P5J.ownQ (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
        (P5J.At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (seatLay (At.X Zp) (At.layout Zp) (At.num Zp)) v 24 a rr c)
      (fun a rr c => InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y) a rr c ∧
        ¬ a ≠ (At.X Zp).hS.NHf + 3)) :
    CellsTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
      (fun _ => some ())
      (fun v a rr c =>
        (ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells v.trace) a rr c) : Int))
      (fun _ _ _ v a rr c => P5J.ownQ (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
        (P5J.At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (seatLay (At.X Zp) (At.layout Zp) (At.num Zp)) v 24 a rr c)
      (InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y)) :=
  cellsTieOn_of_two (P := fun a _ _ => a ≠ (At.X Zp).hS.NHf + 3)
    (k6_cellsOn_own_of_sym h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells hG hSym hSmall)
    hStream

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_name_of_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_cellsOn_own_of_sym
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_cellsOn_of_sym_and_stream
