-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadCellsAtCaller.lean: THE CELLS THAT THE LOOKUP'S CALLER AT THE OUTPUT HEAD
READS OFF THE TABLE'S WITNESS (Johnson/Desc/First/Look/K3CallerHead.lean: headCells at
K3LayGoodIn.lean's layMs w: what the table's item "worth 24 3" speaks of) AND THE CELLS THAT THE
HEAD'S LAW READS OFF THE SAME WITNESS (Law/K6Cut.lean: compCut w) ARE THE SAME INSIDE THE RANGES
THAT THE HEAD'S RELATION NAMES: the assembly of Law/HeadCellsMeet.lean and Law/HeadSymsMeet.lean.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.Came).
  tlAt_head: the plan's entry for segment 24 is the public parameters' head's.
  sameCells_caller: SameCells (headCells (adrOf ...) x Wp.H.tl D rad oW wOf nr nc (layMs x D rad oW
      seatT arr msgW w)) (compCut ... w).1.
  fourMeet_caller: the same without the weights: the four tables of integers agree AT EVERY WITNESS
      (no premise on the witness is left: SmallH holds by the make).
  mask_meets: THE MASK ROW: compCut's second component, read into the field, is the caller's reading
      headNu at the places "mask": under the like facts at the link's own first message with a mask
      row; at a mask row that lies in one row of its table.
WHAT sameCells_caller RESTS ON, ALL NAMED. ON PUBLIC DATA ALONE: InRanges (the geometry) · hsz (the
four ranges
lie inside the plan's sizes) · the test laidThere · PlanK6's clause named (p1) · CallsSeated
(eight facts a matrix) · the caller's layout and codes are the table's. ON THE WITNESS:
SmallH of segment 24's own integers (what the table's item "constr 24 small" says at
headPartK6) · hW: the caller's weights are whOf of the witness's cells.

Every letter under "there is": none.
What it does not say. None of the premises is shown here. By Law/CellsAlike.lean the conclusion
gives the same key tables and the same two corner values: that step stands elsewhere. Nothing on
soundness.
-/
import Johnson.Desc.First.Look.K3HeadGoodIn
import Johnson.Desc.Kinds.Law.HeadCellsMeet
import Johnson.Desc.Kinds.Law.HeadSymsMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes OnBytes.Params
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles (layMs)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls wOfE msgLay)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce)
open Norm (d)

theorem tlAt_head (Wp : OnBytes.Model.Verify.Public) : Meaning.tlAt Wp 24 = Wp.H.tl := by
  unfold Meaning.tlAt
  simp

/-- **The caller's cells and the law's, off one witness.** -/
theorem sameCells_caller [Sizes] {rows cols : Nat} {Tok : Type} (cs : OnBytes.Codes)
    (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
    (lay : ReqLayout) (num : Nat → Nat → Nat) (pl : Nat → Nat × Bool × Nat × Nat)
    (x : First.Look.Place) (D : Sent) (rad : OracleShape → Nat) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → Nat → Nat → Cb.Gl.E) (nr nc : Nat)
    (seatT : Fin (sigListCalls D rad x.link).length → Nat × Nat)
    (msgW : Wit (Fin rows → Fin cols → GE) Tok MsgT → oW.Msg)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hG : InRanges Wp.hS Wp.HLy (borderOf Wp.y))
    (hsz : ∀ a r c, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c →
      a < (Meaning.sizesOf Wp 24).NM ∧ c < (Meaning.sizesOf Wp 24).k a ∧
        r < (Meaning.sizesOf Wp 24).m a)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay = true) (hlay : D.layout = lay)
    (hcs : D.codes = cs)
    (p1 : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      namedOnce arr N 24 (seatLay Wp lay num 24 μ r c).1 = true)
    (hC : CallsSeated (ColFour Wp.hS Wp.HLy (borderOf Wp.y)) arr msR N Wp lay num D rad x.link
        seatT)
    (hS : OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y)
      (P5J.ownQ cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp lay num) w 24))
    (hW : ∀ k v, k < d → v < V →
      intW (Inst.Model.Head.Hof (wOfE (msgLay x Wp.H.tl D rad oW wOf nr nc
        (layMs x D rad oW seatT arr msgW w))) k v) = whOf w.cells k v) :
    SameCells
      (headCells (adrOf Wp.hS Wp.HLy (borderOf Wp.y)) x Wp.H.tl D rad oW wOf nr nc
        (layMs x D rad oW seatT arr msgW w))
      (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp lay num) Wp pl w).1 := by
  have e := tlAt_head Wp
  rw [← e] at hW ⊢
  exact sameCells_head cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp lay num) Wp pl _ w hG
    (entriesMeet_of_syms cs arr msR N Wp (seatLay Wp lay num) x D rad oW wOf nr nc _ w hsz
      fun μ c hcol i' => syms_meet _ cs arr msR N Wp lay num D rad x.link seatT w T hlay hcs p1 hC μ
          c
        hcol i') hS hW

/-- **The same without the weights: at EVERY witness.** The four tables of integers, one by one. -/
theorem fourMeet_caller [Sizes] {rows cols : Nat} {Tok : Type} (cs : OnBytes.Codes)
    (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
    (lay : ReqLayout) (num : Nat → Nat → Nat) (pl : Nat → Nat × Bool × Nat × Nat)
    (x : First.Look.Place) (D : Sent) (rad : OracleShape → Nat) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → Nat → Nat → Cb.Gl.E) (nr nc : Nat)
    (seatT : Fin (sigListCalls D rad x.link).length → Nat × Nat)
    (msgW : Wit (Fin rows → Fin cols → GE) Tok MsgT → oW.Msg)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hG : InRanges Wp.hS Wp.HLy (borderOf Wp.y))
    (hsz : ∀ a r c, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c →
      a < (Meaning.sizesOf Wp 24).NM ∧ c < (Meaning.sizesOf Wp 24).k a ∧
        r < (Meaning.sizesOf Wp 24).m a)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay = true) (hlay : D.layout = lay)
    (hcs : D.codes = cs)
    (p1 : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      namedOnce arr N 24 (seatLay Wp lay num 24 μ r c).1 = true)
    (hC : CallsSeated (ColFour Wp.hS Wp.HLy (borderOf Wp.y)) arr msR N Wp lay num D rad x.link
        seatT) :
    (∀ M f t, (M = .wide ∧ f < 4 * d + 6 * JV ∨ M = .act ∧ f < 2 * d ∨ M = .row ∧ f < NR + 21) →
      t < Norm.T →
      (headCells (adrOf Wp.hS Wp.HLy (borderOf Wp.y)) x Wp.H.tl D rad oW wOf nr nc
        (layMs x D rad oW seatT arr msgW w)).cell M f t =
      (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp lay num) Wp pl w).1.cell M f t) ∧
    ∀ f t, f < 5 * d → t < Norm.T →
      (headCells (adrOf Wp.hS Wp.HLy (borderOf Wp.y)) x Wp.H.tl D rad oW wOf nr nc
        (layMs x D rad oW seatT arr msgW w)).stream f t =
      (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp lay num) Wp pl w).1.stream f t := by
  have e := tlAt_head Wp
  rw [← e]
  have hE := entriesMeet_of_syms cs arr msR N Wp (seatLay Wp lay num) x D rad oW wOf nr nc
    (layMs x D rad oW seatT arr msgW w) w hsz
    fun μ c hcol i' => syms_meet _ cs arr msR N Wp lay num D rad x.link seatT w T hlay hcs p1 hC μ c
      hcol i'
  have hS := smallH_own cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp lay num) Wp w
    (by rw [beta_landed]; norm_num) (by rw [beta_landed]; norm_num)
  refine ⟨fun M f t hM ht => ?_, fun f t hf ht =>
    cell_meets cs arr msR N _ _ Wp _ w hE hS _ _ _ (hG.stream f t hf ht)⟩
  rcases hM with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩
  · exact cell_meets cs arr msR N _ _ Wp _ w hE hS _ _ _ (hG.wide f t hf ht)
  · exact cell_meets cs arr msR N _ _ Wp _ w hE hS _ _ _ (hG.act f t hf ht)
  · exact cell_meets cs arr msR N _ _ Wp _ w hE hS _ _ _ (hG.row f t hf ht)

/-- SameCells is symmetric. -/
theorem SameCells.symm' [Sizes] {c c' : NCells} (h : SameCells c c') : SameCells c' c :=
  ⟨fun f t hf ht => (h.wide f t hf ht).symm, fun f t hf ht => (h.act f t hf ht).symm,
    fun f t hf ht => (h.row f t hf ht).symm, fun f t hf ht => (h.stream f t hf ht).symm,
    fun k v hk hv => (h.Wh k v hk hv).symm⟩

/-- **THE MASK ROW: the law's, read, is the caller's reading of the places "mask".** At a mask row
that lies in one row of its table (rb = 0). -/
theorem mask_meets {rows cols : Nat} {Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (n : Nat) (adr : HeadAdr) (x : First.Look.Place) (tl : OnBytes.Model.HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → Nat → Nat → Cb.Gl.E)
    (nr nc : Nat) (seatT : Fin (sigListCalls D rad x.link).length → Nat × Nat)
    (msgW : Wit (Fin rows → Fin cols → GE) Tok MsgT → oW.Msg)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (m0 : Nat) (xt : Nat × Nat) (y : Mem)
    (hns : x.ns = Wp.H.ns) (hcs : D.codes = cs)
    (hk : (First.Look.keptAt D x.link).length + m0 < (sigListCalls D rad x.link).length)
    (h1 : ((First.Look.messagesAt D x.link).findIdx? fun z => z.shape.maskRows != 0) = some m0)
    (h5 : 0 < ((sigListCalls D rad x.link).get
      ⟨(First.Look.keptAt D x.link).length + m0, hk⟩).1.maskRows)
    (h6 : ∀ j, j < Wp.H.ns → j < (Johnson.Pack.pMask D.codes ((sigListCalls D rad x.link).get
      ⟨(First.Look.keptAt D x.link).length + m0, hk⟩).1).ell)
    (hseat : seatT ⟨(First.Look.keptAt D x.link).length + m0, hk⟩ = xt)
    (hshape : ((sigListCalls D rad x.link).get
      ⟨(First.Look.keptAt D x.link).length + m0, hk⟩).1 = (y.1.l.get y.2).1)
    (g1 : namedOnce arr N 24 n = true) (hg : xt ∈ N.group 24) (hn : arr xt.1 xt.2 = n)
    (hy : (msR.find? fun y => Decidable.decide (Sound.seatOf y = xt)) = some y) (j : Nat) :
    rd ((compCut cs arr msR N s seat Wp (plAt n 0) w).2 j) =
      VerifiableInference.OnPublicFiles.headNu adr x tl D rad oW wOf nr nc seatT arr msgW w (.mask j) :=
          by
  have e2 : (compCut cs arr msR N s seat Wp (plAt n 0) w).2 =
      maskQ cs arr msR N 24 Wp.H.ns (plAt n 0) w := rfl
  rw [e2]
  show _ = First.Look.msgLay x tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w)
    (First.Look.lyMask x.ns tl nr nc j)
  unfold First.Look.lyMask
  by_cases hj : j < Wp.H.ns
  · rw [rd_maskQ cs arr msR N 24 Wp.H.ns _ w j hj, First.Look.finOf_some (hns ▸ hj)]
    show Sound.readAt cs arr msR N 24 w n true (j % 2 ^ 0) (j / 2 ^ 0) =
      (First.Look.valAt D.codes (sigListCalls D rad x.link) (First.Look.seatCalls D x.link)
        (Sound.msgsOf D.codes (sigListCalls D rad x.link) seatT arr w) (.mask j)).getD 0
    rw [mask_of_calls D rad x.link seatT arr w j m0 hk h1 h5 (h6 j hj),
      sym_of_table cs arr msR N w n xt y g1 hg hn hy true, hseat, hshape, hcs, hn]
    simp [Nat.mod_one]
  · have e0 : First.Look.finOf x.ns j = none := by
      unfold First.Look.finOf
      rw [dif_neg (hns ▸ hj)]
    rw [e0]
    unfold maskQ
    rw [if_neg hj]
    exact OnBytes.Slice.readE_zero

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.tlAt_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.sameCells_caller
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.mask_meets
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.fourMeet_caller
