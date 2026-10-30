-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormMake.lean: THE FORM's HALF: THE LINK's THREE MAKERS RETURN A ROW ((eq_phi),
Johnson/Desc/K15/K15.lean; (rec_gamma), (loc_x), Johnson/Desc/K14/Text.lean), AND THE GROUND TAKES
ROWS THAT MEET THE SOUNDNESS SIDE's SENTENCES (RowClauses,
Johnson/Desc/First/Batch/Law/DoorTests.lean): addRowP
and addRowsP (Johnson/Desc/First/Base/Ground.lean) return, and the record behind is written out.

Main names.
  cut_some        a vector without a written-out factor can be cut.
  eqPhi_some, recGamma_some, locX_some   the makers return a row: from lengths and sizes alone.
  placeOk_congr, RowClauses.congr   the sentences read of the statement its messages and codes
    alone, and of the group its members and its mark.
  addRowP_yes, addRowsFrom_yes, addRowsP_yes   the ground takes the rows.

Limits. FOR ALL DRAWS: no premise on a drawn value but a length. Nothing on a block: who hands the
lengths and sizes is the caller's.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormRowsLaws
import Johnson.Prover.Link.FormDoorLaws
import OnBytes.Slice.BlkTensCut
import OnBytes.Slice.ProgCodes
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Ground
open _root_.Desc.Plain (DState)

/-- **A vector without a written-out factor can be cut.** -/
theorem cut_some (v : Tensor) (start count len : Nat) (hd : v.denseVars = [])
    (hv : start + count ≤ v.vars) (hl : len ≤ 2 ^ count) :
    ∃ L, tensorBelow v start count len = some L := by
  rw [tensorBelow_plain_at v hd, if_neg]
  · split_ifs <;> exact ⟨_, rfl⟩
  · rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega

/-- **(eq_phi) is made.** -/
theorem eqPhi_some (S : LinkShape) (phi : List E) (o0 o1 : FoldedRow)
    (h : phi.length = S.entryBits) : ∃ row, Desc.K15.eqPhi S phi o0 o1 = some row := by
  have hc : S.cut ≤ 2 ^ S.entryBits := Nat.le_trans (Nat.sub_le _ _) (le_two_pow_ceilLog2 _)
  obtain ⟨plus, hp⟩ := cut_some (Tensor.eq phi oneE) 0 S.entryBits S.cut rfl
    (by rw [vars_eq, h]; omega) hc
  obtain ⟨minus, hm⟩ := cut_some (Tensor.eq phi (negE oneE)) 0 S.entryBits S.cut rfl
    (by rw [vars_eq, h]; omega) hc
  refine ⟨o1.addAll (o0.addAll {} plus) minus, ?_⟩
  unfold Desc.K15.eqPhi
  rw [hp, hm, h]
  simp [guard]

/-- A loop that looks two arrays up at places inside them returns. -/
theorem foldlM_some {α : Type} (f : E → α → Option E) : ∀ (l : List α) (a : E),
    (∀ x ∈ l, ∀ a, ∃ b, f a x = some b) → ∃ b, l.foldlM f a = some b
  | [], a, _ => ⟨a, rfl⟩
  | x :: l, a, h => by
    obtain ⟨b, hb⟩ := h x List.mem_cons_self a
    obtain ⟨c, hc⟩ := foldlM_some f l b fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact ⟨c, by rw [List.foldlM_cons, hb]; exact hc⟩

/-- **(rec_gamma) is made.** -/
theorem recGamma_some (s : IndexShape) (seed : SampleSeed) (a : Nat) (w y : Array E)
    (u : FoldedRow) (hz : seed.z.length = s.cubeBits) (hw : s.rows ≤ w.size)
    (ha : a < s.answers) (hy : s.rows * s.answers ≤ y.size) :
    ∃ row, Desc.K14.recGamma s seed a w y u = some row := by
  obtain ⟨L, hL⟩ := cut_some (Tensor.eq seed.z) 0 s.cubeBits s.code.ell rfl
    (by rw [vars_eq, hz]; omega) (le_two_pow_ceilLog2 _)
  obtain ⟨sum, hs⟩ := foldlM_some
    (fun t r => do pure (maddE t (← w[r]?) (← y[r * s.answers + a]?))) (List.range s.rows) zeroE
    fun r hr t => by
      have hr' : r < s.rows := List.mem_range.1 hr
      have h1 : r < w.size := Nat.lt_of_lt_of_le hr' hw
      have h2 : r * s.answers + a < y.size := by
        have : (r + 1) * s.answers ≤ s.rows * s.answers := Nat.mul_le_mul_right _ hr'
        rw [Nat.succ_mul] at this
        omega
      simp only [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
      exact ⟨_, rfl⟩
  unfold Desc.K14.recGamma
  dsimp only
  rw [hL]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hs ⊢
  rw [hs]
  exact ⟨_, rfl⟩

theorem vars_product (f : List F) (s : E) : (Tensor.product f s).vars = f.length := by
  simp [Tensor.product, Tensor.vars]

/-- **(loc_x) is made.** -/
theorem locX_some (S : FoldeqShape) (x : Nat) (w : Array E) (column : Array F) (u : FoldedRow)
    (hc : w.size ≤ column.size) : ∃ row, Desc.K14.locX S x w column u = some row := by
  have hf : (generatorAt S.index.code x).f.length = S.index.code.logDim := length_squaresOf _ _
  have hdim := le_two_pow_ceilLog2 S.index.code.dim
  have d1 : S.index.code.logEll ≤ S.index.code.logDim :=
    Desc.K14.Law.ceilLog2_le _ _ (Nat.le_trans (Nat.le_add_right _ _) hdim)
  have d2 : S.index.code.logR ≤ S.index.code.logDim :=
    Desc.K14.Law.ceilLog2_le _ _ (Nat.le_trans (Nat.le_add_left _ _) hdim)
  obtain ⟨A, hA⟩ := cut_some (Tensor.product ((generatorAt S.index.code x).f.take
    S.index.code.logEll) (ofF (generatorAt S.index.code x).messageScale)) 0 S.index.code.logEll
    S.index.code.ell rfl (by rw [vars_product, List.length_take, hf]; omega)
    (le_two_pow_ceilLog2 _)
  obtain ⟨B, hB⟩ := cut_some (Tensor.product ((generatorAt S.index.code x).f.take
    S.index.code.logR) (ofF (generatorAt S.index.code x).tailScale)) 0 S.index.code.logR
    S.index.code.r rfl (by rw [vars_product, List.length_take, hf]; omega)
    (le_two_pow_ceilLog2 _)
  obtain ⟨sum, hs⟩ := foldlM_some
    (fun s r => do pure (maddS s (← column[r]?) (← w[r]?))) (List.range w.size) zeroE
    fun r hr t => by
      have h1 : r < w.size := List.mem_range.1 hr
      simp only [Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le h1 hc),
        Array.getElem?_eq_getElem h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      exact ⟨_, rfl⟩
  unfold Desc.K14.locX
  dsimp only
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hs ⊢
  rw [hA]
  by_cases h0 : (S.index.code.r == 0) = true
  · simp only [h0, if_true, Option.bind_some]
    rw [hs]
    exact ⟨_, rfl⟩
  · simp only [h0, Bool.false_eq_true, if_false, Option.bind_some]
    rw [hB]
    simp only [Option.bind_some]
    rw [hs]
    exact ⟨_, rfl⟩

/-! ## The ground takes the rows -/

theorem placeOk_congr {T T' : Statement} {G G' : Group} (ho : T'.oracles = T.oracles)
    (hc : T'.codes = T.codes) (hm : G'.members = G.members) (o : Nat) (pt : Part)
    (vars index : Nat) : Blk.placeOk T' G' o pt vars index = Blk.placeOk T G o pt vars index := by
  unfold Blk.placeOk Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  rw [ho, hc, hm]

theorem tableBits_congr' {T T' : Statement} (ho : T'.oracles = T.oracles)
    (hc : T'.codes = T.codes) (o : Nat) (pt : Part) : T'.tableBits o pt = T.tableBits o pt := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [ho, hc]

/-- **The sentences read of the statement its messages and codes alone, and of the group its members
and its mark.** -/
theorem RowClauses.congr {T T' : Statement} {G G' : Group} {row : Row}
    (ho : T'.oracles = T.oracles) (hc : T'.codes = T.codes) (hm : G'.members = G.members)
    (hi : G'.inRun = G.inRun) (h : K9L.RowClauses T G row) : K9L.RowClauses T' G' row :=
  ⟨hi.trans h.noTest, h.noSample,
    fun t ht => ⟨(h.terms t ht).1, by rw [placeOk_congr ho hc hm]; exact (h.terms t ht).2⟩,
    fun u hu => by rw [placeOk_congr ho hc hm, tableBits_congr' ho hc]; exact h.units u hu,
    fun w hw => ⟨(h.runs w hw).1, (h.runs w hw).2.1, (h.runs w hw).2.2.1, by
      rw [placeOk_congr ho hc hm, tableBits_congr' ho hc]; exact (h.runs w hw).2.2.2⟩,
    fun f hf => ⟨by rw [placeOk_congr ho hc hm, tableBits_congr' ho hc]; exact (h.forms f hf).1,
      by rw [tableBits_congr' ho hc]; exact (h.forms f hf).2⟩,
    fun o hO q hq => h.pads o (hm ▸ hO) q (ho ▸ hq)⟩

/-- **The ground takes a row that meets the sentences.** -/
theorem addRowP_yes {L : Type} (d : DState L) (g : Nat) (G : Group) (row : Row)
    (hG : d.st.groups[g]? = some G) (h : K9L.RowClauses d.st G row) :
    addRowP d g row = some { d with st := withRow d.st g row } := by
  unfold addRowP
  rw [if_pos]
  unfold Ground.ok
  exact List.all_eq_true.2 fun c hc => rowL_of_clauses d.st g G row hG h c hc

theorem addRowsFrom_yes {L : Type} (g : Nat) : ∀ (rows : List Row) (d : DState L) (G : Group),
    d.st.groups[g]? = some G → (∀ row ∈ rows, K9L.RowClauses d.st G row) →
    addRowsFrom g rows d = some { d with st := withRows d.st g rows }
  | [], _, _, _, _ => rfl
  | row :: l, d, G, hG, h => by
    unfold addRowsFrom
    rw [addRowP_yes d g G row hG (h row List.mem_cons_self)]
    exact addRowsFrom_yes g l { d with st := withRow d.st g row } _
      (withRow_group d.st g row G hG) fun r hr =>
        RowClauses.congr (T := d.st) (G := G) rfl rfl rfl rfl (h r (List.mem_cons_of_mem _ hr))

/-- **The ground takes rows that meet the sentences.** -/
theorem addRowsP_yes {L : Type} (d : DState L) (g : Nat) (G : Group) (rows : List Row)
    (hG : d.st.groups[g]? = some G) (hi : G.inRun = false)
    (h : ∀ row ∈ rows, K9L.RowClauses d.st G row) :
    addRowsP d g rows = some { d with st := withRows d.st g rows } := by
  unfold addRowsP
  rw [if_pos, addRowsFrom_yes g rows d G hG h]
  unfold Ground.ok rowsL
  rw [hG]
  simp [Ground.has, hi]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.cut_some
#print axioms Johnson.Prover.Link.eqPhi_some
#print axioms Johnson.Prover.Link.foldlM_some
#print axioms Johnson.Prover.Link.recGamma_some
#print axioms Johnson.Prover.Link.vars_product
#print axioms Johnson.Prover.Link.locX_some
#print axioms Johnson.Prover.Link.placeOk_congr
#print axioms Johnson.Prover.Link.tableBits_congr'
#print axioms Johnson.Prover.Link.RowClauses.congr
#print axioms Johnson.Prover.Link.addRowP_yes
#print axioms Johnson.Prover.Link.addRowsFrom_yes
#print axioms Johnson.Prover.Link.addRowsP_yes
