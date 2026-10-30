-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormRowsLaws.lean: THE FORM's HALF: THE LINK's THREE KINDS OF ROWS PASS ALL
TESTS OF A NEW OPEN ROW, at every statement and group at which their folds are seated (FoldSeat,
Johnson/Prover/Link/FormRowsSeat.lean): in the soundness side's own sentences: RowClauses
(Johnson/Desc/First/Batch/Law/DoorTests.lean). With rowL_of_clauses (FormDoorLaws.lean): every
clause of Ground.rowL says yes.

Main names.
  addLaid_rest, units_foldl   what laid vectors and single coefficients leave of a row.
  ok_of_plain     a vector without a written-out factor, of at most 63 variables, is in order.
  laid_term       a term that a laid vector makes passes the test on a term.
  recGamma_clauses, locX_clauses, eqPhi_clauses   THE STATEMENTS.
  padsFar_of      PadsFar at a record whose message has the public pad.

Limits. FoldSeat is a premise. FOR ALL DRAWS: no premise on a drawn value but a length. A member of
the group that a row does not name costs nothing: the row's coefficient there is 0 everywhere: so
the sentences hold at a later statement and a larger group as well, wherever FoldSeat holds. The
rows that a code switch makes are not here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormRowsSeat
import OnBytes.Slice.BlkLink
import OnBytes.Slice.BlkLinRead
import Johnson.Desc.Means.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc
open Desc.K14.Law (tensorBelow_mem recGamma_inv locX_inv recRow padList recCoeff PlacedU)

/-- Laid vectors leave a row's single coefficients and runs. -/
theorem addLaid_rest (o : Nat) (lay : VectorLay) : ∀ (l : List Tensor) (row : Row),
    (addLaid row o lay l).units = row.units ∧ (addLaid row o lay l).runs = row.runs
  | [], _ => ⟨rfl, rfl⟩
  | t :: l, row => addLaid_rest o lay l (row.add o .main (lay.onTable t))

/-- Single coefficients laid one by one. -/
theorem units_foldl {α : Type} (o : Nat) (idx : α → Nat) (c : α → E) : ∀ (P : List α) (r : Row),
    (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).units.toList =
        r.units.toList ++ P.map (fun x => (⟨o, .main, idx x, c x⟩ : Single)) ∧
      (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).terms = r.terms ∧
      (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).runs = r.runs ∧
      (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).forms = r.forms ∧
      (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).kind = r.kind
  | [], r => ⟨(List.append_nil _).symm, rfl, rfl, rfl, rfl⟩
  | x :: P, r => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := units_foldl o idx c P (r.addUnit o .main (idx x) (c x))
    refine ⟨?_, h2, h3, h4, h5⟩
    rw [List.foldl_cons, h1]
    show (r.units.push _).toList ++ _ = _
    rw [Array.toList_push, List.append_assoc]
    rfl

/-- A vector without a written-out factor, of at most 63 variables, is in order. -/
theorem ok_of_plain {v : Tensor} (hd : v.denseVars = []) (hv : v.vars ≤ 63) : v.ok = true := by
  unfold Tensor.ok
  rw [hd]
  simp [hv, distinctNats]

/-- **A term that a laid vector makes passes the test on a term.** -/
theorem laid_term {T : Statement} {G : Group} {S : FoldeqShape} {u : FoldedRow}
    (H : FoldSeat T G S u) (t : Tensor) (hd : t.denseVars = []) (hv : t.vars ≤ u.lay.bits) :
    (u.lay.onTable t).ok = true ∧
      Blk.placeOk T G u.oracle .main (u.lay.onTable t).vars 0 = true := by
  obtain ⟨e1, e2⟩ := Slice.onTable_vars u.lay t hd hv
  refine ⟨ok_of_plain e2 (by rw [e1]; exact H.bits), ?_⟩
  rw [Means.placeOk_iff, e1]
  exact ⟨Array.mem_toList_iff.2 H.member, H.placed.has, H.placed.bits.symm, Nat.two_pow_pos _⟩

/-- The pads' clause from «0 beyond the folded row's entries». -/
theorem pads_of_beyond {T : Statement} {G : Group} {row : Row}
    (h : ∀ (o : Nat) (x : OnBytes.Oracle), T.oracles[o]? = some x → ∀ q ∈ x.pad,
      isZeroE (row.coefficient o q.1 q.2) = true) :
    ∀ o ∈ G.members, ∀ q ∈ ((T.oracles[o]?).map (·.pad)).getD [],
      isZeroE (row.coefficient o q.1 q.2) = true := by
  intro o _ q hq
  cases hx : T.oracles[o]? with
  | none =>
    rw [hx] at hq
    cases hq
  | some x =>
    rw [hx] at hq
    exact h o x hx q hq

theorem ell_le_tailFirst (S : FoldeqShape) : S.index.code.ell ≤ S.tailFirst := by
  unfold FoldeqShape.tailFirst
  have hp : 0 < 2 ^ S.index.code.logR := Nat.two_pow_pos _
  generalize 2 ^ S.index.code.logR = st at hp
  have h1 := Nat.div_add_mod (S.index.code.ell + st - 1) st
  have h2 := Nat.mod_lt (S.index.code.ell + st - 1) hp
  show S.index.code.ell ≤ (S.index.code.ell + st - 1) / st * st
  rw [Nat.mul_comm]
  omega

/-- **(rec_gamma).** -/
theorem recGamma_clauses (T : Statement) (G : Group) (S : FoldeqShape) (seed : SampleSeed) (a : Nat)
    (w y : Array E) (u : FoldedRow) (row : Row)
    (h : Desc.K14.recGamma S.index seed a w y u = some row)
    (hz : seed.z.length = S.index.cubeBits) (H : FoldSeat T G S u) : K9L.RowClauses T G row := by
  have hok := H.shape
  simp only [IndexShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hp : 3 * S.index.answers ≤ S.index.code.ell := by
    have := hok.1.2
    unfold IndexShape.pads at this
    omega
  have hpads : ∀ (o : Nat) (x : OnBytes.Oracle), T.oracles[o]? = some x → ∀ q ∈ x.pad,
      isZeroE (row.coefficient o q.1 q.2) = true := fun o x hx q hq =>
    recGamma_beyond S.index seed a w y u row h hz H.placed.room hp o q.1 q.2 fun hm ho =>
      (H.far x (ho ▸ hx) q hq hm).mono
        (Nat.le_trans (ell_le_tailFirst S) (Nat.le_add_right _ _))
  obtain ⟨L, sum, hL, _, rfl⟩ := recGamma_inv S.index seed a w y u row h
  have hmem := tensorBelow_mem _ rfl 0 _ _ L hL
  obtain ⟨f1, f2, f3, f4, f5⟩ := units_foldl u.oracle
    (fun x : Nat × Nat => u.lay.index (S.index.padPlace x.1 x.2)) (recCoeff S.index seed a)
    (padList S.index) (u.addAll {} L)
  obtain ⟨g1, g2⟩ := Slice.addLaid_terms u.oracle u.lay L {}
  obtain ⟨g3, g4⟩ := addLaid_rest u.oracle u.lay L {}
  have hell : S.index.code.ell ≤ 2 ^ u.lay.bits :=
    Nat.le_trans (Slice.le_two_pow_ceilLog2 _) (Nat.pow_le_pow_right (by decide) H.placed.room)
  refine ⟨H.idle, ?_, ?_, ?_, ?_, ?_, pads_of_beyond hpads⟩
  · show (recRow S.index seed a u L).kind ≠ .sample
    unfold recRow
    rw [f5]
    show (addLaid {} u.oracle u.lay L).kind ≠ .sample
    rw [(Slice.addLaid_keeps u.oracle u.lay L {}).2]
    exact fun c => by cases c
  · intro t ht
    have ht' : t ∈ (addLaid {} u.oracle u.lay L).terms.toList := by
      have e : (recRow S.index seed a u L).terms = (addLaid {} u.oracle u.lay L).terms := f2
      exact Array.mem_toList_iff.2 (e ▸ ht)
    rw [g1] at ht'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (by simpa using ht')
    exact laid_term H v (hmem v hv).1
      (by rw [(hmem v hv).2, vars_eq, hz]; exact H.placed.room)
  · intro q hq
    have hq' : q ∈ (recRow S.index seed a u L).units.toList := Array.mem_toList_iff.2 hq
    unfold recRow at hq'
    rw [f1] at hq'
    have e0 : (u.addAll {} L).units.toList = [] := by
      show (addLaid {} u.oracle u.lay L).units.toList = []
      rw [g3]
    rw [e0, List.nil_append] at hq'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq'
    simp only [padList, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨a', ha', t, ht, rfl⟩ := hx
    have hlt : S.index.padPlace a' t < S.index.code.ell := by
      unfold IndexShape.padPlace IndexShape.plain IndexShape.pads
      omega
    rw [Means.placeOk_iff, H.placed.bits]
    exact ⟨Array.mem_toList_iff.2 H.member, H.placed.has, rfl,
      Slice.index_lt _ _ (Nat.lt_of_lt_of_le hlt hell)⟩
  · intro r hr
    have e : (recRow S.index seed a u L).runs = #[] := by
      unfold recRow
      rw [f3]
      show (addLaid {} u.oracle u.lay L).runs = #[]
      rw [g4]
    have hr' : r ∈ (recRow S.index seed a u L).runs := hr
    rw [e] at hr'
    exact absurd hr' (by simp)
  · intro f hf
    have e : (recRow S.index seed a u L).forms = #[] := by
      unfold recRow
      rw [f4]
      show (addLaid {} u.oracle u.lay L).forms = #[]
      rw [g2]
    have hf' : f ∈ (recRow S.index seed a u L).forms := hf
    rw [e] at hf'
    exact absurd hf' (by simp)

/-- A row that is made of vectors laid on seated folds alone passes all tests but the pads'. -/
theorem laid_clauses {T : Statement} {G : Group} {row : Row} (hi : G.inRun = false)
    (hk : row.kind ≠ .sample)
    (ht : ∀ t ∈ row.terms.toList, t.v.ok = true ∧
      Blk.placeOk T G t.oracle t.part t.v.vars 0 = true)
    (hu : row.units = #[]) (hr : row.runs = #[]) (hf : row.forms = #[])
    (hp : ∀ (o : Nat) (x : OnBytes.Oracle), T.oracles[o]? = some x → ∀ q ∈ x.pad,
      isZeroE (row.coefficient o q.1 q.2) = true) : K9L.RowClauses T G row :=
  ⟨hi, hk, fun t h => ht t (Array.mem_toList_iff.2 h),
    fun u h => absurd (hu ▸ h) (by simp), fun w h => absurd (hr ▸ h) (by simp),
    fun f h => absurd (hf ▸ h) (by simp), pads_of_beyond hp⟩

/-- **(loc_x).** -/
theorem locX_clauses (T : Statement) (G : Group) (S : FoldeqShape) (x : Nat) (w : Array E)
    (column : Array F) (u : FoldedRow) (row : Row) (h : Desc.K14.locX S x w column u = some row)
    (H : FoldSeat T G S u) : K9L.RowClauses T G row := by
  have hpads : ∀ (o : Nat) (y : OnBytes.Oracle), T.oracles[o]? = some y → ∀ q ∈ y.pad,
      isZeroE (row.coefficient o q.1 q.2) = true := fun o y hy q hq =>
    locX_beyond S x w column u row h H.placed.room (ell_le_tailFirst S) H.placed.roomTail
      (Nat.dvd_of_mod_eq_zero H.placed.aligned) o q.1 q.2 fun hm ho => H.far y (ho ▸ hy) q hq hm
  obtain ⟨A, tail, sum, hA, ht, _, rfl⟩ := locX_inv S x w column u row h
  have hmA := tensorBelow_mem _ rfl 0 _ _ A hA
  have hvA := vars_product_take _ _ _ _ _ hA
  obtain ⟨a1, a2⟩ := Slice.addLaid_terms u.oracle u.lay A {}
  obtain ⟨a3, a4⟩ := addLaid_rest u.oracle u.lay A {}
  obtain ⟨b1, b2⟩ := Slice.addLaid_terms u.oracle u.lay (tail.map (·.insertChoice
    S.index.code.logR (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))
    (addLaid {} u.oracle u.lay A)
  obtain ⟨b3, b4⟩ := addLaid_rest u.oracle u.lay (tail.map (·.insertChoice
    S.index.code.logR (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))
    (addLaid {} u.oracle u.lay A)
  have htail : ∀ t ∈ tail, t.denseVars = [] ∧ t.vars = S.index.code.logR := by
    by_cases h0 : S.index.code.r = 0
    · rw [if_pos (by simp [h0])] at ht
      obtain rfl := Option.some.inj ht
      exact fun t c => absurd c (by simp)
    · rw [if_neg (by simp [h0])] at ht
      intro t c
      have := tensorBelow_mem _ rfl 0 _ _ tail ht t c
      exact ⟨this.1, this.2.trans (vars_product_take _ _ _ _ _ ht)⟩
  have hn : S.index.code.logR ≤ u.lay.bits :=
    Desc.K14.Law.ceilLog2_le _ _ (by have := H.placed.roomTail; omega)
  refine laid_clauses H.idle (fun c => by cases c) ?_ ?_ ?_ ?_ hpads
  · intro t hm
    have hm' : t ∈ (addLaid (addLaid {} u.oracle u.lay A) u.oracle u.lay (tail.map
        (·.insertChoice S.index.code.logR (u.lay.bits - S.index.code.logR)
          (S.tailFirst / 2 ^ S.index.code.logR)))).terms.toList := hm
    rw [b1, a1] at hm'
    rcases List.mem_append.1 hm' with c | c
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (by simpa using c)
      exact laid_term H v (hmA v hv).1 (by rw [(hmA v hv).2, hvA]; exact H.placed.room)
    · obtain ⟨v', hv', rfl⟩ := List.mem_map.1 c
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hv'
      obtain ⟨t1, t2⟩ := htail v hv
      have t3 : v.pairs.length = S.index.code.logR := t2
      refine laid_term H _ (by simp [Tensor.insertChoice, t1]) (le_of_eq ?_)
      simp only [Tensor.vars, Tensor.insertChoice, List.length_append, List.length_take,
        List.length_drop, choicePairs_length, t3]
      omega
  · show (addLaid (addLaid {} u.oracle u.lay A) u.oracle u.lay _).units = #[]
    rw [b3, a3]
  · show (addLaid (addLaid {} u.oracle u.lay A) u.oracle u.lay _).runs = #[]
    rw [b4, a4]
  · show (addLaid (addLaid {} u.oracle u.lay A) u.oracle u.lay _).forms = #[]
    rw [b2, a2]

/-- **(eq_phi).** n: the answers to a sample. -/
theorem eqPhi_clauses (T : Statement) (G : Group) (S : LinkShape) (n : Nat) (phi : List E)
    (o0 o1 : FoldedRow) (row : Row) (h : Desc.K15.eqPhi S phi o0 o1 = some row)
    (H0 : FoldSeat T G (S.side false n) o0) (H1 : FoldSeat T G (S.side true n) o1) :
    K9L.RowClauses T G row := by
  have hcut : ∀ b, S.cut ≤ (S.side b n).entries := fun b =>
    Nat.le_trans (Nat.sub_le _ _)
      (Nat.le_trans (ell_le_tailFirst (S.side b n)) (Nat.le_add_right _ _))
  have hpads : ∀ (o : Nat) (y : OnBytes.Oracle), T.oracles[o]? = some y → ∀ q ∈ y.pad,
      isZeroE (row.coefficient o q.1 q.2) = true := fun o y hy q hq =>
    eqPhi_beyond S phi o0 o1 row h H0.placed.room H1.placed.room o q.1 q.2
      (fun hm ho => (H0.far y (ho ▸ hy) q hq hm).mono (hcut false))
      (fun hm ho => (H1.far y (ho ▸ hy) q hq hm).mono (hcut true))
  unfold Desc.K15.eqPhi at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    beq_iff_eq] at h
  obtain ⟨_, hg, plus, hp, minus, hm, rfl⟩ := h
  have hl : phi.length = S.entryBits := by
    by_contra c
    simp [guard, c] at hg
  have hmP := tensorBelow_mem _ rfl 0 _ _ plus hp
  have hmM := tensorBelow_mem _ rfl 0 _ _ minus hm
  obtain ⟨a1, a2⟩ := Slice.addLaid_terms o0.oracle o0.lay plus {}
  obtain ⟨a3, a4⟩ := addLaid_rest o0.oracle o0.lay plus {}
  obtain ⟨b1, b2⟩ := Slice.addLaid_terms o1.oracle o1.lay minus (addLaid {} o0.oracle o0.lay plus)
  obtain ⟨b3, b4⟩ := addLaid_rest o1.oracle o1.lay minus (addLaid {} o0.oracle o0.lay plus)
  refine laid_clauses H0.idle ?_ ?_ ?_ ?_ ?_ hpads
  · show (addLaid (addLaid {} o0.oracle o0.lay plus) o1.oracle o1.lay minus).kind ≠ .sample
    rw [(Slice.addLaid_keeps _ _ _ _).2, (Slice.addLaid_keeps _ _ _ _).2]
    exact fun c => by cases c
  · intro t ht
    have ht' : t ∈ (addLaid (addLaid {} o0.oracle o0.lay plus) o1.oracle o1.lay
        minus).terms.toList := ht
    rw [b1, a1] at ht'
    rcases List.mem_append.1 ht' with c | c
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (by simpa using c)
      exact laid_term H0 v (hmP v hv).1
        (by rw [(hmP v hv).2, vars_eq, hl]; exact H0.placed.room)
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 c
      exact laid_term H1 v (hmM v hv).1
        (by rw [(hmM v hv).2, vars_eq, hl]; exact H1.placed.room)
  · show (addLaid (addLaid {} o0.oracle o0.lay plus) o1.oracle o1.lay minus).units = #[]
    rw [b3, a3]
  · show (addLaid (addLaid {} o0.oracle o0.lay plus) o1.oracle o1.lay minus).runs = #[]
    rw [b4, a4]
  · show (addLaid (addLaid {} o0.oracle o0.lay plus) o1.oracle o1.lay minus).forms = #[]
    rw [b2, a2]

/-- **PadsFar at a record** whose message has the public pad. -/
theorem padsFar_of (T : Statement) (S : FoldeqShape) (u : FoldedRow) (places : List PadPlace)
    (hx : ∀ x, T.oracles[u.oracle]? = some x → x.pad = places.map fun p => (p.part, p.index))
    (hp : Send.pad T.codes S.u = some places) (hl : u.lay = vectorLay T.codes S.u S.rowsHigh)
    (hok : foldeqOk T.codes S = true) : PadsFar T S u := by
  intro x h q hq hm
  rw [hx x h] at hq
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hq
  simp only [foldeqOk, FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  rw [hl]
  exact (pad_beyond T.codes S.u S.rowsHigh places p hp hpm hm hok.1.1.1.1.1.2).mono hok.2

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.addLaid_rest
#print axioms Johnson.Prover.Link.units_foldl
#print axioms Johnson.Prover.Link.ok_of_plain
#print axioms Johnson.Prover.Link.laid_term
#print axioms Johnson.Prover.Link.pads_of_beyond
#print axioms Johnson.Prover.Link.ell_le_tailFirst
#print axioms Johnson.Prover.Link.recGamma_clauses
#print axioms Johnson.Prover.Link.laid_clauses
#print axioms Johnson.Prover.Link.locX_clauses
#print axioms Johnson.Prover.Link.eqPhi_clauses
#print axioms Johnson.Prover.Link.padsFar_of
