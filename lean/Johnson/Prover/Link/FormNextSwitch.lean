-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormNextSwitch.lean: THE FORM's HALF: **WHERE THE OLD CLAIM's FORM IS DENSE, THE
RECORD BEHIND A SWITCH AND ITS BATCHING MEETS THE NEXT FOLD's FRONT** (foldFront_behind); with it,
under the same premise: the rows taken in and the row returned are dense (DenseRow, DenseForm:
OnBytes/Slice/BlkProxDense.lean: each tensor in order, its slice inside its vector; what has no
written-out factor is dense); and without it: how many rows are taken in; statement and book are in
step. All over the soundness side's own record of a switch: Did (Johnson/Desc/K12/Law/SwDid.lean).

Main names.
  run_dense       where the old claim's form is DenseForm: the rows that the batching behind a
                  switch takes in are DenseRow.
  dense_behind    where it is: the row that the batching returns is DenseForm.
  count_of        two rows, and three for each position drawn.
  openOne_place, readOld_place   the reading of the old rows turns no place of the book.
  step_behind     statement and book are in step behind.
  rider_at        the message that rides with the switch's: as it was announced, untouched.
  stageFront_behind   where it is: StageFront (Johnson/Prover/Link/FormNext.lean) in front of the
                  batching.
  foldFront_behind    THE STATEMENT, under the same premise.
  behindT_mask    the record behind the batching notes the rider as the mask.

Limits. Did is a premise, and «in order» at ITS OWN statement with the claims (D.stR): whoever calls
holds both at one D. The plan's facts (the two stages' codes in the statement's lists; three tests
on their numbers) are premises. The old claim has no kept member and two mask rows; the group was
new. THAT THE OLD CLAIM's FORM IS DENSE (DenseForm) IS A PREMISE of run_dense, dense_behind,
stageFront_behind and foldFront_behind: where it is not they say nothing. Premises besides: ties of
the letters n, t' and p.idx.
Not the last switch. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormNextLaws
import Johnson.Prover.Link.FormSwitchLaws
import Johnson.Desc.K12.Law.SwTies
import OnBytes.Slice.BlkCsPlain
import Johnson.Desc.K12.Law.SwRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open OnBytes.Slice.ProxRun (DenseForm DenseRow combine_dense denseRow_carriedRow denseRow_of_plain)

variable {ft : Nat} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : Nat}
  {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : Nat}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- The rows that the batching behind a switch takes in are dense, where the old claim's form is. -/
theorem run_dense (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hkept : old.kept = #[]) (hmasks : old.masks = 2) (hno : switchKept old = #[])
    (hm : D.G.members = #[]) (hr : D.G.rows = #[]) (hc : DenseForm old.c) :
    ∀ r ∈ (runRows (D.stR T gp others S) (D.grown S)).toList, DenseRow r := by
  obtain ⟨W, _, hrun⟩ := h.run_rows hkept hmasks hno hm hr
  intro r hr2
  rw [hrun] at hr2
  unfold csRowsB at hr2
  simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hr2
  rcases hr2 with rfl | rfl | ⟨x, _, rfl | rfl | rfl⟩
  · exact denseRow_carriedRow W old hc
  · exact denseRow_of_plain (plainRow_form S.codes T.shape _ ⟨_, D.beta⟩ 0 D.smp h.form)
  · exact denseRow_of_plain (plainRow_genMain _ _ _)
  · exact denseRow_of_plain (plainRow_genMask _ _ _ _)
  · exact denseRow_of_plain (plainRow_genMask _ _ _ _)

/-- **The row behind is dense**, where the old claim's form is. -/
theorem dense_behind (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hkept : old.kept = #[]) (hmasks : old.masks = 2) (hno : switchKept old = #[])
    (hm : D.G.members = #[]) (hr : D.G.rows = #[]) (hc : DenseForm old.c) : DenseForm row.c :=
  combine_dense _ gp _ theta row (run_dense h hkept hmasks hno hm hr hc) h.row

/-- **The count**: two rows, and three for each position drawn. -/
theorem count_of (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hkept : old.kept = #[]) (hmasks : old.masks = 2) (hno : switchKept old = #[])
    (hm : D.G.members = #[]) (hr : D.G.rows = #[]) :
    (runRows (D.stR T gp others S) (D.grown S)).size = 2 + 3 * D.rC.drawn.poss.length := by
  obtain ⟨W, _, hrun⟩ := h.run_rows hkept hmasks hno hm hr
  rw [← Array.length_toList, hrun]
  unfold csRowsB
  simp only [List.length_cons, List.length_flatMap, List.length_nil, List.map_const',
    List.sum_replicate, smul_eq_mul]
  omega

/-- The message that rides with the switch's: as it was announced, untouched. -/
theorem rider_at (D : Taken) (T : SwitchTarget) (gp : Nat) (N : OracleNotice) (S : Statement) :
    (D.stR T gp #[N] S).oracles[S.oracles.size + 1]? = some { shape := N.shape } := by
  have hne : S.oracles.size ≠ S.oracles.size + 1 := by omega
  unfold Taken.stR Taken.stJ
  rw [(withRows_oracles gp D.rows _).1, joined_other _ _ _ _ _ _ hne]
  have e1 : (ledgerShut (D.stA T #[N] S) T S.oracles.size).oracles[S.oracles.size + 1]? =
      (D.stA T #[N] S).oracles[S.oracles.size + 1]? := by
    unfold ledgerShut
    split
    · rw [ProxRun.closeLedgers_get]
      have hn : ¬ S.oracles.size + 1 ∈ [S.oracles.size] := by simp
      simp only [hn, if_false]
      cases (D.stA T #[N] S).oracles[S.oracles.size + 1]? <;> rfl
    · rfl
  rw [e1]
  unfold Taken.stA
  rw [admitted_other _ _ _ _ _ _ hne, stSent_new]
  rfl

/-! ## In step -/

/-- The opening of one tree turns no place of the book. -/
theorem openOne_place (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s s' : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F)))
    (h : Tw.L9.openOne S ft pos B0 t s = .ok s') : s'.1.place = s.1.place := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; rfl)
      | cases h
  · cases h

/-- The reading of the old rows turns no place of the book. -/
theorem readOld_place (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) : B.place = i.book.place := by
  obtain ⟨places, cs, opened, _, hf, _, _⟩ := readOld_inv i pos B left ys h
  exact foldlM_keeps'
    (fun (a b : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F))) =>
      b.1.place = a.1.place) (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1) _
    (fun s a s' hs => openOne_place _ _ _ _ _ _ _ hs) _ _ _ hf

/-- Two arrays whose entries are there at the same numbers have one size. -/
theorem size_of_map {α β : Type} (f : α → β) (A B : Array α)
    (h : ∀ i : Nat, (A[i]?).map f = (B[i]?).map f) : A.size = B.size := by
  have key : ∀ (X Y : Array α), (∀ i : Nat, (X[i]?).map f = (Y[i]?).map f) →
      X.size ≤ Y.size := by
    intro X Y hXY
    by_contra c
    have h1 := hXY Y.size
    rw [Array.getElem?_eq_getElem (Nat.lt_of_not_le c),
      Array.getElem?_eq_none (Nat.le_refl _)] at h1
    cases h1
  exact Nat.le_antisymm (key A B h) (key B A fun i => (h i).symm)

/-- **Behind a switch and its batching statement and book are in step.** -/
theorem step_behind (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    S'.oracles.size = Bk'.place.size := by
  obtain ⟨i, left, _, hb, _, _, _, hr⟩ := h.read
  rw [readOld_place i _ _ _ _ hr, hb, size_of_map (·.shape) _ _ h.shape_at]
  show (S.oracles ++ (Slice.sentOf T others).map _).size =
    (Bk.place ++ (Array.range (Slice.sentOf T others).size).map _).size
  rw [Array.size_append, Array.size_append, Array.size_map, Array.size_map, Array.size_range,
    h.places]

/-! ## The next fold's front -/

/-- **StageFront BEHIND A SWITCH**, in front of its batching, where the old claim's form is dense
(hc). -/
theorem stageFront_behind {n : IoppStage} {next nx : Fmt.M1.Stage} {nn : Nat × Nat}
    (h : Did ft cols old (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf false n) S Bk
      roots S' Bk' out row lay theta D)
    (hkept : old.kept = #[]) (hmasks : old.masks = 2) (hno : switchKept old = #[])
    (hc : DenseForm old.c) (hG : D.G = { code := n.code, maskCode := n.maskCode })
    (hI : InOrder (D.stR (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf false n) S))
    (ek : n.k = next.k) (eh : n.h = next.h)
    (b0 : S.codes.base[n.code]? = some ⟨next.C.a, next.C.l, next.C.r⟩)
    (z0 : S.codes.mask[n.maskCode]? = some ⟨next.Z.a, next.Z.l, next.Z.r⟩)
    (b1 : S.codes.base[nn.1]? = some ⟨nx.C.a, nx.C.l, nx.C.r⟩)
    (z1 : S.codes.mask[nn.2]? = some ⟨nx.Z.a, nx.Z.l, nx.Z.r⟩)
    (hs : K12.stageOk false next = true) (hs1 : nx.Z.a ≤ nx.C.a)
    (hv : next.k + ceilLog2 next.C.l ≤ 63) :
    StageFront (D.stR (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf false n) S) gp
      (D.grown S) next nx (n.code, n.maskCode) nn (S.oracles.size + 1) := by
  have hm : D.G.members = #[] := by rw [hG]
  have hk : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  obtain ⟨hcodes, hshape⟩ := D.stR_shape (switchTargetStage n.code n.maskCode n.k n.h 1) gp
    (othersOf false n) S
  have hmem : (D.grown S).members = #[S.oracles.size] := by
    unfold Taken.grown
    simp [hm, Array.insertIdxIfInBounds]
  have hkp : (D.grown S).kept = #[false] := by
    unfold Taken.grown
    simp [hm, hk, Array.insertIdxIfInBounds]
  have elay : layoutOf (D.stR (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf false n)
      S) (D.grown S) = lay :=
    Option.some.inj ((layout_eq _ gp _ h.group_stR).symm.trans h.layout)
  obtain ⟨_, _, s3, s4, _⟩ := stageOk_of hs
  refine ⟨h.group_stR, hI, run_dense h hkept hmasks hno hm hr hc, ?_, ?_, by rw [hcodes]; exact b0,
    by rw [hcodes]; exact z0, by rw [hcodes]; exact b1, by rw [hcodes]; exact z1, ?_, ?_, ?_, ?_,
    ?_, hs, hs1, hv⟩
  · show D.G.code = n.code
    rw [hG]
  · show D.G.maskCode = n.maskCode
    rw [hG]
  · rw [elay, h.lay_eq hm hk]
    show max (max n.k n.h) 1 = next.k
    rw [ek, eh]
    omega
  · rw [elay, h.lay_eq hm hk]
    exact eh
  · cases hx : (D.stR (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf false n)
        S).oracles[S.oracles.size]? with
    | none =>
      rw [hx] at hshape
      cases hshape
    | some x =>
      rw [hx] at hshape
      refine ⟨0, by rw [hmem]; exact Nat.zero_lt_one, x, by rw [hmem]; exact hx, ?_⟩
      have e : x.shape = (switchTargetStage n.code n.maskCode n.k n.h 1).shape :=
        Option.some.inj hshape
      rw [e]
      exact Nat.two_pow_pos _
  · intro j
    rw [hkp]
    cases j <;> rfl
  · refine ⟨_, rider_at D _ gp (foldMaskNotice (ioppFoldShape n {})) S, rfl, ?_, rfl, rfl, rfl, rfl,
      ?_⟩
    · show 2 ^ n.h = 2 ^ next.h
      rw [eh]
    · rw [hmem]
      simp

/-- **foldFront_behind: THE RECORD BEHIND A SWITCH AND ITS BATCHING MEETS THE NEXT FOLD's
FRONT**, where the old claim's form is dense (hc). -/
theorem foldFront_behind (p : P12) (j : Nat) {n : IoppStage} {next nx : Fmt.M1.Stage}
    {nn : Nat × Nat} (t' : T12)
    (h : Did ft cols old (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf false n) S Bk
      roots S' Bk' out row lay theta D)
    (hkept : old.kept = #[]) (hmasks : old.masks = 2) (hno : switchKept old = #[])
    (hc : DenseForm old.c) (hG : D.G = { code := n.code, maskCode := n.maskCode })
    (hI : InOrder (D.stR (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf false n) S))
    (ek : n.k = next.k) (eh : n.h = next.h)
    (b0 : S.codes.base[n.code]? = some ⟨next.C.a, next.C.l, next.C.r⟩)
    (z0 : S.codes.mask[n.maskCode]? = some ⟨next.Z.a, next.Z.l, next.Z.r⟩)
    (b1 : S.codes.base[nn.1]? = some ⟨nx.C.a, nx.C.l, nx.C.r⟩)
    (z1 : S.codes.mask[nn.2]? = some ⟨nx.Z.a, nx.Z.l, nx.Z.r⟩)
    (hs : K12.stageOk false next = true) (hs1 : nx.Z.a ≤ nx.C.a)
    (hv : next.k + ceilLog2 next.C.l ≤ 63) (i0 : p.idx[j + 1]? = some (n.code, n.maskCode))
    (i1 : p.idx[j + 1 + 1]? = some nn) (e1 : t'.st = S') (e2 : t'.pass = .claim row lay)
    (e3 : t'.mask = some (S.oracles.size + 1)) :
    FoldFront p (j + 1) next t' row lay ⟨n.code, n.maskCode, next.k, next.h⟩ nn
      (S.oracles.size + 1) := by
  have elay : layoutOf (D.stR (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf false n)
      S) (D.grown S) = lay :=
    Option.some.inj ((layout_eq _ gp _ h.group_stR).symm.trans h.layout)
  have H := stageFront_behind h hkept hmasks hno hc hG hI ek eh b0 z0 b1 z1 hs hs1 hv
  have := foldFront_at p (j + 1) theta row t' H i0 i1 (by rw [elay]; exact h.row)
    (e1.trans h.st) (by rw [elay]; exact e2) e3
  rw [elay] at this
  exact this

/-- The record behind the batching notes the rider as the mask, where the switch is not the last. -/
theorem behindT_mask (p : P12) (n : IoppStage) (t : T12) (rC : Fmt.RoundView) (gp : Nat) (D : Taken)
    (B : TreeBook) (row : GroupRow) (lay : GroupLayout) :
    (behindT p n false t rC gp D B row lay).mask = some (t.st.oracles.size + 1) := by
  show ((swIds p n false t).extract 1 (swIds p n false t).size)[0]? = _
  unfold swIds
  rw [swNotices_eq]
  simp [othersOf]
  omega

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.run_dense
#print axioms Johnson.Prover.Link.dense_behind
#print axioms Johnson.Prover.Link.count_of
#print axioms Johnson.Prover.Link.rider_at
#print axioms Johnson.Prover.Link.openOne_place
#print axioms Johnson.Prover.Link.readOld_place
#print axioms Johnson.Prover.Link.size_of_map
#print axioms Johnson.Prover.Link.step_behind
#print axioms Johnson.Prover.Link.stageFront_behind
#print axioms Johnson.Prover.Link.foldFront_behind
#print axioms Johnson.Prover.Link.behindT_mask
