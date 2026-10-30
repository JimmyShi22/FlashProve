-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsJoint.lean: from a run of the program's code switch to the claim after the
library's code switch.

OnBytes/Slice/BlkCsRun.lean says what a run of the program's code switch has done, with no
arithmetic. OnBytes/Slice/BlkCsRows.lean, BlkSendCs.lean and BlkCsSem.lean read the rows that the
switch makes in the field. This file joins them, for a switch between two stages s and s' of a
proximity test.

 `order_of`   the order of the rows that are batched: first the claim that is carried over, then
              the sample row, then each draw's three rows.
 `frame_of`   the record that the program computes once for a switch (`SwitchFrame`) is as the laws
              on its rows ask, if the program's four codes are those of the two stages (`CsProg`)
              and the stages' sizes fit (`CsFit`). Its tables have the new stage's sizes.
 `CsRan.plain`  the returned row's form on the main table has no written-out factor, if the old
              claim's has none.
 `csRan_sem`  the row that the run returns, read in the field with the new group's own numbers of
              row bits, is `csNext` (OnBytes/Slice/CsSim.lean) of the program's claim before the
              switch, at the seed, the answer, the positions and the element that the run has taken
              of the view.

Main definition: `CsProg`.
Main theorems: `order_of`, `CsRan.run_rows`, `CsRan.plain`, `switchFrame_bits`, `frame_of`,
`csRan_sem`.
Not claimed. Beside the ties of the program's data to the two stages, `csRan_sem` takes one fact on
another function of the program as a hypothesis: that the symbols read are the long symbols of one
word. Nothing on soundness.
-/
import OnBytes.Slice.BlkCsLay
import OnBytes.Slice.BlkCsRows
import OnBytes.Slice.BlkCsSem
import OnBytes.Slice.BlkSendCs
import OnBytes.Slice.BlkCsMask

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## The order of the rows -/

/-- One plain row, a sample row and generator rows, in the fixed order of a batching. -/
theorem order_of (a smp : Row) (l : List Row) (ha : a.kind = .plain)
    (hl : ∀ r ∈ l, r.kind = .generator) :
    ((a :: l).toArray.filter (·.kind == .plain) ++ #[smp] ++
      (a :: l).toArray.filter (·.kind == .generator)).toList = a :: smp :: l := by
  have h1 : (a :: l).filter (·.kind == .plain) = [a] := by
    rw [List.filter_cons_of_pos (by simp [ha])]
    exact congrArg (a :: ·) (List.filter_eq_nil_iff.2 fun r hr => by simp [hl r hr])
  have h2 : (a :: l).filter (·.kind == .generator) = l := by
    rw [List.filter_cons_of_neg (by simp [ha])]
    exact List.filter_eq_self.2 fun r hr => by simp [hl r hr]
  rw [Array.toList_append, Array.toList_append, Array.toList_filter, Array.toList_filter]
  show (a :: l).filter _ ++ [smp] ++ (a :: l).filter _ = _
  rw [h1, h2]
  rfl

/-! ## The frame of a switch into a stage -/

/-- The index bits that a frame holds of the new tables. -/
theorem switchFrame_bits (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (W : SwitchFrame) (h : switchFrame S old T g #[] = some W) :
    ∃ nc, S.codes.base[T.shape.code]? = some nc ∧
      W.tableBits = switchRowBits T .main + nc.logEll ∧
      W.restBits = S.tableBits g T.rest.part := by
  unfold switchFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨code, hc, zk, hz, nc, hn, -, -, rfl⟩ := h
  exact ⟨nc, hn, rfl, rfl⟩

/-- How the program's data at a switch are those of two stages s and s'. nc, nz: the numbers of
the new codes. Also asked: no kept member, two mask rows, an old main code with logN ≤ 32. -/
structure CsProg (s s' : Sg) (codes : Codes) (old : SingleRows) (nc nz : ℕ) : Prop where
  code : (codes.base[old.code]?).map codeOf = some s.C
  zk : (codes.mask[old.maskCode]?).map codeOf = some s.Z
  code' : (codes.base[nc]?).map codeOf = some s'.C
  zk' : (codes.mask[nz]?).map codeOf = some s'.Z
  noKept : switchKept old = #[]
  masks : old.masks = 2
  keptRows : old.keptRows = 0
  small : s.C.a ≤ 32

/-- The frame of a switch between two stages is as the laws on its rows ask, its codes are the
old stage's, and its tables have the new stage's sizes. Asked: `CsFit`, `CsProg`, and that the
oracle message g has the target's shape in the statement. -/
theorem frame_of {s s' : Sg} (hf : CsFit s s') (S : Statement) (old : SingleRows) (nc nz g : ℕ)
    (P : CsProg s s' S.codes old nc nz)
    (hsh : (S.oracles[g]?).map (·.shape)
      = some (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape) (W : SwitchFrame)
    (hW : switchFrame S old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) g #[] = some W) :
    FrameOK W ∧ codeOf W.code = s.C ∧ codeOf W.zk = s.Z ∧ W.g = g ∧
      2 ^ W.tableBits = 2 ^ (s'.h + s'.g) * s'.C.l ∧ 2 ^ W.restBits = 2 ^ s'.h * s'.Z.l := by
  obtain ⟨f1, f2, f3, _, _, f6, _⟩ := switchFrame_fields S old _ g W hW
  obtain ⟨cd', b1, b2, b3⟩ := switchFrame_bits S old _ g W hW
  -- the four codes
  have hC : codeOf W.code = s.C := by
    have h := P.code
    rw [f1] at h
    exact Option.some.inj h
  have hZ : codeOf W.zk = s.Z := by
    have h := P.zk
    rw [f2] at h
    exact Option.some.inj h
  have hC' : codeOf cd' = s'.C := by
    have h := P.code'
    rw [show S.codes.base[nc]? = some cd' from b1] at h
    exact Option.some.inj h
  obtain ⟨zk', hz1, hZ'⟩ : ∃ zk', S.codes.mask[nz]? = some zk' ∧ codeOf zk' = s'.Z := by
    have h := P.zk'
    cases hz : S.codes.mask[nz]? with
    | none => rw [hz] at h; cases h
    | some z => rw [hz] at h; exact ⟨z, rfl, Option.some.inj h⟩
  -- their sizes
  have eCl : W.code.ell = s.C.l := congrArg (·.l) hC
  have eCr : W.code.r = s.C.r := congrArg (·.r) hC
  have eCa : W.code.logN = s.C.a := congrArg (·.a) hC
  have eZl : W.zk.ell = s.Z.l := congrArg (·.l) hZ
  have eZr : W.zk.r = s.Z.r := congrArg (·.r) hZ
  have eZa : W.zk.logN = s.Z.a := congrArg (·.a) hZ
  have eCl' : cd'.ell = s'.C.l := congrArg (·.l) hC'
  have eZl' : zk'.ell = s'.Z.l := congrArg (·.l) hZ'
  have hgetZ : S.codes.mask.getD nz default = zk' := by
    rw [Array.getD_eq_getD_getElem?, hz1]
    rfl
  -- the logarithms
  have lC' : cd'.logEll = Fmt.M1.lg s'.C.l := by
    unfold Code.logEll
    rw [eCl', hf.powC, ceilLog2_two_pow, ← hf.powC]
  have lZ' : zk'.logEll = Fmt.M1.lg s'.Z.l := by
    unfold Code.logEll
    rw [eZl', hf.powZ, ceilLog2_two_pow, ← hf.powZ]
  have hell : W.code.ell = 2 ^ (s'.h + s'.g + Fmt.M1.lg s'.C.l) := by
    rw [eCl, ← hf.main, pow_add 2 (s'.h + s'.g) (Fmt.M1.lg s'.C.l), ← hf.powC]
  have lC : W.code.logEll = s'.h + s'.g + Fmt.M1.lg s'.C.l := by
    unfold Code.logEll
    rw [hell, ceilLog2_two_pow]
  have hrow : W.rowBits = s'.h + s'.g := by
    rw [f6]
    exact ceilLog2_two_pow _
  have htab : W.tableBits = s'.h + s'.g + Fmt.M1.lg s'.C.l := by
    rw [b2, lC']
    exact congrArg (· + _) (ceilLog2_two_pow _)
  have hrest : W.restBits = s'.h + Fmt.M1.lg s'.Z.l := by
    rw [b3]
    obtain ⟨x, hx1, hx2⟩ : ∃ x, S.oracles[g]? = some x ∧
        x.shape = (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape := by
      have h := hsh
      cases hx : S.oracles[g]? with
      | none => rw [hx] at h; cases h
      | some x => rw [hx] at h; exact ⟨x, rfl, Option.some.inj h⟩
    have hpos : ¬ (2 ^ s'.h = 0) := Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _)
    show S.tableBits g .mask = _
    unfold Statement.tableBits Statement.rowBits Statement.placeBits
    simp only [hx1, hx2, switchTargetStage, OracleShape.rows, ceilLog2_two_pow, beq_iff_eq, hpos,
      if_false, hgetZ, lZ']
  have hmask := hf.mask
  have pT : 2 ^ W.tableBits = 2 ^ (s'.h + s'.g) * s'.C.l := by
    rw [htab, pow_add 2 (s'.h + s'.g) (Fmt.M1.lg s'.C.l), ← hf.powC]
  have pR : 2 ^ W.restBits = 2 ^ s'.h * s'.Z.l := by
    rw [hrest, pow_add 2 s'.h (Fmt.M1.lg s'.Z.l), ← hf.powZ]
  refine ⟨frame_ok S old _ g W hW P.noKept P.masks P.keptRows rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, hC, hZ,
    f3, pT, pR⟩
  · -- the main row's message fills all rows of the new main table
    show (⟨.main, s'.h + s'.g, 0⟩ : RowCut) = ⟨.main, ceilLog2 (2 ^ (s'.h + s'.g)), 0⟩
    rw [ceilLog2_two_pow]
  · -- the rest is before the pad
    intro i hi
    refine make_flat S.codes _ rfl rfl (ceilLog2_two_pow _).symm (Nat.two_pow_pos _) i ?_
    show i < 2 ^ s'.h - 1 + ((S.codes.mask.getD nz default).ell - 1) * 2 ^ ceilLog2 (2 ^ s'.h)
    rw [hgetZ, eZl', ceilLog2_two_pow, Nat.sub_one_mul]
    rw [eZl, eCr, eZr] at hi
    have hp : 0 < 2 ^ s'.h := Nat.two_pow_pos _
    have hl : 0 < s'.Z.l := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hmask; omega
    have h2 : 2 ^ s'.h ≤ s'.Z.l * 2 ^ s'.h := Nat.le_mul_of_pos_left _ hl
    rw [Nat.mul_comm (2 ^ s'.h) s'.Z.l] at hmask
    omega
  · rw [lC]; exact hell
  · rw [hrow, lC]; omega
  · rw [lC, htab]
  · rw [pR, eZl]; omega
  · rw [eCa]; exact P.small
  · rw [eZa]; exact hf.short.trans P.small

/-! ## From a run of the switch to the claim after the library's switch -/

section
variable {s s' : Sg} {old : SingleRows} {nc nz gp : ℕ} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- The rows that a run of the switch batches, one by one, in the order of batching: first the claim
that is carried over, then the sample row, then each draw's three rows, whose targets are the
symbols read. For old rows without a kept member and with two mask rows, and a group that had no
member and no row. -/
theorem CsRan.run_rows {T : SwitchTarget}
    (h : CsRan old T gp others c c' out row lay theta D) (hkept : old.kept = #[])
    (hmasks : old.masks = 2) (hno : switchKept old = #[]) (hm : D.G.members = #[])
    (hr : D.G.rows = #[]) :
    ∃ W, switchFrame (D.stJ T gp others c) old T c.st.oracles.size #[] = some W ∧
      (runRows (D.stR T gp others c) (D.grown c)).toList =
        csRowsB W old D.sample D.rC.drawn.poss (fun x => symAtB old out.positions D.y x 0)
          (fun x => symAtB old out.positions D.y x (old.maskRow 0))
          (fun x => symAtB old out.positions D.y x (old.maskRow 1)) := by
  obtain ⟨W, hW, hrows⟩ := switchRows_eq _ old _ _ out.positions D.y D.rows hkept hmasks
    (fun W hW => by
      have hl := (switchFrame_fields _ old _ _ W hW).2.2.2.2.2.2.2.2.1
      rw [hno] at hl
      exact List.length_eq_zero_iff.1 hl) h.rows
  have hdraws : out.positions.draws.toList = D.rC.drawn.poss := by rw [h.positions]; rfl
  rw [hdraws] at hrows
  have hlist := order_of (carriedRow W old) D.sample
    (D.rC.drawn.poss.flatMap fun x =>
      [genMain W x (symAtB old out.positions D.y x 0),
        genMask W x 0 (symAtB old out.positions D.y x (old.maskRow 0)),
        genMask W x 1 (symAtB old out.positions D.y x (old.maskRow 1))])
    (kind_carriedRow W old)
    (fun r hr => by
      obtain ⟨x, _, hx⟩ := List.mem_flatMap.1 hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> rfl)
  refine ⟨W, hW, ?_⟩
  rw [D.runRows_fresh _ gp others c hm hr, hrows, hlist]
  rfl

/-- The row that a run of the switch returns has a plain form on the main table, if the old
claim has: no tensor of it has a written-out factor. -/
theorem CsRan.plain {T : SwitchTarget}
    (h : CsRan old T gp others c c' out row lay theta D) (hkept : old.kept = #[])
    (hmasks : old.masks = 2) (hno : switchKept old = #[]) (hm : D.G.members = #[])
    (hr : D.G.rows = #[]) (hc : PlainForm old.c) : PlainForm row.c := by
  obtain ⟨W, _, hrun⟩ := h.run_rows hkept hmasks hno hm hr
  refine combine_plain _ gp _ theta row (fun r hr' => ?_) h.row
  have hr2 : r ∈ (runRows (D.stR T gp others c) (D.grown c)).toList := hr'
  rw [hrun] at hr2
  unfold csRowsB at hr2
  simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hr2
  rcases hr2 with rfl | rfl | ⟨x, _, rfl | rfl | rfl⟩
  · exact plainRow_carriedRow W old hc
  · exact plainRow_form c.st.codes T.shape _ ⟨_, D.beta⟩ 0 D.smp h.form
  · exact plainRow_genMain _ _ _
  · exact plainRow_genMask _ _ _ _
  · exact plainRow_genMask _ _ _ _

/-- From a run of the program's code switch to the claim after the library's switch. The row
that the run returns, read in the field with the new group's own numbers of row bits, is `csNext` of
the program's claim before the switch, at the seed, the answer, the positions and the element that
the run has taken of the view.
What is asked beside the run. The program's codes and old rows are those of the two stages (P,
hkept, hd0, hd1, hc), and the group was new, under the new codes (hG). The plan's entry has the old
stage's number of positions, and the view's positions lie in the old code's range (ht, hx). β is the
drawn factor.
One hypothesis takes the place of a law on another function of the program. hy: the symbols read
are the long symbols of a word y at the drawn positions. -/
theorem csRan_sem (hf : CsFit s s')
    (h : CsRan old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others c c' out row lay theta
      D)
    (P : CsProg s s' c.st.codes old nc nz) (hkept : old.kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : (old.d.getD 0 #[]).size = s.Z.l) (hd1 : (old.d.getD 1 #[]).size = s.Z.l)
    (hc : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l)
    (ht : D.eC.poss = s.t) (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (y : s.cMid.Word) (Qs : Fin s.t → s.Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (hy : ∀ i α, s.cMid.T y (Qs i) α = symS s old out.positions D.y (Qs i).val α) :
    stmGk s' lay.k lay.h row = csNext hf (readE old.target) (vecS s old) y
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) c), β) (readE D.alpha)
      (Qs, readE theta) := by
  have hm : D.G.members = #[] := by rw [hG]
  have hkp : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  obtain ⟨hcodes, hshape⟩ :=
    D.stJ_shape (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others c
  -- the rows that are batched, in their order
  obtain ⟨W, hW, hrun⟩ := h.run_rows hkept P.masks P.noKept hm hr
  obtain ⟨hFr, hC, hZ, hg, pT, pR⟩ := frame_of hf _ old nc nz _ (hcodes ▸ P) hshape W hW
  -- the sample
  have hfits := sendFits_stage hf c.st.codes nc nz
    (by
      have h1 := P.code'
      cases hz : c.st.codes.base[nc]? with
      | none => rw [hz] at h1; cases h1
      | some z =>
        rw [hz] at h1
        rw [Array.getD_eq_getD_getElem?, hz]
        exact congrArg (·.l) (Option.some.inj h1))
    (by
      have h1 := P.zk'
      cases hz : c.st.codes.mask[nz]? with
      | none => rw [hz] at h1; cases h1
      | some z =>
        rw [hz] at h1
        rw [Array.getD_eq_getD_getElem?, hz]
        exact congrArg (·.l) (Option.some.inj h1))
  have hzlen : (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) c).length = s'.st.na := by
    have h1 := congrArg List.length h.seed
    rw [List.length_drop, hfits.bits] at h1
    unfold CsTaken.z
    rw [List.length_take, hfits.bits]
    simp only [List.length_cons, List.length_nil] at h1
    omega
  -- the structured vectors on the mask table reach over all places of the group
  have hl := h.lay_eq hm hkp
  have hlogZ : (c.st.codes.mask.getD D.G.maskCode default).logEll = Fmt.M1.lg s'.Z.l := by
    have h1 := P.zk'
    rw [hG]
    show (c.st.codes.mask.getD nz default).logEll = _
    cases hz : c.st.codes.mask[nz]? with
    | none => rw [hz] at h1; cases h1
    | some z =>
      rw [hz] at h1
      rw [Array.getD_eq_getD_getElem?, hz]
      show ceilLog2 z.ell = _
      rw [show z.ell = s'.Z.l from congrArg (·.l) (Option.some.inj h1), hf.powZ, ceilLog2_two_pow,
        ← hf.powZ]
  have hrbZ : (begun (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others c) gp
      (D.grown c)).rowBits c.st.oracles.size .mask = s'.h := by
    rw [D.rowBits_begun, rowBits_of_shape _ _ _ .mask hshape]
    exact ceilLog2_two_pow s'.h
  have hlz : lay.logEllZk = Fmt.M1.lg s'.Z.l := by rw [hl]; exact hlogZ
  have hrestB : W.restBits = s'.h + Fmt.M1.lg s'.Z.l :=
    Nat.pow_right_injective (Nat.le_refl 2) (by
      show 2 ^ W.restBits = 2 ^ (s'.h + Fmt.M1.lg s'.Z.l)
      rw [pR, pow_add 2 s'.h (Fmt.M1.lg s'.Z.l), ← hf.powZ])
  have hsF : MaskFits (begun (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others c) gp
      (D.grown c)) lay D.sample :=
    maskFits_target _ _ _ (maskFits_form c.st.codes _ _ ⟨_, D.beta⟩ 0 D.smp h.form _ _
      (by rw [hfits.bits]; exact le_of_eq hzlen.symm)
      (fun _ => by rw [hrbZ, hlz]; exact le_of_eq hfits.maskBits.symm)) D.alpha
  have hmf : ∀ r ∈ (runRows (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others c)
      (D.grown c)).toList, MaskFits (begun (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp
        others c) gp (D.grown c)) lay r := by
    intro r hr'
    rw [hrun] at hr'
    unfold csRowsB at hr'
    simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | ⟨x, _, rfl | rfl | rfl⟩
    · exact maskFits_carriedRow _ _ _ _
    · exact hsF
    · exact maskFits_genMain _ _ _ _ _
    · exact maskFits_genMask _ _ hFr (by rw [hg, hrbZ, hlz, hrestB]) _ _ _
    · exact maskFits_genMask _ _ hFr (by rw [hg, hrbZ, hlz, hrestB]) _ _ _
  -- the returned row is their sum under the powers of theta
  have hk : lay.k = max (max (s'.h + s'.g) s'.h) 1 := by rw [hl]
  have hh : lay.h = s'.h := by rw [hl]
  have hB : BatchedAt s' lay.k lay.h row
      (runRows (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others c)
        (D.grown c)).toList c.st.oracles.size (readE theta) :=
    batchedAt_of_index s' lay.k lay.h row _ _ (readE theta)
      (fun idx _ => by
        rw [hk]
        exact h.bat_main hm hkp hr idx)
      (fun idx hi => by
        rw [hh]
        refine h.bat_mask hm hkp hr hmf idx ?_
        rw [hlogZ, pow_add 2 s'.h (Fmt.M1.lg s'.Z.l), ← hf.powZ]
        exact hi)
      (h.bat_target hm hr)
  rw [hrun, ← hg] at hB
  refine cs_batchedAt_sem hf hFr hC hZ old (hd0.trans (congrArg (·.l) hZ).symm)
    (hd1.trans (congrArg (·.l) hZ).symm) ?_ (le_of_eq pT.symm) (le_of_eq pR.symm) D.sample
    D.rC.drawn.poss (h.poss.trans ht) ?_ _ _ _ row theta lay.k lay.h hB _ _ rfl ?_ y Qs hQ
    (fun i => hy i _) (fun i => hy i _) (fun i => hy i _)
  · intro v hv
    rw [hc v hv]
    unfold Code.logEll
    rw [show W.code.ell = s.C.l from congrArg (·.l) hC]
  · intro x hx'
    rw [show W.code.logN = s.C.a from congrArg (·.a) hC]
    exact hx x hx'
  · intro n
    rw [hg]
    exact (sendCs_mat hf c.st.codes _ hfits _ ⟨_, D.beta⟩ D.smp h.form hzlen β hβ n).symm

end

end OnBytes.Slice

#print axioms OnBytes.Slice.frame_of
#print axioms OnBytes.Slice.CsRan.run_rows
#print axioms OnBytes.Slice.CsRan.plain
#print axioms OnBytes.Slice.csRan_sem
#print axioms OnBytes.Slice.order_of
#print axioms OnBytes.Slice.switchFrame_bits
