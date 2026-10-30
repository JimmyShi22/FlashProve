-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SwClaim.lean: the row behind a code switch of the proximity test, read in the
field, is the chain's next claim.

From `Did` (Johnson/Desc/K12/Law/SwDid.lean), the public facts and "what was read is the folded
words" follows: the row behind the switch, read in the field, is the chain's claim `csNextW`.
Statements and proofs.
How the file was made: it is a port by a program of the library's lemmas on `CsTaken` and `CsRan`
(OnBytes/Slice/BlkCsRun.lean, BlkCsJoint.lean, BlkCsClaim.lean); each theorem stands under a line
"ported from ...". The statements' and the proofs' text is the library's to the letter, but for:
`CsRan ... c c'` became `Did ... S Bk roots S' Bk'`; `CsTaken` became `Taken`; `c.st` became `S`; a
context became a statement; the entry's count of positions became the drawn list's length; the
pending rounds became the two rounds as `Block.step` shows them; and a few proof lines that fell
away with these.
Main names:
  `did_sem`: the port of `csRan_sem`.
  `did_claim`: the port of `csRan_claim`.
Limits: No statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); that program's plain
records and pure functions, some with names that begin with `Blk.`, and lemmas on them, are used. No
soundness is claimed. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.SwDid
import OnBytes.Slice.BlkCsClaim

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc (noDigest)

section
variable {ft : Nat} {cols : List Tw.L9.Col} {s s' : Sg} {old : SingleRows} {T : SwitchTarget}
  {nc nz gp : ℕ} {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : Nat}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

-- ported from OnBytes/Slice/BlkCsRun.lean: CsRan.group0
/-- The group before the switch is the group that the statement had at the start. -/
theorem Did.group0 (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    S.groups[gp]? = some D.G := by
  have h1 := h.group
  rw [ledgerShut_groups] at h1
  exact h1

-- ported from OnBytes/Slice/BlkCsRun.lean: CsTaken.sampleRows_stR
/-- The sample rows of the new oracle message, in the statement with the claims. -/
theorem Taken.sampleRows_stR (D : Taken) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (S : Statement) :
    ((D.stR T gp others S).oracles[S.oracles.size]?).map (·.sampleRows) = some #[D.sample] := by
  have hlt : S.oracles.size < (stSent S (sentOf T others)).oracles.size := by
    unfold stSent sentOf
    simp
    omega
  unfold Taken.stR Taken.stJ Taken.stA
  rw [(withRows_oracles gp D.rows _).1, joined_sampleRows, ledgerShut_sampleRows,
    admitted_sampleRows _ _ _ _ _ hlt]

-- ported from OnBytes/Slice/BlkCsRun.lean: CsTaken.runRows_fresh
/-- The rows that the switch batches, if the group had no member and no row before: the plain
rows among the claims, the sample row of the new oracle message, the generator rows. -/
theorem Taken.runRows_fresh (D : Taken) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (S : Statement) (hm : D.G.members = #[]) (hr : D.G.rows = #[]) :
    runRows (D.stR T gp others S) (D.grown S) =
      D.rows.toArray.filter (·.kind == .plain) ++ #[D.sample] ++
        D.rows.toArray.filter (·.kind == .generator) := by
  have hrows : (D.grown S).rows = D.rows.toArray := by
    unfold Taken.grown
    simp [hr]
  have hmem : (D.grown S).members = #[S.oracles.size] := by
    unfold Taken.grown
    simp [hm, Array.insertIdxIfInBounds]
  unfold runRows
  rw [hrows, hmem]
  have hs := D.sampleRows_stR T gp others S
  simp only [List.foldl_toArray', List.foldl_cons, List.foldl_nil, hs, Option.getD_some,
    Array.empty_append]

-- ported from OnBytes/Slice/BlkCsLay.lean: CsTaken.stJ_shape
/-- The codes, and the shape of the new oracle message, in the statement in which it has joined its
group. -/
theorem Taken.stJ_shape (D : Taken) (T : SwitchTarget) (gp : ℕ) (others : Array OracleNotice)
    (S : Statement) :
    (D.stJ T gp others S).codes = S.codes ∧
      ((D.stJ T gp others S).oracles[S.oracles.size]?).map (·.shape) = some T.shape := by
  have h1 := ledgerShut_shape (D.stA T others S) T S.oracles.size S.oracles.size
  constructor
  · exact h1.1
  · have h2 : ((D.stJ T gp others S).oracles[S.oracles.size]?).map (·.shape) =
        ((ledgerShut (D.stA T others S) T S.oracles.size).oracles[S.oracles.size]?).map
          (·.shape) := by
      unfold Taken.stJ withMessageInGroup
      simp only [Array.getElem?_modify, if_true, Option.map_map]
      rfl
    rw [h2, h1.2]
    unfold Taken.stA admitted sentOf
    simp only [Array.getElem?_modify, if_true, Option.map_map, sent_first]
    rfl

-- ported from OnBytes/Slice/BlkCsLay.lean: CsTaken.stR_shape
/-- The same in the statement with the claims. -/
theorem Taken.stR_shape (D : Taken) (T : SwitchTarget) (gp : ℕ) (others : Array OracleNotice)
    (S : Statement) :
    (D.stR T gp others S).codes = S.codes ∧
      ((D.stR T gp others S).oracles[S.oracles.size]?).map (·.shape) = some T.shape := by
  obtain ⟨h1, h2⟩ := D.stJ_shape T gp others S
  obtain ⟨w1, w2⟩ := withRows_oracles gp D.rows (D.stJ T gp others S)
  unfold Taken.stR
  rw [w1, w2]
  exact ⟨h1, h2⟩

-- ported from OnBytes/Slice/BlkCsLay.lean: CsRan.group_stR
/-- The group, in the statement with the claims. -/
theorem Did.group_stR (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    (D.stR T gp others S).groups[gp]? = some (D.grown S) := by
  unfold Taken.stR Taken.stJ
  rw [withRows_group gp D.rows _ _ (joined_group _ gp S.oracles.size false D.G h.group)]
  rfl

-- ported from OnBytes/Slice/BlkCsLay.lean: CsRan.lay_eq
/-- The layout that a switch into a stage returns, for a group that had no member: the new
oracle message's 2^a main rows and 2^b mask rows begin at the row 0 of the group's tables. The
group's main table has at least two rows. -/
theorem Did.lay_eq {nc nz a b : ℕ}
    (h : Did ft cols old (switchTargetStage nc nz a b 1) gp others S Bk roots S' Bk' out row lay
        theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) :
    lay = { k := max (max a b) 1, h := b
            logEll := (S.codes.base.getD D.G.code default).logEll
            logEllZk := (S.codes.mask.getD D.G.maskCode default).logEll
            members := #[S.oracles.size], kept := #[false]
            mainFirst := #[some 0], maskFirst := #[some 0] } := by
  obtain ⟨hcodes, hshape⟩ := D.stR_shape (switchTargetStage nc nz a b 1) gp others S
  obtain ⟨x, hx1, hx2⟩ : ∃ x, (D.stR (switchTargetStage nc nz a b 1) gp others S).oracles[
      S.oracles.size]? = some x ∧ x.shape = (switchTargetStage nc nz a b 1).shape := by
    cases hx : (D.stR (switchTargetStage nc nz a b 1) gp others S).oracles[S.oracles.size]? with
    | none => rw [hx] at hshape; cases hshape
    | some x => rw [hx] at hshape; exact ⟨x, rfl, Option.some.inj hshape⟩
  have hmem : (D.grown S).members = #[S.oracles.size] := by
    unfold Taken.grown
    simp [hm, Array.insertIdxIfInBounds]
  have hkept : (D.grown S).kept = #[false] := by
    unfold Taken.grown
    simp [hm, hk, Array.insertIdxIfInBounds]
  have hl := layout_one _ gp S.oracles.size a b (D.grown S) x h.group_stR hmem hkept hx1
    (by rw [hx2]; rfl) (by rw [hx2]; rfl)
  rw [h.layout, hcodes] at hl
  exact Option.some.inj hl

-- ported from OnBytes/Slice/BlkCsLay.lean: CsTaken.rowBits_begun
/-- The row bits in the statement in which the batching is done are those in the statement in which
the new oracle message has joined its group. -/
theorem Taken.rowBits_begun (D : Taken) (T : SwitchTarget) (gp : ℕ)
    (others : Array OracleNotice) (S : Statement) (o : ℕ) (part : Part) :
    (begun (D.stR T gp others S) gp (D.grown S)).rowBits o part
      = (D.stJ T gp others S).rowBits o part := by
  rw [begun_rowBits]
  unfold Statement.rowBits Taken.stR
  rw [(withRows_oracles gp D.rows _).1]

-- ported from OnBytes/Slice/BlkCsLay.lean: CsRan.fits
/-- Every row that the switch batches meets the conditions of the laws on batching, if the group
had no member and no row. -/
theorem Did.fits (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hm : D.G.members = #[]) (hr : D.G.rows = #[]) :
    ∀ r ∈ (runRows (D.stR T gp others S) (D.grown S)).toList,
      RowFits (begun (D.stR T gp others S) gp (D.grown S)) r := by
  have hclaim : ∀ r ∈ D.rows, RowFits (begun (D.stR T gp others S) gp (D.grown S)) r :=
    fun r hr' => rowFits_congr (D.rowBits_begun T gp others S)
      (rowFits_of_checked (h.kinds r hr').2)
  have hsample : RowFits (begun (D.stR T gp others S) gp (D.grown S)) D.sample := by
    refine rowFits_target _ _ (rowFits_form S.codes T.shape S.oracles.size ⟨D.z T S, D.beta⟩ 0
      D.smp h.form _ ?_ fun part hp => ?_) D.alpha
    · have h1 := congrArg List.length h.seed
      rw [List.length_drop] at h1
      show _ ≤ (D.z T S).length
      unfold Taken.z
      rw [List.length_take]
      simp only [List.length_cons, List.length_nil] at h1
      omega
    · rw [D.rowBits_begun T gp others S,
        rowBits_of_shape _ _ T.shape part (D.stJ_shape T gp others S).2]
      exact rowBits_le_partBits S.codes T.shape part hp
  intro r hr'
  rw [D.runRows_fresh T gp others S hm hr] at hr'
  simp only [Array.toList_append, Array.toList_filter, List.mem_append, List.mem_filter,
    List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with (⟨h1, _⟩ | rfl) | ⟨h1, _⟩
  · exact hclaim r h1
  · exact hsample
  · exact hclaim r h1

-- ported from OnBytes/Slice/BlkCsLay.lean: CsRan.bat_main
/-- What the switch returns, on the main table: at the place to which entry idx of the new
oracle message's main table goes, the returned row has the sum of the batched rows' coefficients on
that entry under the powers of theta. -/
theorem Did.bat_main {nc nz a b : ℕ}
    (h : Did ft cols old (switchTargetStage nc nz a b 1) gp others S Bk roots S' Bk' out row lay
        theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) (hr : D.G.rows = #[]) (idx : ℕ) :
    formAt row.c (groupIndex idx a 0 (max (max a b) 1)) = hornerSum (readE theta)
      ((runRows (D.stR (switchTargetStage nc nz a b 1) gp others S) (D.grown S)).toList.map
        fun r => coefAt r S.oracles.size .main idx) := by
  have hl := h.lay_eq hm hk
  have hrb : (begun (D.stR (switchTargetStage nc nz a b 1) gp others S) gp (D.grown S)).rowBits
      S.oracles.size .main = a := by
    rw [D.rowBits_begun, rowBits_of_shape _ _ _ .main (D.stJ_shape _ gp others S).2]
    exact ceilLog2_two_pow a
  have h1 := combine_one_main _ S.oracles.size a gp _ theta row h.row (h.fits hm hr)
    (by rw [hl]) (by rw [hl]) (by rw [hl]) hrb (by rw [hl]; show a ≤ max (max a b) 1; omega) idx
  rw [hl] at h1
  exact h1

-- ported from OnBytes/Slice/BlkCsLay.lean: CsRan.bat_mask
/-- The same on the mask table, for the entries idx below 2^(b + logEll), with the logEll of the
group's mask code. hmf: every structured vector on a mask table, in the rows that are batched,
reaches over the whole of the group's places. -/
theorem Did.bat_mask {nc nz a b : ℕ}
    (h : Did ft cols old (switchTargetStage nc nz a b 1) gp others S Bk roots S' Bk' out row lay
        theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) (hr : D.G.rows = #[])
    (hmf : ∀ r ∈ (runRows (D.stR (switchTargetStage nc nz a b 1) gp others S) (D.grown S)).toList,
      MaskFits (begun (D.stR (switchTargetStage nc nz a b 1) gp others S) gp (D.grown S)) lay r)
    (idx : ℕ) (hi : idx < 2 ^ (b + (S.codes.mask.getD D.G.maskCode default).logEll)) :
    readV row.d (groupIndex idx b 0 b) = hornerSum (readE theta)
      ((runRows (D.stR (switchTargetStage nc nz a b 1) gp others S) (D.grown S)).toList.map
        fun r => coefAt r S.oracles.size .mask idx) := by
  have hl := h.lay_eq hm hk
  have hrb : (begun (D.stR (switchTargetStage nc nz a b 1) gp others S) gp (D.grown S)).rowBits
      S.oracles.size .mask = b := by
    rw [D.rowBits_begun, rowBits_of_shape _ _ _ .mask (D.stJ_shape _ gp others S).2]
    exact ceilLog2_two_pow b
  have hsame : groupIndex idx b 0 b = idx := by
    unfold groupIndex
    rw [Nat.zero_add, Nat.mul_comm]
    exact Nat.mod_add_div idx (2 ^ b)
  have h1 := combine_one_mask _ S.oracles.size b gp _ theta row h.row
    (fun r hr' => ⟨h.fits hm hr r hr', hmf r hr'⟩) (by rw [hl]) (by rw [hl]) hrb
    (by rw [hl]) idx (by rw [hl]; show groupIndex idx b 0 b < _; rw [hsame]; exact hi)
  rw [hl] at h1
  exact h1

-- ported from OnBytes/Slice/BlkCsLay.lean: CsRan.bat_target
/-- The same for the target. -/
theorem Did.bat_target (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hm : D.G.members = #[]) (hr : D.G.rows = #[]) :
    readE row.target = hornerSum (readE theta)
      ((runRows (D.stR T gp others S) (D.grown S)).toList.map fun r => readE r.target) :=
  combine_one_target _ gp _ theta row h.row (h.fits hm hr)

-- ported from OnBytes/Slice/BlkCsJoint.lean: CsRan.run_rows
/-- The rows that a switch and the batching behind it (Did) batches, one by one, in the order of
batching: first the claim
that is carried over, then the sample row, then each draw's three rows, whose targets are the
symbols read. For old rows without a kept member and with two mask rows, and a group that had no
member and no row. -/
theorem Did.run_rows {T : SwitchTarget}
    (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (hkept : old.kept = #[])
    (hmasks : old.masks = 2) (hno : switchKept old = #[]) (hm : D.G.members = #[])
    (hr : D.G.rows = #[]) :
    ∃ W, switchFrame (D.stJ T gp others S) old T S.oracles.size #[] = some W ∧
      (runRows (D.stR T gp others S) (D.grown S)).toList =
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
  rw [D.runRows_fresh _ gp others S hm hr, hrows, hlist]
  rfl

-- ported from OnBytes/Slice/BlkCsJoint.lean: csRan_sem
/-- From a switch and the batching behind it (Did) to the claim after the library's switch. The row
that the switch returns, read in the field with the new group's own numbers of row bits, is `csNext`
of
the program's claim before the switch, at the seed, the answer, the positions and the element that
the switch has taken of the view.
What is asked beside the switch. The program's codes and old rows are those of the two stages (P,
hkept, hd0, hd1, hc), and the group was new, under the new codes (hG). The plan's entry has the old
stage's number of positions, and the view's positions lie in the old code's range (ht, hx). β is the
drawn factor.
One hypothesis takes the place of a law on another function of the program. hy: the symbols read
are the long symbols of a word y at the drawn positions. -/
theorem did_sem (hf : CsFit s s')
    (h : Did ft cols old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk'
        out row lay theta D)
    (P : CsProg s s' S.codes old nc nz) (hkept : old.kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : (old.d.getD 0 #[]).size = s.Z.l) (hd1 : (old.d.getD 1 #[]).size = s.Z.l)
    (hc : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l)
    (ht : D.rC.drawn.poss.length = s.t) (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (y : s.cMid.Word) (Qs : Fin s.t → s.Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (hy : ∀ i α, s.cMid.T y (Qs i) α = symS s old out.positions D.y (Qs i).val α) :
    stmGk s' lay.k lay.h row = csNext hf (readE old.target) (vecS s old) y
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S), β) (readE D.alpha)
      (Qs, readE theta) := by
  have hm : D.G.members = #[] := by rw [hG]
  have hkp : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  obtain ⟨hcodes, hshape⟩ :=
    D.stJ_shape (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S
  -- the rows that are batched, in their order
  obtain ⟨W, hW, hrun⟩ := h.run_rows hkept P.masks P.noKept hm hr
  obtain ⟨hFr, hC, hZ, hg, pT, pR⟩ := frame_of hf _ old nc nz _ (hcodes ▸ P) hshape W hW
  -- the sample
  have hfits := sendFits_stage hf S.codes nc nz
    (by
      have h1 := P.code'
      cases hz : S.codes.base[nc]? with
      | none => rw [hz] at h1; cases h1
      | some z =>
        rw [hz] at h1
        rw [Array.getD_eq_getD_getElem?, hz]
        exact congrArg (·.l) (Option.some.inj h1))
    (by
      have h1 := P.zk'
      cases hz : S.codes.mask[nz]? with
      | none => rw [hz] at h1; cases h1
      | some z =>
        rw [hz] at h1
        rw [Array.getD_eq_getD_getElem?, hz]
        exact congrArg (·.l) (Option.some.inj h1))
  have hzlen : (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S).length = s'.st.na := by
    have h1 := congrArg List.length h.seed
    rw [List.length_drop, hfits.bits] at h1
    unfold Taken.z
    rw [List.length_take, hfits.bits]
    simp only [List.length_cons, List.length_nil] at h1
    omega
  -- the structured vectors on the mask table reach over all places of the group
  have hl := h.lay_eq hm hkp
  have hlogZ : (S.codes.mask.getD D.G.maskCode default).logEll = Fmt.M1.lg s'.Z.l := by
    have h1 := P.zk'
    rw [hG]
    show (S.codes.mask.getD nz default).logEll = _
    cases hz : S.codes.mask[nz]? with
    | none => rw [hz] at h1; cases h1
    | some z =>
      rw [hz] at h1
      rw [Array.getD_eq_getD_getElem?, hz]
      show ceilLog2 z.ell = _
      rw [show z.ell = s'.Z.l from congrArg (·.l) (Option.some.inj h1), hf.powZ, ceilLog2_two_pow,
        ← hf.powZ]
  have hrbZ : (begun (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S) gp
      (D.grown S)).rowBits S.oracles.size .mask = s'.h := by
    rw [D.rowBits_begun, rowBits_of_shape _ _ _ .mask hshape]
    exact ceilLog2_two_pow s'.h
  have hlz : lay.logEllZk = Fmt.M1.lg s'.Z.l := by rw [hl]; exact hlogZ
  have hrestB : W.restBits = s'.h + Fmt.M1.lg s'.Z.l :=
    Nat.pow_right_injective (Nat.le_refl 2) (by
      show 2 ^ W.restBits = 2 ^ (s'.h + Fmt.M1.lg s'.Z.l)
      rw [pR, pow_add 2 s'.h (Fmt.M1.lg s'.Z.l), ← hf.powZ])
  have hsF : MaskFits (begun (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S) gp
      (D.grown S)) lay D.sample :=
    maskFits_target _ _ _ (maskFits_form S.codes _ _ ⟨_, D.beta⟩ 0 D.smp h.form _ _
      (by rw [hfits.bits]; exact le_of_eq hzlen.symm)
      (fun _ => by rw [hrbZ, hlz]; exact le_of_eq hfits.maskBits.symm)) D.alpha
  have hmf : ∀ r ∈ (runRows (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S)
      (D.grown S)).toList, MaskFits (begun (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp
        others S) gp (D.grown S)) lay r := by
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
      (runRows (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S)
        (D.grown S)).toList S.oracles.size (readE theta) :=
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
    D.rC.drawn.poss ht ?_ _ _ _ row theta lay.k lay.h hB _ _ rfl ?_ y Qs hQ
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
    exact (sendCs_mat hf S.codes _ hfits _ ⟨_, D.beta⟩ D.smp h.form hzlen β hβ n).symm

-- ported from OnBytes/Slice/BlkCsClaim.lean: csRan_claim
/-- The row that a switch and the batching behind it (Did) returns is the claim after the switch, at
the
values of the two written rounds. hr: what the two rounds send and draw. hp: the two rounds that
the switch took ARE the two written rounds, without the sealed digest. hbits: the point of the
sample has as many coordinates as the
library's. hy: the symbols that the switch has read are the long symbols of the word y at the drawn
positions. The other hypotheses are those of `did_sem` (above). -/
theorem did_claim (hf : CsFit s s') (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τ : Tr (PQ.uL (ckP .two) [dS, dC]))
    (h : Did ft cols old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk'
        out row lay theta D)
    (hp : [D.rS, D.rC] = (PQ.rvSL (ckP .two) [dS, dC] τ).map noDigest)
    (P : CsProg s s' S.codes old nc nz) (hkept : old.kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : (old.d.getD 0 #[]).size = s.Z.l) (hd1 : (old.d.getD 1 #[]).size = s.Z.l)
    (hc : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l)
    (hbits : (Send.cube S.codes (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape).bits
      = s'.st.na)
    (y : s.cMid.Word)
    (hy : ∀ i α, s.cMid.T y ((gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).1 i) α =
      symS s old out.positions D.y ((gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).1 i).val α) :
    stmGk s' lay.k lay.h row = csNextW hf dS dC (stmS s old) y τ := by
  -- the two rounds that the switch has taken are the two written rounds
  injection hp with eS e2
  injection e2 with eC _
  have elS : D.rS.drawn.elems = (rvOf dS τ.1 τ.2.1).els := by rw [eS]; rfl
  have elC : D.rC.drawn.elems = (rvOf dC τ.2.2.1 τ.2.2.2.1).els := by rw [eC]; rfl
  have poC : D.rC.drawn.poss = (rvOf dC τ.2.2.1 τ.2.2.2.1).poss := by rw [eC]; rfl
  have seC : Fmt.M1.sentOf D.rC.vals = (rvOf dC τ.2.2.1 τ.2.2.2.1).sent := by rw [eC]; rfl
  -- as the library reads them
  obtain ⟨β, hseed, hβ⟩ := seed_read hr.nz τ.1 τ.2.1
  obtain ⟨alpha, th, xs, hrv, hxs, hans, hth, hQ⟩ := cs_read hr.cs τ.2.2.1 τ.2.2.2.1
  rw [hrv] at elC poC seC
  -- the factor of the seed
  have hbeta : β.val = readE D.beta := by
    have k := congrArg (fun l => readL l 0) h.seed
    simp only at k
    rw [readL_drop, readL_ofTriple, hbits, Nat.add_zero, elS] at k
    rw [hβ]
    exact k
  -- the point of the seed
  have hz : readP s'.st.na (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S) =
      ptL s'.st.na ((rvOf dS τ.1 τ.2.1).els.take s'.st.na) := by
    funext i
    show readL ((D.rS.drawn.elems.map E.ofTriple).take _) i.val = lst (List.take _ _) i.val
    rw [hbits, readL_take _ _ _ i.isLt, readL_ofTriple, lst_take _ _ _ i.isLt, elS]
  -- the answer
  have halpha : readE D.alpha = (ansOf dC τ.2.2.1).getD 0 0 := by
    rw [hans, readE_def]
    rw [h.valsC] at seC
    exact congrArg toE (List.head_eq_of_cons_eq seC)
  -- the element
  have htheta : readE theta = (gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).2 := by
    have k := h.elem
    rw [elC] at k
    rw [hth, ← List.head_eq_of_cons_eq k, readE_ofTriple]
  have hsem := did_sem hf h P hkept hG hd0 hd1 hc
    (by rw [poC]; exact hxs)
    (fun x hx => by
      rw [poC] at hx
      have hx' : x ∈ (rvOf dC τ.2.2.1 τ.2.2.2.1).poss := by rw [hrv]; exact hx
      exact hr.cs.poss_lt τ.2.2.1 τ.2.2.2.1 x hx')
    β hbeta y (gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).1 (fun i => by rw [poC]; exact hQ i) hy
  rw [hsem, hz, halpha, htheta, ← hseed]
  rfl

end

end H2K.Sw
