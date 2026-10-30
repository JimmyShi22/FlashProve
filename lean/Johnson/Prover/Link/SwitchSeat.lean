-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchSeat.lean: at a code switch between two stages of the proximity test the
frame is as the laws on the made rows ask, and the statement in which the new message is a member
of its group holds the seat (`RowSeat`, Johnson/Prover/Link/SwitchRows.lean): so every made row is
added.

Main names (namespace `Johnson.Prover.Link`).
  `stJ_pad`   the new message's pad in that statement is what the admitting has laid
  `pad_stage`   at a stage's target with one answer the pad is one place: the mask table's last
      entry
  `seat_stJ`   the two stages fit (`CsFit`), the program's codes and old rows are theirs (`CsProg`),
      the pad's places, the new group was empty and in no test, two bounds on the new tables' sizes:
      then `FrameOK`, the frame's two old codes, and `RowSeat`
  `addOk_of`   the clause `addOk` of `SwitchFacts` (Johnson/Prover/Link/FormSwitch.lean)

By: `frame_of`, `switchFrame_bits` (OnBytes/Slice/BlkCsJoint.lean), `Taken.stJ_shape`
(Johnson/Desc/K12/Law/SwClaim.lean), `rowsCan_some` (Johnson/Top/H0/Tw/K2/RowsMadeAgree.lean),
`made_add`.

Limits. Every premise is asked. The old claim's form is asked to be dense (`DenseForm`) and to fit
the old message (`Means.CFits`: each tensor has the message's index bits as its variables, each
single entry lies below the message's length). Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchRows
import Johnson.Top.H0.Tw.K2.RowsMadeAgree
import Johnson.Desc.K12.Law.SwClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

/-- The new message's pad in the statement in which it is a member. -/
theorem stJ_pad (D : Taken) (T : SwitchTarget) (gp : ℕ) (others : Array OracleNotice)
    (S : Statement) :
    ((D.stJ T gp others S).oracles[S.oracles.size]?).map (·.pad) =
      some (D.places.map fun q => (q.part, q.index)) := by
  have hx := sent_first S ⟨T.shape, T.leafClass⟩ others
  unfold Taken.stJ OnBytes.Slice.withMessageInGroup ledgerShut Taken.stA admitted
  split
  · unfold closeLedgers
    simp only [List.foldl_cons, List.foldl_nil, Array.getElem?_modify, if_true]
    unfold OnBytes.Slice.sentOf
    rw [hx]
    rfl
  · simp only [Array.getElem?_modify, if_true]
    unfold OnBytes.Slice.sentOf
    rw [hx]
    rfl

/-- At a stage's target with one answer the pad is the mask table's last entry. -/
theorem pad_stage (codes : Codes) (nc nz k h : ℕ) (places : List PadPlace)
    (hp : Send.pad codes (switchTargetStage nc nz k h 1).shape = some places) :
    ∀ q ∈ places, q.part = .mask ∧ q.index = 2 ^ h * (codes.mask.getD nz default).ell - 1 := by
  have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
  unfold Send.pad Send.cube switchTargetStage at hp
  simp only [hpos, decide_true, if_true, Bool.true_or, ceilLog2_two_pow, Nat.one_mul] at hp
  split at hp
  · cases hp
  · rename_i hlen
    obtain rfl := Option.some.inj hp
    intro q hq
    simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.append_nil, List.mem_singleton] at hq
    subst hq
    refine ⟨rfl, ?_⟩
    show 2 ^ h - 1 + ((codes.mask.getD nz default).ell - 1 + 0 + 0) * 2 ^ h = _
    obtain ⟨m, hm⟩ : ∃ m, (codes.mask.getD nz default).ell = m + 1 :=
      ⟨(codes.mask.getD nz default).ell - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, Nat.add_zero, Nat.add_zero, Nat.mul_add, Nat.mul_one,
      Nat.mul_comm m]
    omega

/-- **The frame and the seat, at the statement in which the new message is a member.** -/
theorem seat_stJ {s s' : Sg} (hf : CsFit s s') (D : Taken) (gp : ℕ) (others : Array OracleNotice)
    (S : Statement) (old : SingleRows) (nc nz : ℕ) (P : CsProg s s' S.codes old nc nz)
    (hpad : Send.pad S.codes (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape = some D.places)
    (hm : D.G.members = #[]) (hrun : D.G.inRun = false)
    (hsmall : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ 63 ∧ 2 ^ s'.h * s'.Z.l ≤ 2 ^ 63) (W : SwitchFrame)
    (hW : switchFrame (D.stJ (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S) old
      (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S.oracles.size #[] = some W) :
    FrameOK W ∧ codeOf W.code = s.C ∧ codeOf W.zk = s.Z ∧
      RowSeat (D.stJ (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S)
        { D.G with
          members := D.G.members.insertIdxIfInBounds
            (D.G.members.filter (· < S.oracles.size)).size S.oracles.size
          kept := D.G.kept.insertIdxIfInBounds
            (D.G.members.filter (· < S.oracles.size)).size false } W := by
  obtain ⟨hcodes, hshape⟩ :=
    D.stJ_shape (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S
  obtain ⟨hF, hC, hZ, hg, hT, hR⟩ := frame_of hf _ old nc nz _ (hcodes ▸ P) hshape W hW
  obtain ⟨cd', b1, b2, b3⟩ := switchFrame_bits _ old _ _ W hW
  obtain ⟨x, hx, hxs⟩ : ∃ x, (D.stJ (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others
      S).oracles[S.oracles.size]? = some x ∧
      x.shape = (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape := by
    cases hx : (D.stJ (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others
        S).oracles[S.oracles.size]? with
    | none => rw [hx] at hshape; cases hshape
    | some x => rw [hx] at hshape; exact ⟨x, rfl, Option.some.inj hshape⟩
  have eZl : W.zk.ell = s.Z.l := congrArg (·.l) hZ
  have eZr : W.zk.r = s.Z.r := congrArg (·.r) hZ
  have eCr : W.code.r = s.C.r := congrArg (·.r) hC
  have hmask := hf.mask
  have hell : (S.codes.mask.getD nz default).ell = s'.Z.l := by
    have h := P.zk'
    cases hz : S.codes.mask[nz]? with
    | none => rw [hz] at h; cases h
    | some z =>
      rw [hz] at h
      rw [Array.getD_eq_getD_getElem?, hz]
      exact congrArg (·.l) (Option.some.inj h)
  refine ⟨hF, hC, hZ, hrun, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · show D.G.members.insertIdxIfInBounds _ _ = _
    rw [hm, hg]
    simp
  · rw [hg]
    unfold Statement.has
    simp only [hx, hxs]
    exact decide_eq_true (Nat.two_pow_pos _)
  · rw [hg, b2]
    unfold Statement.tableBits Statement.rowBits Statement.placeBits
    simp only [hx, hxs]
    have hne : ((switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape.rows .main == 0) = false := by
      show (2 ^ (s'.h + s'.g) == 0) = false
      simpa using (Nat.two_pow_pos (s'.h + s'.g)).ne'
    simp only [hne, Bool.false_eq_true, if_false]
    have hb : (D.stJ (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S).codes.base.getD
        (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape.code default = cd' := by
      rw [Array.getD_eq_getD_getElem?, b1]
      rfl
    rw [hb]
    rfl
  · rw [hg]
    unfold Statement.has
    simp only [hx, hxs]
    exact decide_eq_true (Nat.two_pow_pos _)
  · rw [hg, b3]
    rfl
  · exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (hT ▸ hsmall.1)
  · exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (hR ▸ hsmall.2)
  · rw [hR, eZl, eZr, eCr]
    omega
  · intro q hq
    rw [hg, stJ_pad] at hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hq
    obtain ⟨p1, p2⟩ := pad_stage S.codes nc nz (s'.h + s'.g) s'.h D.places hpad q0 hq0
    refine ⟨p1, ?_, ?_⟩
    · show _ ≤ q0.index
      rw [p2, hell, eZl, eZr, eCr]
      omega
    · show q0.index < _
      rw [p2, hell, hR]
      omega

/-- **Clause `addOk` is paid**: every row that the switch makes is added. -/
theorem addOk_of {s s' : Sg} (hf : CsFit s s') {p : P12} {n : IoppStage} {last : Bool} {t : T12}
    {rC : Fmt.RoundView} {rows : SingleRows} {gp : ℕ} {D : Taken}
    (ff : FoldedFit s s' t.st.codes n.code n.maskCode rows) (hnk : n.k = s'.h + s'.g)
    (hnh : n.h = s'.h) (h1 : p.answers = 1)
    (hgroup : (ledgerShut (D.stA (swTarget p n) (othersOf last n) t.st) (swTarget p n)
      t.st.oracles.size).groups[gp]? = some D.G)
    (hpad : Own.padMade t.st.codes (swTarget p n).shape = some D.places)
    (hcan : Tw.K2.rowsCan (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows (swTarget p n) #[]
      (swPos rC D) D.y = true)
    (hmade : D.rows = (Own.swRows (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows
      (swTarget p n) t.st.oracles.size #[] (swPos rC D) D.y).getD [])
    (hm : D.G.members = #[]) (hrun : D.G.inRun = false)
    (hsmall : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ 63 ∧ 2 ^ s'.h * s'.Z.l ≤ 2 ^ 63)
    (hc : Means.CFits (ceilLog2 s.C.l) rows.c) (hp : DenseForm rows.c)
    (hx : ∀ x ∈ rC.drawn.poss, x < 2 ^ s.C.a) :
    (D.rows.foldlM (fun S r => Tw.L9.addRowS S gp r)
      (D.stJ (swTarget p n) gp (othersOf last n) t.st)).toOption.isSome = true := by
  have eT : swTarget p n = switchTargetStage n.code n.maskCode (s'.h + s'.g) s'.h 1 := by
    unfold swTarget
    rw [hnk, hnh, h1]
  rw [eT] at hgroup hpad hcan hmade ⊢
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1
    (Tw.K2.rowsCan_some (g := t.st.oracles.size) hcan)
  have hrows : D.rows = l := by
    rw [hmade]
    show (switchRows _ _ _ _ _ _ _).getD [] = l
    rw [hl]
    rfl
  obtain ⟨W, hW, -⟩ := switchRows_eq _ rows _ _ _ _ l ff.kept ff.prog.masks
    (fun W1 h1 => by
      have hk := (switchFrame_fields _ rows _ _ W1 h1).2.2.2.2.2.2.2.2.1
      rw [ff.prog.noKept] at hk
      exact List.length_eq_zero_iff.1 hk) hl
  obtain ⟨hF, hC, hZ, hSeat⟩ := seat_stJ hf D gp (othersOf last n) t.st rows n.code n.maskCode
    ff.prog hpad hm hrun hsmall W hW
  have eZl : W.zk.ell = s.Z.l := congrArg (·.l) hZ
  have eCl : W.code.ell = s.C.l := congrArg (·.l) hC
  have eCa : W.code.logN = s.C.a := congrArg (·.a) hC
  have h := made_add (joined_group _ gp _ false D.G hgroup) hW hF hSeat ff.kept ff.prog.masks
    (ff.d0.trans eZl.symm) (ff.d1.trans eZl.symm)
    (by
      show Means.CFits (ceilLog2 W.code.ell) rows.c
      rw [eCl]
      exact hc) hp
    (fun x hx' => by
      rw [eCa]
      exact hx x (by simpa [swPos, Positions.ofDraws] using hx')) hl
  rw [hrows]
  have h' : l.foldlM (fun S r => Tw.L9.addRowS S gp r)
      (D.stJ (switchTargetStage n.code n.maskCode (s'.h + s'.g) s'.h 1) gp (othersOf last n)
        t.st) = .ok _ := h
  rw [h']
  rfl

end Johnson.Prover.Link
