-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSwitchPay.lean: small payers for the clauses of `SwitchFacts`
(Johnson/Prover/Link/FormSwitch.lean): each clause of the description's own tests at a code switch
of the proximity test, from public facts on the codes, the statement and the old rows.

Main names (namespace `Johnson.Prover.Link`).
  `pad_some`, `pad_one`   at a stage's target with one answer the pad's places can be made where a
      mask row's message has an entry; and they are one place
  `form_some`   the sample row's left side can be made where the pad's places can
  `seed_of`   of one element more than the point has coordinates, one stands behind the point
  `admit_of`   the clauses of the admitting, at the new message
  `shut_groups`, `shut_at`   the statement behind the sending, with the new message's ledger closed:
      its groups are the old ones; the new message is there, sampled, with the target's shape
  `join_of`   the new message joins an empty group of its two codes that is in no test
  `draws_listed`, `can_of`   each draw is among the positions; the eight clauses of `rowsCan`
  `recv_of`   the clauses of the receiving, at a switch's announcements
  `guard_of`   the public test in front of the sending, from `CsFit` and `CsProg`
  `factor_of`   the drawn factor's words are not all 0, from the format's test on never-0 draws

Limits. Every premise is asked. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchSeat
import Johnson.Prover.Send.Factors
import Johnson.Top.H0.Tw.K2.TargetMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

/-- The pad's places can be made. -/
theorem pad_some (codes : Codes) (nc nz k h : ℕ) (hz : 1 ≤ (codes.mask.getD nz default).ell) :
    ∃ places, Send.pad codes (switchTargetStage nc nz k h 1).shape = some places := by
  have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
  unfold Send.pad Send.cube switchTargetStage
  simp only [hpos, decide_true, if_true, Bool.true_or, Nat.one_mul]
  rw [if_neg (by omega)]
  exact ⟨_, rfl⟩

/-- They are one place. -/
theorem pad_one (codes : Codes) (nc nz k h : ℕ) (places : List PadPlace)
    (hp : Send.pad codes (switchTargetStage nc nz k h 1).shape = some places) :
    places.length = 1 := by
  have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
  unfold Send.pad Send.cube switchTargetStage at hp
  simp only [hpos, decide_true, if_true, Bool.true_or, Nat.one_mul] at hp
  split at hp
  · cases hp
  · obtain rfl := Option.some.inj hp
    rfl

/-- The sample row's left side can be made. -/
theorem form_some (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (i : ℕ)
    (places : List PadPlace) (hp : Send.pad codes s = some places) :
    ∃ row, Send.form codes s o seed i = some row := by
  unfold Send.form
  rw [hp]
  exact ⟨_, rfl⟩

/-- One element stands behind the point. -/
theorem seed_of {α : Type} (l : List α) (bits : ℕ) (h : l.length = bits + 1) :
    ∃ b, l.drop bits = [b] := by
  have h1 : (l.drop bits).length = 1 := by
    rw [List.length_drop, h]
    omega
  exact List.length_eq_one_iff.1 h1

/-- The clauses of the admitting, at the new message. -/
theorem admit_of (S : Statement) (N : OracleNotice) (others : Array OracleNotice) (r : Row)
    (places : List PadPlace) (hp : Send.pad S.codes N.shape = some places)
    (h1 : N.shape.answers = 1) :
    Ground.ok (Ground.admitL (stSent S (#[N] ++ others)) S.oracles.size #[r]) = true := by
  have hp' : Own.padMade (stSent S (#[N] ++ others)).codes N.shape = some places := hp
  simp [Ground.ok, Ground.admitL, sent_first, Ground.has, hp', h1]

/-- The groups behind the sending are the old ones. -/
theorem shut_groups (D : Taken) (T : SwitchTarget) (others : Array OracleNotice) (S : Statement) :
    (ledgerShut (D.stA T others S) T S.oracles.size).groups = S.groups := by
  rw [ledgerShut_groups]
  rfl

/-- The new message behind the sending: there, sampled, with the target's shape. -/
theorem shut_at (D : Taken) (T : SwitchTarget) (others : Array OracleNotice) (S : Statement) :
    ∃ x, (ledgerShut (D.stA T others S) T S.oracles.size).oracles[S.oracles.size]? = some x ∧
      x.shape = T.shape ∧ x.sampled = true := by
  have hx := sent_first S ⟨T.shape, T.leafClass⟩ others
  unfold ledgerShut Taken.stA admitted
  split
  · unfold closeLedgers
    simp only [List.foldl_cons, List.foldl_nil, Array.getElem?_modify, if_true]
    unfold OnBytes.Slice.sentOf
    rw [hx]
    exact ⟨_, rfl, rfl, rfl⟩
  · simp only [Array.getElem?_modify, if_true]
    unfold OnBytes.Slice.sentOf
    rw [hx]
    exact ⟨_, rfl, rfl, rfl⟩

/-- The new message joins an empty group of its two codes that is in no test. -/
theorem join_of (D : Taken) (T : SwitchTarget) (gp : ℕ) (others : Array OracleNotice)
    (S : Statement) (hG : S.groups[gp]? = some D.G) (hm : D.G.members = #[])
    (hrun : D.G.inRun = false) (hc : T.shape.code = D.G.code)
    (hz : T.shape.maskCode = D.G.maskCode) :
    (Tw.L9.joinS (ledgerShut (D.stA T others S) T S.oracles.size) gp S.oracles.size
      false).toOption.isSome = true := by
  obtain ⟨x, hx, hs, hsm⟩ := shut_at D T others S
  have hG' : (ledgerShut (D.stA T others S) T S.oracles.size).groups[gp]? = some D.G := by
    rw [shut_groups]
    exact hG
  have h := (joinS_iff (ledgerShut (D.stA T others S) T S.oracles.size) _ gp S.oracles.size
    false).2 ⟨by
      simp [Ground.ok, Ground.joinL, Ground.has, hG', hx, hs, hsm, hrun, hm, hc, hz], D.G, hG',
        rfl⟩
  rw [h]
  rfl

/-- Each draw is among the positions. -/
theorem draws_listed (a : ℕ) (poss : List ℕ) :
    ((Positions.ofDraws a poss).draws.toList.all fun x =>
      ((Positions.ofDraws a poss).all.idxOf? x).isSome) = true := by
  rw [List.all_eq_true]
  intro x hx
  have hx' : x ∈ poss := by simpa [Positions.ofDraws] using hx
  have hm : x ∈ (Positions.ofDraws a poss).all := by
    show x ∈ (listOfT poss).toArray
    rw [listOfT_eq]
    exact List.mem_toArray.2 ((Fmt.listOf_mem _ x).2 hx')
  cases h : (Positions.ofDraws a poss).all.idxOf? x with
  | some _ => rfl
  | none => exact absurd hm (Array.idxOf?_eq_none_iff.1 h)

/-- The eight clauses of `rowsCan`. -/
theorem can_of {s s' : Sg} (S : Statement) (old : SingleRows) (nc nz k h a : ℕ)
    (P : CsProg s s' S.codes old nc nz) (hk : old.kept = #[]) (poss : List ℕ) (y : Array E)
    (hy : y.size = (Positions.ofDraws a poss).all.size * old.rows) :
    Tw.K2.rowsCan S old (switchTargetStage nc nz k h 1) #[] (Positions.ofDraws a poss) y =
      true := by
  have lt_of {α : Type} {A : Array α} {i : ℕ} {β : Type} {f : α → β} {b : β}
      (h : (A[i]?).map f = some b) : i < A.size := by
    rcases Nat.lt_or_ge i A.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at h
      cases h
  have h2 := lt_of P.code
  have h3 := lt_of P.zk
  have h4 : (switchTargetStage nc nz k h 1).shape.code < S.codes.base.size := lt_of P.code'
  simp only [Tw.K2.rowsCan, Tw.K2.rowsCanL, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨hy, h2, h3, h4, ?_, ?_, ?_, draws_listed a poss⟩
  · rw [P.noKept]
  · rw [hk]
    rfl
  · rw [P.noKept]
    rfl

/-- The drawn factor's words are not all 0. -/
theorem factor_of (dS : Fmt.DeclaredRound) (rS : Fmt.RoundView) (bits : ℕ) (beta : E)
    (hn : dS.entry.name = "SEND seed") (hz : dS.entry.drawNZ = 1)
    (hE : dS.entry.drawE = bits + 1) (hl : rS.drawn.elems.length = bits + 1)
    (hnz : drawsMarkedNonzeroHaveNonzeroWords dS rS = true)
    (hb : (rS.drawn.elems.map E.ofTriple).drop bits = [beta]) : Own.allZero beta = false := by
  have hkind : Fmt.kindOf dS.entry.name = some .seeds := by
    rw [hn]
    rfl
  unfold drawsMarkedNonzeroHaveNonzeroWords at hnz
  rw [hkind] at hnz
  have hds : Fmt.dsElems dS.entry .seeds =
      List.replicate bits Fmt.Draw.elem ++ [Fmt.Draw.elemNZ] := by
    unfold Fmt.dsElems
    rw [if_pos rfl, hz, hE]
    simp [Fmt.dsSeeds, Nat.mod_one]
  obtain ⟨x, hx⟩ := seed_of rS.drawn.elems bits hl
  have hsplit : rS.drawn.elems = rS.drawn.elems.take bits ++ [x] := by
    rw [← hx, List.take_append_drop]
  have hall : ((List.replicate bits Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]).zip
      (rS.drawn.elems.take bits ++ [x])).all
      (fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true := by
    rw [← hsplit, ← hds]
    exact hnz
  rw [List.zip_append (by rw [List.length_replicate, List.length_take, hl]; omega),
    List.all_append, Bool.and_eq_true] at hall
  have hx0 : x ≠ (0, 0, 0) := by simpa using hall.2
  have hbx : beta = E.ofTriple x := by
    rw [← List.map_drop, hx] at hb
    exact (List.head_eq_of_cons_eq hb).symm
  rw [hbx, ← Own.allZero_agrees]
  exact Johnson.Prover.Send.isZeroE_ofTriple x hx0

/-- An entry that is read is in the list. -/
theorem lt_of_map_some {α β : Type} {A : Array α} {i : ℕ} {f : α → β} {b : β}
    (h : (A[i]?).map f = some b) : i < A.size := by
  rcases Nat.lt_or_ge i A.size with h1 | h1
  · exact h1
  · rw [Array.getElem?_eq_none h1] at h
    cases h

/-- The entry itself. -/
theorem getD_of_map_some {A : Array OnBytes.Code} {i : ℕ} {C : Fmt.M1.Code}
    (h : (A[i]?).map codeOf = some C) : codeOf (A.getD i default) = C := by
  cases hz : A[i]? with
  | none => rw [hz] at h; cases h
  | some z =>
    rw [hz] at h
    rw [Array.getD_eq_getD_getElem?, hz]
    exact Option.some.inj h

/-- The clauses of the receiving, at a switch's announcements. -/
theorem recv_of {p : P12} {n : IoppStage} {last : Bool} (S : Statement) (B : TreeBook)
    (hc : n.code < S.codes.base.size) (hz : n.maskCode < S.codes.mask.size)
    (htrees : Own.treesCan S.codes (swNotices p n last) = true)
    (hstep : S.oracles.size = B.place.size) :
    Ground.ok (Ground.recvL S B (swNotices p n last)) = true := by
  have hshapes : ((swNotices p n last).all fun x => Own.sentShapeFits S.codes x.shape) = true := by
    rw [swNotices_eq, Array.all_eq_true_iff_forall_mem]
    intro x hx
    rcases Array.mem_append.1 hx with hx | hx
    · obtain rfl := Array.mem_singleton.1 hx
      have h0 : 0 < 2 ^ n.k + 2 ^ n.h := Nat.add_pos_left (Nat.two_pow_pos _) _
      simp [Own.sentShapeFits, swTarget, switchTargetStage, hc, hz, h0]
    · cases last
      · obtain rfl := Array.mem_singleton.1 hx
        have h0 : 0 < 2 ^ n.h := Nat.two_pow_pos _
        simp [Own.sentShapeFits, foldMaskNotice, ioppFoldShape, hz, h0]
      · obtain rfl := Array.mem_singleton.1 hx
        simp [Own.sentShapeFits, baseMaskNotice, hc, hz]
  simp only [Ground.ok, Ground.recvL, Ground.sentL, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hshapes, htrees⟩, hstep⟩

/-- **The public test in front of the sending.** -/
theorem guard_of {s s' : Sg} (hf : CsFit s s') (S : Statement) (old : SingleRows) (nc nz : ℕ)
    (P : CsProg s s' S.codes old nc nz) :
    Tw.L9.switchGuard S old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) = true := by
  have eC := getD_of_map_some P.code
  have eC' := getD_of_map_some P.code'
  have eZ' := getD_of_map_some P.zk'
  have lC : (S.codes.base.getD old.code default).ell = s.C.l := congrArg (·.l) eC
  have lC' : (S.codes.base.getD nc default).ell = s'.C.l := congrArg (·.l) eC'
  have lZ' : (S.codes.mask.getD nz default).ell = s'.Z.l := congrArg (·.l) eZ'
  have hmask := hf.mask
  have hmain := hf.main
  have hpos' : 1 ≤ s'.C.l := by
    rw [hf.powC]
    exact Nat.one_le_two_pow
  have hZpos : 1 ≤ s'.Z.l := by
    rcases Nat.eq_zero_or_pos s'.Z.l with h0 | h0
    · rw [h0] at hmask
      omega
    · exact h0
  obtain ⟨cd, hcd⟩ : ∃ cd, S.codes.base[old.code]? = some cd := by
    cases h : S.codes.base[old.code]? with
    | none => have := P.code; rw [h] at this; cases this
    | some c => exact ⟨c, rfl⟩
  obtain ⟨zk, hzk⟩ : ∃ zk, S.codes.mask[old.maskCode]? = some zk := by
    cases h : S.codes.mask[old.maskCode]? with
    | none => have := P.zk; rw [h] at this; cases this
    | some c => exact ⟨c, rfl⟩
  have ecd : codeOf cd = s.C := by
    have := P.code
    rw [hcd] at this
    exact Option.some.inj this
  have ezk : codeOf zk = s.Z := by
    have := P.zk
    rw [hzk] at this
    exact Option.some.inj this
  obtain ⟨places, hpl⟩ := pad_some S.codes nc nz (s'.h + s'.g) s'.h (by rw [lZ']; exact hZpos)
  have hpow : s.C.l = 2 ^ (s'.h + s'.g + Fmt.M1.lg s'.C.l) := by
    rw [pow_add (2 : ℕ) (s'.h + s'.g), ← hf.powC]
    exact hmain.symm
  unfold Tw.L9.switchGuard
  rw [Tw.K2.targetOk_means]
  refine
    { masks := P.masks, oldCode := lt_of_map_some P.code, oldMaskCode := lt_of_map_some P.zk
      code := lt_of_map_some P.code', rows := Nat.two_pow_pos _, degree := rfl
      sampled := Nat.le_refl 1, pad := ?_, mainPart := rfl, power := ?_
      mainAligned := Nat.zero_mod _, restAligned := Nat.zero_mod _
      fill := ⟨lt_of_map_some P.zk', rfl, rfl, rfl, rfl⟩, mainSmall := ?_, mainRoom := ?_
      restRoom := ?_, keptCount := ?_, keptShapes := ?_ }
  · rw [Tw.K2.padFits_iff]
    have h0 : 0 < (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape.maskRows :=
      Nat.two_pow_pos _
    rw [if_pos (Or.inl h0), if_pos h0]
    show 1 * 1 ≤ (S.codes.mask.getD nz default).ell
    rw [lZ']
    omega
  · rw [lC, hpow, ceilLog2_two_pow]
    exact ⟨(Nat.two_pow_pos _).ne', rfl⟩
  · show 2 ^ (s'.h + s'.g) ≤ _
    rw [lC, ← hmain]
    exact Nat.le_mul_of_pos_right _ hpos'
  · show _ ≤ (S.codes.base.getD nc default).ell * 2 ^ (s'.h + s'.g)
    rw [lC, lC', ← hmain, Nat.mul_comm]
  · rw [switchParts_eq S old cd zk hcd hzk P.noKept P.masks P.keptRows]
    have key : ∀ f : PadPlace → Option ℕ, (List.filterMap f (padPlaces S.codes
        (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape)).length ≤ 1 := fun f => by
      refine (List.length_filterMap_le _ _).trans ?_
      unfold padPlaces
      rw [hpl]
      exact (pad_one S.codes nc nz _ _ places hpl).le
    have e1 : zk.ell = s.Z.l := congrArg (·.l) ezk
    have e2 : zk.r = s.Z.r := congrArg (·.r) ezk
    have e3 : cd.r = s.C.r := congrArg (·.r) ecd
    refine le_trans (?_ : 2 * zk.ell + cd.r + 0 * cd.r + 2 * zk.r ≤
      (S.codes.mask.getD nz default).ell * 2 ^ s'.h - 1) (Nat.sub_le_sub_left (key _) _)
    rw [lZ', e1, e2, e3, Nat.mul_comm s'.Z.l]
    omega
  · rw [P.noKept]
    rfl
  · intro q hq
    rw [P.noKept, show (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).kept = #[] from rfl] at hq
    exact absurd hq (by simp)

end Johnson.Prover.Link
