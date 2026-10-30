-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Tower.lean: WHAT A YES OF THE PROXIMITY TEST LEAVES OF THE STATEMENT, FOURTH PART: THE LATER STAGES' MESSAGES AND GROUPS, ONE BY ONE, AND THE ELDER MESSAGES TO THE LETTER. Statements with proofs.
OBJECT. (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide. USER. The book-keeping's step across the key file's proximity tests on the shared and the last chain (shape₂ | shape₃: their clause towerIs, and the clauses on the members' and the first mask's marks): Johnson/RunOne/Law/K12Fwd29 | 210 | 32.lean.
LETTERS. p t0 tE rs gs: free. Premises: early · answers = 1 (as the kind's files' laws on what a yes leaves) · the yes · the test's state names the first fold's mask (t0.mask = some m), or names none (the second arm).
WHY. OutK2 (Johnson/Desc/K12/Law/OutK2.lean) says of a group that has come: marked, no open row; of the second message of a switch: spent. The tables ask more: the group's members are just the stage's target; the target is sampled, with one sample row, unspent; the mask has no sample and no sample row; a member of the group under test keeps all but its ledger's mark; the first mask turns in its mark "spent" alone. All of it lies in the kind's files' closed forms (foldJ_form · Did.st · BaseSt): here it is read off them.

  mk: a message's three marks: sampled · the sample rows · spent as a mask. closeLedgers_mk · ledgerShut_mk · joined_mk: these effects leave them.
  did_target · did_rider · did_group: behind a switch and its batching: the new target, the message that rides with it, the new group.
  Tgt · Rdr · Grp: what the tables ask of the three. stage_tower: a stage but the last. stages_tower: by recursion along the stages.
  Tower · k12_tower: the top.
  stage_tower_own · TowerOwn · k12_tower_own: the arm in which the first fold sends its own mask.
Limits. A block that says no to all meets every statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Law.SwClaim
import Johnson.Desc.K12.Law.FitsLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Tower
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open H2K.FoldLaw (bind_ok got_ok)

/-- A message's three marks. -/
def mk (x : OnBytes.Oracle) : Bool × Array Row × Bool := (x.sampled, x.sampleRows, x.spentAsMask)

/-- A change of one message that leaves its marks leaves every message's marks. -/
theorem modify_mk (A : Array OnBytes.Oracle) (a o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle) (hf : ∀ x, mk (f x) = mk x) :
    ((A.modify a f)[o]?).map mk = (A[o]?).map mk := by
  rw [Array.getElem?_modify]
  split
  · cases A[o]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · rfl

theorem closeLedgers_mk : ∀ (l : List ℕ) (S : Statement) (o : ℕ), ((closeLedgers S l).oracles[o]?).map mk = (S.oracles[o]?).map mk
  | [], _, _ => rfl
  | a :: l, S, o => by
    show ((closeLedgers _ l).oracles[o]?).map mk = _
    rw [closeLedgers_mk l]
    exact modify_mk _ _ _ _ fun _ => rfl

theorem ledgerShut_mk (S : Statement) (T : SwitchTarget) (g o : ℕ) : ((ledgerShut S T g).oracles[o]?).map mk = (S.oracles[o]?).map mk := by
  unfold ledgerShut
  split
  · exact closeLedgers_mk _ _ _
  · rfl

theorem joined_mk (S : Statement) (g a : ℕ) (k : Bool) (G : Group) (o : ℕ) : ((withMessageInGroup S g a k G).oracles[o]?).map mk = (S.oracles[o]?).map mk :=
  modify_mk _ _ _ _ fun _ => rfl

theorem begun_mk (S : Statement) (g : ℕ) (G : Group) (o : ℕ) : ((begun S g G).oracles[o]?).map mk = (S.oracles[o]?).map mk :=
  closeLedgers_mk _ _ _

section
variable {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : ℕ}
  {others : Array OracleNotice} {S : Statement} {Bk : TreeBook} {roots : ℕ} {S' : Statement}
  {Bk' : TreeBook} {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- Behind a switch and its batching every message's marks are those behind the sending. -/
theorem did_mk (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (o : ℕ) :
    (S'.oracles[o]?).map mk = ((D.stA T others S).oracles[o]?).map mk := by
  rw [h.st, begun_mk]
  unfold Taken.stR Taken.stJ
  rw [(withRows_oracles gp D.rows _).1, joined_mk, ledgerShut_mk]

/-- The new target: sampled, one sample row, unspent. -/
theorem did_target (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    (S'.oracles[S.oracles.size]?).map mk = some (true, #[D.sample], false) := by
  rw [did_mk h]
  unfold Taken.stA
  have e : (stSent S (Slice.sentOf T others)).oracles[S.oracles.size]? = some { shape := T.shape } := by
    have e0 := stSent_new S (Slice.sentOf T others) 0
    rw [Nat.add_zero] at e0
    rw [e0]
    simp [Slice.sentOf]
  rw [admitted_same _ _ _ _ _ _ e]
  rfl

/-- The message that rides with it: no sample, no sample row, unspent. -/
theorem did_rider (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (n : OracleNotice) (hn : others[0]? = some n) :
    (S'.oracles[S.oracles.size + 1]?).map mk = some (false, #[], false) := by
  rw [did_mk h]
  unfold Taken.stA
  rw [admitted_other _ _ _ _ _ _ (by omega), stSent_new S (Slice.sentOf T others) 1]
  have e : (Slice.sentOf T others)[1]? = some n := by
    unfold Slice.sentOf
    rw [Array.getElem?_append_right (by simp)]
    simpa using hn
  rw [e]
  rfl

/-- The new group, where it had no member: just the target; marked; no open row. -/
theorem did_group (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (hG : D.G.members = #[]) :
    ∃ G', S'.groups[gp]? = some G' ∧ G'.members.toList = [S.oracles.size] ∧ G'.rows = #[] ∧ G'.inRun = true := by
  have hmem : (D.grown S).members.toList = [S.oracles.size] := by
    unfold Taken.grown
    rw [hG]
    simp [Array.insertIdxIfInBounds]
  rw [h.st, begun_group _ _ _ h.group_stR]
  exact ⟨_, rfl, hmem, rfl, rfl⟩

end

/-- What the tables ask of a later stage's target. -/
def Tgt (S : Statement) (o : ℕ) : Prop := ∃ x, S.oracles[o]? = some x ∧ x.sampled = true ∧ x.sampleRows.size = 1 ∧ x.spentAsMask = false
/-- Of a mask: sp: whether it is spent. -/
def Rdr (S : Statement) (o : ℕ) (sp : Bool) : Prop := ∃ x, S.oracles[o]? = some x ∧ x.sampled = false ∧ x.sampleRows = #[] ∧ x.spentAsMask = sp
/-- Of a later stage's group. -/
def Grp (S : Statement) (g o : ℕ) : Prop := ∃ G, S.groups[g]? = some G ∧ G.members.toList = [o] ∧ G.rows = #[] ∧ G.inRun = true

theorem of_mk {A : Array OnBytes.Oracle} {o : ℕ} {a : Bool} {r : Array Row} {c : Bool} (h : (A[o]?).map mk = some (a, r, c)) :
    ∃ x, A[o]? = some x ∧ x.sampled = a ∧ x.sampleRows = r ∧ x.spentAsMask = c := by
  cases hx : A[o]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    have e : mk x = (a, r, c) := Option.some.inj h
    unfold mk at e
    exact ⟨x, rfl, congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩

/-- The mark "spent". -/
abbrev spent (x : OnBytes.Oracle) : OnBytes.Oracle := { x with spentAsMask := true }

/-- **A stage but the last**, where the record names its mask. -/
theorem stage_tower (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ) (cur nxt : Fmt.M1.Stage) (last : Bool)
    (cutF cutS : List Fmt.DeclaredRound) (t t1 t2 t3 : T12) (rsF rsS : List Fmt.RoundView) (gsF gsS : Gs) (hlen : rsS.length ≤ 2)
    (f1 : (foldJ p j cur cutF).decide t rsF gsF = .ok t1) (f2 : (switchJ p j cur nxt last cutS).decide t1 rsS gsS = .ok t2)
    (f3 : (behindJ p (j + 1) nxt cutS).decide t2 [] [] = .ok t3) (m : ℕ) (hm : t.mask = some m) :
    m < t.st.oracles.size ∧ t3.st.oracles[m]? = (t.st.oracles[m]?).map spent ∧ Tgt t3.st t.st.oracles.size ∧
      Rdr t3.st (t.st.oracles.size + 1) false ∧ Grp t3.st t.st.groups.size t.st.oracles.size := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ := foldJ_form p j cur cutF t t1 rsF gsF f1
  obtain ⟨rows', gp, nx, out, row', L', th, D, hp, hd, _⟩ := switch_did p he ha j cur nxt last cutS _ t2 t3 rsS gsS hlen f2 f3
  obtain ⟨rfl, rfl⟩ : rows = rows' ∧ d'.st.groups.size = gp := by
    cases hp
    exact ⟨rfl, rfl⟩
  have hthere := spendP_there hsp
  have hd' := spendP_form hsp
  rcases hcase with ⟨hmk, rfl⟩ | ⟨hn, _⟩
  swap
  · rw [hm] at hn
    cases hn
  obtain rfl : id = m := Option.some.inj (hmk.symm.trans hm)
  have hG : D.G.members = #[] := by
    have hg := hd.group
    rw [ledgerShut_groups] at hg
    have hg' : (d'.st.groups.push { code := n.1, maskCode := n.2 })[d'.st.groups.size]? = some D.G := hg
    rw [Array.getElem?_push_size] at hg'
    rw [← Option.some.inj hg']
  have hosz : d'.st.oracles.size = t.st.oracles.size := by
    rw [hd']
    show (t.st.oracles.modify id _).size = _
    rw [Array.size_modify]
  have hgr : d'.st.groups.size = t.st.groups.size := by rw [hd']
  have hS : (Ground.withGroup d'.st n.1 n.2).oracles.size = t.st.oracles.size := hosz
  obtain ⟨_, c2⟩ := did_oracles hd hG
  have b := did_target hd
  have r := did_rider hd ((othersOf last nx)[0]'(by rw [othersOf_size]; omega)) (Array.getElem?_eq_getElem _)
  obtain ⟨G', g1, g2, g3, g4⟩ := did_group hd hG
  rw [hS] at b r g2
  rw [hgr] at g1
  refine ⟨hthere, ?_, ?_, ?_, ⟨G', g1, g2, g3, g4⟩⟩
  · rw [c2 id (by rw [hS]; exact hthere)]
    show d'.st.oracles[id]? = _
    rw [hd']
    show (t.st.oracles.modify id _)[id]? = _
    rw [Array.getElem?_modify, if_pos rfl]
  · obtain ⟨x, hx, x1, x2, x3⟩ := of_mk b
    exact ⟨x, hx, x1, by rw [x2]; rfl, x3⟩
  · exact of_mk r

/-- **By recursion along the stages.** -/
theorem stages_tower (p : P12) (he : p.early = true) (ha : p.answers = 1) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom guardedProximityTestParts p j cur rest l : Blk').decide t rs gs = .ok tE → ∀ m, t.mask = some m →
      m < t.st.oracles.size ∧ tE.st.oracles[m]? = (t.st.oracles[m]?).map spent ∧
        ∀ i, i < rest.length → Tgt tE.st (t.st.oracles.size + 2 * i) ∧ Rdr tE.st (t.st.oracles.size + 2 * i + 1) true ∧
          Grp tE.st (t.st.groups.size + i) (t.st.oracles.size + 2 * i)
  | [], j, cur, l, t, tE, rs, gs, h, m, hm => by
    rw [stagesFrom_last] at h
    obtain ⟨star, h1, h2, h3⟩ := baseJ5_st p _ _ _ t tE rs gs (ranged_ok _ _ _ _ _ _ h).1
    obtain rfl : star = m := Option.some.inj (h1.symm.trans hm)
    refine ⟨h2, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    rw [h3]
    show (t.st.oracles.modify star _)[star]? = _
    rw [Array.getElem?_modify, if_pos rfl]
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h, m, hm => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok guardedProximityTestParts p j cur nxt rest l t tE rs gs).1 h
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur l : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have f1' := (like_P5 p).fold _ _ _ _ _ _ _ f1
    have f2' := (like_P5 p).switch _ _ _ _ _ _ _ _ _ f2
    have f3' := (like_P5 p).behind _ _ _ _ _ f3
    obtain ⟨a0, a1, a2, a3, a4⟩ := stage_tower p he ha j cur nxt rest.isEmpty _ _ t t1 t2 t3 _ _ _ _ hlen f1' f2' f3' m hm
    obtain ⟨s1, _, _, s4, _, _, _, s8⟩ := stage_st p he ha j cur nxt rest.isEmpty _ _ t t1 t2 t3 _ _ _ _ hlen f1' f2' f3'
    have hown : own t = 0 := by simp [own, hm]
    rw [hown, Nat.add_zero] at s4 s8
    have hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs),
        (guardedProximityTestParts.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t' :=
      fun j cur cut t t' rs gs h => baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1
    have K := stages_st guardedProximityTestParts p (like_P5 p) hB he ha rest (j + 1) nxt _ t3 tE _ _ f5
    obtain ⟨_, i1, i2⟩ := stages_tower p he ha rest (j + 1) nxt _ t3 tE _ _ f5 _ s8
    have old : ∀ o, o < t.st.oracles.size + 1 → tE.st.oracles[o]? = t3.st.oracles[o]? := fun o ho =>
      K.oraclesOld o (by rw [s4]; omega) (by
        rw [s8]
        intro e
        have := Option.some.inj e
        omega)
    refine ⟨a0, by rw [old m (by omega)]; exact a1, fun i hi => ?_⟩
    cases i with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨x, hx, hx'⟩ := a2
        exact ⟨x, by rw [Nat.mul_zero, Nat.add_zero, old _ (by omega)]; exact hx, hx'⟩
      · obtain ⟨x, hx, x1, x2, _⟩ := a3
        refine ⟨spent x, ?_, x1, x2, rfl⟩
        rw [Nat.mul_zero, Nat.add_zero, i1, hx]
        rfl
      · obtain ⟨G, hG, hG'⟩ := a4
        exact ⟨G, by rw [Nat.add_zero, K.groupsOld _ (by rw [s1]; omega)]; exact hG, by rw [Nat.mul_zero, Nat.add_zero]; exact hG'⟩
    | succ i =>
      have hi' : i < rest.length := by
        rw [List.length_cons] at hi
        omega
      have k := i2 i hi'
      rw [s4, s1] at k
      have e1 : t.st.oracles.size + 2 + 2 * i = t.st.oracles.size + 2 * (i + 1) := by omega
      have e2 : t.st.groups.size + 1 + i = t.st.groups.size + (i + 1) := by omega
      rw [e1, e2] at k
      exact k

/-- What a yes of the test leaves, fourth part. n: the switches. G: the group under test as it stood. m: the first fold's mask. -/
structure Tower (t0 tE : T12) (n : ℕ) (G : Group) (m : ℕ) : Prop where
  /-- the group under test was there -/
  was : t0.st.groups[t0.g]? = some G
  /-- an elder message but the first mask: as the beginning of the test leaves it (its ledger's mark alone may turn) -/
  old : ∀ o, o < t0.st.oracles.size → o ≠ m → tE.st.oracles[o]? = (begun t0.st t0.g G).oracles[o]?
  /-- the first mask: and spent -/
  there : m < t0.st.oracles.size
  mask : tE.st.oracles[m]? = ((begun t0.st t0.g G).oracles[m]?).map spent
  /-- each later stage's target, mask and group -/
  later : ∀ i, i < n → Tgt tE.st (t0.st.oracles.size + 2 * i) ∧ Rdr tE.st (t0.st.oracles.size + 2 * i + 1) true ∧
    Grp tE.st (t0.st.groups.size + i) (t0.st.oracles.size + 2 * i)

/-- **A yes of the test's decision leaves Tower.** -/
theorem k12_tower (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (m : ℕ) (hm : t0.mask = some m) :
    ∃ G, Tower t0 tE (p.nums.stages.length - 1) G m := by
  obtain ⟨first, rest, ds, tF, t1, hs, _, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)
  obtain ⟨G, hG, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (guardedProximityTestParts.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t' :=
    fun j cur cut t t' rs gs h => baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1
  have K := stages_st guardedProximityTestParts p (like_P5 p) hB he ha rest 0 first _ _ tE _ _ hst
  obtain ⟨k0, k1, k2⟩ := stages_tower p he ha rest 0 first _ _ tE _ _ hst m hm
  have osz : (begun tF.st tF.g G).oracles.size = tF.st.oracles.size := H2K.Out.closeLedgers_size _ _
  have gsz : (begun tF.st tF.g G).groups.size = tF.st.groups.size := by
    show ((closeLedgers tF.st _).groups.modify _ _).size = _
    rw [Array.size_modify, H2K.Out.closeLedgers_groups]
  dsimp only at k0 k1 k2
  rw [osz] at k0 k2
  rw [gsz] at k2
  have hn : p.nums.stages.length - 1 = rest.length := by
    rw [hs]
    rfl
  refine ⟨G, hG, fun o ho hne => ?_, k0, k1, by rw [hn]; exact k2⟩
  exact K.oraclesOld o (by rw [osz]; exact ho) (fun e => hne (Option.some.inj (e.symm.trans hm) ▸ rfl))

/-! ## The arm in which the first fold sends its own mask -/

/-- **The first stage, where the fold sends its own mask.** -/
theorem stage_tower_own (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ) (cur nxt : Fmt.M1.Stage) (last : Bool)
    (cutF cutS : List Fmt.DeclaredRound) (t t1 t2 t3 : T12) (rsF rsS : List Fmt.RoundView) (gsF gsS : Gs) (hlen : rsS.length ≤ 2)
    (f1 : (foldJ p j cur cutF).decide t rsF gsF = .ok t1) (f2 : (switchJ p j cur nxt last cutS).decide t1 rsS gsS = .ok t2)
    (f3 : (behindJ p (j + 1) nxt cutS).decide t2 [] [] = .ok t3) (hm : t.mask = none) :
    Rdr t3.st t.st.oracles.size true ∧ Tgt t3.st (t.st.oracles.size + 1) ∧ Rdr t3.st (t.st.oracles.size + 1 + 1) false ∧
      Grp t3.st t.st.groups.size (t.st.oracles.size + 1) := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ := foldJ_form p j cur cutF t t1 rsF gsF f1
  obtain ⟨rows', gp, nx, out, row', L', th, D, hp, hd, _⟩ := switch_did p he ha j cur nxt last cutS _ t2 t3 rsS gsS hlen f2 f3
  obtain ⟨rfl, rfl⟩ : rows = rows' ∧ d'.st.groups.size = gp := by
    cases hp
    exact ⟨rfl, rfl⟩
  have hd' := spendP_form hsp
  rcases hcase with ⟨hmk, _⟩ | ⟨_, ids, hr, hi⟩
  · rw [hm] at hmk
    cases hmk
  obtain ⟨lay, _, _, rfl, rfl⟩ := recvP_ok hr
  have hid : id = t.st.oracles.size := by
    simp at hi
    omega
  subst hid
  have hG : D.G.members = #[] := by
    have hg := hd.group
    rw [ledgerShut_groups] at hg
    have hg' : (d'.st.groups.push { code := n.1, maskCode := n.2 })[d'.st.groups.size]? = some D.G := hg
    rw [Array.getElem?_push_size] at hg'
    rw [← Option.some.inj hg']
  have hosz : d'.st.oracles.size = t.st.oracles.size + 1 := by
    rw [hd']
    show ((stSent t.st #[foldMaskNotice (ioppFoldShape c L)]).oracles.modify _ _).size = _
    rw [Array.size_modify]
    simp [stSent]
  have hgr : d'.st.groups.size = t.st.groups.size := by rw [hd']; rfl
  have hS : (Ground.withGroup d'.st n.1 n.2).oracles.size = t.st.oracles.size + 1 := hosz
  obtain ⟨_, c2⟩ := did_oracles hd hG
  have b := did_target hd
  have r := did_rider hd ((othersOf last nx)[0]'(by rw [othersOf_size]; omega)) (Array.getElem?_eq_getElem _)
  obtain ⟨G', g1, g2, g3, g4⟩ := did_group hd hG
  rw [hS] at b r g2
  rw [hgr] at g1
  refine ⟨?_, ?_, of_mk r, ⟨G', g1, g2, g3, g4⟩⟩
  · refine ⟨spent { shape := (foldMaskNotice (ioppFoldShape c L)).shape }, ?_, rfl, rfl, rfl⟩
    rw [c2 t.st.oracles.size (by rw [hS]; omega)]
    show d'.st.oracles[t.st.oracles.size]? = _
    rw [hd']
    show ((stSent t.st #[foldMaskNotice (ioppFoldShape c L)]).oracles.modify _ _)[t.st.oracles.size]? = _
    rw [Array.getElem?_modify, if_pos rfl]
    have e0 := stSent_new t.st #[foldMaskNotice (ioppFoldShape c L)] 0
    rw [Nat.add_zero] at e0
    rw [e0]
    rfl
  · obtain ⟨x, hx, x1, x2, x3⟩ := of_mk b
    exact ⟨x, hx, x1, by rw [x2]; rfl, x3⟩

/-- What a yes of the test leaves, fourth part, where the first fold sends its own mask. -/
structure TowerOwn (t0 tE : T12) (n : ℕ) (G : Group) : Prop where
  was : t0.st.groups[t0.g]? = some G
  /-- every elder message: as the beginning of the test leaves it -/
  old : ∀ o, o < t0.st.oracles.size → tE.st.oracles[o]? = (begun t0.st t0.g G).oracles[o]?
  /-- the test's own first mask: the next message: no sample, spent -/
  own : Rdr tE.st t0.st.oracles.size true
  later : ∀ i, i < n → Tgt tE.st (t0.st.oracles.size + 1 + 2 * i) ∧ Rdr tE.st (t0.st.oracles.size + 1 + 2 * i + 1) true ∧
    Grp tE.st (t0.st.groups.size + i) (t0.st.oracles.size + 1 + 2 * i)

/-- **A yes of the test's decision leaves TowerOwn**, where the state names no mask. -/
theorem k12_tower_own (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (hm : t0.mask = none) :
    ∃ G, TowerOwn t0 tE (p.nums.stages.length - 1) G := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)
  obtain ⟨G, hG, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (guardedProximityTestParts.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t' :=
    fun j cur cut t t' rs gs h => baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1
  have K := stages_st guardedProximityTestParts p (like_P5 p) hB he ha rest 0 first _ _ tE _ _ hst
  have osz : (begun tF.st tF.g G).oracles.size = tF.st.oracles.size := H2K.Out.closeLedgers_size _ _
  have gsz : (begun tF.st tF.g G).groups.size = tF.st.groups.size := by
    show ((closeLedgers tF.st _).groups.modify _ _).size = _
    rw [Array.size_modify, H2K.Out.closeLedgers_groups]
  cases rest with
  | nil =>
    exfalso
    unfold H2U.roundsOfNums at hr
    rw [hs] at hr
    cases hr
  | cons nxt rest =>
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok guardedProximityTestParts p 0 first nxt rest _ _ tE _ _).1 hst
    have hlen : ∀ (l : Laid) (rs : List Fmt.RoundView), ((rs.drop (foldAt guardedProximityTestParts p 0 first l : Blk').rounds.length).take
               (switchAt guardedProximityTestParts p 0 first nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      intro l rs
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + first.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have f1' := (like_P5 p).fold _ _ _ _ _ _ _ f1
    have f2' := (like_P5 p).switch _ _ _ _ _ _ _ _ _ f2
    have f3' := (like_P5 p).behind _ _ _ _ _ f3
    obtain ⟨a1, a2, a3, a4⟩ := stage_tower_own p he ha 0 first nxt rest.isEmpty _ _ _ t1 t2 t3 _ _ _ _ (hlen _ _) f1' f2' f3' hm
    obtain ⟨s1, _, _, s4, _, _, _, s8⟩ := stage_st p he ha 0 first nxt rest.isEmpty _ _ _ t1 t2 t3 _ _ _ _ (hlen _ _) f1' f2' f3'
    have hown : own ({ tF with st := begun tF.st tF.g G, pass := .claim row L } : T12) = 1 := by simp [own, hm]
    rw [hown] at s4 s8
    dsimp only at a1 a2 a3 a4 s1 s4 s8
    rw [osz] at a1 a2 a3 a4 s4 s8
    rw [gsz] at a4 s1
    have K3 := stages_st guardedProximityTestParts p (like_P5 p) hB he ha rest (0 + 1) nxt _ t3 tE _ _ f5
    obtain ⟨_, i1, i2⟩ := stages_tower p he ha rest (0 + 1) nxt _ t3 tE _ _ f5 _ s8
    have old3 : ∀ o, o < tF.st.oracles.size + 2 → tE.st.oracles[o]? = t3.st.oracles[o]? := fun o ho =>
      K3.oraclesOld o (by rw [s4]; omega) (by
        rw [s8]
        intro e
        have := Option.some.inj e
        omega)
    refine ⟨G, hG, fun o ho => ?_, ?_, fun i hi => ?_⟩
    · exact K.oraclesOld o (by rw [osz]; exact ho) (by
        show tF.mask ≠ some o
        rw [hm]
        exact fun e => by cases e)
    · obtain ⟨x, hx, hx'⟩ := a1
      exact ⟨x, by rw [old3 _ (by omega)]; exact hx, hx'⟩
    · cases i with
      | zero =>
        refine ⟨?_, ?_, ?_⟩
        · obtain ⟨x, hx, hx'⟩ := a2
          exact ⟨x, by rw [Nat.mul_zero, Nat.add_zero, old3 _ (by omega)]; exact hx, hx'⟩
        · obtain ⟨x, hx, x1, x2, _⟩ := a3
          refine ⟨spent x, ?_, x1, x2, rfl⟩
          rw [Nat.mul_zero, Nat.add_zero, i1, hx]
          rfl
        · obtain ⟨G', hG', hG''⟩ := a4
          exact ⟨G', by rw [Nat.add_zero, K3.groupsOld _ (by rw [s1]; omega)]; exact hG', by rw [Nat.mul_zero, Nat.add_zero]; exact hG''⟩
      | succ i =>
        have hi' : i < rest.length := by
          rw [hs] at hi
          simp only [List.length_cons] at hi
          omega
        have k := i2 i hi'
        rw [s4, s1] at k
        have e1 : tF.st.oracles.size + 1 + 2 + 2 * i = tF.st.oracles.size + 1 + 2 * (i + 1) := by omega
        have e2 : tF.st.groups.size + 1 + i = tF.st.groups.size + (i + 1) := by omega
        rw [e1, e2] at k
        exact k

end Johnson.RunOne.Law.K12Tower

#print axioms Johnson.RunOne.Law.K12Tower.stage_tower_own
#print axioms Johnson.RunOne.Law.K12Tower.k12_tower_own
#print axioms Johnson.RunOne.Law.K12Tower.did_target
#print axioms Johnson.RunOne.Law.K12Tower.did_rider
#print axioms Johnson.RunOne.Law.K12Tower.did_group
#print axioms Johnson.RunOne.Law.K12Tower.stage_tower
#print axioms Johnson.RunOne.Law.K12Tower.stages_tower
#print axioms Johnson.RunOne.Law.K12Tower.k12_tower
