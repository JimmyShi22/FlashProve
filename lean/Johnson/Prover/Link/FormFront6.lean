-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormFront6.lean: THE FORM's HALF: **front6_yes: THE LINK's SIX FRONT BLOCKS SAY
ok** (foldBlocks over frontBlock P :: blocksOrV P, Johnson/Desc/Link/LinkDesc.lean), and behind them
stands what is carried to the proximity test's front (LinkSeats,
Johnson/Prover/Link/FormSeats.lean).

Main names.
  point_yes       "LINK point" returns pointT.
  linkSent_of     behind "LINK point" and the sending stands LinkSent.
  step_no_cols    a block that reads no column is, as a step, its decision, whatever columns lie
  there.
  cols_lookup     columns that match a list of positions: each is found, with its width.
  linkOk_gives    what the plan's test on the link's shape is spent for.
  bLink_step      "LINK" as a step.
  front6_yes      THE STATEMENT.

Limits. THE SENDING's BLOCK ENTERS AS A PREMISE HERE: its step's yes, no column taken, and SendGave
(Johnson/Prover/Link/FormGave.lean): paid by the shared sending's laws in FormSendGave.lean
(sendK1_gave, under SendFront, rounds that fit and 1 ≤ samples; front6_whole is front6_yes with the
sending paid). roundsFit at three
blocks and "the columns" at "LINK" are premises: Block.step's own two tests. The keys' sizes and "no
seed's factor is 0" are premises. FOR ALL DRAWS that meet these. It ends in front of the proximity
test. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormGave
import Johnson.Desc.Sound.FoldLaw
import Johnson.Desc.K15.FoldInv
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open Desc.K15 (St Par15 P15)

/-- **"LINK point" returns pointT.** -/
theorem point_yes (p : Par15) (d : St) (r : Fmt.RoundView)
    (h : Ground.ok (Ground.newGroupL d.st p.S.code p.S.maskCode) = true) :
    Desc.K15.point p d [r] = some (pointT p d r) := by
  show (do
    let (g, d) ← Ground.newGroupP d p.S.code p.S.maskCode
    some { d with loc := { d.loc with gamma := Desc.K14.drawn r, g := g } }) = _
  unfold Ground.newGroupP
  rw [if_pos h]
  rfl

/-- **Behind "LINK point" and the sending stands LinkSent.** -/
theorem linkSent_of (p : Par15) (d d2 : St) (r : Fmt.RoundView) (H : SendGave p (pointT p d r) d2)
    (ok0 : foldeqOk d.st.codes (p.S.side false p.samples) = true)
    (ok1 : foldeqOk d.st.codes (p.S.side true p.samples) = true)
    (hr : r.drawn.elems.length = p.S.table.v) (k0 : Own.keyFits d.loc.key0 p.S.table = true)
    (k1 : Own.keyFits d.loc.key1 p.S.table = true)
    (z0 : d.loc.key0.seeds.all (!isZeroE ·.beta) = true)
    (z1 : d.loc.key1.seeds.all (!isZeroE ·.beta) = true) :
    LinkSent p d2 { code := p.S.code, maskCode := p.S.maskCode } := by
  have hc : d2.st.codes = d.st.codes := H.codes
  have hg : d2.loc.gamma.length = p.S.table.v := by
    rw [H.gamma]
    show (Desc.K14.drawn r).length = _
    unfold Desc.K14.drawn
    rw [List.length_map, hr]
  refine ⟨?_, rfl, rfl, rfl, rfl, H.two, H.m0, H.m1, H.lay0, H.lay1, by rw [hc]; exact ok0,
    by rw [hc]; exact ok1, ?_⟩
  · rw [H.groups, H.g]
    show (d.st.groups.push _)[d.st.groups.size]? = _
    simp
  · have e0 : d2.loc.key0 = d.loc.key0 := H.key0
    have e1 : d2.loc.key1 = d.loc.key1 := H.key1
    simp only [Ground.ok, Desc.K15.laysRecL, Desc.K15.keyL, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq, e0, e1]
    exact ⟨⟨k0, z0, hg⟩, k1, z1, hg⟩

/-- **A block that reads no column is, as a step, its decision**, whatever columns lie there. -/
theorem step_no_cols {S Cl : Type} (b : Block S Cl) (ft : Nat) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hb : ∀ r ∈ b.rounds, r.stored = [] ∧ r.opens = [])
    (hfit : roundsFit b.rounds rs = true) (hd : b.decide s (rs.map noDigest) [] = .ok s') :
    b.step ft s rs cols = .ok (s', 0) := by
  unfold Block.step
  rw [hfit, groupsOf_none ft b.rounds _ hb]
  simp only [need, List.flatMap_nil, List.length_nil, List.take_zero, List.map_nil, regroup]
  show (do let s' ← b.decide s (rs.map noDigest) []; pure (s', 0) : Except String (S × Nat)) = _
  rw [hd]
  rfl

/-- **Columns that match a list of positions: each is found, with its width.** -/
theorem cols_lookup : ∀ (got : List OpenedColumn) (key W : Nat) (xs : List Nat),
    got.map (fun c => (c.1, c.2.1, c.2.2.length)) = xs.map (fun x => (key, x, W)) →
    ∀ x ∈ xs, ∃ c, (got.map fun c => (c.2.1, c.2.2)).lookup x = some c ∧ c.length = W
  | [], _, _, [], _, _, hx => absurd hx (by simp)
  | [], _, _, _ :: _, h, _, _ => by simp at h
  | _ :: _, _, _, [], h, _, _ => by simp at h
  | c :: got, key, W, y :: xs, h, x, hx => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨_, h2, h3⟩, h4⟩ := h
    by_cases e : x = y
    · subst e
      exact ⟨c.2.2, by simp [List.lookup, h2], h3⟩
    · obtain ⟨c', e1, e2⟩ := cols_lookup got key W xs h4 x
        ((List.mem_cons.1 hx).resolve_left e)
      refine ⟨c', ?_, e2⟩
      rw [List.map_cons, List.lookup_cons, h2]
      have : (x == y) = false := by simpa using e
      rw [this]
      exact e1

/-- **What the plan's test on the link's shape is spent for.** -/
theorem linkOk_gives (codes : Codes) (S : LinkShape) (n : Nat) (h : linkOk codes S n = true) :
    Ground.ok (Ground.groupL codes S.code S.maskCode) = true ∧
      foldeqOk codes (S.side false n) = true ∧ foldeqOk codes (S.side true n) = true := by
  simp only [linkOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hS, hF⟩, _⟩, hI⟩ := h
  refine ⟨?_, hF, ?_⟩
  · simp only [ioppOk, LinkShape.test, ioppStagesOk, Bool.and_eq_true] at hI
    have h1 := hI.2.1
    unfold ioppStageOk at h1
    show Ground.ok (Ground.groupL codes S.firstStage.code S.firstStage.maskCode) = true
    cases hb : codes.base[S.firstStage.code]? with
    | none => simp [hb] at h1
    | some c =>
      cases hm : codes.mask[S.firstStage.maskCode]? with
      | none => simp [hb, hm] at h1
      | some z =>
        simp only [hb, hm, Bool.and_eq_true, maskFits] at h1
        unfold Ground.ok Ground.groupL
        rw [hb, hm]
        simpa [Ground.has] using h1.1.1.1.2
  · simp only [LinkShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hS
    simp only [foldeqOk, FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hF ⊢
    exact ⟨⟨⟨⟨⟨⟨⟨hF.1.1.1.1.1.1.1, hF.1.1.1.1.1.1.2⟩, hF.1.1.1.1.1.2⟩, hF.1.1.1.1.2⟩,
      hF.1.1.1.2⟩, hS.1.1.1.2⟩, hF.1.2⟩, hF.2⟩

/-- A drawn location of a stored part is in the part's list. -/
theorem mem_part (s : Fmt.Stored) (poss : List Nat) (x : Nat)
    (h : x ∈ ((poss.map (· % 2 ^ s.sh.a)).drop s.lo).take s.count) :
    x ∈ Fmt.listOf ((Fmt.partOf s poss).map (· % 2 ^ s.sh.a)) := by
  rw [Fmt.listOf_mem]
  unfold Fmt.partOf
  rw [List.map_take, List.map_drop]
  exact h

/-- **"LINK" as a step.** -/
theorem bLink_step (P : P15) (d : St) (G : Group) (r : Fmt.RoundView) (cols : List OpenedColumn)
    (H : LinkSeats P.par d G)
    (hfit : roundsFit (Desc.K15.bLink P (Desc.K15.fiveOf P)).rounds [r] = true)
    (hc : (cols.take (linkWant P.S r).length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      linkWant P.S r) :
    ∃ d' G', (Desc.K15.bLink P (Desc.K15.fiveOf P)).step 0 d [r] cols =
        .ok (d', (linkWant P.S r).length) ∧ LinkSeats P.par d' G' := by
  obtain ⟨s0, s1, hs, a0, a1, w0, w1, l0, l1, n0, n1⟩ : ∃ s0 s1 : Fmt.Stored,
      Desc.K15.readsAtLink P.S = [s0, s1] ∧ s0.sh.a = P.S.table.code.logN ∧
      s1.sh.a = P.S.table.code.logN ∧ s0.sh.W = 2 ^ P.S.table.v ∧ s1.sh.W = 2 ^ P.S.table.v ∧
      s0.lo = 0 ∧ s1.lo = P.S.columnsFirst ∧ s0.count = P.S.columnsFirst ∧
      s1.count = P.S.columnsFurther := ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hw : linkWant P.S r = partWant s0 r ++ partWant s1 r := by
    unfold linkWant
    rw [hs]
    simp
  have hg : groupsOf 0 (Desc.K15.bLink P (Desc.K15.fiveOf P)).rounds ([r].map (·.drawn)) =
      [partWant s0 r, partWant s1 r] := by
    show groupsOf 0 [{ entry := _, stored := Desc.K15.readsAtLink P.S }] [r.drawn] = _
    unfold groupsOf
    rw [hs]
    rfl
  rw [hw] at hc
  have c0 : ((cols.take (partWant s0 r ++ partWant s1 r).length).take (partWant s0 r).length).map
      (fun c => (c.1, c.2.1, c.2.2.length)) = partWant s0 r := by
    rw [List.map_take, hc, List.take_left']
    rfl
  have c1 : (((cols.take (partWant s0 r ++ partWant s1 r).length).drop
      (partWant s0 r).length).take (partWant s1 r).length).map
      (fun c => (c.1, c.2.1, c.2.2.length)) = partWant s1 r := by
    rw [List.map_take, List.map_drop, hc, List.drop_left', List.take_length]
    rfl
  obtain ⟨rows0, rows1, e, H'⟩ := linkLoc_yes P.par d G (noDigest r) _ _ H
    (fun x hx => by
      obtain ⟨c, e1, e2⟩ := cols_lookup _ _ _ _ c0 x (mem_part s0 r.drawn.poss x
        (by rw [a0, l0, n0, List.drop_zero]; exact hx))
      exact ⟨c, e1, by rw [e2, w0]; exact Nat.le_refl _⟩)
    (fun x hx => by
      obtain ⟨c, e1, e2⟩ := cols_lookup _ _ _ _ c1 x (mem_part s1 r.drawn.poss x
        (by rw [a1, l1, n1]; exact hx))
      exact ⟨c, e1, by rw [e2, w1]; exact Nat.le_refl _⟩)
  refine ⟨_, _, ?_, H'⟩
  unfold Block.step
  rw [hfit, hg, hw]
  have hf : ([partWant s0 r, partWant s1 r].flatMap id) = partWant s0 r ++ partWant s1 r := by
    simp
  simp only [hf, hc, need, beq_self_eq_true, if_true, List.map_cons, List.map_nil, regroup]
  show (do
    let s' ← Desc.K15.why [] (Desc.K15.link P.par d [noDigest r] _)
    pure (s', (partWant s0 r ++ partWant s1 r).length) : Except String (St × Nat)) = _
  rw [e]
  rfl

/-- How many elements a round that fits one declared round draws. -/
theorem elems_of_fit (dcl : Fmt.DeclaredRound) (r : Fmt.RoundView) (h : roundsFit [dcl] [r] = true) :
    r.drawn.elems.length = dcl.entry.drawE := by
  unfold roundsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.2

/-- **front6_yes: THE LINK's SIX FRONT BLOCKS SAY ok**, and behind them stands LinkSeats. -/
theorem front6_yes (P : P15) (x : TableKey × TableKey) (r0 r1 r2 r3 r4 : Fmt.RoundView) (cols : List OpenedColumn)
    (d2 : St) (he : Desc.K15.entries P = some (Desc.K15.fiveOf P))
    (hok : linkOk P.codes P.S P.set.samples = true) (k0 : Own.keyFits x.1 P.S.table = true)
    (k1 : Own.keyFits x.2 P.S.table = true) (z0 : x.1.seeds.all (!isZeroE ·.beta) = true)
    (z1 : x.2.seeds.all (!isZeroE ·.beta) = true)
    (f0 : roundsFit (Desc.K15.bPoint P (Desc.K15.fiveOf P)).rounds [r0] = true)
    (hs : (Desc.K15.sendK1 P).step 0 (pointT P.par (Desc.K15.first P.codes x) (noDigest r0))
      [r1, r2] cols = .ok (d2, 0))
    (hg : SendGave P.par (pointT P.par (Desc.K15.first P.codes x) (noDigest r0)) d2)
    (f3 : roundsFit (Desc.K15.bLink P (Desc.K15.fiveOf P)).rounds [r3] = true)
    (hc : (cols.take (linkWant P.S r3).length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      linkWant P.S r3)
    (f4 : roundsFit (Desc.K15.bPhi P (Desc.K15.fiveOf P)).rounds [r4] = true) :
    ∃ d' G', foldBlocks 0 (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P)
        (Desc.K15.first P.codes x) [r0, r1, r2, r3, r4] cols =
        .ok (d', [], cols.drop (linkWant P.S r3).length) ∧ LinkSeats P.par d' G' := by
  obtain ⟨g1, g2, g3⟩ := linkOk_gives P.codes P.S P.set.samples hok
  have e0 : r0.drawn.elems.length = P.S.table.v := elems_of_fit _ r0 f0
  have e4 : r4.drawn.elems.length = P.S.entryBits := elems_of_fit _ r4 f4
  have hSent := linkSent_of P.par (Desc.K15.first P.codes x) d2 (noDigest r0) hg g2 g3 e0 k0 k1 z0
    z1
  obtain ⟨rows0, rows1, eR, HR⟩ := laysRec_yes P.par d2 _ [] hSent
  obtain ⟨d4, G4, eL, HL⟩ := bLink_step P _ _ r3 cols HR f3 hc
  obtain ⟨row, eP, HP⟩ := linkPhi_yes P.par d4 G4 (noDigest r4) HL e4
  refine ⟨_, _, ?_, HP⟩
  have s0 : (Desc.K15.frontBlock P).step 0 (Desc.K15.first P.codes x) [] cols =
      .ok (Desc.K15.first P.codes x, 0) :=
    step_no_cols _ 0 _ _ [] cols (fun r hr => absurd hr (by simp [Desc.K15.frontBlock, roundlessBlock]))
      rfl rfl
  have s1 : (Desc.K15.bPoint P (Desc.K15.fiveOf P)).step 0 (Desc.K15.first P.codes x) [r0] cols =
      .ok (pointT P.par (Desc.K15.first P.codes x) (noDigest r0), 0) :=
    step_no_cols _ 0 _ _ [r0] cols
      (fun r hr => by
        obtain rfl := List.mem_singleton.1 hr
        exact ⟨rfl, rfl⟩) f0
      (by
        show Desc.K15.why [] (Desc.K15.point P.par (Desc.K15.first P.codes x) [noDigest r0]) = _
        rw [point_yes P.par (Desc.K15.first P.codes x) (noDigest r0) g1]
        rfl)
  have s3 : (Desc.K15.bRec P (Desc.K15.fiveOf P)).step 0 d2 [] cols = .ok (_, 0) :=
    step_no_cols _ 0 _ _ [] cols (fun r hr => absurd hr (by simp [Desc.K15.bRec])) rfl
      (by
        show Desc.K15.why _ (Desc.K15.laysRec P.par d2 []) = _
        rw [eR]
        rfl)
  have s5 : (Desc.K15.bPhi P (Desc.K15.fiveOf P)).step 0 d4 [r4]
      (cols.drop (linkWant P.S r3).length) = .ok (_, 0) :=
    step_no_cols _ 0 _ _ [r4] _
      (fun r hr => by
        obtain rfl := List.mem_singleton.1 hr
        exact ⟨rfl, rfl⟩) f4
      (by
        show Desc.K15.why [] (Desc.K15.phi P.par d4 [noDigest r4]) = _
        rw [eP]
        rfl)
  rw [Desc.K15.blocksV_eq P _ he]
  refine (foldBlocks_ok 0 _ _ _ [] [r0, r1, r2, r3, r4] cols rfl _ 0 s0).trans ?_
  refine (foldBlocks_ok 0 _ _ _ [r0] [r1, r2, r3, r4] cols rfl _ 0 s1).trans ?_
  refine (foldBlocks_ok 0 _ _ _ [r1, r2] [r3, r4] cols rfl _ 0 hs).trans ?_
  refine (foldBlocks_ok 0 _ _ _ [] [r3, r4] cols rfl _ 0 s3).trans ?_
  refine (foldBlocks_ok 0 _ _ _ [r3] [r4] cols rfl _ _ eL).trans ?_
  exact foldBlocks_ok 0 _ [] _ [r4] [] _ rfl _ 0 s5

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.point_yes
#print axioms Johnson.Prover.Link.linkSent_of
#print axioms Johnson.Prover.Link.step_no_cols
#print axioms Johnson.Prover.Link.cols_lookup
#print axioms Johnson.Prover.Link.linkOk_gives
#print axioms Johnson.Prover.Link.mem_part
#print axioms Johnson.Prover.Link.bLink_step
#print axioms Johnson.Prover.Link.elems_of_fit
#print axioms Johnson.Prover.Link.front6_yes
