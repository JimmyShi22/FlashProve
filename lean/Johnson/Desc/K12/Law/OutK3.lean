-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OutK3.lean: what the record is that a yes of the decision of the proximity test
(the kind K12) leaves, third part: the book's counts.

An outright theorem on the text of the block: no premise on the view, and of the place only p.early
= true and p.answers = 1. It stands over Johnson/Desc/K12/Law/OutK.lean,
Johnson/Desc/K12/Law/OutK2.lean, switchE_roots (Johnson/Desc/K12/Law/SwRoots.lean) and readOld_inv
(Johnson/Desc/K12/Law/SwRead.lean), and holds of both `proximityTestParts` and `guardedProximityTestParts`. Statements and
proofs.
Main names:
  `BookN`: the roots rise as the trees do; the messages as the places do; no root is lost. It is
    reflexive and transitive.
  `treesSent_sz`, `partsLaid_sz`, `bookSentP_sizes`: a prover's message brings as many trees as it
    lays, and a place for each of its oracle messages.
  `SameN`, `openOne_same`, `readOld_same`, `openOneB_same`, `readPlain_same`: a reading makes no
    tree and moves no place.
  `foldJ_book`, `behindJ_roots`, `switch_roots`, `switch_book`, `BaseBk`, `baseJ5_bk`, `baseJ_bk`:
    part by part (baseJ5_bk off the closed form baseJ5_form of Johnson/Desc/K12/Law/OutK.lean).
  `stages_book`: by recursion along the stages; and in front of a stage but the last the statement
    and the book are in step (the switch's own test, carried back through the fold).
  `OutK3`, `k12_out3_of`, `k12_out3`, `k12_out3_joined`: the roots have risen just as trees have
    come; no root is lost; in front of the test and behind it the book has as many places as the
    statement has oracle messages.
Limits: No soundness is claimed, and nothing is said on hiding.
Not proved (evaluated by outOk, Johnson/Desc/K12/Law/OutOk.lean): how many trees come (one for each
switch, and one where the fold sends its own mask) and which (the plan's depths, widths, numbers,
sources). Both hang on "each prover's message of the test lays one tree" (layTrees at the record's
codes), which is no theorem on the text alone: it needs the record's codes. Nor: that the plan's
ownMask and count of trees sent are the record's. That the plan's count of roots in front of the
test is the record's follows from a yes of proximityTestKind guardedProximityTestParts p, whose front tests it (the first conjunct
of k12_guards, Johnson/Desc/K12/Law/TopH.lean).
The field step0 says something of the record that the test was handed: a yes of the test says that
this record was in step.
Of the 23 clauses of outOk this file proves step, and of roots and trees.n that the two go together.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.OutK2
import Johnson.Desc.K12.Law.SwRead

set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)

/-- The book's counts go with the record's: the roots rise as the trees do, the messages as the
places do. -/
structure BookN (t t' : T12) : Prop where
  rt : t'.roots + t.book.trees.size = t.roots + t'.book.trees.size
  op : t'.st.oracles.size + t.book.place.size = t.st.oracles.size + t'.book.place.size
  mono : t.roots ≤ t'.roots

theorem BookN.refl (t : T12) : BookN t t := ⟨rfl, rfl, Nat.le_refl _⟩

theorem BookN.trans {a b c : T12} (h1 : BookN a b) (h2 : BookN b c) : BookN a c :=
  ⟨by have := h1.rt; have := h2.rt; omega, by have := h1.op; have := h2.op; omega,
    h1.mono.trans h2.mono⟩

theorem treesSent_sz (first : ℕ) : ∀ (l : List TreeShape) (roots : ℕ) (trees : Array OnBytes.Tree),
    (treesSent first l roots trees).size = trees.size + l.length
  | [], _, _ => rfl
  | s :: l, roots, trees => by
    show (treesSent first l (roots + 1) (trees.push _)).size = _
    rw [treesSent_sz first l, Array.size_push, List.length_cons]
    omega

theorem partsLaid_sz (sent : Array OracleNotice) (lay : TreeLay) (n0 base : ℕ)
    (trees : Array OnBytes.Tree) : (partsLaid sent lay n0 base trees).size = trees.size := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih => rw [List.foldl_cons, ih, Array.size_modify]

theorem bookSentP_sizes (ft roots : ℕ) (S : Statement) (Bk : TreeBook) (sent : Array OracleNotice)
    (lay : TreeLay) :
    (bookSentP ft roots S Bk sent lay).trees.size = Bk.trees.size + lay.shapes.size ∧
      (bookSentP ft roots S Bk sent lay).place.size = Bk.place.size + sent.size := by
  constructor
  · show (partsLaid _ _ _ _ _).size = _
    rw [partsLaid_sz, treesSent_sz, Array.length_toList]
  · show (Bk.place ++ (Array.range sent.size).map _).size = _
    rw [Array.size_append, Array.size_map, Array.size_range]

/-- A reading makes no tree and moves no place. -/
def SameN (B B' : TreeBook) : Prop := B'.trees.size = B.trees.size ∧ B'.place = B.place

theorem openOne_same (S : Statement) (ft : ℕ) (pos : Positions) (B0 : TreeBook) (t : ℕ)
    (s s' : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F)))
    (h : Tw.L9.openOne S ft pos B0 t s = .ok s') : SameN s.1 s'.1 := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact ⟨Array.size_modify .., rfl⟩)
      | cases h
  · cases h

theorem readOld_same (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) : SameN i.book B := by
  obtain ⟨places, cols, opened, _, h3, _, _⟩ := readOld_inv i pos B left ys h
  exact foldlM_keeps'
    (fun (a b : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F))) =>
      SameN a.1 b.1) (fun _ => ⟨rfl, rfl⟩)
    (fun _ _ _ h1 h2 => ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩) _
    (fun s a s' hs => openOne_same _ _ _ _ _ _ _ hs) _ _ _ h3

theorem openOneB_same (S : Statement) (ft : ℕ) (pos : Positions) (B0 : TreeBook) (t : ℕ)
    (s s' : TreeBook × List First.Base.Col × Array (ℕ × Array ℕ × Array (Array F)))
    (h : First.Base.openOne S ft pos B0 t s = some s') : SameN s.1 s'.1 := by
  unfold First.Base.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact ⟨Array.size_modify .., rfl⟩)
      | cases h
  · cases h

theorem readPlain_same (S : Statement) (B : TreeBook) (ft : ℕ) (cols : List First.Base.Col)
    (ids : Array ℕ) (pos : Positions) (o : First.Base.Got)
    (h : First.Base.readPlain S B ft cols ids pos = some o) : SameN B o.book := by
  unfold First.Base.readPlain at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i B' left' got' hfold
        obtain ⟨opened, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact foldlM_keepsO
          (fun (a b : TreeBook × List First.Base.Col × Array (ℕ × Array ℕ × Array (Array F))) =>
            SameN a.1 b.1) (fun _ => ⟨rfl, rfl⟩)
          (fun _ _ _ h1 h2 => ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩) _
          (fun s a s' hs => openOneB_same _ _ _ _ _ _ _ hs) _ _ _ hfold

/-- The fold's part. -/
theorem foldJ_book (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) : BookN t t1 :=
        by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ := foldJ_form p j cur cut t t1 rs
      gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · refine ⟨rfl, ?_, Nat.le_refl _⟩
    show (t.st.oracles.modify id _).size + _ = _
    rw [Array.size_modify]
  · obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok hr
    obtain ⟨b1, b2⟩ := bookSentP_sizes p.nums.firstTree t.roots t.st t.book
      #[foldMaskNotice (ioppFoldShape c L)] lay
    refine ⟨?_, ?_, Nat.le_add_right _ _⟩
    · show t.roots + lay.shapes.size + t.book.trees.size = t.roots + (bookSentP _ _ _ _ _
        _).trees.size
      rw [b1]
      omega
    · show ((stSent t.st _).oracles.modify id _).size + _ = _ + (bookSentP _ _ _ _ _ _).place.size
      rw [Array.size_modify, b2]
      simp [stSent]
      omega

theorem behindJ_roots (p : P12) (j : ℕ) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t2 t3 : T12) (h : (behindJ p j nxt cut).decide t2 [] [] = .ok t3) : t3.roots = t2.roots := by
  simp only [behindJ] at h
  split at h
  · obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    replace hx := H2K.Sw.named_ok hx
    unfold VerifiableInference.Desc.Test.csTest at hx
    dsimp only at hx
    split at hx
    · cases hx
    · rename_i run s2 hb
      split at hx
      · cases hx
      · rename_i s3 ha
        split at hx
        · cases hx
        · cases hx
          obtain ⟨G, lay, _, _, _, a4⟩ := beginRunE_ok hb
          have a5 := askOwedE_ok ha
          show s3.d.roots = _
          rw [a5, a4]
          rfl
  · cases h

/-- The roots behind the switch's part: risen by the trees that its message lays. -/
theorem switch_roots (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2) :
    ∃ (nx : IoppStage) (lay : TreeLay), stageAt p (j + 1) nxt = some nx ∧
      layTrees t1.st.codes (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1)
        (othersOf last nx)) = some lay ∧ t2.roots = t1.roots + lay.shapes.size := by
  simp only [switchJ] at h1
  split at h1
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out', theta⟩, s'⟩, hx, h1⟩ := bind_ok h1
    obtain ⟨rfl, _⟩ := back_ok h1
    have hoth : (if (!p.early) = true then (#[] : Array OracleNotice)
        else if last = true then #[baseMaskNotice nx.code nx.maskCode 1 0]
        else #[foldMaskNotice (ioppFoldShape nx {})]) = othersOf last nx := by
      rw [he]
      rfl
    rw [hoth, ha] at hx
    obtain ⟨_, _, _, _, _, _, lay, _, _, hl, hr, _⟩ := switchE_roots rows
      (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) gp (othersOf last nx) _ s' out' theta rfl
      rfl (othersOf_none last nx) hx
    exact ⟨nx, lay, e2, hl, hr⟩
  · cases h1

/-- The switch's part and the batching behind it. hfresh: the group that the fold has made has no
member. -/
theorem switch_book (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (hfresh : ∀ rows gp, t1.pass = .single rows gp →
      ∃ G, t1.st.groups[gp]? = some G ∧ G.members = #[])
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) :
    BookN t1 t3 ∧ t1.st.oracles.size = t1.book.place.size := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out0, theta0⟩, s'⟩, hx, _⟩ := bind_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out, row, L, th, D, _, _, hd, _, _⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    obtain ⟨nx', lay, e2', hl, hroots⟩ := switch_roots p he ha j cur nxt last cut t1 t2 _ gs h1
    obtain rfl : nx = nx' := Option.some.inj (e2.symm.trans e2')
    obtain rfl : D.lay = lay := Option.some.inj (hd.trees.symm.trans hl)
    have h3 := behindJ_roots p (j + 1) nxt cut t2 t3 h2
    obtain ⟨G, hG, hGm⟩ := hfresh rows gp e1
    have hDG : D.G.members = #[] := by
      have hg := hd.group
      rw [ledgerShut_groups] at hg
      have hg' : t1.st.groups[gp]? = some D.G := hg
      rw [hG] at hg'
      rw [← Option.some.inj hg']
      exact hGm
    obtain ⟨c1, _⟩ := did_oracles hd hDG
    obtain ⟨i, left, _, hb, _, _, _, hread⟩ := hd.read
    obtain ⟨s1, s2⟩ := readOld_same i _ _ _ _ hread
    rw [hb] at s1 s2
    obtain ⟨b1, b2⟩ := bookSentP_sizes p.nums.firstTree t1.roots t1.st t1.book
      (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) (othersOf last nx)) D.lay
    refine ⟨⟨?_, ?_, ?_⟩, hd.places⟩
    · rw [h3, hroots, s1, b1]
      omega
    · rw [c1, s2, b2]
      omega
    · rw [h3, hroots]
      exact Nat.le_add_right _ _
  · cases h1'

/-- What the base case leaves of the book and the roots. -/
def BaseBk (t tE : T12) : Prop := SameN t.book tE.book ∧ tE.roots = t.roots

theorem baseJ5_bk (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) :
    BaseBk t tE := by
  obtain ⟨star, a, _, _, rfl⟩ := baseJ5_form p j cur cut t tE rs gs h
  exact ⟨⟨Array.size_modify, rfl⟩, rfl⟩

theorem baseJ_bk (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ p j cur cut).decide t rs gs = .ok tE) :
    BaseBk t tE := by
  simp only [baseJ] at h
  split at h
  · obtain ⟨R, _, h⟩ := bind_ok h
    obtain ⟨s, hs, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.baseE' at hs
    split at hs
    · obtain ⟨_, _, hs⟩ := bind_ok hs
      obtain ⟨_, _, hs⟩ := bind_ok hs
      obtain ⟨_, _, hs⟩ := bind_ok hs
      obtain ⟨⟨b, took⟩, h3, hs⟩ := bind_ok hs
      cases hs
      obtain ⟨star, S1, ids, pos, o, _, _, k3, _, k5⟩ :=
        baseEW_state _ _ _ _ _ _ _ _ (mapError_ok h3)
      have k5' : b.book = o.book := k5
      refine ⟨?_, rfl⟩
      show SameN t.book b.book
      rw [k5']
      exact readPlain_same _ _ _ _ _ _ _ k3
    · cases hs
  · cases h

/-- By recursion along the stages: the counts go together; and in front of a stage but the last the
statement and the book are in step. -/
theorem stages_book (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' →
      BaseSt t t' ∧ BaseBk t t')
    (he : p.early = true) (ha : p.answers = 1) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
      (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE →
      BookN t tE ∧ (rest ≠ [] → t.st.oracles.size = t.book.place.size)
  | [], j, cur, l, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    obtain ⟨⟨star, _, _, h3⟩, ⟨s1, s2⟩, h5⟩ := hB _ _ _ _ _ _ _ h
    refine ⟨⟨by rw [h5, s1], ?_, by rw [h5]⟩, fun hne => absurd rfl hne⟩
    rw [h3, s2]
    show (t.st.oracles.modify star _).size + _ = _
    rw [Array.size_modify]
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok X p j cur nxt rest l t tE rs gs).1 h
    have hlen : ((rs.drop (foldAt X p j cur l : Blk').rounds.length).take
        (switchAt X p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have f1' := hX.fold _ _ _ _ _ _ _ f1
    have k1 := foldJ_book p j cur _ t t1 _ _ f1'
    have hfresh : ∀ rows gp, t1.pass = .single rows gp →
        ∃ G, t1.st.groups[gp]? = some G ∧ G.members = #[] := by
      obtain ⟨row, L, c, n, id, d1, d', rows, _, _, _, _, rfl⟩ := foldJ_form p j cur _ t t1 _ _ f1'
      intro rows' gp hp
      cases hp
      refine ⟨{ code := n.1, maskCode := n.2 }, ?_, rfl⟩
      show (d'.st.groups.push _)[d'.st.groups.size]? = _
      rw [Array.getElem?_push_size]
    obtain ⟨k2, hstep⟩ := switch_book p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen hfresh
      (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3)
    obtain ⟨k3, _⟩ := stages_book X p hX hB he ha rest (j + 1) nxt _ t3 tE _ _ f5
    refine ⟨(k1.trans k2).trans k3, fun _ => ?_⟩
    have := k1.op
    omega

/-- What a yes of the test leaves, third part: the book's counts. -/
structure OutK3 (t0 tE : T12) : Prop where
  /-- The roots have risen just as the trees have come -/
  rootsTrees : tE.roots + t0.book.trees.size = t0.roots + tE.book.trees.size
  /-- No root is lost -/
  rootsUp : t0.roots ≤ tE.roots
  /-- In front of the test, and behind it, the book has a place for each oracle message, and for no
  other -/
  step0 : t0.st.oracles.size = t0.book.place.size
  step : tE.st.oracles.size = tE.book.place.size

/-- A yes of the test's decision leaves OutK3. -/
theorem k12_out3_of (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' →
      BaseSt t t' ∧ BaseBk t t')
    (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind X p : Blk').decide t0 rs gs = .ok tE) : OutK3 t0 tE := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok X p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := hX.front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ (hX.bat _ _ _ _ _ hbat)
  obtain ⟨G, hG, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have hne : rest ≠ [] := by
    intro e0
    subst e0
    unfold H2U.roundsOfNums at hr
    rw [hs] at hr
    cases hr
  obtain ⟨k, kstep⟩ := stages_book X p hX hB he ha rest 0 first _ _ tE _ _ hst
  have osz : (begun tF.st tF.g G).oracles.size = tF.st.oracles.size := closeLedgers_size _ _
  have k1 := k.rt
  have k2 := k.op
  have k3 := k.mono
  have k4 := kstep hne
  dsimp only at k1 k2 k3 k4
  rw [osz] at k2 k4
  exact ⟨k1, k3, k4, by omega⟩

/-- Of the variant proximityTestKind guardedProximityTestParts p. -/
theorem k12_out3 (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    OutK3 t0 tE :=
  k12_out3_of guardedProximityTestParts p (like_P5 p)
    (fun j cur cut t t' rs gs h => ⟨baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1,
      baseJ5_bk p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1⟩) he ha t0 tE rs gs h

/-- Of proximityTestKind proximityTestParts p (Join.lean's own parts). -/
theorem k12_out3_joined (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind K12.proximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    OutK3 t0 tE :=
  k12_out3_of K12.proximityTestParts p (like_joined p)
    (fun j cur cut t t' rs gs h => ⟨baseJ_st p j cur cut t t' rs gs h, baseJ_bk p j cur cut t t' rs
        gs h⟩)
    he ha t0 tE rs gs h

end H2K.Out
