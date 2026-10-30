-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/Fold.lean: The fold of the proximity test's parts
(`guardedProximityTestParts.fold`, Johnson/Desc/K12/JoinGuarded.lean) reads no row's target: at two records that agree but
for targets (`Agree`, Wipe.lean), at one list of rounds and one list of groups of columns, it
refuses with one word, or returns twice and the two records agree but for targets (`AlikeE wipeT`:
Johnson/Desc/ProofFile/Honest/K10/Wipe/Alike.lean). No premise but `Agree`.

  `foldD_none`   the library's fold on the ground's carried record (`First.Close.foldD`), in the arm
                 in which the fold's own first message brings the fresh mask: at the wiped record
                 and at the record. The other arm is the kind K10's authors' `foldD_wiped`, whose
                 proof this one follows line by line behind the message's entry
  `foldD_rel`    both arms, at two records and two claims that agree once wiped
  `lay_alike`, `back_alike`   how a part lays the record, its rounds and its columns into the plain
                 state, and lays the state back: FOR EVERY PART's WRAPPING
  `foldE_alike`, `newGroupE_alike`   the two calls of the part
  `foldJ_alike`  the part of Johnson/Desc/K12/Join.lean
  `fold_agree`   the statement, at `guardedProximityTestParts.fold`

Over what it stands. Files of the kind K10's authors that are not in the library yet
(Johnson/Desc/ProofFile/Honest/K10/: StAtZero, WipeFold, BatWipe, WipeS, Wipe/).

Limits. AT ONE LIST OF GROUPS: THIS IS NO LAW ON A FOLD AT MADE-UP COLUMNS THROUGH THE TEST'S BLOCK:
the columns are the same words on both sides. The fold alone, of the five parts that the prover's
text runs (front, batching, fold, switch, the batching behind the switch). The sixth part, the base
case, is not treated: by reading it tests a target's value; the verifier runs it, the prover's text
of the test never does. Nothing on what reads the record besides the parts. Nothing on completeness,
soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.Wipe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open OnBytes (E GroupRow SingleRows FoldShape foldOutput foldMaskNotice)
open VerifiableInference.Desc.First.Close (foldD)
open VerifiableInference.Desc.Ground (newGroupP recvL recvP spendAsMaskL spendAsMaskP)
open VerifiableInference.Desc.K12 (T12 Passing P12 guardedProximityTestParts foldJ lay back ranged stageAt)
open _root_.Desc.Plain (DState)
open ProofFile.Honest.K10 (wipeSt wipeG singleRowsWithZeroTarget wipeD wipeRD AlikeE ebind_same ebind_rel need_rel got_map
  foldShapeFits_wipe foldMaskFits_wipe foldRowFits_rel foldOutput_rel rounds_blind foldD_wiped
  recvL_wipe recvP_wipe spendAsMaskL_wipe spendAsMaskP_wipe newGroupP_rel wipeD_idem)

/-! ## 1 The library's fold, both arms -/

/-- **The fold on the carried record, where its own first message brings the fresh mask.** -/
theorem foldD_none {L : Type} (ft : ℕ) (d : DState L) (F : FoldShape) {row row' : GroupRow}
    (h : wipeG row' = wipeG row) (es : List Fmt.Entry) (rs : List Fmt.RoundView) :
    (foldD ft (wipeD d) F row' none es rs).map wipeRD =
      (foldD ft d F row none es rs).map wipeRD := by
  have e0 : recvL (wipeD d).st (wipeD d).book #[foldMaskNotice F] =
      recvL d.st d.book #[foldMaskNotice F] := recvL_wipe d.st d.book _
  unfold VerifiableInference.Desc.First.Close.foldD
  cases es with
  | nil => cases rs <;> rfl
  | cons eE eR =>
    cases rs with
    | nil => rfl
    | cons rE rR =>
      dsimp only
      refine ebind_same fun _ => ?_
      refine ebind_same fun _ => ?_
      refine need_rel (foldShapeFits_wipe d.st F) ?_
      simp only [pure_bind]
      rw [e0, recvP_wipe]
      refine ebind_same fun _ => ?_
      refine got_map (Prod.map id wipeD) fun x => ?_
      obtain ⟨ids, d1⟩ := x
      dsimp only [Prod.map, id]
      refine ebind_same fun fr => ?_
      have e1 : spendAsMaskL (wipeD d1).st fr = spendAsMaskL d1.st fr := spendAsMaskL_wipe d1.st fr
      refine need_rel (foldMaskFits_wipe d1.st F fr) ?_
      rw [e1, spendAsMaskP_wipe]
      refine ebind_same fun _ => ?_
      refine got_map wipeD fun d2 => ?_
      refine ebind_same fun y => ?_
      obtain ⟨l, eps⟩ := y
      rcases l with _ | ⟨sum, _ | ⟨s2, l⟩⟩
      · rfl
      · dsimp only
        refine need_rel (foldRowFits_rel d2.st F h) ?_
        refine ebind_rel (fun x : List E × E => x.1) (rounds_blind eR rR _ _) fun b b' hb => ?_
        obtain ⟨γ, c⟩ := b
        obtain ⟨γ', c'⟩ := b'
        have hγ : γ = γ' := hb
        subst hγ
        show (Except.ok (singleRowsWithZeroTarget (foldOutput (wipeSt d2.st) F row' fr eps γ c), wipeD (wipeD d2)) :
            Except String (SingleRows × DState L)) =
          Except.ok (singleRowsWithZeroTarget (foldOutput d2.st F row fr eps γ c'), wipeD d2)
        rw [foldOutput_rel d2.st F h fr eps γ c c', wipeD_idem]
      · rfl

/-- **Both arms, at two records and two claims that agree once wiped.** -/
theorem foldD_rel {L : Type} (ft : ℕ) {d d' : DState L} (hd : wipeD d = wipeD d') (F : FoldShape)
    {r r' : GroupRow} (hr : wipeG r = wipeG r') (mask : Option ℕ) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) :
    AlikeE wipeRD (foldD ft d F r mask es rs) (foldD ft d' F r' mask es rs) := by
  show (foldD ft d F r mask es rs).map wipeRD = (foldD ft d' F r' mask es rs).map wipeRD
  cases mask with
  | none =>
    rw [← foldD_none ft d F (rfl : wipeG r = wipeG r) es rs, hd]
    exact foldD_none ft d' F hr es rs
  | some fr =>
    rw [← foldD_wiped ft d F (rfl : wipeG r = wipeG r) fr es rs, hd]
    exact foldD_wiped ft d' F hr fr es rs

/-! ## 2 A part's wrapping -/

/-- The plain states that `lay` makes agree once wiped. -/
theorem lay_alike (p : P12) (cut : List Fmt.DeclaredRound) (last : Option Fmt.Entry) {t t' : T12}
    (ht : Agree t t') (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    wipePS (lay p cut last t rs gs) = wipePS (lay p cut last t' rs gs) := by
  have h1 : wipeSt t.st = wipeSt t'.st := congrArg (·.st) ht
  have h2 : t.book = t'.book := congrArg (·.book) ht
  have h3 : t.roots = t'.roots := congrArg (·.roots) ht
  unfold wipePS wipeD lay
  simp only [h1, h2, h3]

/-- The state laid back. -/
theorem back_alike {t t' : T12} (hg : t.g = t'.g) {s s' : H2K.PS} (hs : wipePS s = wipePS s')
    {x x' : Passing} (hx : wipeP x = wipeP x') (mask : Option ℕ) :
    AlikeE wipeT (back t s x mask) (back t' s' x' mask) := by
  have h1 : s.rounds = s'.rounds := congrArg (·.rounds) hs
  have h2 : s.entries = s'.entries := congrArg (·.entries) hs
  have h3 : s.d.opened = s'.d.opened := congrArg (·.d.opened) hs
  have h4 : wipeSt s.d.st = wipeSt s'.d.st := congrArg (·.d.st) hs
  have h5 : s.d.book = s'.d.book := congrArg (·.d.book) hs
  have h6 : s.d.roots = s'.d.roots := congrArg (·.d.roots) hs
  unfold back
  rw [h1, h2, h3]
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.ok ?_
  simp only [wipeT, h4, h5, h6, hg, hx]

/-! ## 3 The part's two calls -/

theorem foldE_alike (F : FoldShape) {r r' : GroupRow} (hr : wipeG r = wipeG r') (mask : Option ℕ)
    {s s' : H2K.PS} (hs : wipePS s = wipePS s') :
    AlikeE (fun x : SingleRows × H2K.PS => (singleRowsWithZeroTarget x.1, wipePS x.2)) (H2K.foldE F r mask s)
      (H2K.foldE F r' mask s') := by
  obtain ⟨q, d, rounds, entries, last, asked, later, cur⟩ := s
  obtain ⟨q', d', rounds', entries', last', asked', later', cur'⟩ := s'
  simp only [wipePS, H2K.PS.mk.injEq] at hs
  obtain ⟨rfl, hd, rfl, rfl, rfl, rfl, rfl, hcur⟩ := hs
  unfold H2K.foldE
  refine AlikeE.head' fun _ => AlikeE.head' fun _ => ?_
  have hD := foldD_rel q.firstTree hd F hr mask (entries.take (1 + F.layout.k))
    (rounds.take (1 + F.layout.k))
  refine AlikeE.bind' (w := wipeRD) ?_ fun x x' e => ?_
  · rcases hD.split with ⟨e, a, b⟩ | ⟨x, x', a, b, c⟩
    · rw [a, b]
      exact AlikeE.rfl'
    · rw [a, b]
      exact AlikeE.ok c
  · obtain ⟨e1, e2⟩ := Prod.mk.inj (e : (singleRowsWithZeroTarget x.1, wipeD x.2) = (singleRowsWithZeroTarget x'.1, wipeD x'.2))
    refine AlikeE.ok ?_
    simp only [wipePS, e1, e2, hcur]

theorem newGroupE_alike (a b : ℕ) {s s' : H2K.PS} (hs : wipePS s = wipePS s') :
    AlikeE (fun x : ℕ × H2K.PS => (x.1, wipePS x.2)) (H2K.newGroupE a b s)
      (H2K.newGroupE a b s') := by
  obtain ⟨q, d, rounds, entries, last, asked, later, cur⟩ := s
  obtain ⟨q', d', rounds', entries', last', asked', later', cur'⟩ := s'
  simp only [wipePS, H2K.PS.mk.injEq] at hs
  obtain ⟨rfl, hd, rfl, rfl, rfl, rfl, rfl, hcur⟩ := hs
  have h := newGroupP_rel hd a b
  unfold H2K.newGroupE
  cases e : newGroupP d a b with
  | none =>
    cases e' : newGroupP d' a b with
    | none => exact AlikeE.rfl'
    | some y => rw [e, e'] at h; cases h
  | some x =>
    cases e' : newGroupP d' a b with
    | none => rw [e, e'] at h; cases h
    | some y =>
      rw [e, e'] at h
      obtain ⟨e1, e2⟩ := Prod.mk.inj
        (Option.some.inj h : (x.1, wipeD x.2) = (y.1, wipeD y.2))
      refine AlikeE.ok ?_
      simp only [wipePS, e1, e2, hcur]

/-! ## 4 The part -/

/-- The part of Johnson/Desc/K12/Join.lean. -/
theorem foldJ_alike (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) {t t' : T12}
    (ht : Agree t t') (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    AlikeE wipeT ((foldJ p j cur cut).decide t rs gs) ((foldJ p j cur cut).decide t' rs gs) := by
  have hl := lay_alike p cut none ht rs gs
  have hg : t.g = t'.g := congrArg (·.g) ht
  have hm : t.mask = t'.mask := congrArg (·.mask) ht
  have hp : wipeP t.pass = wipeP t'.pass := congrArg (·.pass) ht
  unfold foldJ
  rcases pass_cases _ _ hp with ⟨a, b⟩ | ⟨r, r', L, a, b, hr⟩ | ⟨R, R', n, a, b, -⟩ |
    ⟨out, theta, n, a, b⟩
  · simp only [a, b]
    exact AlikeE.rfl'
  · cases stageAt p j cur with
    | none =>
      simp only [a, b]
      exact AlikeE.rfl'
    | some c =>
      cases p.idx[j + 1]? with
      | none =>
        simp only [a, b]
        exact AlikeE.rfl'
      | some n =>
        simp only [a, b]
        rw [← hm]
        refine AlikeE.bind' (foldE_alike _ hr t.mask hl) fun x x' ex => ?_
        obtain ⟨x1, x2⟩ := Prod.mk.inj
          (ex : (singleRowsWithZeroTarget x.1, wipePS x.2) = (singleRowsWithZeroTarget x'.1, wipePS x'.2))
        refine AlikeE.bind' (newGroupE_alike n.1 n.2 x2) fun y y' ey => ?_
        obtain ⟨y1, y2⟩ := Prod.mk.inj (ey : (y.1, wipePS y.2) = (y'.1, wipePS y'.2))
        refine back_alike hg y2 ?_ t.mask
        show Passing.single (singleRowsWithZeroTarget x.1) y.1 = Passing.single (singleRowsWithZeroTarget x'.1) y'.1
        rw [x1, y1]
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    exact AlikeE.rfl'

/-- **The fold of `guardedProximityTestParts` at two records that agree but for targets**: one word, or two records
that agree but for targets. -/
theorem fold_agree (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) {t t' : T12}
    (ht : Agree t t') (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    AlikeE wipeT ((guardedProximityTestParts.fold p j cur cut).decide t rs gs)
      ((guardedProximityTestParts.fold p j cur cut).decide t' rs gs) := by
  show AlikeE wipeT ((ranged cut (foldJ p j cur cut)).decide t rs gs)
    ((ranged cut (foldJ p j cur cut)).decide t' rs gs)
  unfold ranged
  exact AlikeE.head' fun _ => foldJ_alike p j cur cut ht rs gs

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.foldD_none
#print axioms ProofFile.Honest.K12.Blind.foldD_rel
#print axioms ProofFile.Honest.K12.Blind.lay_alike
#print axioms ProofFile.Honest.K12.Blind.back_alike
#print axioms ProofFile.Honest.K12.Blind.foldE_alike
#print axioms ProofFile.Honest.K12.Blind.newGroupE_alike
#print axioms ProofFile.Honest.K12.Blind.foldJ_alike
#print axioms ProofFile.Honest.K12.Blind.fold_agree
