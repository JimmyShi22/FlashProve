-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/Switch.lean: The switch of the proximity test's parts
(`guardedProximityTestParts.switch`, Johnson/Desc/K12/JoinGuarded.lean) reads no row's target: at two records that agree
but for targets (`Agree`, Wipe.lean), at one list of rounds and one list of groups of columns, it
refuses with one word, or returns twice and the two records agree but for targets. No premise but
`Agree`.

  `ground_one`   the two records of the seven ground functions are one: the test calls the sending
                 at the second name, the kind K10's authors' law on the sending stands at the first
  `guard9_rel`, `openOne9_wipe`, `symbolsAt_wipe`, `rowsSymbols_old`   what the step behind the
                 sending (Johnson/Top/H0/Tw/L9/Switch.lean) reads of the statement and of the
                 carried rows
  `wIn`, `readOld9_wipe`   the step's argument with the statement and the carried rows wiped; the
                 old rows read at the positions are THE SAME: book, columns left and symbols
  `joinS_wipe`, `joinS_rel`, `coefficient_wipe`, `addRowS_wipe`, `addRowS_rel`, `addRows9_rel`,
  `rowsMade_rel`, `inRun_rel`   a message joins a group; a row's coefficient at a place; a row is
                 added; the new rows; whether a group's test has begun
  `wOut9`, `behind9_wiped`, `behind9_rel`   the step behind the sending
  `switchE_alike`, `switchJ_alike`, `switch_agree`   the part

Over what it stands. Files of the kind K10's authors that are not in the library yet
(Johnson/Desc/ProofFile/Honest/K10/: StAtZero, WipeFold, BatWipe, WipeS, Wipe/).

Limits. AT ONE LIST OF GROUPS: THIS IS NO LAW ON A FOLD AT MADE-UP COLUMNS THROUGH THE TEST'S BLOCK:
the columns are the same words on both sides. That is why what is read off the columns is equal
here, not only of one size. The switch alone, of the five parts that the prover's text runs. Values
of coefficients are tested on this road (a row may read no pad): they are held equal by `Agree`.
Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.Fold
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open OnBytes (E Statement Row TreeBook Positions Column SingleRows SwitchTarget Switched
  OracleNotice)
open VerifiableInference.Desc.Own (Opened symbolsAt rowsSymbols shapeFits)
open VerifiableInference.Desc.K12 (T12 Passing P12 guardedProximityTestParts switchJ lay back ranged stageAt)
open ProofFile.Honest.K10 (wipeRow wipeSt wipeG singleRowsWithZeroTarget wipeD wipeOr wipeGr AlikeE wipeSt_idem
  wipeSt_oracle_at wipeSt_group_at wipeSt_size wipeSt_modifyO told_wipe targetL_rel rowsFrom_old
  singleRowsOracles_old joined_wipe withRow_wipe placeFits_wipe tableBits_wipe pad_at_wipe
  rowsCan_rel swRows_rel getDRel sendP_rel wSend5 alikeFoldA alikeIfLet alikeIte omapSplit
  st_of_wipeD shutO)

/-! ## 1 The sending -/

/-- The two records of the seven ground functions are one. -/
theorem ground_one {L : Type} :
    (VerifiableInference.Desc.Ground.groundG : Desc.Plain.Ground L) = Desc.Plain.groundG := rfl

/-! ## 2 The leaves -/

theorem guard9_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') {old old' : SingleRows}
    (ho : singleRowsWithZeroTarget old = singleRowsWithZeroTarget old') (T : SwitchTarget) :
    Tw.L9.switchGuard S old T = Tw.L9.switchGuard S' old' T := by
  unfold Tw.L9.switchGuard Tw.K2.targetOk
  rw [targetL_rel hS ho T]

/-- The opening of one tree reads of the statement, at a message, its shape's count of answers and
its groups. -/
theorem openOne9_wipe (S : Statement) : Tw.L9.openOne (wipeSt S) = Tw.L9.openOne S := by
  funext ft pos B0 t s
  unfold Tw.L9.openOne
  simp only [told_wipe]

/-- What a message holds at the positions: of the statement the message's shape alone. -/
theorem symbolsAt_wipe (S : Statement) (B : TreeBook) (pos : Positions) (cols : List Opened)
    (o : ℕ) (pl : ℕ × ℕ) : symbolsAt (wipeSt S) B pos cols o pl = symbolsAt S B pos cols o pl := by
  unfold VerifiableInference.Desc.Own.symbolsAt
  rw [wipeSt_oracle_at]
  cases B.trees[pl.1]? <;> cases S.oracles[o]? <;> cases cols.find? (·.1 == pl.1) <;> rfl

theorem rowsSymbols_old (s : SingleRows) (opened : Array (Array Column)) (n : ℕ) :
    rowsSymbols (singleRowsWithZeroTarget s) opened n = rowsSymbols s opened n := by
  have e : shapeFits (singleRowsWithZeroTarget s) = shapeFits s := by
    unfold VerifiableInference.Desc.Own.shapeFits
    rfl
  unfold VerifiableInference.Desc.Own.rowsSymbols
  rw [e, rowsFrom_old]

/-- The step's argument: the statement and the carried rows wiped; the columns stay. -/
def wIn (i : Tw.L9.SwIn) : Tw.L9.SwIn := { i with st := wipeSt i.st, old := singleRowsWithZeroTarget i.old }

/-- **The old rows read at the positions are the same**: book, columns left and symbols. -/
theorem readOld9_wipe (i : Tw.L9.SwIn) (pos : Positions) :
    Tw.L9.readOld (wIn i) pos = Tw.L9.readOld i pos := by
  obtain ⟨st, book, ft, opened, old, T, grp, ids, entry, settled, drawn, itemsLeft⟩ := i
  unfold Tw.L9.readOld wIn
  dsimp only
  rw [singleRowsOracles_old, openOne9_wipe]
  simp only [symbolsAt_wipe, rowsSymbols_old]

/-- A message joins a group. -/
theorem joinS_wipe (S : Statement) (g o : ℕ) (kept : Bool) :
    Tw.L9.joinS (wipeSt S) g o kept = (Tw.L9.joinS S g o kept).map wipeSt := by
  unfold Tw.L9.joinS
  rw [wipeSt_group_at, wipeSt_oracle_at]
  cases S.groups[g]? with
  | none => cases S.oracles[o]? <;> rfl
  | some G =>
    cases S.oracles[o]? with
    | none => rfl
    | some x =>
      dsimp only [Option.map, wipeOr, wipeGr]
      split_ifs
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact congrArg Except.ok (joined_wipe S g o kept G)

theorem joinS_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (g o : ℕ) (kept : Bool) :
    AlikeE wipeSt (Tw.L9.joinS S g o kept) (Tw.L9.joinS S' g o kept) := by
  show (Tw.L9.joinS S g o kept).map wipeSt = (Tw.L9.joinS S' g o kept).map wipeSt
  rw [← joinS_wipe, ← joinS_wipe, hS]

/-- A row's coefficient at a place reads no target. -/
theorem coefficient_wipe (row : Row) : (wipeRow row).coefficient = row.coefficient := by
  funext o part i
  unfold OnBytes.Row.coefficient
  rfl

/-- A row is added to a group. -/
theorem addRowS_wipe (S : Statement) (g : ℕ) (row : Row) :
    Tw.L9.addRowS (wipeSt S) g (wipeRow row) = (Tw.L9.addRowS S g row).map wipeSt := by
  unfold Tw.L9.addRowS
  rw [wipeSt_group_at]
  cases S.groups[g]? with
  | none => rfl
  | some G =>
    simp only [Option.map_some, placeFits_wipe, tableBits_wipe, pad_at_wipe, coefficient_wipe]
    dsimp only [wipeRow, wipeGr]
    split_ifs
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact congrArg Except.ok (withRow_wipe S g row)

theorem addRowS_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (g : ℕ) {r r' : Row}
    (hr : wipeRow r = wipeRow r') :
    AlikeE wipeSt (Tw.L9.addRowS S g r) (Tw.L9.addRowS S' g r') := by
  show (Tw.L9.addRowS S g r).map wipeSt = (Tw.L9.addRowS S' g r').map wipeSt
  rw [← addRowS_wipe, ← addRowS_wipe, hS, hr]

/-- Rows are added one after the other: at two lists that agree but for targets. -/
theorem addRows9_rel (g : ℕ) : ∀ (l l' : List Row), l.map wipeRow = l'.map wipeRow →
    ∀ S S' : Statement, wipeSt S = wipeSt S' →
      AlikeE wipeSt (l.foldlM (fun S r => Tw.L9.addRowS S g r) S)
        (l'.foldlM (fun S r => Tw.L9.addRowS S g r) S')
  | [], [], _, _, _, hS => AlikeE.ok hS
  | [], _ :: _, h, _, _, _ => by cases h
  | _ :: _, [], h, _, _, _ => by cases h
  | r :: l, r' :: l', h, S, S', hS => by
    obtain ⟨h1, h2⟩ := List.cons.inj (h : wipeRow r :: l.map wipeRow = wipeRow r' :: l'.map wipeRow)
    rw [List.foldlM_cons, List.foldlM_cons]
    exact AlikeE.bind' (addRowS_rel hS g h1) fun c c' hc => addRows9_rel g l l' h2 c c' hc

/-- The new rows: none on both sides, or lists that part at most in their targets. -/
theorem rowsMade_rel {S S' : Statement} (hS : wipeSt S' = wipeSt S) (old : SingleRows)
    (T : SwitchTarget) (g : ℕ) (anew : Array ℕ) (pos : Positions) (y : Array E) :
    (Tw.K2.rowsMade S' (singleRowsWithZeroTarget old) T g anew pos y).map (List.map wipeRow) =
      (Tw.K2.rowsMade S old T g anew pos y).map (List.map wipeRow) := by
  unfold Tw.K2.rowsMade
  rw [rowsCan_rel hS old T anew pos (rfl : y.size = y.size)]
  cases Tw.K2.rowsCan S old T anew pos y with
  | false => rfl
  | true =>
    exact congrArg some (getDRel wipeRow (swRows_rel hS old T g anew pos (rfl : y.size = y.size)))

/-! ## 3 The step behind the sending -/

/-- What the step returns, its statement wiped. -/
def wOut9 (o : Tw.L9.SwOut) : Tw.L9.SwOut := { o with st := wipeSt o.st }

/-- Whether a group's test has begun is one at two statements that agree but for targets. -/
theorem inRun_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (g : ℕ) :
    (S.groups[g]?).map (·.inRun) = (S'.groups[g]?).map (·.inRun) := by
  have k : ∀ Z : Statement, ((wipeSt Z).groups[g]?).map (·.inRun) = (Z.groups[g]?).map (·.inRun) :=
    fun Z => by
      rw [wipeSt_group_at]
      cases Z.groups[g]? <;> rfl
  rw [← k S, ← k S', hS]

theorem behind9_wiped (i : Tw.L9.SwIn) :
    AlikeE wOut9 (Tw.L9.switchBehind (wIn i)) (Tw.L9.switchBehind i) := by
  have hR := fun pos => readOld9_wipe i pos
  obtain ⟨st, book, ft, opened, old, T, grp, ids, entry, settled, drawn, itemsLeft⟩ := i
  have hC : (wipeSt st).codes = st.codes := rfl
  have hO : (singleRowsWithZeroTarget old).code = old.code := rfl
  unfold Tw.L9.switchBehind
  dsimp only [wIn] at hR ⊢
  rw [hC, hO]
  cases st.codes.base[old.code]? with
  | none => exact AlikeE.error _
  | some c0 =>
    dsimp only
    refine AlikeE.head' fun code => ?_
    refine AlikeE.head_eq' rfl fun pos => ?_
    rw [hR pos]
    refine AlikeE.head' fun z => ?_
    obtain ⟨B, left, y⟩ := z
    dsimp only
    refine alikeIfLet ?_ (AlikeE.ok (wipeSt_idem st)) fun S1' S1 h1 => ?_
    · simp only [wipeSt_size]
      refine alikeIte (AlikeE.ok ?_) (AlikeE.error _)
      exact (congrArg wipeSt (wipeSt_modifyO st (ids.getD 0 OnBytes.noId) shutO shutO
        fun _ => rfl)).trans (wipeSt_idem _)
    refine AlikeE.bind' (joinS_rel h1 _ _ _) fun S2' S2 h2 => ?_
    refine AlikeE.bind' (alikeFoldA wipeSt _ _
      (fun b b' p hb => joinS_rel hb grp p.1 p.2.keptAgain) _ h2) fun S3' S3 h3 => ?_
    have hG := inRun_rel h3 grp
    have hM := rowsMade_rel h3 old T (ids.getD 0 OnBytes.noId)
      (ids.extract 1 (1 + T.kept.size)) pos y
    cases e : S3'.groups[grp]? with
    | none =>
      cases e' : S3.groups[grp]? with
      | none => exact AlikeE.error _
      | some G => rw [e, e'] at hG; cases hG
    | some G' =>
      cases e' : S3.groups[grp]? with
      | none => rw [e, e'] at hG; cases hG
      | some G =>
        rw [e, e'] at hG
        have hg : G'.inRun = G.inRun := Option.some.inj hG
        dsimp only
        rw [hg]
        by_cases hr : G.inRun = true
        · rw [if_pos hr, if_pos hr]
          exact AlikeE.error _
        · rw [if_neg hr, if_neg hr]
          refine AlikeE.head' fun _ => ?_
          rcases omapSplit hM with ⟨a, b⟩ | ⟨l', l, a, b, hl⟩
          · rw [a, b]
            exact AlikeE.error _
          · rw [a, b]
            dsimp only
            refine AlikeE.bind' (w := List.map wipeRow) (AlikeE.ok hl) fun l₁' l₁ hl₁ => ?_
            refine AlikeE.bind' (addRows9_rel grp l₁' l₁ hl₁ S3' S3 h3) fun S4' S4 h4 => ?_
            refine AlikeE.ok ?_
            unfold wOut9
            simp only [h4]

theorem behind9_rel {i i' : Tw.L9.SwIn} (h : wIn i = wIn i') :
    AlikeE wOut9 (Tw.L9.switchBehind i) (Tw.L9.switchBehind i') := by
  have a := behind9_wiped i
  rw [h] at a
  exact a.symm.trans (behind9_wiped i')

/-! ## 4 The part -/

theorem switchE_alike {old old' : SingleRows} (ho : singleRowsWithZeroTarget old = singleRowsWithZeroTarget old') (T : SwitchTarget)
    (n : ℕ) (others : Array OracleNotice) (b : Bool) {s s' : H2K.PS} (hs : wipePS s = wipePS s') :
    AlikeE (fun x : (Switched × E) × H2K.PS => (x.1, wipePS x.2)) (H2K.switchE old T n others b s)
      (H2K.switchE old' T n others b s') := by
  obtain ⟨q, d, rounds, entries, last, asked, later, cur⟩ := s
  obtain ⟨q', d', rounds', entries', last', asked', later', cur'⟩ := s'
  simp only [wipePS, H2K.PS.mk.injEq] at hs
  obtain ⟨rfl, hd, rfl, rfl, rfl, rfl, rfl, hcur⟩ := hs
  have hst : wipeSt d.st = wipeSt d'.st := st_of_wipeD hd
  unfold H2K.switchE
  rcases entries with _ | ⟨e₁, _ | ⟨e₂, es⟩⟩
  · exact AlikeE.rfl'
  · exact AlikeE.rfl'
  rcases rounds with _ | ⟨r₁, _ | ⟨r₂, rs⟩⟩
  · exact AlikeE.rfl'
  · exact AlikeE.rfl'
  dsimp only
  rw [guard9_rel hst ho T, ground_one]
  iterate 9 refine AlikeE.head' fun _ => ?_
  have hP := sendP_rel q false hd (Tw.L9.switchNotices T others) r₁ r₂
  refine AlikeE.bind' (w := wSend5) ?_ fun x x' hx => ?_
  · rcases omapSplit hP with ⟨a, c⟩ | ⟨x, x', a, c, e⟩
    · rw [a, c]
      exact AlikeE.rfl'
    · rw [a, c]
      exact AlikeE.ok e
  obtain ⟨ids, a1, a2, took, d₂⟩ := x
  obtain ⟨ids', a1', a2', took', d₂'⟩ := x'
  have hx' : (ids, a1, a2, took, wipeD d₂) = (ids', a1', a2', took', wipeD d₂') := hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, -, -, rfl, h2⟩ := hx'
  have k1 : wipeSt d₂.st = wipeSt d₂'.st := st_of_wipeD h2
  have k2 : d₂.book = d₂'.book := congrArg (·.book) h2
  have k3 : d₂.opened = d₂'.opened := congrArg (·.opened) h2
  have k4 : d₂.roots = d₂'.roots := congrArg (·.roots) h2
  dsimp only
  have hW : wIn ⟨d₂.st, d₂.book, q.firstTree, d₂.opened, old, T, n, ids,
      { e₂ with name := "LOC", drawE := 0 }, true, { r₂.drawn with elems := [] },
      r₂.vals.length - took⟩ =
    wIn ⟨d₂'.st, d₂'.book, q.firstTree, d₂'.opened, old', T, n, ids,
      { e₂ with name := "LOC", drawE := 0 }, true, { r₂.drawn with elems := [] },
      r₂.vals.length - took⟩ := by
    simp only [wIn, k1, k2, k3, ho]
  have hB := behind9_rel hW
  have hE : AlikeE wOut9
      (Except.mapError (fun x => "switch " ++ x) (Tw.L9.switchBehind ⟨d₂.st, d₂.book, q.firstTree,
        d₂.opened, old, T, n, ids, { e₂ with name := "LOC", drawE := 0 }, true,
        { r₂.drawn with elems := [] }, r₂.vals.length - took⟩))
      (Except.mapError (fun x => "switch " ++ x) (Tw.L9.switchBehind ⟨d₂'.st, d₂'.book,
        q.firstTree, d₂'.opened, old', T, n, ids, { e₂ with name := "LOC", drawE := 0 }, true,
        { r₂.drawn with elems := [] }, r₂.vals.length - took⟩)) := by
    rcases hB.split with ⟨e, a, c⟩ | ⟨o, o', a, c, e⟩
    · rw [a, c]
      exact AlikeE.rfl'
    · rw [a, c]
      exact AlikeE.ok e
  cases r₂.drawn.elems with
  | nil => exact AlikeE.error _
  | cons x l =>
    cases l with
    | cons _ _ => exact AlikeE.error _
    | nil =>
      dsimp only
      refine AlikeE.head' fun y => ?_
      refine AlikeE.bind' hE fun o o' ho' => ?_
      have m1 : wipeSt o.st = wipeSt o'.st := congrArg (·.st) ho'
      have m2 : o.book = o'.book := congrArg (·.book) ho'
      have m3 : o.opened = o'.opened := congrArg (·.opened) ho'
      have m4 : o.out = o'.out := congrArg (·.out) ho'
      refine AlikeE.ok ?_
      simp only [wipePS, wipeD, m1, m2, m3, m4, k4, hcur]

/-- The part of Johnson/Desc/K12/Join.lean. -/
theorem switchJ_alike (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) {t t' : T12} (ht : Agree t t') (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) :
    AlikeE wipeT ((switchJ p j cur next last cut).decide t rs gs)
      ((switchJ p j cur next last cut).decide t' rs gs) := by
  have hl := lay_alike p cut none ht rs gs
  have hg : t.g = t'.g := congrArg (·.g) ht
  have hm : t.mask = t'.mask := congrArg (·.mask) ht
  have hp : wipeP t.pass = wipeP t'.pass := congrArg (·.pass) ht
  unfold switchJ
  rcases pass_cases _ _ hp with ⟨a, b⟩ | ⟨r, r', L, a, b, -⟩ | ⟨R, R', n, a, b, hR⟩ |
    ⟨out, theta, n, a, b⟩
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    exact AlikeE.rfl'
  · cases stageAt p (j + 1) next with
    | none =>
      simp only [a, b]
      exact AlikeE.rfl'
    | some c =>
      simp only [a, b]
      rw [← hm]
      refine AlikeE.bind' (switchE_alike hR _ n _ true hl) fun x x' ex => ?_
      obtain ⟨x1, x2⟩ := Prod.mk.inj (ex : (x.1, wipePS x.2) = (x'.1, wipePS x'.2))
      rw [x1]
      exact back_alike hg x2 rfl t.mask
  · simp only [a, b]
    exact AlikeE.rfl'

/-- **The switch of `guardedProximityTestParts` at two records that agree but for targets**: one word, or two records
that agree but for targets. -/
theorem switch_agree (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) {t t' : T12} (ht : Agree t t') (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) :
    AlikeE wipeT ((guardedProximityTestParts.switch p j cur next last cut).decide t rs gs)
      ((guardedProximityTestParts.switch p j cur next last cut).decide t' rs gs) := by
  show AlikeE wipeT ((ranged cut (switchJ p j cur next last cut)).decide t rs gs)
    ((ranged cut (switchJ p j cur next last cut)).decide t' rs gs)
  unfold ranged
  exact AlikeE.head' fun _ => switchJ_alike p j cur next last cut ht rs gs

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.ground_one
#print axioms ProofFile.Honest.K12.Blind.guard9_rel
#print axioms ProofFile.Honest.K12.Blind.openOne9_wipe
#print axioms ProofFile.Honest.K12.Blind.symbolsAt_wipe
#print axioms ProofFile.Honest.K12.Blind.rowsSymbols_old
#print axioms ProofFile.Honest.K12.Blind.wIn
#print axioms ProofFile.Honest.K12.Blind.readOld9_wipe
#print axioms ProofFile.Honest.K12.Blind.joinS_wipe
#print axioms ProofFile.Honest.K12.Blind.joinS_rel
#print axioms ProofFile.Honest.K12.Blind.coefficient_wipe
#print axioms ProofFile.Honest.K12.Blind.addRowS_wipe
#print axioms ProofFile.Honest.K12.Blind.addRowS_rel
#print axioms ProofFile.Honest.K12.Blind.addRows9_rel
#print axioms ProofFile.Honest.K12.Blind.rowsMade_rel
#print axioms ProofFile.Honest.K12.Blind.wOut9
#print axioms ProofFile.Honest.K12.Blind.inRun_rel
#print axioms ProofFile.Honest.K12.Blind.behind9_wiped
#print axioms ProofFile.Honest.K12.Blind.behind9_rel
#print axioms ProofFile.Honest.K12.Blind.switchE_alike
#print axioms ProofFile.Honest.K12.Blind.switchJ_alike
#print axioms ProofFile.Honest.K12.Blind.switch_agree
