-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/Bat.lean: the two batchings of a proximity test (the kind
K12), as the verifier's own text decides them (`guardedProximityTestParts.bat`, `guardedProximityTestParts.batBehind`,
Johnson/Desc/K12/JoinGuarded.lean), at two records that agree but for the targets of their rows (`Agree`,
Wipe.lean in this folder): both refuse with one word, or both return, and the two records behind
agree but for targets. No premise but `Agree`. Statements and proofs; one definition (`wipeCs`).

  `bat_agree`         the batching in front of the first fold
  `batBehind_agree`   the batching behind a switch
  `layout_wipe`, `placeOk_wipe`, `groupOkB_wipe`, `rowInB_wipe`, `combineAt_wipe`, `codesFit_wipe`,
  `anyGroup_wipe`, `seatOf_wipe`   each function that the kind's own guards call is one at a
                 statement and at that statement with every target set to zero
  `combOk_wipe`, `noKept_wipe`, `gpOk_wipe`, `labelsOk_wipe`   so are the guards (c), (k), (g) at a
                 record; `entered_wipe`, `gpOf_wipe` on the way; the four `…_agree` at two records
  `bat_rel`, `batE_alike`, `batJ_alike`, `wipeCs`, `csTail_alike`   the steps beneath
  `entered_aux`   a helper

What for. The prover's text of a proximity test advances a record by these decisions, and keeps the
record before where one refuses. With the like for the front, the fold and the switch it follows
that the text shows the same at two states on entry that agree but for targets (Top.lean and
All.lean in this folder).

By what. Of the authors of the kind K10 (Johnson/Desc/ProofFile/Honest/K10/): `bat_alike`
(Wipe/KeepK10.lean); `batch_wipe`, `begun_wipe`, `runRows_wipe`, `has_wipe`, `rowBits_wipe`,
`tableBits_wipe`, `wipeSt_group_at`, `wipeSt_oracle_at`, `wipeSt_size` (BatWipe.lean); `recvP_wipe`,
`beginRunP_rel` (Wipe/WipeGround.lean); the calculus `AlikeE` (Wipe/Alike.lean). Of this folder:
`pass_cases` (Wipe.lean); `lay_alike`, `back_alike` (Fold.lean).

Over what it stands. Files of the kind K10's authors that are not in the library yet
(Johnson/Desc/ProofFile/Honest/K10/: StAtZero, WipeFold, BatWipe, WipeS, Wipe/Alike, Wipe/WipeLaws,
Wipe/WipeGround, Wipe/KeepK10), and this folder's Wipe.lean and Fold.lean.

Limits.
- AT ONE LIST OF GROUPS: this is no law on a fold at made-up columns through the test's block.
- The base case is not treated. By reading it is the one part of the test that tests a target's
  value. The verifier runs it; the prover's text of the test (Test.lean in the folder above) never
  does.
- Nothing on what a record or a row means. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open OnBytes (Statement Row GroupRow GroupLayout TreeBook Switched E RunInput)
open OnBytes.Params (IoppStage)
open OnBytes.Means (groupOkB rowInB combineFrameAt combineRowsAt combineAt)
open OnBytes.Slice (runRows begun)
open VerifiableInference.Desc.Ground (recvP beginRunP)
open VerifiableInference.Desc.First.Close (bat)
open VerifiableInference.Desc.Own (batch)
open VerifiableInference.Desc.Test (csTest)
open VerifiableInference.Desc.K12 (T12 Passing P12 guardedProximityTestParts batJ behindJ codesFit combOk noKept lay
  back ranged)
open _root_.Desc.Plain (DState)
open ProofFile.Honest.K10 (wipeRow wipeSt wipeOr wipeGr wipeG wipeD wipeB wipeRun AlikeE bat_alike
  batch_wipe begun_wipe runRows_wipe has_wipe rowBits_wipe tableBits_wipe wipeSt_group_at
  wipeSt_oracle_at wipeSt_size recvP_wipe beginRunP_rel)

/-! ## 1 At a statement: the functions that the kind's own guards call -/

/-- The layout of a group. -/
theorem layout_wipe (S : Statement) (g : ℕ) : (wipeSt S).layout g = S.layout g := by
  unfold OnBytes.Statement.layout
  rw [wipeSt_group_at, has_wipe, rowBits_wipe]
  cases S.groups[g]? <;> rfl

/-- A summand fits its place. -/
theorem placeOk_wipe (S : Statement) (G : OnBytes.Group) :
    OnBytes.Blk.placeOk (wipeSt S) (wipeGr G) = OnBytes.Blk.placeOk S G := by
  funext o part vars index
  unfold OnBytes.Blk.placeOk
  rw [has_wipe, tableBits_wipe]
  rfl

/-- The group is in order. -/
theorem groupOkB_wipe (S : Statement) (G : OnBytes.Group) :
    groupOkB (wipeSt S) (wipeGr G) = groupOkB S G := by
  unfold groupOkB
  rw [wipeSt_size]
  refine congrArg₂ (· && ·) rfl (congrArg (List.all G.members.toList) (funext fun o => ?_))
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- Each summand of the row is on a member's table. -/
theorem rowInB_wipe (S : Statement) (G : OnBytes.Group) (row : Row) :
    rowInB (wipeSt S) (wipeGr G) (wipeRow row) = rowInB S G row := by
  unfold rowInB
  rw [placeOk_wipe, tableBits_wipe]
  rfl

/-- All conditions of the law of the batching. -/
theorem combineAt_wipe (S : Statement) (g : ℕ) (L : GroupLayout) (rows : Array Row) :
    combineAt (wipeSt S) g ⟨L, rows.map wipeRow⟩ = combineAt S g ⟨L, rows⟩ := by
  unfold combineAt combineFrameAt combineRowsAt
  rw [wipeSt_group_at, layout_wipe]
  cases S.groups[g]? with
  | none => rfl
  | some G =>
    have hf : ((rows.map wipeRow).toList.filter (rowInB (wipeSt S) (wipeGr G))).length =
        (rows.toList.filter (rowInB S G)).length := by
      rw [Array.toList_map, List.filter_map, List.length_map]
      exact congrArg (fun f => (rows.toList.filter f).length)
        (funext fun r => rowInB_wipe S G r)
    have hs : (rows.map wipeRow).size = rows.size := Array.size_map
    cases S.layout g with
    | none => rfl
    | some L' =>
      show (groupOkB (wipeSt S) (wipeGr G) && OnBytes.Means.layoutEqB L' L &&
          ((rows.map wipeRow).toList.filter (rowInB (wipeSt S) (wipeGr G))).length ==
            (rows.map wipeRow).size) =
        (groupOkB S G && OnBytes.Means.layoutEqB L' L &&
          (rows.toList.filter (rowInB S G)).length == rows.size)
      rw [groupOkB_wipe, hf, hs]

/-- Guard (w). -/
theorem codesFit_wipe (p : P12) (S : Statement) : codesFit p (wipeSt S) = codesFit p S := rfl

/-- Guard (x), and every test on a group that does not read its rows. -/
theorem anyGroup_wipe (S : Statement) (g : ℕ) (f : OnBytes.Group → Bool)
    (hf : ∀ G, f (wipeGr G) = f G) : ((wipeSt S).groups[g]?).any f = (S.groups[g]?).any f := by
  rw [wipeSt_group_at]
  cases S.groups[g]? with
  | none => rfl
  | some G => exact hf G

/-- An oracle message as a part of a tree. -/
theorem seatOf_wipe (S : Statement) (book : TreeBook) (id : ℕ) :
    H2K.First.seatOf (wipeSt S) book id = H2K.First.seatOf S book id := by
  unfold H2K.First.seatOf
  rw [wipeSt_oracle_at]
  cases S.oracles[id]? <;> rfl

/-! ## 2 At a record: the guards (c), (k), (g) -/

theorem combOk_wipe (t : T12) : combOk (wipeT t) = combOk t := by
  obtain ⟨st, book, roots, g, pass, mask⟩ := t
  unfold combOk wipeT
  dsimp only
  rw [wipeSt_group_at, layout_wipe]
  cases st.groups[g]? with
  | none => rfl
  | some G0 =>
    cases st.layout g with
    | none => rfl
    | some Ly =>
      show combineAt (begun (wipeSt st) g (wipeGr G0)) g ⟨Ly, runRows (wipeSt st) (wipeGr G0)⟩ =
        combineAt (begun st g G0) g ⟨Ly, runRows st G0⟩
      rw [begun_wipe, runRows_wipe, combineAt_wipe]

theorem noKept_wipe (t : T12) : noKept (wipeT t) = noKept t := by
  obtain ⟨st, book, roots, g, pass, mask⟩ := t
  cases pass <;> rfl

/-- A value of `recvP`, read as `entered` reads it. -/
theorem entered_aux (r : Option (Array ℕ × DState Unit)) :
    ((r.map (Prod.map id wipeD)).bind fun x => (x.1[0]?).map fun id => (id, x.2.st, x.2.book)) =
      (r.bind fun x => (x.1[0]?).map fun id => (id, x.2.st, x.2.book)).map
        fun e => (e.1, wipeSt e.2.1, e.2.2) := by
  cases r with
  | none => rfl
  | some x =>
    obtain ⟨a, d⟩ := x
    show (a[0]?).map (fun id => (id, wipeSt d.st, d.book)) =
      ((a[0]?).map fun id => (id, d.st, d.book)).map fun e => (e.1, wipeSt e.2.1, e.2.2)
    cases a[0]? <;> rfl

theorem entered_wipe (p : P12) (t : T12) (cu : IoppStage) (L : GroupLayout) :
    H2K.First.entered p (wipeT t) cu L =
      (H2K.First.entered p t cu L).map fun e => (e.1, wipeSt e.2.1, e.2.2) := by
  obtain ⟨st, book, roots, g, pass, mask⟩ := t
  cases mask with
  | some id => rfl
  | none =>
    show ((recvP p.nums.firstTree (wipeD (⟨st, book, roots, [], ()⟩ : DState Unit)) _).bind
      fun x => (x.1[0]?).map fun id => (id, x.2.st, x.2.book)) = _
    rw [recvP_wipe]
    exact entered_aux _

theorem gpOf_wipe (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) :
    H2K.First.gpOf p (wipeT t) a L =
      (H2K.First.gpOf p t a L).map fun D => { D with st := wipeSt D.st } := by
  unfold H2K.First.gpOf
  cases VerifiableInference.Desc.K12.stageAt p 0 a with
  | none => rfl
  | some cu =>
    show (H2K.First.entered p (wipeT t) cu L).bind _ =
      ((H2K.First.entered p t cu L).bind _).map _
    rw [entered_wipe]
    cases H2K.First.entered p t cu L with
    | none => rfl
    | some e =>
      obtain ⟨id, st', bk⟩ := e
      have hs : H2K.First.seatOf (wipeSt st') bk = H2K.First.seatOf st' bk :=
        funext fun i => seatOf_wipe st' bk i
      show ((L.members.toList.mapM (H2K.First.seatOf (wipeSt st') bk)).bind fun ms =>
          (H2K.First.seatOf (wipeSt st') bk id).map _) =
        ((L.members.toList.mapM (H2K.First.seatOf st' bk)).bind fun ms =>
          (H2K.First.seatOf st' bk id).map _).map _
      rw [hs]
      cases L.members.toList.mapM (H2K.First.seatOf st' bk) with
      | none => rfl
      | some ms => cases H2K.First.seatOf st' bk id <;> rfl

theorem gpOk_wipe (p : P12) (t : T12) : H2K.First.gpOk p (wipeT t) = H2K.First.gpOk p t := by
  obtain ⟨st, book, roots, g, pass, mask⟩ := t
  unfold H2K.First.gpOk H2K.First.gpAll
  cases p.nums.stages with
  | nil => rfl
  | cons a rest =>
    cases pass with
    | nothing => rfl
    | single _ _ => rfl
    | switched _ _ _ => rfl
    | claim row L =>
      have h := gpOf_wipe p ⟨st, book, roots, g, .claim row L, mask⟩ a L
      dsimp only [wipeT, wipeP] at h ⊢
      rw [h]
      cases H2K.First.gpOf p ⟨st, book, roots, g, .claim row L, mask⟩ a L <;> rfl

theorem labelsOk_wipe (p : P12) (t : T12) :
    H2K.First.labelsOk p (wipeT t) = H2K.First.labelsOk p t := by
  obtain ⟨st, book, roots, g, pass, mask⟩ := t
  unfold H2K.First.labelsOk H2K.First.labelsL
  cases p.nums.stages with
  | nil => rfl
  | cons a rest =>
    cases pass with
    | nothing => rfl
    | single _ _ => rfl
    | switched _ _ _ => rfl
    | claim row L =>
      have h := gpOf_wipe p ⟨st, book, roots, g, .claim row L, mask⟩ a L
      dsimp only [wipeT, wipeP] at h ⊢
      rw [h]
      cases H2K.First.gpOf p ⟨st, book, roots, g, .claim row L, mask⟩ a L <;> rfl

theorem combOk_agree {t t' : T12} (h : Agree t t') : combOk t = combOk t' := by
  rw [← combOk_wipe t, ← combOk_wipe t', h]

theorem noKept_agree {t t' : T12} (h : Agree t t') : noKept t = noKept t' := by
  rw [← noKept_wipe t, ← noKept_wipe t', h]

theorem gpOk_agree (p : P12) {t t' : T12} (h : Agree t t') :
    H2K.First.gpOk p t = H2K.First.gpOk p t' := by
  rw [← gpOk_wipe p t, ← gpOk_wipe p t', h]

theorem labelsOk_agree (p : P12) {t t' : T12} (h : Agree t t') :
    H2K.First.labelsOk p t = H2K.First.labelsOk p t' := by
  rw [← labelsOk_wipe p t, ← labelsOk_wipe p t', h]

/-! ## 3 The batching -/

/-- The batching's text at two statements that are one once wiped. -/
theorem bat_rel {S S' : Statement} (h : wipeSt S = wipeSt S') (g : ℕ) (e : Fmt.Entry)
    (r : Fmt.RoundView) : AlikeE wipeB (bat S g e r) (bat S' g e r) :=
  (bat_alike S g e r).symm.trans ((congrArg (fun X => (bat X g e r).map wipeB) h).trans
    (bat_alike S' g e r))

theorem batE_alike (g : ℕ) {s s' : H2K.PS} (h : wipePS s = wipePS s') :
    AlikeE (fun x : (GroupRow × GroupLayout) × H2K.PS => ((wipeG x.1.1, x.1.2), wipePS x.2))
      (H2K.batE g s) (H2K.batE g s') := by
  obtain ⟨q, d, rounds, entries, last, asked, later, cur⟩ := s
  obtain ⟨q', d', rounds', entries', last', asked', later', cur'⟩ := s'
  simp only [wipePS, H2K.PS.mk.injEq] at h
  obtain ⟨rfl, hd, rfl, rfl, rfl, rfl, rfl, hcur⟩ := h
  have hst : wipeSt d.st = wipeSt d'.st := congrArg (·.st) hd
  have hbk : d.book = d'.book := congrArg (·.book) hd
  have hrt : d.roots = d'.roots := congrArg (·.roots) hd
  have hop : d.opened = d'.opened := congrArg (·.opened) hd
  have hlc : d.loc = d'.loc := congrArg (·.loc) hd
  unfold H2K.batE
  cases entries with
  | nil => exact AlikeE.rfl'
  | cons e es =>
    cases rounds with
    | nil => exact AlikeE.rfl'
    | cons r rs =>
      dsimp only
      refine AlikeE.head' fun _ => ?_
      refine AlikeE.bind' (w := wipeB) ?_ fun x x' ex => ?_
      · rcases (bat_rel hst g e r).split with ⟨w, a, b⟩ | ⟨x, x', a, b, c⟩
        · rw [a, b]
          exact AlikeE.rfl'
        · rw [a, b]
          exact AlikeE.ok c
      · obtain ⟨x1, x23⟩ := Prod.mk.inj
          (ex : (wipeG x.1, x.2.1, wipeSt x.2.2) = (wipeG x'.1, x'.2.1, wipeSt x'.2.2))
        obtain ⟨x2, x3⟩ := Prod.mk.inj x23
        refine AlikeE.ok ?_
        simp only [wipePS, wipeD, x1, x2, x3, hbk, hrt, hop, hlc, hcur]

theorem batJ_alike (p : P12) (cut : List Fmt.DeclaredRound) {t t' : T12} (h : Agree t t')
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    AlikeE wipeT ((batJ p cut).decide t rs gs) ((batJ p cut).decide t' rs gs) := by
  have hl := lay_alike p cut none h rs gs
  have hg : t.g = t'.g := congrArg (·.g) h
  have hm : t.mask = t'.mask := congrArg (·.mask) h
  have hst : wipeSt t.st = wipeSt t'.st := congrArg (·.st) h
  have hp : wipeP t.pass = wipeP t'.pass := congrArg (·.pass) h
  have hw : codesFit p t.st = codesFit p t'.st := by
    rw [← codesFit_wipe p t.st, ← codesFit_wipe p t'.st, hst]
  unfold batJ
  rcases pass_cases _ _ hp with ⟨a, b⟩ | ⟨r, r', L, a, b, -⟩ | ⟨R, R', n, a, b, -⟩ |
    ⟨out, theta, n, a, b⟩
  · cases p.idx with
    | nil =>
      simp only [a, b]
      exact AlikeE.rfl'
    | cons i _ =>
      simp only [a, b]
      rw [← hg, ← hm, hw]
      refine AlikeE.head' fun _ => ?_
      refine AlikeE.bind' (batE_alike t.g hl) fun x x' ex => ?_
      obtain ⟨x1, x2⟩ := Prod.mk.inj
        (ex : ((wipeG x.1.1, x.1.2), wipePS x.2) = ((wipeG x'.1.1, x'.1.2), wipePS x'.2))
      obtain ⟨x11, x12⟩ := Prod.mk.inj x1
      have hx : wipeSt x.2.d.st = wipeSt x'.2.d.st := congrArg (·.d.st) x2
      have hq : ((x.2.d.st.groups[t.g]?).any fun G => G.code == i.1 && G.maskCode == i.2) =
          ((x'.2.d.st.groups[t.g]?).any fun G => G.code == i.1 && G.maskCode == i.2) := by
        rw [← anyGroup_wipe x.2.d.st t.g _ fun _ => rfl,
          ← anyGroup_wipe x'.2.d.st t.g _ fun _ => rfl, hx]
      rw [hq]
      refine AlikeE.head' fun _ => ?_
      refine back_alike hg x2 ?_ _
      show Passing.claim (wipeG x.1.1) x.1.2 = Passing.claim (wipeG x'.1.1) x'.1.2
      rw [x11, x12]
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    exact AlikeE.rfl'

/-- **The batching of `guardedProximityTestParts`, at two records that agree but for targets**: one word, or two
records that agree but for targets. -/
theorem bat_agree (p : P12) (cut : List Fmt.DeclaredRound) {t t' : T12} (h : Agree t t')
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    AlikeE wipeT ((guardedProximityTestParts.bat p cut).decide t rs gs) ((guardedProximityTestParts.bat p cut).decide t' rs gs) := by
  unfold guardedProximityTestParts ranged
  dsimp only
  refine AlikeE.head' fun _ => ?_
  rw [combOk_agree h]
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.bind' (batJ_alike p cut h rs gs) fun a a' ha => ?_
  have ha' : Agree a a' := ha
  rw [noKept_agree ha', gpOk_agree p ha', labelsOk_agree p ha']
  refine AlikeE.head' fun _ => AlikeE.head' fun _ => ?_
  exact AlikeE.ok ha

/-! ## 4 The batching behind a switch -/

/-- What `csTest` returns, wiped. -/
def wipeCs (x : (Switched × GroupRow × GroupLayout) × H2K.PS) :
    (Switched × GroupRow × GroupLayout) × H2K.PS :=
  ((x.1.1, wipeG x.1.2.1, x.1.2.2), wipePS x.2)

/-- The last lines of the code switch inside a test, its switch handing on what the switch before
has returned. -/
theorem csTail_alike (out : Switched) (theta : E) (old : OnBytes.SingleRows)
    (T : OnBytes.SwitchTarget) (n : ℕ) (others : Array OnBytes.OracleNotice) {s s' : H2K.PS}
    (h : wipePS s = wipePS s') :
    (csTest { H2K.csParts with switch := fun _ _ _ _ _ s => some ((out, theta), s) } old T n others
        s).map wipeCs =
      (csTest { H2K.csParts with switch := fun _ _ _ _ _ s => some ((out, theta), s) } old T n
        others s').map wipeCs := by
  obtain ⟨q, d, rounds, entries, last, asked, later, cur⟩ := s
  obtain ⟨q', d', rounds', entries', last', asked', later', cur'⟩ := s'
  simp only [wipePS, H2K.PS.mk.injEq] at h
  obtain ⟨rfl, hd, rfl, rfl, rfl, rfl, rfl, hcur⟩ := h
  have hb := beginRunP_rel hd n
  unfold csTest
  simp only [H2K.csParts, H2K.beginRunE, H2K.opt]
  cases e : beginRunP d n with
  | none =>
    cases e' : beginRunP d' n with
    | none => rfl
    | some y => rw [e, e'] at hb; cases hb
  | some x =>
    cases e' : beginRunP d' n with
    | none => rw [e, e'] at hb; cases hb
    | some y =>
      rw [e, e'] at hb
      obtain ⟨b1, b2⟩ := Prod.mk.inj (Option.some.inj hb :
        ((⟨x.1.layout, x.1.rows.map wipeRow⟩ : RunInput), wipeD x.2) =
          (⟨y.1.layout, y.1.rows.map wipeRow⟩, wipeD y.2))
      have bl : x.1.layout = y.1.layout := congrArg (·.layout) b1
      have br : x.1.rows.map wipeRow = y.1.rows.map wipeRow := congrArg (·.rows) b1
      have bs : x.1.rows.size = y.1.rows.size := by
        have := congrArg Array.size br
        simpa only [Array.size_map] using this
      have bst : wipeSt x.2.st = wipeSt y.2.st := congrArg (·.st) b2
      have hB : (batch x.2.st n x.1 theta).map wipeG = (batch y.2.st n y.1 theta).map wipeG := by
        rw [batch_wipe x.2.st n x.1 theta, batch_wipe y.2.st n y.1 theta, bst, bl, br]
      simp only [Except.map, Except.toOption, H2K.askOwedE, H2K.PS.owed, bs]
      cases last with
      | none => rfl
      | some e0 =>
        by_cases h1 : (e0.rows == 0 || asked) = true
        · simp only [h1, ↓reduceIte]
        · by_cases h2 : (e0.rows == y.1.rows.size) = true
          · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
            cases ex : batch x.2.st n x.1 theta with
            | none =>
              cases ey : batch y.2.st n y.1 theta with
              | none => rfl
              | some r' => rw [ex, ey] at hB; cases hB
            | some r =>
              cases ey : batch y.2.st n y.1 theta with
              | none => rw [ex, ey] at hB; cases hB
              | some r' =>
                rw [ex, ey] at hB
                have hr : wipeG r = wipeG r' := Option.some.inj hB
                show some (wipeCs _) = some (wipeCs _)
                simp only [wipeCs, wipePS, hr, bl, b2, hcur]
          · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

/-- **The batching behind a switch, the like.** `guardedProximityTestParts.batBehind` is `behindJ`. -/
theorem batBehind_agree (p : P12) (j : ℕ) (next : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    {t t' : T12} (h : Agree t t') (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    AlikeE wipeT ((guardedProximityTestParts.batBehind p j next cut).decide t rs gs)
      ((guardedProximityTestParts.batBehind p j next cut).decide t' rs gs) := by
  have hl := lay_alike p [] (cut.getLast?.map (·.entry)) h rs gs
  have hg : t.g = t'.g := congrArg (·.g) h
  have hp : wipeP t.pass = wipeP t'.pass := congrArg (·.pass) h
  show AlikeE wipeT ((behindJ p j next cut).decide t rs gs) ((behindJ p j next cut).decide t' rs gs)
  unfold behindJ
  rcases pass_cases _ _ hp with ⟨a, b⟩ | ⟨r, r', L, a, b, -⟩ | ⟨R, R', n, a, b, -⟩ |
    ⟨out, theta, n, a, b⟩
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    refine AlikeE.named (w := wipeCs) (csTail_alike out theta _ _ n _ hl) fun x x' ex => ?_
    obtain ⟨x1, x2⟩ := Prod.mk.inj (ex : ((x.1.1, wipeG x.1.2.1, x.1.2.2), wipePS x.2) =
      ((x'.1.1, wipeG x'.1.2.1, x'.1.2.2), wipePS x'.2))
    obtain ⟨-, x12⟩ := Prod.mk.inj x1
    obtain ⟨xa, xb⟩ := Prod.mk.inj x12
    refine back_alike hg x2 ?_ _
    show Passing.claim (wipeG x.1.2.1) x.1.2.2 = Passing.claim (wipeG x'.1.2.1) x'.1.2.2
    rw [xa, xb]

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.layout_wipe
#print axioms ProofFile.Honest.K12.Blind.placeOk_wipe
#print axioms ProofFile.Honest.K12.Blind.groupOkB_wipe
#print axioms ProofFile.Honest.K12.Blind.rowInB_wipe
#print axioms ProofFile.Honest.K12.Blind.combineAt_wipe
#print axioms ProofFile.Honest.K12.Blind.codesFit_wipe
#print axioms ProofFile.Honest.K12.Blind.anyGroup_wipe
#print axioms ProofFile.Honest.K12.Blind.seatOf_wipe
#print axioms ProofFile.Honest.K12.Blind.combOk_wipe
#print axioms ProofFile.Honest.K12.Blind.noKept_wipe
#print axioms ProofFile.Honest.K12.Blind.entered_aux
#print axioms ProofFile.Honest.K12.Blind.entered_wipe
#print axioms ProofFile.Honest.K12.Blind.gpOf_wipe
#print axioms ProofFile.Honest.K12.Blind.gpOk_wipe
#print axioms ProofFile.Honest.K12.Blind.labelsOk_wipe
#print axioms ProofFile.Honest.K12.Blind.combOk_agree
#print axioms ProofFile.Honest.K12.Blind.noKept_agree
#print axioms ProofFile.Honest.K12.Blind.gpOk_agree
#print axioms ProofFile.Honest.K12.Blind.labelsOk_agree
#print axioms ProofFile.Honest.K12.Blind.bat_rel
#print axioms ProofFile.Honest.K12.Blind.batE_alike
#print axioms ProofFile.Honest.K12.Blind.batJ_alike
#print axioms ProofFile.Honest.K12.Blind.bat_agree
#print axioms ProofFile.Honest.K12.Blind.wipeCs
#print axioms ProofFile.Honest.K12.Blind.csTail_alike
#print axioms ProofFile.Honest.K12.Blind.batBehind_agree
