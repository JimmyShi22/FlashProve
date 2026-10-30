-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK2.lean: the code switch (kind K2) as a block of the first chain (codeSwitchKind,
Johnson/Top/H0/Tw/K2C/Kind.lean). Its decide is handed opened columns. This file shows that the columns' words, and the
targets already in the state, change neither whether the block fails nor the message of its failure, and reach nothing
but targets in the state that it returns. Twelve definitions with code; the rest are theorems.

Words. The wiped copy of a state (wipeS, Honest/K10/WipeS.lean) is the state with these targets set to zero: those of
the statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched row. The
rows on the table (the pile out.pending, and the claim at the chain's end) keep theirs. wipeSt, wipeFrame, wipeCheck and
wipeD do the like to a statement, a frame, a ChainCheck and the ground's record. A row's target is its right side; the
plan's SwitchTarget (the letters T and G.target) is another thing: the codes and shapes of the group to which a switch
leads. Two groups of columns have the same shape if their columns have the same positions and numbers of words (SameG,
Wipe/Alike.lean). Two outcomes are alike under w (AlikeE w, Wipe/Alike.lean) if both fail with the same message, or both
succeed with values that are equal after w is applied.

What is proved. **k2_whole2 : Whole2 wipeS (codeSwitchKind p)**, for all numbers p of a place and for each of the three sorts of
place (a link, the head's link, the finish): at two states with the same wiped copy and at groups of the same shapes,
decide fails with the same message, or returns states with the same wiped copy. The steps, bottom up:
  closeLedgerG_rel, swJoin_rel, whyRow_rel, addRowsG_rel, swNewGroup_rel   the switch's adapters over the plain ground,
                 with the messages of their failures
  sampleLoop_rel, sendP_rel, sendOpen_rel, sendByL8_rel   the sending; the new sample rows' targets are answers taken
                 from the round, so they are equal on both sides
  swBehind_wiped, swBehind_rel   the step after the sending (switchBehind, K2/Switch.lean)
  swSwitchE_rel  the guard, the sending and that step (switchE, K2/Step.lean)
  swFirstFront_rel, swFirstBehind_rel, swFirstEW_rel, swChain_rel   a later link's first call (K2/First.lean, Step.lean,
                 Cuts.lean)
  swAlone_rel, swHead_rel, swFinish_rel   the switch alone, at the head's link and at the finish (K2/Cuts.lean)
  flat_same, allTaken_rel, decideWith_wiped   the block's own lines

By what. Wipe/KeepK2Cols.lean (from columns to symbols only sizes matter), Wipe/KeepK2Rows.lean (the two public tests;
the new rows differ at most in targets), Wipe/WipeGround.lean (the plain ground) and Wipe/WipeLaws.lean, carried through
each bind by the lemmas of Wipe/Alike.lean. Most lemmas compare two statements with the same wiped copy, not a statement
with its own wiped copy: after the sending the side that started wiped holds new sample rows with their true targets.
The last lemma, decideWith_wiped, compares the wiped state with the state: that is the form that Decides2.of_wiped_cols
takes.

Limits. The theorems hold for all states and columns, whether or not a run can reach them. They are about decideWith at
sendByL8 and switchBehind; nothing is said of other functions put in their places. Nothing says what a wiped state
means. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK2Rows
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeGround
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement Oracle Row TreeBook Codes OracleShape OracleNotice SampleSeed SingleRows SwitchTarget Switched
  ReqFrame GroupLayout zipT)
open OnBytes.Params (ReqMessage)
open Desc.Plain (DState GPar groundG rowsFor sampleLoop sendP)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.First.Send (sendOpen)
open VerifiableInference.Desc.First.K2 (P2 decideWith flat allTaken rightGroup par9 codeSwitchKind)
open VerifiableInference.Desc.Ground (newGroupL closeLedgerL joinL rowL rowsL admitP)
open Tw.K2 (SwIn SwOut Sent Par9 S9 S9C S9S dOf closeLedgerG whyRow addRowsG newGroupG switchBehind switchE
  sendByL8 firstFront firstBehind firstEW chainFirstEW switchAloneEW headSwitchEW finishSwitchEW)

/-! ## 1 General laws -/

/-- `if c then throw e` followed by k, and the same with c', e', k', are alike if c ↔ c', e = e', and k and k' are
alike. -/
theorem alikeThrow {γ δ : Type} {v : γ → δ} {c c' : Prop} [Decidable c] [Decidable c'] {e e' : String}
    {k k' : Except String γ} (hc : c ↔ c') (he : e = e') (h : AlikeE v k k') :
    AlikeE v
      (do
        if c then throw e
        k)
      (do
        if c' then throw e'
        k') := by
  subst he
  by_cases h1 : c
  · have h2 : c' := hc.1 h1
    simp only [if_pos h1, if_pos h2]
    exact AlikeE.error e
  · have h2 : ¬c' := fun x => h1 (hc.2 x)
    simp only [if_neg h1, if_neg h2]
    exact h

/-- `let y ← if c then a else b` followed by `k y`, written on two sides, are alike if a and a', b and b' are alike and
k, k' send alike values to alike results. -/
theorem alikeIfLet {α β γ δ : Type} {w : α → β} {v : γ → δ} {c : Prop} [Decidable c] {a a' b b' : Except String α}
    {k k' : α → Except String γ} (ha : AlikeE w a a') (hb : AlikeE w b b')
    (hk : ∀ x x', w x = w x' → AlikeE v (k x) (k' x')) :
    AlikeE v
      (do
        let y ← if c then a else b
        k y)
      (do
        let y ← if c then a' else b'
        k' y) := by
  by_cases h1 : c
  · simp only [if_pos h1]
    exact AlikeE.bind' ha hk
  · simp only [if_neg h1]
    exact AlikeE.bind' hb hk

/-- `alikeFold` (Wipe/KeepK2Cols.lean) for `Array.foldlM`. -/
theorem alikeFoldA {α β γ : Type} (φ : β → γ) (f f' : β → α → Except String β)
    (h : ∀ b b' a, φ b = φ b' → AlikeE φ (f b a) (f' b' a)) (A : Array α) {b b' : β} (hb : φ b = φ b') :
    AlikeE φ (A.foldlM f b) (A.foldlM f' b') := by
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact alikeFold φ f f' h A.toList b b' hb

/-- If two optional lists are equal under φ, so are the lists got by taking the empty list for `none`. -/
theorem getDRel {α β : Type} (φ : α → β) {o o' : Option (List α)} (h : o.map (List.map φ) = o'.map (List.map φ)) :
    (o.getD []).map φ = (o'.getD []).map φ := by
  rcases omapSplit h with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · subst h1 h2
    rfl
  · subst h1 h2
    exact ha

/-- A function of an oracle message that gives the same value on the wiped message reads the same value at two
statements with the same wiped copy. -/
theorem oracleRead {α : Type} (f : Oracle → α) (hf : ∀ x, f (wipeOr x) = f x) {S S' : Statement}
    (h : wipeSt S = wipeSt S') (o : Nat) : (S.oracles[o]?).map f = (S'.oracles[o]?).map f := by
  have k : ∀ Z : Statement, ((wipeSt Z).oracles[o]?).map f = (Z.oracles[o]?).map f := fun Z => by
    rw [wipeSt_oracle_at]
    cases Z.oracles[o]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  rw [← k S, ← k S', h]

/-! ## 2 The effects on the statement: the switch's adapters over the plain ground -/

/-- If two statements have the same wiped copy, so do the ground's records that `dOf` makes of them. -/
theorem dOf_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') : wipeD (dOf S) = wipeD (dOf S') :=
  (congrArg dOf hS :)

/-- If two of the ground's records have the same wiped copy, so do their statements. -/
theorem st_of_wipeD {L : Type} {d d' : DState L} (h : wipeD d = wipeD d') : wipeSt d.st = wipeSt d'.st :=
  (congrArg (fun z : DState L => z.st) h :)

/-- `closeLedgerG` at two statements with the same wiped copy fails with the same message, or returns statements with
the same wiped copy. -/
theorem closeLedgerG_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (o : Nat) :
    AlikeE wipeSt (closeLedgerG S o) (closeLedgerG S' o) := by
  have hL : closeLedgerL S o = closeLedgerL S' o := by
    rw [← closeLedgerL_wipe S o, ← closeLedgerL_wipe S' o, hS]
  unfold Tw.K2.closeLedgerG
  rw [hL]
  rcases omapSplit (closeLedgerP_rel (dOf_rel hS) o) with ⟨h1, h2⟩ | ⟨d, d', h1, h2, hd⟩
  · rw [h1, h2]
    exact AlikeE.error _
  · rw [h1, h2]
    exact AlikeE.ok (st_of_wipeD hd)

/-- The same for `Tw.K2.joinG`. -/
theorem swJoin_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (g o : Nat) (kept : Bool) :
    AlikeE wipeSt (Tw.K2.joinG S g o kept) (Tw.K2.joinG S' g o kept) := by
  have hL : joinL S g o kept = joinL S' g o kept := by
    rw [← joinL_wipe S g o kept, ← joinL_wipe S' g o kept, hS]
  unfold Tw.K2.joinG
  rw [hL]
  rcases omapSplit (joinP_rel (dOf_rel hS) g o kept) with ⟨h1, h2⟩ | ⟨d, d', h1, h2, hd⟩
  · rw [h1, h2]
    exact AlikeE.error _
  · rw [h1, h2]
    exact AlikeE.ok (st_of_wipeD hd)

/-- `rowL` is the same list of clauses at statements and rows with the same wiped copies. -/
theorem rowL_rel2 {S S' : Statement} (hS : wipeSt S = wipeSt S') (g : Nat) {r r' : Row}
    (hr : wipeRow r = wipeRow r') : rowL S g r = rowL S' g r' := by
  rw [← rowL_wipe S g r, ← rowL_wipe S' g r', hS, hr]

/-- `whyRow` gives the same message at records and lists of rows with the same wiped copies. -/
theorem whyRow_rel (g : Nat) : ∀ (rows rows' : List Row) (d d' : DState Unit),
    rows.map wipeRow = rows'.map wipeRow → wipeD d = wipeD d' → whyRow g rows d = whyRow g rows' d'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | r :: l, r' :: l', d, d', h, hd => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨hr, hl⟩ := List.cons.inj h
    rw [Tw.K2.whyRow, Tw.K2.whyRow]
    rcases omapSplit (addRowP_rel hd g hr) with ⟨h1, h2⟩ | ⟨e, e', h1, h2, he⟩
    · simp only [h1, h2]
      rw [rowL_rel2 (st_of_wipeD hd) g hr]
    · simp only [h1, h2]
      exact whyRow_rel g l l' e e' hl he

/-- `addRowsG`, at statements and lists of rows with the same wiped copies, fails with the same message, or returns
statements with the same wiped copy. -/
theorem addRowsG_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (g : Nat) {rows rows' : List Row}
    (hr : rows.map wipeRow = rows'.map wipeRow) : AlikeE wipeSt (addRowsG S g rows) (addRowsG S' g rows') := by
  have hL : rowsL S g = rowsL S' g := by rw [← rowsL_wipe S g, ← rowsL_wipe S' g, hS]
  have hW : whyRow g rows (dOf S) = whyRow g rows' (dOf S') := whyRow_rel g rows rows' _ _ hr (dOf_rel hS)
  unfold Tw.K2.addRowsG
  rw [hL, hW]
  rcases omapSplit (addRowsP_rel (dOf_rel hS) g hr) with ⟨h1, h2⟩ | ⟨d, d', h1, h2, hd⟩
  · rw [h1, h2]
    exact AlikeE.error _
  · rw [h1, h2]
    exact AlikeE.ok (st_of_wipeD hd)

/-! ## 3 The sending -/

/-- What is compared of `sendP`'s result: everything, with the record wiped. -/
def wSend5 {L : Type} (x : Array Nat × List E × List E × Nat × DState L) :
    Array Nat × List E × List E × Nat × DState L :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, wipeD x.2.2.2.2)

/-- The same for `sendOpen`'s result. -/
def wSend3 {L : Type} (x : Array Nat × Nat × DState L) : Array Nat × Nat × DState L := (x.1, x.2.1, wipeD x.2.2)

/-- The same for `sendByL8`'s result. -/
def wSent (y : Sent) : Sent := { y with st := wipeSt y.st }

/-- `sampleLoop` at two records with the same wiped copy returns nothing at both, or the same answers left and records
with the same wiped copy. -/
theorem sampleLoop_rel {L : Type} (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L), wipeD d = wipeD d' →
      (sampleLoop groundG p codes seeds l ys d).map (Prod.map wipeD id) =
        (sampleLoop groundG p codes seeds l ys d').map (Prod.map wipeD id)
  | [], ys, _, _, h => (congrArg (fun z => some (z, ys)) h :)
  | (o, s) :: l, ys, d, d', h => by
    rw [Desc.Plain.sampleLoop, Desc.Plain.sampleLoop]
    cases rowsFor codes s o seeds (List.range s.answers) ys #[] with
    | none => rfl
    | some z =>
      obtain ⟨rows, ys'⟩ := z
      show (match admitP d o rows with
          | none => none
          | some d1 => sampleLoop groundG p codes seeds l ys' d1).map (Prod.map wipeD id) =
        (match admitP d' o rows with
          | none => none
          | some d1 => sampleLoop groundG p codes seeds l ys' d1).map (Prod.map wipeD id)
      rcases omapSplit (admitP_rel h o (rfl : rows.map wipeRow = rows.map wipeRow)) with
        ⟨h1, h2⟩ | ⟨e, e', h1, h2, he⟩
      · simp only [h1, h2]
      · simp only [h1, h2]
        exact sampleLoop_rel p codes seeds l ys' e e' he

/-- **`sendP` at two records with the same wiped copy** returns nothing at both, or results equal under `wSend5`. -/
theorem sendP_rel {L : Type} (p : GPar) (own : Bool) {d d' : DState L} (hd : wipeD d = wipeD d')
    (sent : Array OracleNotice) (r₁ r₂ : Fmt.RoundView) :
    (sendP groundG p own d sent r₁ r₂).map wSend5 = (sendP groundG p own d' sent r₁ r₂).map wSend5 := by
  unfold Desc.Plain.sendP
  refine bind_rel (Prod.map id wipeD) wSend5 (recvP_rel hd p.firstTree sent) fun x x' hx => ?_
  obtain ⟨ids, d₁⟩ := x
  obtain ⟨ids', d₁'⟩ := x'
  have hi : ids = ids' := (congrArg (fun z : Array Nat × DState L => z.1) hx :)
  have h1 : wipeD d₁ = wipeD d₁' := (congrArg (fun z : Array Nat × DState L => z.2) hx :)
  subst hi
  have hst := st_of_wipeD h1
  have hA := oracleRead (fun x => x.shape.answers) (fun _ => rfl) hst
  have hSh := oracleRead (fun x => x.shape) (fun _ => rfl) hst
  have hSa := oracleRead (fun x => !x.sampled) (fun _ => rfl) hst
  have hC : d₁.st.codes = d₁'.st.codes := (congrArg (fun Z : Statement => Z.codes) hst :)
  dsimp only
  simp only [hA, hSh, hSa, hC]
  refine bind_rel id _ rfl fun sh sh' e1 => ?_
  have e1' : sh = sh' := e1
  subst e1'
  refine bind_rel id _ rfl fun seeds seeds' e2 => ?_
  have e2' : seeds = seeds' := e2
  subst e2'
  refine bind_rel id _ rfl fun an an' e3 => ?_
  have e3' : an = an' := e3
  subst e3'
  refine swIte (Option.map wSend5) (Option.map wSend5) ?_ rfl
  refine bind_rel (Prod.map wipeD id) _ (sampleLoop_rel p _ _ _ _ d₁ d₁' h1) fun z z' hz => ?_
  obtain ⟨d₂, left⟩ := z
  obtain ⟨d₂', left'⟩ := z'
  have h2 : wipeD d₂ = wipeD d₂' := (congrArg (fun z : DState L × List E => z.1) hz :)
  have hl : left = left' := (congrArg (fun z : DState L × List E => z.2) hz :)
  subst hl
  refine swIte (Option.map wSend5) (Option.map wSend5) ?_ rfl
  exact congrArg (fun q => some (ids, _, an, _, q)) h2

/-- The same for `sendOpen`, under `wSend3`. -/
theorem sendOpen_rel {L : Type} (p : GPar) (owed : Option Nat) (sent : Array OracleNotice) (e₁ : Fmt.Entry)
    {d d' : DState L} (hd : wipeD d = wipeD d') (r₁ r₂ : Fmt.RoundView) :
    (sendOpen groundG p owed sent e₁ d r₁ r₂).map wSend3 = (sendOpen groundG p owed sent e₁ d' r₁ r₂).map wSend3 := by
  unfold VerifiableInference.Desc.First.Send.sendOpen
  refine swIte (Option.map wSend3) (Option.map wSend3) ?_ rfl
  refine omapRel wSend5 wSend3 (sendP_rel p false hd sent r₁ r₂) fun x x' hx => ?_
  have a1 : x.1 = x'.1 :=
    (congrArg (fun z : Array Nat × List E × List E × Nat × DState L => z.1) hx :)
  have a2 : x.2.2.2.1 = x'.2.2.2.1 :=
    (congrArg (fun z : Array Nat × List E × List E × Nat × DState L => z.2.2.2.1) hx :)
  have a3 : wipeD x.2.2.2.2 = wipeD x'.2.2.2.2 :=
    (congrArg (fun z : Array Nat × List E × List E × Nat × DState L => z.2.2.2.2) hx :)
  show (x.1, x.2.2.2.1, wipeD x.2.2.2.2) = (x'.1, x'.2.2.2.1, wipeD x'.2.2.2.2)
  rw [a1, a2, a3]

/-- **`sendByL8` at two statements with the same wiped copy** fails with the same message, or returns results equal
under `wSent`. -/
theorem sendByL8_rel (P : Par9) {S S' : Statement} (hS : wipeSt S = wipeSt S') (B : TreeBook) (roots : Nat)
    (settled : Bool) (notices : Array OracleNotice) (rS rL : Fmt.RoundView) :
    AlikeE wSent (sendByL8 P S B roots settled notices rS rL) (sendByL8 P S' B roots settled notices rS rL) := by
  have hd : wipeD (⟨S, B, roots, [], ()⟩ : DState Unit) = wipeD ⟨S', B, roots, [], ()⟩ :=
    (congrArg (fun Z => (⟨Z, B, roots, [], ()⟩ : DState Unit)) hS :)
  unfold Tw.K2.sendByL8
  rcases omapSplit (sendOpen_rel ⟨P.samples, P.firstTree⟩ (if settled then none else some 1) notices P.eSeed hd rS
      rL) with ⟨h1, h2⟩ | ⟨z, z', h1, h2, hz⟩
  · rw [h1, h2]
    exact AlikeE.error _
  · rw [h1, h2]
    obtain ⟨ids, took, d⟩ := z
    obtain ⟨ids', took', d'⟩ := z'
    have a1 : ids = ids' := (congrArg (fun z : Array Nat × Nat × DState Unit => z.1) hz :)
    have a2 : took = took' := (congrArg (fun z : Array Nat × Nat × DState Unit => z.2.1) hz :)
    have a3 : wipeD d = wipeD d' := (congrArg (fun z : Array Nat × Nat × DState Unit => z.2.2) hz :)
    have b1 : d.book = d'.book := (congrArg (fun z : DState Unit => z.book) a3 :)
    have b2 : d.roots = d'.roots := (congrArg (fun z : DState Unit => z.roots) a3 :)
    refine AlikeE.ok ?_
    show (⟨wipeSt d.st, d.book, d.roots, ids, took⟩ : Sent) = ⟨wipeSt d'.st, d'.book, d'.roots, ids', took'⟩
    rw [st_of_wipeD a3, b1, b2, a1, a2]

/-! ## 4 The step behind the sending -/

/-- What is compared of `switchBehind`'s result: the wiped statement, the book, the shapes of the columns left, and the
switch's numbers. -/
def wOut (w : SwOut) : Statement × TreeBook × List (Nat × Nat × Nat) × Switched :=
  (wipeSt w.st, w.book, w.opened.map colShape, w.out)

/-- **`switchBehind`** is alike at its argument and at that argument with a statement that has the same wiped copy,
columns of the same shapes, and the carried rows' target set to zero. -/
theorem swBehind_wiped (i : SwIn) {S' : Statement} {c' : List OpenedColumn} (hS : wipeSt S' = wipeSt i.st)
    (hc : SameShape c' i.opened) :
    AlikeE wOut (switchBehind { i with st := S', opened := c', old := singleRowsWithZeroTarget i.old }) (switchBehind i) := by
  have hR := fun pos => readOld_rel i pos hS hc
  obtain ⟨st, book, ft, opened, old, T, grp, ids, entry, settled, drawn, itemsLeft⟩ := i
  have hS' : wipeSt S' = wipeSt st := hS
  have hC : S'.codes = st.codes := (congrArg (fun Z : Statement => Z.codes) hS' :)
  have hO : (singleRowsWithZeroTarget old).code = old.code := rfl
  unfold Tw.K2.switchBehind
  dsimp only
  rw [hC, hO]
  cases st.codes.base[old.code]? with
  | none => exact AlikeE.error _
  | some c0 =>
    dsimp only
    refine AlikeE.head' fun code => ?_
    refine AlikeE.head_eq' rfl fun pos => ?_
    refine AlikeE.bind' (hR pos) fun z' z hz => ?_
    obtain ⟨B', left', y'⟩ := z'
    obtain ⟨B, left, y⟩ := z
    have hB : B' = B := (congrArg (fun q : TreeBook × List (Nat × Nat × Nat) × Nat => q.1) hz :)
    have hl : left'.map colShape = left.map colShape :=
      (congrArg (fun q : TreeBook × List (Nat × Nat × Nat) × Nat => q.2.1) hz :)
    have hy : y'.size = y.size := (congrArg (fun q : TreeBook × List (Nat × Nat × Nat) × Nat => q.2.2) hz :)
    dsimp only
    refine alikeIfLet (closeLedgerG_rel hS' _) (AlikeE.ok hS') fun S1' S1 h1 => ?_
    refine AlikeE.bind' (swJoin_rel h1 _ _ _) fun S2' S2 h2 => ?_
    refine AlikeE.bind' (alikeFoldA wipeSt _ _ (fun b b' p hb => swJoin_rel hb grp p.1 p.2.keptAgain) _ h2)
      fun S3' S3 h3 => ?_
    have hL : rowsL S3' grp = rowsL S3 grp := by rw [← rowsL_wipe S3' grp, ← rowsL_wipe S3 grp, h3]
    rw [hL, rowsCan_rel h3 old T _ _ hy, rowsWhy_rel h3 old T _ _ hy]
    refine alikeThrow Iff.rfl rfl ?_
    refine alikeThrow Iff.rfl rfl ?_
    refine AlikeE.bind' (addRowsG_rel h3 grp (getDRel wipeRow (swRows_rel h3 old T _ _ _ hy))) fun S4' S4 h4 => ?_
    refine AlikeE.ok ?_
    show (wipeSt S4', B', left'.map colShape, _) = (wipeSt S4, B, left.map colShape, _)
    rw [h4, hB, hl]

/-- What is compared of `switchBehind`'s argument: all fields, with the statement and the carried rows wiped, and of the
columns their shapes. -/
def shIn (i : SwIn) : SwIn × List (Nat × Nat × Nat) :=
  ({ i with st := wipeSt i.st, opened := [], old := singleRowsWithZeroTarget i.old }, i.opened.map colShape)

/-- **`switchBehind` is alike at two arguments equal under `shIn`.** -/
theorem swBehind_rel {i i' : SwIn} (h : shIn i' = shIn i) : AlikeE wOut (switchBehind i') (switchBehind i) := by
  have hs : SameShape i.opened i'.opened :=
    (congrArg (fun q : SwIn × List (Nat × Nat × Nat) => q.2) h :).symm
  have A1 := swBehind_wiped i (S' := wipeSt i.st) (c' := i.opened) (wipeSt_idem _) rfl
  have A2 := swBehind_wiped i' (S' := wipeSt i'.st) (c' := i.opened) (wipeSt_idem _) hs
  have e : ({ i' with st := wipeSt i'.st, opened := i.opened, old := singleRowsWithZeroTarget i'.old } : SwIn) =
      { i with st := wipeSt i.st, opened := i.opened, old := singleRowsWithZeroTarget i.old } :=
    (congrArg (fun q : SwIn × List (Nat × Nat × Nat) => ({ q.1 with opened := i.opened } : SwIn)) h :)
  rw [e] at A2
  exact A2.symm.trans A1

/-! ## 5 The guard, the sending, the step behind it -/

/-- A `Tw.K2.Front` with its statement and its frame wiped. -/
def wFront (x : Tw.K2.Front) : Tw.K2.Front := { x with st := wipeSt x.st, f := wipeFrame x.f }

/-- What is compared of `switchE`'s result: its first part under `wOut`, and the number of roots. -/
def wSw (z : SwOut × Nat) : (Statement × TreeBook × List (Nat × Nat × Nat) × Switched) × Nat := (wOut z.1, z.2)

/-- **`switchE` is alike on two sides** that have the same book, roots and `settled`, fronts with the same wiped copy,
and columns of the same shapes. -/
theorem swSwitchE_rel (P : Par9) {s s' : S9} (h1 : s'.settled = s.settled) (h2 : s'.book = s.book)
    (h3 : s'.roots = s.roots) {x x' : Tw.K2.Front} (hx : wFront x' = wFront x) (rS rL : Fmt.RoundView) {cols cols' : List OpenedColumn}
    (hc : SameShape cols' cols) :
    AlikeE wSw (switchE switchBehind P sendByL8 s' x' rS rL cols')
      (switchE switchBehind P sendByL8 s x rS rL cols) := by
  have hst : wipeSt x'.st = wipeSt x.st := (congrArg (fun q : Tw.K2.Front => q.st) hx :)
  have hf : wipeFrame x'.f = wipeFrame x.f := (congrArg (fun q : Tw.K2.Front => q.f) hx :)
  have hr : singleRowsWithZeroTarget x'.f.rows = singleRowsWithZeroTarget x.f.rows := (congrArg (fun q : ReqFrame => q.rows) hf :)
  have hg : x'.f.group = x.f.group := (congrArg (fun q : ReqFrame => q.group) hf :)
  have hT : x'.T = x.T := (congrArg (fun q : Tw.K2.Front => q.T) hx :)
  have hO : x'.others = x.others := (congrArg (fun q : Tw.K2.Front => q.others) hx :)
  have hc' : cols'.map colShape = cols.map colShape := hc
  unfold Tw.K2.switchE
  rw [h1, h2, h3, hT, hO, hg, switchGuard_rel hst hr x.T, targetWhy_rel hst hr x.T]
  refine alikeThrow Iff.rfl rfl ?_
  refine alikeThrow Iff.rfl rfl ?_
  refine alikeThrow Iff.rfl rfl ?_
  refine AlikeE.bind' (sendByL8_rel P hst s.book s.roots s.settled _ rS rL) fun y' y hy => ?_
  obtain ⟨yst', ybook', yroots', yids', ytook'⟩ := y'
  obtain ⟨yst, ybook, yroots, yids, ytook⟩ := y
  have a0 : wipeSt yst' = wipeSt yst := (congrArg (fun q : Sent => q.st) hy :)
  have a1 : ybook' = ybook := (congrArg (fun q : Sent => q.book) hy :)
  have a2 : yroots' = yroots := (congrArg (fun q : Sent => q.roots) hy :)
  have a3 : yids' = yids := (congrArg (fun q : Sent => q.ids) hy :)
  have a4 : ytook' = ytook := (congrArg (fun q : Sent => q.took) hy :)
  subst a1 a2 a3 a4
  dsimp only
  refine alikeThrow Iff.rfl rfl ?_
  refine alikeThrow Iff.rfl rfl ?_
  refine AlikeE.bind' (swBehind_rel ?_) fun w' w hw => ?_
  · show ((⟨wipeSt yst', _, _, [], singleRowsWithZeroTarget x'.f.rows, _, _, _, _, _, _, _⟩ : SwIn), cols'.map colShape) =
      (⟨wipeSt yst, _, _, [], singleRowsWithZeroTarget x.f.rows, _, _, _, _, _, _, _⟩, cols.map colShape)
    rw [a0, hr, hc']
  · exact AlikeE.ok (congrArg (fun q => (q, _)) hw)

/-! ## 6 Around the switch in a later link's first call -/

/-- What is compared of `newGroupG`'s result: the wiped statement and the group's number. -/
def wStN (z : Statement × Nat) : Statement × Nat := (wipeSt z.1, z.2)

/-- `newGroupG` at two statements with the same wiped copy fails with the same message, or returns results equal under
`wStN`. -/
theorem swNewGroup_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (c m : Nat) :
    AlikeE wStN (newGroupG S c m) (newGroupG S' c m) := by
  have hL : newGroupL S c m = newGroupL S' c m := by
    rw [← newGroupL_wipe S c m, ← newGroupL_wipe S' c m, hS]
  unfold Tw.K2.newGroupG
  rw [hL]
  rcases omapSplit (newGroupP_rel (dOf_rel hS) c m) with ⟨h1, h2⟩ | ⟨z, z', h1, h2, hz⟩
  · rw [h1, h2]
    exact AlikeE.error _
  · rw [h1, h2]
    obtain ⟨g, d⟩ := z
    obtain ⟨g', d'⟩ := z'
    have a1 : g = g' := (congrArg (fun q : Nat × DState Unit => q.1) hz :)
    have a2 : wipeD d = wipeD d' := (congrArg (fun q : Nat × DState Unit => q.2) hz :)
    refine AlikeE.ok ?_
    show (wipeSt d.st, g) = (wipeSt d'.st, g')
    rw [st_of_wipeD a2, a1]

/-- `ReqFrame.atMoment` is the same at a frame and at its wiped copy. -/
theorem atMoment_wipe (f : ReqFrame) (m : Nat) : (wipeFrame f).atMoment m = f.atMoment m := by
  unfold OnBytes.ReqFrame.atMoment
  rfl

/-- So is `ReqFrame.foldShape`. -/
theorem foldShape_wipe (f : ReqFrame) (l : Nat) (L : GroupLayout) : (wipeFrame f).foldShape l L = f.foldShape l L := by
  unfold OnBytes.ReqFrame.foldShape
  rfl

/-- **`firstFront`** at a wiped frame, and at a statement with the same wiped copy, is alike to `firstFront` at the
frame and the statement. -/
theorem swFirstFront_rel {S S' : Statement} (hS : wipeSt S' = wipeSt S) (f : ReqFrame) :
    AlikeE wFront (firstFront S' (wipeFrame f)) (firstFront S f) := by
  unfold Tw.K2.firstFront
  rw [atMoment_wipe, foldShape_wipe]
  dsimp only [wipeFrame]
  refine alikeIte (AlikeE.error _) ?_
  refine alikeIte (AlikeE.error _) ?_
  cases f.shape.link[f.link]? with
  | none => exact AlikeE.error _
  | some L =>
    cases f.groups[f.link]? with
    | none => exact AlikeE.error _
    | some G =>
      dsimp only
      rcases (swNewGroup_rel hS f.shape.code f.shape.maskCode).split with ⟨e, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
      · rw [h1, h2]
        exact AlikeE.error e
      · rw [h1, h2]
        obtain ⟨S1', g'⟩ := a
        obtain ⟨S1, g⟩ := a'
        have e1 : wipeSt S1' = wipeSt S1 := (congrArg (fun q : Statement × Nat => q.1) ha :)
        have e2 : g' = g := (congrArg (fun q : Statement × Nat => q.2) ha :)
        subst e2
        refine AlikeE.ok ?_
        show (⟨wipeSt S1', _, _, _, _, _⟩ : Tw.K2.Front) = ⟨wipeSt S1, _, _, _, _, _⟩
        rw [e1]
        rfl

/-- What is compared of `firstBehind`'s result: the wiped statement, the wiped frame, and the numbers. -/
def wBehind (z : Statement × ReqFrame × Array Nat) : Statement × ReqFrame × Array Nat :=
  (wipeSt z.1, wipeFrame z.2.1, z.2.2)

/-- **`firstBehind` is alike** at statements and fronts with the same wiped copies. -/
theorem swFirstBehind_rel {S S' : Statement} (hS : wipeSt S' = wipeSt S) {x x' : Tw.K2.Front}
    (hx : wFront x' = wFront x) (s : Switched) (plain : List E) :
    AlikeE wBehind (firstBehind S' x' s plain) (firstBehind S x s plain) := by
  obtain ⟨st, f, own, others, T, pl⟩ := x
  obtain ⟨st', f', own', others', T', pl'⟩ := x'
  have hf : wipeFrame f' = wipeFrame f := (congrArg (fun q : Tw.K2.Front => q.f) hx :)
  have ho : own' = own := (congrArg (fun q : Tw.K2.Front => q.own) hx :)
  have ht : others' = others := (congrArg (fun q : Tw.K2.Front => q.others) hx :)
  subst ho ht
  have hg : f'.group = f.group := (congrArg (fun q : ReqFrame => q.group) hf :)
  unfold Tw.K2.firstBehind
  dsimp only
  refine alikeIte (AlikeE.error _) ?_
  cases s.others[own'.length]? with
  | none => exact AlikeE.error _
  | some mask =>
    dsimp only
    refine alikeIte (AlikeE.error _) ?_
    rcases (alikeFold wipeSt
        (fun (S : Statement) (y : ReqMessage × Nat) => Tw.K2.joinG S f'.group y.2 (decide (0 < y.1.life)))
        (fun (S : Statement) (y : ReqMessage × Nat) => Tw.K2.joinG S f.group y.2 (decide (0 < y.1.life)))
        (fun b b' y hb => by
          rw [hg]
          exact swJoin_rel hb f.group y.2 (decide (0 < y.1.life)))
        (zipT own' (s.others.extract 0 own'.length).toList) S' S hS).split with
      ⟨e, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
    · rw [h1, h2]
      exact AlikeE.error e
    · rw [h1, h2]
      refine AlikeE.ok ?_
      show (wipeSt a, wipeFrame _, _) = (wipeSt a', wipeFrame _, _)
      rw [ha]
      exact (congrArg (fun F : ReqFrame => (wipeSt a',
        ({ ({ F with
              plain := plain, keptBefore := s.kept, mask := some mask,
              atStart := F.atStart ++ s.others.extract (own'.length + 1) s.others.size } : ReqFrame) with
            own := F.own ++ s.others.extract 0 own'.length, next := .laterOrClose } : ReqFrame),
        s.others.extract 0 own'.length)) hf :)

/-- What is compared of `firstEW`'s result: the record with its statement and frame wiped, and the shapes of the columns
left. -/
def w9 (z : S9 × List OpenedColumn) : S9 × List (Nat × Nat × Nat) :=
  ({ z.1 with st := wipeSt z.1.st, frame := wipeFrame z.1.frame }, z.2.map colShape)

/-- **`firstEW` is alike** at a record and at that record with its frame wiped and a statement that has the same wiped
copy, at columns of the same shapes. -/
theorem swFirstEW_rel (P : Par9) (s : S9) {S' : Statement} (hS : wipeSt S' = wipeSt s.st) (rounds : List Fmt.RoundView)
    {cols cols' : List OpenedColumn} (hc : SameShape cols' cols) :
    AlikeE w9 (firstEW switchBehind P sendByL8 { s with st := S', frame := wipeFrame s.frame } rounds cols')
      (firstEW switchBehind P sendByL8 s rounds cols) := by
  rcases rounds with _ | ⟨rS, _ | ⟨rL, _ | ⟨r3, l⟩⟩⟩
  · exact AlikeE.error _
  · exact AlikeE.error _
  · unfold Tw.K2.firstEW
    dsimp only
    refine AlikeE.bind' (swFirstFront_rel hS s.frame) fun x' x hx => ?_
    have hp : x'.plain = x.plain := (congrArg (fun q : Tw.K2.Front => q.plain) hx :)
    rw [hp]
    refine alikeThrow Iff.rfl rfl ?_
    refine AlikeE.bind' (swSwitchE_rel P (s := s) (s' := { s with st := S', frame := wipeFrame s.frame }) rfl rfl rfl hx
      rS rL hc) fun z' z hz => ?_
    obtain ⟨w', roots'⟩ := z'
    obtain ⟨w, roots⟩ := z
    have hw : wOut w' = wOut w :=
      (congrArg (fun q : (Statement × TreeBook × List (Nat × Nat × Nat) × Switched) × Nat => q.1) hz :)
    have hr : roots' = roots :=
      (congrArg (fun q : (Statement × TreeBook × List (Nat × Nat × Nat) × Switched) × Nat => q.2) hz :)
    have w1 : wipeSt w'.st = wipeSt w.st :=
      (congrArg (fun q : Statement × TreeBook × List (Nat × Nat × Nat) × Switched => q.1) hw :)
    have w2 : w'.book = w.book :=
      (congrArg (fun q : Statement × TreeBook × List (Nat × Nat × Nat) × Switched => q.2.1) hw :)
    have w3 : w'.opened.map colShape = w.opened.map colShape :=
      (congrArg (fun q : Statement × TreeBook × List (Nat × Nat × Nat) × Switched => q.2.2.1) hw :)
    have w4 : w'.out = w.out :=
      (congrArg (fun q : Statement × TreeBook × List (Nat × Nat × Nat) × Switched => q.2.2.2) hw :)
    subst hr
    dsimp only
    rw [w4]
    refine AlikeE.bind' (swFirstBehind_rel w1 hx w.out s.plain) fun u' u hu => ?_
    obtain ⟨S2', f2', m'⟩ := u'
    obtain ⟨S2, f2, m⟩ := u
    have u1 : wipeSt S2' = wipeSt S2 := (congrArg (fun q : Statement × ReqFrame × Array Nat => q.1) hu :)
    have u2 : wipeFrame f2' = wipeFrame f2 := (congrArg (fun q : Statement × ReqFrame × Array Nat => q.2.1) hu :)
    refine AlikeE.ok ?_
    show ((⟨wipeSt S2', w'.book, _, wipeFrame f2', _, _⟩ : S9), w'.opened.map colShape) =
      (⟨wipeSt S2, w.book, _, wipeFrame f2, _, _⟩, w.opened.map colShape)
    rw [u1, u2, w2, w3]
  · exact AlikeE.error _

/-! ## 7 The row cut as the walk's steps are cut -/

/-- What is compared of `chainFirstEW`'s result: the record with its statement and its `ChainCheck` wiped, and the
shapes of the columns left. -/
def w9C (z : S9C × List OpenedColumn) : S9C × List (Nat × Nat × Nat) :=
  ({ z.1 with st := wipeSt z.1.st, check := wipeCheck z.1.check }, z.2.map colShape)

/-- **`chainFirstEW` is alike** in the same sense, with the record's `ChainCheck` wiped. -/
theorem swChain_rel (P : Par9) (s : S9C) {S' : Statement} (hS : wipeSt S' = wipeSt s.st) (rounds : List Fmt.RoundView)
    {cols cols' : List OpenedColumn} (hc : SameShape cols' cols) :
    AlikeE w9C (chainFirstEW switchBehind P sendByL8 { s with st := S', check := wipeCheck s.check } rounds cols')
      (chainFirstEW switchBehind P sendByL8 s rounds cols) := by
  unfold Tw.K2.chainFirstEW
  refine alikeIte (AlikeE.error _) ?_
  refine AlikeE.bind' (swFirstEW_rel P ⟨s.st, s.book, s.roots, s.check.frame, [], s.settled⟩ hS rounds hc)
    fun z' z hz => ?_
  obtain ⟨t', left'⟩ := z'
  obtain ⟨t, left⟩ := z
  have ht : ({ t' with st := wipeSt t'.st, frame := wipeFrame t'.frame } : S9) =
      { t with st := wipeSt t.st, frame := wipeFrame t.frame } :=
    (congrArg (fun q : S9 × List (Nat × Nat × Nat) => q.1) hz :)
  have hl : left'.map colShape = left.map colShape := (congrArg (fun q : S9 × List (Nat × Nat × Nat) => q.2) hz :)
  refine AlikeE.ok (Prod.ext ?_ hl)
  exact (congrArg (fun u : S9 => (⟨u.st, u.book, u.roots,
    { s.check with frame := u.frame, sent := u.frame.own, inLink := true, moments := 1 }, u.settled⟩ : S9C)) ht :)

/-- What is compared of `switchAloneEW`'s result: the switch's numbers, the record with its statement wiped, and the
shapes of the columns left. -/
def wAl (z : Switched × S9S × List OpenedColumn) : Switched × S9S × List (Nat × Nat × Nat) :=
  (z.1, { z.2.1 with st := wipeSt z.2.1.st }, z.2.2.map colShape)

/-- **`switchAloneEW` is alike** at fronts with the same wiped copy and columns of the same shapes, whatever statement
the record itself holds. -/
theorem swAlone_rel (P : Par9) (s : S9S) (S' : Statement) {x x' : Tw.K2.Front} (hx : wFront x' = wFront x)
    (rounds : List Fmt.RoundView) {cols cols' : List OpenedColumn} (hc : SameShape cols' cols) :
    AlikeE wAl (switchAloneEW switchBehind P sendByL8 { s with st := S' } x' rounds cols')
      (switchAloneEW switchBehind P sendByL8 s x rounds cols) := by
  rcases rounds with _ | ⟨rS, _ | ⟨rL, _ | ⟨r3, l⟩⟩⟩
  · exact AlikeE.error _
  · exact AlikeE.error _
  · unfold Tw.K2.switchAloneEW
    dsimp only
    refine AlikeE.bind' (swSwitchE_rel P (s := ⟨s.st, s.book, s.roots, x.f, [], s.settled⟩)
      (s' := ⟨S', s.book, s.roots, x'.f, [], s.settled⟩) rfl rfl rfl hx rS rL hc) fun z' z hz => ?_
    obtain ⟨w', roots'⟩ := z'
    obtain ⟨w, roots⟩ := z
    have hw : wOut w' = wOut w :=
      (congrArg (fun q : (Statement × TreeBook × List (Nat × Nat × Nat) × Switched) × Nat => q.1) hz :)
    have hr : roots' = roots :=
      (congrArg (fun q : (Statement × TreeBook × List (Nat × Nat × Nat) × Switched) × Nat => q.2) hz :)
    have w1 : wipeSt w'.st = wipeSt w.st :=
      (congrArg (fun q : Statement × TreeBook × List (Nat × Nat × Nat) × Switched => q.1) hw :)
    have w2 : w'.book = w.book :=
      (congrArg (fun q : Statement × TreeBook × List (Nat × Nat × Nat) × Switched => q.2.1) hw :)
    have w3 : w'.opened.map colShape = w.opened.map colShape :=
      (congrArg (fun q : Statement × TreeBook × List (Nat × Nat × Nat) × Switched => q.2.2.1) hw :)
    have w4 : w'.out = w.out :=
      (congrArg (fun q : Statement × TreeBook × List (Nat × Nat × Nat) × Switched => q.2.2.2) hw :)
    refine AlikeE.ok ?_
    show (w'.out, (⟨wipeSt w'.st, w'.book, roots', _⟩ : S9S), w'.opened.map colShape) =
      (w.out, ⟨wipeSt w.st, w.book, roots, _⟩, w.opened.map colShape)
    rw [w1, w2, w3, w4, hr]
  · exact AlikeE.error _

/-- **`headSwitchEW` is alike** at two frames and at their wiped copies, at statements with the same wiped copy. -/
theorem swHead_rel (P : Par9) (s : S9S) {S' : Statement} (hS : wipeSt S' = wipeSt s.st) (f0 fr : ReqFrame)
    (rounds : List Fmt.RoundView) {cols cols' : List OpenedColumn} (hc : SameShape cols' cols) :
    AlikeE wAl (headSwitchEW switchBehind P sendByL8 { s with st := S' } (wipeFrame f0) (wipeFrame fr) rounds cols')
      (headSwitchEW switchBehind P sendByL8 s f0 fr rounds cols) := by
  have e1 : (wipeFrame f0).link = f0.link := rfl
  have e2 : (wipeFrame f0).groups = f0.groups := rfl
  unfold Tw.K2.headSwitchEW
  rw [e1, e2, atMoment_wipe, foldShape_wipe]
  cases f0.groups[f0.link]? with
  | none => exact AlikeE.error _
  | some G =>
    refine swAlone_rel P s S' ?_ rounds hc
    show (⟨wipeSt S', wipeFrame (wipeFrame fr), _, _, _, _⟩ : Tw.K2.Front) = ⟨wipeSt s.st, wipeFrame fr, _, _, _, _⟩
    rw [hS]
    rfl

/-- **`finishSwitchEW` is alike** at a frame and at its wiped copy, at statements with the same wiped copy. -/
theorem swFinish_rel (P : Par9) (s : S9S) {S' : Statement} (hS : wipeSt S' = wipeSt s.st) (fr : ReqFrame)
    (T : SwitchTarget) (rounds : List Fmt.RoundView) {cols cols' : List OpenedColumn} (hc : SameShape cols' cols) :
    AlikeE wAl (finishSwitchEW switchBehind P sendByL8 { s with st := S' } (wipeFrame fr) T rounds cols')
      (finishSwitchEW switchBehind P sendByL8 s fr T rounds cols) := by
  have e1 : (wipeFrame fr).link = fr.link := rfl
  unfold Tw.K2.finishSwitchEW
  rw [e1, foldShape_wipe]
  refine swAlone_rel P s S' ?_ rounds hc
  show (⟨wipeSt S', wipeFrame (wipeFrame fr), _, _, _, _⟩ : Tw.K2.Front) = ⟨wipeSt s.st, wipeFrame fr, _, _, _, _⟩
  rw [hS]
  rfl

/-! ## 8 The kind at the first chain's state -/

/-- The shapes of the columns that `flat` makes can be computed from the groups' shapes alone. -/
theorem flatShape : ∀ (rd : List (Nat × Nat × Nat)) (gs : List (List (Nat × List UInt64))),
    ((rd.zip gs).flatMap fun x => x.2.map fun c => ((x.1.1, c.1, c.2) : OpenedColumn)).map colShape =
      (rd.zip (gs.map grpShape)).flatMap fun x => x.2.map fun c => (x.1.1, c.1, c.2)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | r :: rd, g :: gs => by
    have ih := flatShape rd gs
    have hd : (g.map fun c => ((r.1, c.1, c.2) : OpenedColumn)).map colShape =
        (grpShape g).map fun c => (r.1, c.1, c.2) := by
      unfold grpShape
      rw [List.map_map, List.map_map]
      rfl
    rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons, List.map_append,
      ih]
    exact congrArg (fun l => l ++ _) hd

/-- **`flat` turns groups of the same shapes into columns of the same shapes.** -/
theorem flat_same (p : P2) {gs gs' : List (List (Nat × List UInt64))} (h : SameG gs gs') :
    SameShape (flat p gs) (flat p gs') := by
  have h' : gs.map grpShape = gs'.map grpShape := h
  unfold SameShape VerifiableInference.Desc.First.K2.flat
  rw [flatShape, flatShape, h']

/-- Two lists of columns with the same shapes are both empty or both not. -/
theorem isEmpty_shape {l l' : List OpenedColumn} (h : l'.map colShape = l.map colShape) : l'.isEmpty = l.isEmpty := by
  cases l' with
  | nil =>
    cases l with
    | nil => rfl
    | cons a t => simp at h
  | cons a' t' =>
    cases l with
    | nil => simp at h
    | cons a t => rfl

/-- `allTaken` gives the same result at equally many groups and at columns left of the same shapes. -/
theorem allTaken_rel (p : P2) {gs gs' : List (List (Nat × List UInt64))} (hg : gs'.length = gs.length)
    {l l' : List OpenedColumn} (h : l'.map colShape = l.map colShape) : allTaken p gs' l' = allTaken p gs l := by
  unfold VerifiableInference.Desc.First.K2.allTaken
  rw [isEmpty_shape h, hg]

/-- **`decideWith sendByL8 p` is alike at the wiped state and at the state**, at groups of the same shapes. -/
theorem decideWith_wiped (p : P2) (s : S) (rs : List Fmt.RoundView) {gs gs' : List (List (Nat × List UInt64))}
    (h : SameG gs gs') : AlikeE wipeS (decideWith sendByL8 p (wipeS s) rs gs') (decideWith sendByL8 p s rs gs) := by
  have hc : SameShape (flat p gs') (flat p gs) := flat_same p h.symm
  have hn : gs'.length = gs.length := h.symm.length
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  unfold VerifiableInference.Desc.First.K2.decideWith
  dsimp only [wipeS]
  refine alikeIte (AlikeE.error _) ?_
  cases p.stands with
  | link =>
    cases here with
    | between =>
      try dsimp only [wipeHere]
      refine AlikeE.bind' (swChain_rel (par9 p)
        ⟨st, book, roots, check, S.noneWaits ⟨st, book, roots, owed, failed, check, out, Here.between, req⟩⟩
        (wipeSt_idem st) rs hc) fun x' x hx => ?_
      obtain ⟨t', left'⟩ := x'
      obtain ⟨t, left⟩ := x
      have ht : ({ t' with st := wipeSt t'.st, check := wipeCheck t'.check } : S9C) =
          { t with st := wipeSt t.st, check := wipeCheck t.check } :=
        (congrArg (fun q : S9C × List (Nat × Nat × Nat) => q.1) hx :)
      have hl : left'.map colShape = left.map colShape :=
        (congrArg (fun q : S9C × List (Nat × Nat × Nat) => q.2) hx :)
      have hg : t'.check.frame.group = t.check.frame.group :=
        (congrArg (fun q : S9C => q.check.frame.group) ht :)
      refine AlikeE.head_eq' (allTaken_rel p hn hl) fun _ => ?_
      refine AlikeE.head_eq' (congrArg (rightGroup p) hg) fun _ => ?_
      exact AlikeE.ok (congrArg (fun q : S9C =>
        (⟨q.st, q.book, q.roots, none, failed, q.check, out, Here.between, req⟩ : S)) ht :)
    | lay a => exact AlikeE.error _
    | att a => exact AlikeE.error _
    | head a => exact AlikeE.error _
    | fin a => exact AlikeE.error _
    | mem a => exact AlikeE.error _
  | head =>
    cases here with
    | between => exact AlikeE.error _
    | lay a => exact AlikeE.error _
    | att a => exact AlikeE.error _
    | head a =>
      try dsimp only [wipeHere]
      refine AlikeE.head_eq' rfl fun _ => ?_
      refine AlikeE.bind' (swHead_rel (par9 p)
        ⟨st, book, roots, S.noneWaits ⟨st, book, roots, owed, failed, check, out, Here.head a, req⟩⟩
        (wipeSt_idem st) check.frame a.fr rs hc) fun x' x hx => ?_
      obtain ⟨sw', t', left'⟩ := x'
      obtain ⟨sw, t, left⟩ := x
      have hs : sw' = sw := (congrArg (fun q : Switched × S9S × List (Nat × Nat × Nat) => q.1) hx :)
      have ht : ({ t' with st := wipeSt t'.st } : S9S) = { t with st := wipeSt t.st } :=
        (congrArg (fun q : Switched × S9S × List (Nat × Nat × Nat) => q.2.1) hx :)
      have hl : left'.map colShape = left.map colShape :=
        (congrArg (fun q : Switched × S9S × List (Nat × Nat × Nat) => q.2.2) hx :)
      subst hs
      refine AlikeE.head_eq' (allTaken_rel p hn hl) fun _ => ?_
      exact AlikeE.ok (congrArg (fun q : S9S =>
        (⟨q.st, q.book, q.roots, none, failed, wipeCheck check, out,
          wipeHere (Here.head { a with kept := sw'.kept, ids := sw'.others }), req⟩ : S)) ht :)
    | fin a => exact AlikeE.error _
    | mem a => exact AlikeE.error _
  | finish =>
    cases here with
    | between => exact AlikeE.error _
    | lay a => exact AlikeE.error _
    | att a => exact AlikeE.error _
    | head a => exact AlikeE.error _
    | fin a =>
      try dsimp only [wipeHere]
      refine AlikeE.head_eq' rfl fun _ => ?_
      refine AlikeE.head_eq' rfl fun G => ?_
      refine AlikeE.bind' (swFinish_rel (par9 p)
        ⟨st, book, roots, S.noneWaits ⟨st, book, roots, owed, failed, check, out, Here.fin a, req⟩⟩
        (wipeSt_idem st) a.fr G.target rs hc) fun x' x hx => ?_
      obtain ⟨sw', t', left'⟩ := x'
      obtain ⟨sw, t, left⟩ := x
      have hs : sw' = sw := (congrArg (fun q : Switched × S9S × List (Nat × Nat × Nat) => q.1) hx :)
      have ht : ({ t' with st := wipeSt t'.st } : S9S) = { t with st := wipeSt t.st } :=
        (congrArg (fun q : Switched × S9S × List (Nat × Nat × Nat) => q.2.1) hx :)
      have hl : left'.map colShape = left.map colShape :=
        (congrArg (fun q : Switched × S9S × List (Nat × Nat × Nat) => q.2.2) hx :)
      subst hs
      refine AlikeE.head_eq' (allTaken_rel p hn hl) fun _ => ?_
      exact AlikeE.ok (congrArg (fun q : S9S =>
        (⟨q.st, q.book, q.roots, none, failed, wipeCheck check, out,
          wipeHere (Here.fin { a with sw := sw' }), req⟩ : S)) ht :)
    | mem a => exact AlikeE.error _

/-- **The code switch satisfies `Whole2 wipeS`**: at states with the same wiped copy and groups of columns of the same
shapes its `decide` fails with the same message, or returns states with the same wiped copy; its lists `claims` and
`after` are empty. -/
theorem k2_whole2 {Cl : Type} (p : P2) : Whole2 wipeS (codeSwitchKind p : Block S Cl) := by
  refine ⟨Decides2.of_wiped_cols fun s rs gs gs' h => decideWith_wiped p s rs h, ?_, ?_⟩
  · intro c hc
    cases hc
  · intro c hc
    cases hc

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.alikeThrow
#print axioms ProofFile.Honest.K10.alikeIfLet
#print axioms ProofFile.Honest.K10.alikeFoldA
#print axioms ProofFile.Honest.K10.getDRel
#print axioms ProofFile.Honest.K10.oracleRead
#print axioms ProofFile.Honest.K10.dOf_rel
#print axioms ProofFile.Honest.K10.st_of_wipeD
#print axioms ProofFile.Honest.K10.closeLedgerG_rel
#print axioms ProofFile.Honest.K10.swJoin_rel
#print axioms ProofFile.Honest.K10.rowL_rel2
#print axioms ProofFile.Honest.K10.whyRow_rel
#print axioms ProofFile.Honest.K10.addRowsG_rel
#print axioms ProofFile.Honest.K10.wSend5
#print axioms ProofFile.Honest.K10.wSend3
#print axioms ProofFile.Honest.K10.wSent
#print axioms ProofFile.Honest.K10.sampleLoop_rel
#print axioms ProofFile.Honest.K10.sendP_rel
#print axioms ProofFile.Honest.K10.sendOpen_rel
#print axioms ProofFile.Honest.K10.sendByL8_rel
#print axioms ProofFile.Honest.K10.wOut
#print axioms ProofFile.Honest.K10.swBehind_wiped
#print axioms ProofFile.Honest.K10.shIn
#print axioms ProofFile.Honest.K10.swBehind_rel
#print axioms ProofFile.Honest.K10.wFront
#print axioms ProofFile.Honest.K10.wSw
#print axioms ProofFile.Honest.K10.swSwitchE_rel
#print axioms ProofFile.Honest.K10.wStN
#print axioms ProofFile.Honest.K10.swNewGroup_rel
#print axioms ProofFile.Honest.K10.atMoment_wipe
#print axioms ProofFile.Honest.K10.foldShape_wipe
#print axioms ProofFile.Honest.K10.swFirstFront_rel
#print axioms ProofFile.Honest.K10.wBehind
#print axioms ProofFile.Honest.K10.swFirstBehind_rel
#print axioms ProofFile.Honest.K10.w9
#print axioms ProofFile.Honest.K10.swFirstEW_rel
#print axioms ProofFile.Honest.K10.w9C
#print axioms ProofFile.Honest.K10.swChain_rel
#print axioms ProofFile.Honest.K10.wAl
#print axioms ProofFile.Honest.K10.swAlone_rel
#print axioms ProofFile.Honest.K10.swHead_rel
#print axioms ProofFile.Honest.K10.swFinish_rel
#print axioms ProofFile.Honest.K10.flatShape
#print axioms ProofFile.Honest.K10.flat_same
#print axioms ProofFile.Honest.K10.isEmpty_shape
#print axioms ProofFile.Honest.K10.allTaken_rel
#print axioms ProofFile.Honest.K10.decideWith_wiped
#print axioms ProofFile.Honest.K10.k2_whole2
