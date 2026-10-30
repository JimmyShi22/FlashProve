-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SwUnfold.lean: a yes of the code switch's part on two rounds, and of what
stands behind it on none, gives the record `Did` of Johnson/Desc/K12/Law/SwDid.lean.

Statements and proofs: `theorem switchUnfolds (p : P12) : SwitchUnfolds p`. Code against a record,
by unfolding: no field, no probability, no hash.
Main names:
  `joinS_ok`, `addRowS_ok`, `addRowsS_ok`: the plain texts `Tw.L9.joinS` and `Tw.L9.addRowS` leave
    the library's pure `withMessageInGroup`, `withRow` and `withRows`, and have asked what `RowChecked` keeps.
  `locPositions_ok`: the closing of the round of the positions: no item is left, and the positions
    are `Positions.ofDraws`.
  `tailB`, `switchBehind_eq`, `tailB_ok`: a device of the proof: the last lines of `switchBehind`
    under a name, tied to the source by rfl, so that the two arms of the ledger's closing meet in
    one lemma. `tailB` stands in no statement outside this file.
  `switchBehind_ok`: what a yes of `switchBehind` holds at a target without kept members; the
    ledger's closing is the library's `ledgerShut`.
  `recvP_ok`, `admitP_ok`, `sendOne_ok`: what a yes of `recvP`, of `admitP` and of `sendP` over
    `groundG` holds: one sampled message with one answer, the others not sampled.
  `switchE_ok`: what a yes of `switchE` holds on a stretch of just two rounds.
  `beginRunP_ok`, `beginRunE_ok`, `askOwedE_ok`, `behindJ_ok`: the last lines of the switch's test.
  `switchUnfolds`: the statement.
Limits: The proofs follow the patterns of the library's lemmas on runs in a context (`sendOne_inv`,
`switchAdmit_inv`, `switchVerify_inv`, `csVerify_inv`, `join_inv`, `addRow_inv`, `addRows_inv`,
`admit_inv`) and call none of them. They call six lemmas on pure functions and plain records:
`todo_one`, `sent_first`, `seedsOf_one`, `RowChecked.withRow`, `withRows_group`, `joined_group`.
Where the plain text asks a test in the description's own words, the proofs go back to the older
test by eight theorems of agreement: `Own.placeFits_agrees`, `Own.formFits_agrees`,
`Own.treesMade_eq`, `Own.seedsMade_eq`, `Own.formMade_eq`, `Own.layout_of_group`,
`Tw.K2.targetOk_eq`, and, in one direction alone, `Tw.K2.rowsMade_some`. `Did` keeps less than the
parts ask: the proof does not spend the entries' names and numbers, «all is used up», most of the
guards on the target, of `joinS` all but «the group is there» and «no test has begun», and of the
four clauses of `beginRunP` all but «the group is there». The premises (p.early = true, p.answers =
1, t1.pass = .single, the two yeses) are not shown here to be met by anything: that is a run's to
show. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.SwDid
import Johnson.Desc.K12.Law.FoldKeeps
import Johnson.Desc.Own.RowsAgree
import Johnson.Desc.Own.ShapesAgree
import Johnson.Desc.Own.TreesAgree
import Johnson.Desc.Own.LayoutAgree
import Johnson.Desc.Own.SendAgree
import Johnson.Top.H0.Tw.K2.TargetAgree
import Johnson.Top.H0.Tw.K2.RowsMadeAgree

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.FoldLaw (bind_ok)
open _root_.Desc.Plain (DState GPar sendP sampleLoop rowsFor answersOf)

/-! ## Small tools -/

theorem obind_ok {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem opt_ok {α : Type} {n : String} {x : Option α} {a : α} (h : H2K.opt n x = .ok a) :
    x = some a := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

theorem named_ok {α : Type} {n : String} {x : Option α} {a : α}
    (h : VerifiableInference.Desc.named n x = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

theorem nn {b : Bool} (h : ¬ (!b) = true) : b = true := by
  cases b with
  | true => rfl
  | false => exact absurd rfl h

/-! ## The texts typed anew against the library's pure effects -/

/-- joinS (a plain text after Blk.join) leaves the library's withMessageInGroup. -/
theorem joinS_ok {S S' : Statement} {g o : Nat} {kept : Bool}
    (h : Tw.L9.joinS S g o kept = .ok S') :
    ∃ G, S.groups[g]? = some G ∧ G.inRun = false ∧ S' = withMessageInGroup S g o kept G := by
  unfold Tw.L9.joinS at h
  split at h
  · rename_i G x hG hx
    split at h
    · cases h
    · rename_i h18
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h
              replace h18 := nn h18
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at h18
              exact ⟨G, hG, h18.2, rfl⟩
  · cases h

/-- addRowS (a plain text after Blk.addRow) leaves the library's withRow, and has asked what
RowChecked keeps. -/
theorem addRowS_ok {S S' : Statement} {g : Nat} {row : Row}
    (h : Tw.L9.addRowS S g row = .ok S') :
    row.kind ≠ .sample ∧ RowChecked S row ∧ S' = withRow S g row := by
  unfold Tw.L9.addRowS at h
  split at h
  · cases h
  · rename_i G hG
    split at h
    · cases h
    · rename_i m1
      split at h
      · cases h
      · rename_i t1
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i t3
            split at h
            · cases h
            · rename_i t4
              split at h
              · cases h
              · cases h
                replace m1 := nn m1
                replace t1 := nn t1
                replace t3 := nn t3
                replace t4 := nn t4
                simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at m1
                simp only [← Own.placeFits_agrees, ← Own.formFits_agrees] at t1 t3 t4
                simp only [Array.all_eq_true_iff_forall_mem,
                  Blk.placeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at t1 t3 t4
                exact ⟨m1.2, ⟨fun t ht => (t1 t (Array.mem_toList_iff.1 ht)).2.1.2,
                  fun w hw => (t3 w (Array.mem_toList_iff.1 hw)).1.2,
                  fun f hf => (t4 f (Array.mem_toList_iff.1 hf)).2⟩, rfl⟩

/-- The rows one by one. -/
theorem addRowsS_ok (g : Nat) : ∀ (l : List Row) (S S' : Statement),
    l.foldlM (fun S r => Tw.L9.addRowS S g r) S = .ok S' →
    (∀ r ∈ l, r.kind ≠ .sample ∧ RowChecked S r) ∧ S' = withRows S g l
  | [], S, S', h => by
    cases h
    exact ⟨fun _ hr => (nomatch hr), rfl⟩
  | r :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bind_ok h
    obtain ⟨hk, hch, rfl⟩ := addRowS_ok h1
    obtain ⟨hl, rfl⟩ := addRowsS_ok g l _ _ h2
    refine ⟨fun x hx => ?_, rfl⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hk, hch⟩
    · exact ⟨(hl x hx).1, (hl x hx).2.withRow g r⟩

/-- The closing of the round of the positions. -/
theorem locPositions_ok {i : Tw.L9.SwIn} {logN : Nat} {pos : Positions}
    (h : Tw.L9.locPositions i logN = .ok pos) :
    i.itemsLeft = 0 ∧ pos = Positions.ofDraws logN i.drawn.poss := by
  unfold Tw.L9.locPositions at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i h4
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · cases h
                exact ⟨by simpa using h4, rfl⟩

/-! ## The step behind the sending -/

/-- A device of the proof, no new text: switchBehind's own last lines (Switch.lean, from «joinS S1»
on) under a name, so that the two arms of the ledger's closing meet in one lemma; tied to the source
by rfl (switchBehind_eq). -/
def tailB (i : Tw.L9.SwIn) (out : Switched) (B : TreeBook) (left : List Tw.L9.Col) (y : Array E)
    (S1 : Statement) : Except String Tw.L9.SwOut := do
  let S2 ← Tw.L9.joinS S1 i.grp out.g false
  let S3 ← (out.kept.zip i.T.kept).foldlM (fun S p => Tw.L9.joinS S i.grp p.1 p.2.keptAgain) S2
  let _ ← match S3.groups[i.grp]? with
    | some G => if G.inRun then throw "G32: the new group's test has begun" else pure ()
    | none => throw "G32: the new group is not there"
  let rows ← match _root_.Tw.K2.rowsMade S3 i.old i.T out.g out.kept out.positions y with
    | some l => pure l
    | none => throw "G33: the rows cannot be made"
  let S4 ← rows.foldlM (fun S r => Tw.L9.addRowS S i.grp r) S3
  pure ⟨S4, B, left, out⟩

theorem switchBehind_eq (i : Tw.L9.SwIn) : Tw.L9.switchBehind i = (do
  let code ← match i.st.codes.base[i.old.code]? with
    | some c => pure c
    | none => throw "G30: the old main code is not there"
  let pos ← Tw.L9.locPositions i code.logN
  let out : Switched :=
    { g := i.ids.getD 0 noId, kept := i.ids.extract 1 (1 + i.T.kept.size),
      others := i.ids.extract (1 + i.T.kept.size) i.ids.size, positions := pos }
  let x ← Tw.L9.readOld i pos
  let S1 ← if 0 < i.T.shape.maskRows then
      (if out.g < i.st.oracles.size then
        pure { i.st with oracles := i.st.oracles.modify out.g fun x =>
          { x with ledger := x.ledger.map fun l => { l with closed := true } } }
      else throw "G31: g is not there")
    else pure i.st
  tailB i out x.1 x.2.1 x.2.2 S1) := rfl

theorem tailB_ok (i : Tw.L9.SwIn) (out : Switched) (B : TreeBook) (left : List Tw.L9.Col)
    (y : Array E) (S1 : Statement) (o : Tw.L9.SwOut) (hk : i.T.kept = #[])
    (h : tailB i out B left y S1 = .ok o) :
    ∃ (G : Group) (rows : List Row),
      S1.groups[i.grp]? = some G ∧ G.inRun = false ∧
      switchRows (withMessageInGroup S1 i.grp out.g false G) i.old i.T out.g out.kept out.positions y
        = some rows ∧
      (∀ r ∈ rows, r.kind ≠ .sample ∧ RowChecked (withMessageInGroup S1 i.grp out.g false G) r) ∧
      o = ⟨withRows (withMessageInGroup S1 i.grp out.g false G) i.grp rows, B, left, out⟩ := by
  unfold tailB at h
  obtain ⟨S2, h2, h⟩ := bind_ok h
  obtain ⟨S3, h3, h⟩ := bind_ok h
  obtain ⟨G, hG, hrun, rfl⟩ := joinS_ok h2
  have e3 : S3 = withMessageInGroup S1 i.grp out.g false G := by
    rw [hk] at h3
    have hz : out.kept.zip (#[] : Array KeptTarget) = #[] := by simp
    rw [hz] at h3
    cases h3
    rfl
  subst e3
  dsimp only at h
  split at h
  · split at h
    · cases h
    · simp only [pure_bind] at h
      split at h
      · rename_i rows h5
        obtain ⟨S4, h6, h⟩ := bind_ok h
        cases h
        obtain ⟨hkinds, rfl⟩ := addRowsS_ok _ _ _ _ h6
        exact ⟨G, rows, hG, hrun, (_root_.Tw.K2.rowsMade_some h5).2, hkinds, rfl⟩
      · cases h
  · cases h

/-- What a yes of switchBehind holds, where the target names no kept member. -/
theorem switchBehind_ok (i : Tw.L9.SwIn) (o : Tw.L9.SwOut) (hk : i.T.kept = #[])
    (h : Tw.L9.switchBehind i = .ok o) :
    ∃ (code : OnBytes.Code) (y : Array E) (G : Group) (rows : List Row),
      i.st.codes.base[i.old.code]? = some code ∧ i.itemsLeft = 0 ∧
      o.out = { g := i.ids.getD 0 noId, kept := #[], others := i.ids.extract 1 i.ids.size,
                positions := Positions.ofDraws code.logN i.drawn.poss } ∧
      Tw.L9.readOld i o.out.positions = .ok (o.book, o.opened, y) ∧
      (ledgerShut i.st i.T o.out.g).groups[i.grp]? = some G ∧ G.inRun = false ∧
      switchRows (withMessageInGroup (ledgerShut i.st i.T o.out.g) i.grp o.out.g false G) i.old i.T o.out.g #[]
        o.out.positions y = some rows ∧
      (∀ r ∈ rows, r.kind ≠ .sample ∧
        RowChecked (withMessageInGroup (ledgerShut i.st i.T o.out.g) i.grp o.out.g false G) r) ∧
      o.st = withRows (withMessageInGroup (ledgerShut i.st i.T o.out.g) i.grp o.out.g false G) i.grp rows := by
  rw [switchBehind_eq] at h
  cases hcode : i.st.codes.base[i.old.code]? with
  | none => simp only [hcode] at h; cases h
  | some code =>
  simp only [hcode, pure_bind] at h
  obtain ⟨pos, hp, h⟩ := bind_ok h
  obtain ⟨⟨B, left, y⟩, hr, h⟩ := bind_ok h
  obtain ⟨hleft, rfl⟩ := locPositions_ok hp
  have hkept : i.ids.extract 1 (1 + i.T.kept.size) = #[] := by
    rw [hk]
    simp
  have hoth : i.ids.extract (1 + i.T.kept.size) i.ids.size = i.ids.extract 1 i.ids.size := by
    rw [hk]
    rfl
  rw [hkept, hoth] at h
  replace h : tailB i
      (⟨i.ids.getD 0 noId, #[], i.ids.extract 1 i.ids.size,
        Positions.ofDraws code.logN i.drawn.poss⟩ : Switched) B left y
      (ledgerShut i.st i.T (i.ids.getD 0 noId)) = .ok o := by
    unfold ledgerShut
    by_cases hm : 0 < i.T.shape.maskRows
    · rw [if_pos hm] at h ⊢
      obtain ⟨S1, h1, h⟩ := bind_ok h
      split at h1
      · cases h1
        exact h
      · cases h1
    · rw [if_neg hm] at h ⊢
      exact h
  obtain ⟨G, rows, g1, g2, g3, g4, rfl⟩ := tailB_ok _ _ _ _ _ _ _ hk h
  exact ⟨code, y, G, rows, rfl, hleft, rfl, hr, g1, g2, g3, g4, rfl⟩

/-! ## The sending -/

/-- What a yes of recvP holds. -/
theorem recvP_ok {firstTree : Nat} {d d₁ : DState Unit} {sent : Array OracleNotice}
    {ids : Array Nat} (h : Ground.recvP firstTree d sent = some (ids, d₁)) :
    ∃ lay, layTrees d.st.codes sent = some lay ∧ d.st.oracles.size = d.book.place.size ∧
      ids = (Array.range sent.size).map (· + d.st.oracles.size) ∧
      d₁ = { d with st := stSent d.st sent
                    book := bookSentP firstTree d.roots d.st d.book sent lay
                    roots := d.roots + lay.shapes.size } := by
  unfold Ground.recvP at h
  split at h
  · rename_i hok
    rw [Own.treesMade_eq] at h
    cases hl : layTrees d.st.codes sent with
    | none => rw [hl] at h; cases h
    | some lay =>
      rw [hl] at h
      cases h
      simp only [Ground.ok, Ground.recvL, Ground.sentL, List.all_append, List.all_cons,
        List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hok
      exact ⟨lay, rfl, hok.2, rfl, rfl⟩
  · cases h

/-- What a yes of admitP holds. -/
theorem admitP_ok {d d' : DState Unit} {o : Nat} {rows : Array Row}
    (h : Ground.admitP d o rows = some d') :
    ∃ x places, d.st.oracles[o]? = some x ∧ Send.pad d.st.codes x.shape = some places ∧
      d' = { d with st := admitted d.st o x.shape places rows } := by
  unfold Ground.admitP at h
  split at h
  · obtain ⟨x, hx, h⟩ := obind_ok h
    obtain ⟨places, hp, h⟩ := obind_ok h
    cases h
    exact ⟨x, places, hx, hp, rfl⟩
  · cases h

/-- What a yes of the sending holds: one sampled oracle message with one answer, with others in the
same prover's message that are not sampled. (The pattern: sendOne_inv.) -/
theorem sendOne_ok (p : GPar) (d d₂ : DState Unit) (N : OracleNotice)
    (others : Array OracleNotice) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (sd an : List E) (took : Nat)
    (h1 : N.shape.answers = 1) (ho : ∀ n ∈ others, n.shape.answers = 0)
    (h : sendP Ground.groundG p false d (#[N] ++ others) r₁ r₂ = some (ids, sd, an, took, d₂)) :
    ∃ lay beta row alpha places vs,
      layTrees d.st.codes (#[N] ++ others) = some lay ∧
      d.st.oracles.size = d.book.place.size ∧
      ids = (Array.range (#[N] ++ others).size).map (· + d.st.oracles.size) ∧
      r₁.vals = [] ∧
      (r₁.drawn.elems.map E.ofTriple).drop (Send.cube d.st.codes N.shape).bits = [beta] ∧
      isZeroE beta = false ∧
      Send.form d.st.codes N.shape d.st.oracles.size
        ⟨(r₁.drawn.elems.map E.ofTriple).take (Send.cube d.st.codes N.shape).bits, beta⟩ 0
        = some row ∧
      r₂.vals = .answer alpha.triple :: vs ∧ took = 1 ∧
      Send.pad d.st.codes N.shape = some places ∧
      d₂ = { d with
        st := admitted (stSent d.st (#[N] ++ others)) d.st.oracles.size N.shape places
          #[{ row with target := alpha }]
        book := bookSentP p.firstTree d.roots d.st d.book (#[N] ++ others) lay
        roots := d.roots + lay.shapes.size } := by
  unfold sendP at h
  obtain ⟨⟨ids', d₁⟩, hr, h⟩ := obind_ok h
  obtain ⟨lay, hlay, hplaces, rfl, rfl⟩ := recvP_ok hr
  have htodo := todo_one d.st N others (by omega) ho
  unfold todoOf at htodo
  dsimp only at h
  rw [htodo] at h
  obtain ⟨shapes, hsh, h⟩ := obind_ok h
  have hshapes : shapes = [N.shape] := by
    simp only [List.mapM_cons, List.mapM_nil, sent_first] at hsh
    exact (Option.some.inj hsh).symm
  subst hshapes
  have hcodes : (stSent d.st (#[N] ++ others)).codes = d.st.codes := rfl
  simp only [List.foldl_cons, List.foldl_nil, h1, Nat.zero_max, Nat.zero_add, hcodes] at h
  obtain ⟨seeds, hseeds, h⟩ := obind_ok h
  rw [Own.seedsMade_eq] at hseeds
  obtain ⟨beta, hbeta, rfl⟩ := seedsOf_one _ _ _ hseeds
  obtain ⟨an', han, h⟩ := obind_ok h
  split at h
  · rename_i hc
    obtain ⟨⟨d2, left⟩, hloop, h⟩ := obind_ok h
    split at h
    · cases h
      simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_cons, List.all_nil, Bool.and_true,
        Bool.not_eq_true', beq_iff_eq] at hc
      have hans : ∃ x vs, r₂.vals = .answer x :: vs ∧ an = [E.ofTriple x] := by
        unfold answersOf at han
        cases hv : r₂.vals with
        | nil =>
          rw [hv] at han
          cases han
          cases hc.1.2
        | cons v vs =>
          rw [hv] at han
          simp only [List.take_succ_cons, List.take_zero, List.mapM_cons, List.mapM_nil] at han
          cases v <;> first | (cases han; done) | skip
          cases han
          exact ⟨_, vs, rfl, rfl⟩
      obtain ⟨x, vs, hv, rfl⟩ := hans
      simp only [List.zip_cons_cons, List.zip_nil_left, sampleLoop, h1,
        show List.range 1 = [0] from rfl, rowsFor, List.getElem?_cons_zero,
        Own.formMade_eq] at hloop
      cases hf : Send.form d.st.codes N.shape d.st.oracles.size
          ⟨(r₁.drawn.elems.map E.ofTriple).take (Send.cube d.st.codes N.shape).bits, beta⟩ 0 with
      | none => rw [hf] at hloop; cases hloop
      | some row =>
        rw [hf] at hloop
        dsimp only at hloop
        split at hloop
        · cases hloop
        · rename_i d' had
          cases hloop
          obtain ⟨x', places, a1, a2, rfl⟩ := admitP_ok had
          obtain rfl : ({ shape := N.shape } : OnBytes.Oracle) = x' :=
            Option.some.inj ((sent_first d.st N others).symm.trans a1)
          exact ⟨lay, beta, row, E.ofTriple x, places, vs, hlay, hplaces, rfl, hc.1.1.1.1.1.1.2,
            hbeta, hc.1.1.2, hf, hv, rfl, a2, rfl⟩
    · cases h
  · cases h

/-! ## The switch's part -/

/-- What a yes of switchE holds, on a stretch of two rounds, at a target without kept members and
with one answer. -/
theorem switchE_ok (old : SingleRows) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice)
    (s s' : H2K.PS) (out : Switched) (theta : E) (rS rC : Fmt.RoundView) (hk : T.kept = #[])
    (h1 : T.shape.answers = 1) (ho : ∀ n ∈ others, n.shape.answers = 0)
    (hrs : s.rounds = [rS, rC])
    (h : H2K.switchE old T gp others true s = .ok ((out, theta), s')) :
    ∃ (lay : TreeLay) (beta alpha : E) (smp : Row) (places : List PadPlace) (code : OnBytes.Code)
      (y : Array E) (G : Group) (rows : List Row) (i : Tw.L9.SwIn),
      switchTargetCheck s.d.st old T = true ∧
      layTrees s.d.st.codes (sentOf T others) = some lay ∧
      s.d.st.oracles.size = s.d.book.place.size ∧
      rS.vals = [] ∧
      (rS.drawn.elems.map E.ofTriple).drop (Send.cube s.d.st.codes T.shape).bits = [beta] ∧
      isZeroE beta = false ∧
      Send.form s.d.st.codes T.shape s.d.st.oracles.size
        ⟨(rS.drawn.elems.map E.ofTriple).take (Send.cube s.d.st.codes T.shape).bits, beta⟩ 0
        = some smp ∧
      Send.pad s.d.st.codes T.shape = some places ∧
      rC.vals = [.answer alpha.triple] ∧
      rC.drawn.elems.map E.ofTriple = [theta] ∧
      s.d.st.codes.base[old.code]? = some code ∧
      out = { g := s.d.st.oracles.size, kept := #[],
              others := (Array.range others.size).map (· + (s.d.st.oracles.size + 1)),
              positions := Positions.ofDraws code.logN rC.drawn.poss } ∧
      i.st = admitted (stSent s.d.st (sentOf T others)) s.d.st.oracles.size T.shape places
        #[{ smp with target := alpha }] ∧
      i.book = bookSentP s.p.firstTree s.d.roots s.d.st s.d.book (sentOf T others) lay ∧
      i.firstTree = s.p.firstTree ∧ i.opened = s.d.opened ∧ i.old = old ∧
      Tw.L9.readOld i out.positions = .ok (s'.d.book, s'.d.opened, y) ∧
      (ledgerShut i.st T s.d.st.oracles.size).groups[gp]? = some G ∧ G.inRun = false ∧
      switchRows (withMessageInGroup (ledgerShut i.st T s.d.st.oracles.size) gp s.d.st.oracles.size false G) old
        T s.d.st.oracles.size #[] out.positions y = some rows ∧
      (∀ r ∈ rows, r.kind ≠ .sample ∧
        RowChecked (withMessageInGroup (ledgerShut i.st T s.d.st.oracles.size) gp s.d.st.oracles.size false G)
          r) ∧
      s'.d.st = withRows
        (withMessageInGroup (ledgerShut i.st T s.d.st.oracles.size) gp s.d.st.oracles.size false G) gp rows :=
            by
  unfold H2K.switchE at h
  rw [hrs] at h
  split at h
  · rename_i e₁ e₂ es r₁ r₂ rs he hr
    cases hr
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, hG0, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨ids, sd, an, took, d₂⟩, hsend, h⟩ := bind_ok h
    have hsent : Tw.L9.switchNotices T others = #[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others
        := by
      unfold Tw.L9.switchNotices
      rw [hk]
      simp
    rw [hsent] at hsend
    obtain ⟨lay, beta, smp, alpha, places, vs, s1, s0, rfl, s6, s7, s8, s9, s10, rfl, s11, rfl⟩ :=
      sendOne_ok _ _ _ ⟨T.shape, T.leafClass⟩ others _ _ _ _ _ _ h1 ho (opt_ok hsend)
    dsimp only at h
    split at h
    · rename_i x hx
      simp only [pure_bind] at h
      obtain ⟨o, hb, h⟩ := bind_ok h
      cases h
      obtain ⟨code, y, G, rows, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
        switchBehind_ok _ _ hk (mapError_ok hb)
      dsimp only at b1 b2 b3 b4 b5 b6 b7 b8 b9
      have hg : ((Array.range (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others).size).map
          (· + s.d.st.oracles.size)).getD 0 noId = s.d.st.oracles.size := by
        have h0 : (Array.range (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others).size)[0]?
            = some 0 := by
          rw [Array.getElem?_eq_getElem (by simp)]
          simp
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, h0]
        simp
      have hriders : ((Array.range (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others).size).map
          (· + s.d.st.oracles.size)).extract 1
            ((Array.range (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others).size).map
              (· + s.d.st.oracles.size)).size
          = (Array.range others.size).map (· + (s.d.st.oracles.size + 1)) := by
        refine Array.ext (by simp) fun i h1 h2 => ?_
        simp only [Array.getElem_extract, Array.getElem_map, Array.getElem_range]
        omega
      rw [hg, hriders] at b3
      have hog : o.out.g = s.d.st.oracles.size := by rw [b3]
      rw [hog] at b5 b7 b8 b9
      have hvs : vs = [] := by
        rw [s10] at b2
        simp only [List.length_cons, Nat.add_sub_cancel] at b2
        exact List.eq_nil_of_length_eq_zero b2
      subst hvs
      exact ⟨lay, beta, alpha, smp, places, code, y, G, rows, _,
        (_root_.Tw.K2.targetOk_eq _ _ _).symm.trans (needK_ok hG0), s1, s0, s6, s7, s8,
        s9, s11, s10, by rw [hx]; rfl, b1, b3, rfl, rfl, rfl, rfl, rfl, b4, b5, b6, b7, b8, b9⟩
    · cases h
  · cases h

/-! ## The batching behind the switch -/

/-- What a yes of beginRunP holds. -/
theorem beginRunP_ok {d d' : DState Unit} {g : Nat} {run : RunInput}
    (h : Ground.beginRunP d g = some (run, d')) :
    ∃ G lay, d.st.groups[g]? = some G ∧ d.st.layout g = some lay ∧
      run = ⟨lay, runRows d.st G⟩ ∧ d' = { d with st := begun d.st g G } := by
  unfold Ground.beginRunP at h
  split at h
  · obtain ⟨G, hG, h⟩ := obind_ok h
    cases h
    exact ⟨G, _, hG, Own.layout_of_group hG, rfl, rfl⟩
  · cases h

theorem askOwedE_ok {rows : Nat} {s s' : H2K.PS} (h : (H2K.askOwedE rows s).toOption = some s') :
    s'.d = s.d := by
  unfold H2K.askOwedE at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

theorem beginRunE_ok {g : Nat} {s s' : H2K.PS} {run : RunInput}
    (h : (H2K.beginRunE g s).toOption = some (run, s')) :
    ∃ G lay, s.d.st.groups[g]? = some G ∧ s.d.st.layout g = some lay ∧
      run = ⟨lay, runRows s.d.st G⟩ ∧ s'.d = { s.d with st := begun s.d.st g G } := by
  unfold H2K.beginRunE at h
  cases hb : Ground.beginRunP s.d g with
  | none => rw [hb] at h; cases h
  | some v =>
    rw [hb] at h
    cases h
    obtain ⟨G, lay, a1, a2, a3, a4⟩ := beginRunP_ok hb
    exact ⟨G, lay, a1, a2, a3, a4⟩

/-- What a yes of behindJ (csTest's last lines) holds. -/
theorem behindJ_ok (p : P12) (j : Nat) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t2 t3 : T12) (out : Switched) (theta : E) (gp : Nat) (hp : t2.pass = .switched out theta gp)
    (h : (behindJ p j nxt cut).decide t2 [] [] = .ok t3) :
    ∃ G lay row, t2.st.groups[gp]? = some G ∧ t2.st.layout gp = some lay ∧
      Bat.combine (begun t2.st gp G) gp ⟨lay, runRows t2.st G⟩ theta = some row ∧
      t3.st = begun t2.st gp G ∧ t3.book = t2.book ∧ t3.pass = .claim row lay ∧
      t3.mask = (if p.early then out.others[0]? else none) := by
  simp only [behindJ, hp] at h
  obtain ⟨x, hx, h⟩ := bind_ok h
  obtain ⟨rfl, _⟩ := back_ok h
  replace hx := named_ok hx
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
      · rename_i row hrow
        cases hx
        obtain ⟨G, lay, a1, a2, rfl, a4⟩ := beginRunE_ok hb
        have a5 := askOwedE_ok ha
        have hst : H2K.csParts.statement s3 = begun t2.st gp G := by
          show s3.d.st = _
          rw [a5, a4]
          rfl
        rw [hst] at hrow
        refine ⟨G, lay, row, a1, a2, hrow, hst, ?_, rfl, rfl⟩
        show s3.d.book = _
        rw [a5, a4]
        rfl

/-! ## The top -/

theorem othersOf_none (last : Bool) (nx : IoppStage) : ∀ n ∈ othersOf last nx, n.shape.answers = 0
    := by
  intro n hn
  unfold othersOf at hn
  split at hn
  · simp only [Array.mem_singleton] at hn
    subst hn
    rfl
  · simp only [Array.mem_singleton] at hn
    subst hn
    rfl

/-- (U). -/
theorem switchUnfolds (p : P12) : SwitchUnfolds p := by
  intro j cur nxt last cut t1 t2 t3 rS rC gs rows gp nx he ha hp hs h1 h2
  simp only [switchJ, hp, hs] at h1
  obtain ⟨⟨⟨out, theta⟩, s'⟩, hx, h1⟩ := bind_ok h1
  obtain ⟨rfl, _⟩ := back_ok h1
  have hoth : (if (!p.early) = true then (#[] : Array OracleNotice)
      else if last = true then #[baseMaskNotice nx.code nx.maskCode 1 0]
      else #[foldMaskNotice (ioppFoldShape nx {})]) = othersOf last nx := by
    rw [he]
    rfl
  rw [hoth, ha] at hx
  obtain ⟨lay0, beta, alpha, smp, places, code, y, G, rws, i, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23⟩ :=
    switchE_ok rows (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) gp (othersOf last nx) _ s'
      out theta rS rC rfl rfl (othersOf_none last nx) rfl hx
  obtain ⟨G4, L, row, b1, b2, b3, b4, b5, b6, b7⟩ := behindJ_ok p (j + 1) nxt cut _ t3 out theta gp
      rfl h2
  dsimp only at b1 b2 b3 b4 b5 b6 b7
  rw [c13] at c19 c21 c22 c23
  rw [c23] at b1 b2 b3 b4
  rw [withRows_group gp rws _ _ (joined_group _ gp _ false G c19)] at b1
  have hG4 := Option.some.inj b1
  subst hG4
  refine ⟨out, row, L, theta, ⟨lay0, rS, rC, beta, alpha, smp, places, code, y, G, rws⟩, rfl, rfl,
    { check := c1, trees := c2, places := c3, valsS := c4, seed := c5, factor := c6, form := c7,
      pad := c8, valsC := c9, elem := c10, code := c11, g := congrArg Switched.g c12,
      kept := congrArg Switched.kept c12, riders := congrArg Switched.others c12,
      positions := congrArg Switched.positions c12,
      read := ⟨i, s'.d.opened, c13, c14, c15, c16, c17, by rw [b5]; exact c18⟩,
      group := c19, fresh := c20, rows := c21, kinds := c22, layout := b2, row := b3, st := b4 },
    b6, ?_⟩
  rw [b7, he]
  rfl

end H2K.Sw
