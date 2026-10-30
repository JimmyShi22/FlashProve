-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TopD.lean: the law of the proximity test names its claim: the row that the
batching returns, read in the field.

Main names:
  `bat_unique`: what the batching returns hangs on the statement, the group and the round alone, not
    on the entry.
  `claimNow_step`: at a place whose numbers give rounds (two stages at least) the joint's clause on
    the claim is `stmG s row = q`.
  `k12_bat`: a yes of the block's decision holds a yes of the batching on the first round.
  `StartI`: what is still assumed: `gp` and `keys` (public), `reads : ReadsK`, the layout and the
    places.
  `k12_step_accD`: the test on the plan and `pubOk p t0.st.codes = true` give the chain c such that
    for all transcripts b: `StartI` and a yes of `Block.step` give a row that the batching returns
    on the first round as shown, and `c.Acc` at that row read in the field and at the words read off
    the members' and the first mask's written oracles.
Limits: The law of the proximity test is not proved for a view that comes from bytes: `ReadsK` is a
premise. That the premises on the view and the block's yes hold together on any view is not shown;
the two public fields of `StartK` have a member wherever `pubOk` says yes (`pub_of_ok`,
Johnson/Desc/K12/Law/ChainOf.lean). It is stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean): the
parts of Johnson/Desc/K12/Join.lean behind guards, with the base case deciding by
Johnson/Desc/Prox/BaseCase.lean. It is not stated of `proximityTestParts`, the parts of Join.lean themselves. No
statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); plain functions of that
program, some with names that begin with `Blk.`, are reached. No soundness is claimed. Nothing here
is about hiding.
-/
import Johnson.Desc.K12.Law.TopC

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok got_ok)
open H2K.Sw (PartsP)
open H2K.Pub (Letters pubOk pub_of_ok sgOf writtenOf WR)

/-- What `heard` draws hangs on the round alone. -/
theorem heard_drawn (name : String) (items : Nat) (e e' : Fmt.Entry) (r : Fmt.RoundView) (a a' : List E ×
           E)
    (h : First.Close.heard name items e r = .ok a) (h' : First.Close.heard name items e' r = .ok
        a') :
    a.2 = a'.2 := by
  obtain ⟨_, t, ht, hx⟩ := H2K.FoldLaw.heard_ok _ _ _ _ _ a.1 a.2 h
  obtain ⟨_, t', ht', hx'⟩ := H2K.FoldLaw.heard_ok _ _ _ _ _ a'.1 a'.2 h'
  rw [ht] at ht'
  cases ht'
  rw [hx, hx']

theorem map_ok {ε α β : Type} {f : α → β} {x : Except ε α} {b : β} (h : x.map f = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

/-- What the batching returns does not hang on the entry. -/
theorem bat_unique (S : Statement) (g : Nat) (e e' : Fmt.Entry) (r : Fmt.RoundView)
    (x x' : GroupRow × GroupLayout × Statement) (h : First.Close.bat S g e r = .ok x)
    (h' : First.Close.bat S g e' r = .ok x') : x = x' := by
  unfold First.Close.bat at h h'
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨input, d⟩, hb, h⟩ := bind_ok h
  obtain ⟨v, hv, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨row, hr, h⟩ := bind_ok h
  obtain ⟨_, _, h'⟩ := bind_ok h'
  obtain ⟨⟨input', d'⟩, hb', h'⟩ := bind_ok h'
  obtain ⟨v', hv', h'⟩ := bind_ok h'
  obtain ⟨_, _, h'⟩ := bind_ok h'
  obtain ⟨row', hr', h'⟩ := bind_ok h'
  cases h
  cases h'
  have e1 := (got_ok hb).symm.trans (got_ok hb')
  cases e1
  obtain ⟨a, ha, rfl⟩ := map_ok hv
  obtain ⟨a', ha', rfl⟩ := map_ok hv'
  rw [heard_drawn _ _ _ _ _ _ _ ha ha'] at hr
  have e2 := (got_ok hr).symm.trans (got_ok hr')
  cases e2
  rfl

/-- Where the place's numbers give rounds, the chain begins with a step, and the joint's clause on
the claim is an equation in the field. -/
theorem claimNow_step (p : P12) {s : Sg} (c : Chain s) (row : GroupRow) (ds : List Fmt.DeclaredRound)
    (hs : stagesOf c = p.nums.stages) (hd : H2U.roundsOfNums p.nums = some ds) :
    ClaimNow c (stmG s row) row := by
  cases c with
  | last s e' dL dB fu fs εb =>
    exfalso
    have h1 : p.nums.stages = [s.st] := hs.symm
    unfold H2U.roundsOfNums at hd
    rw [h1] at hd
    cases hd
  | step s s' hf n0 e' dE dT dS dC fW fZ fG εf εc next => rfl

/-- What is still assumed in front of the test. -/
structure StartI (p : P12) {s : Sg} (c : Chain s) (b : c.Bl) {G : Gp s}
    (P : GpData G) (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc)
    (g : ℕ → ℕ → Option (List UInt64)) (t0 : T12) (rs : List Fmt.RoundView) (gs : Gs) : Prop where
  /-- public -/
  gp : P.Pub p.nums.firstTree
  /-- public -/
  keys : ((cutS (laidS p) (s.h + s.g)).flatMap fun r =>
    r.opens.map fun x => x.1.tree - p.nums.firstTree) = P.ts.map P.key
  /-- on the reading of the view -/
  reads : ReadsK p c b P o oF g rs gs
  /-- on the record: the layout and the places, of whatever the batching returns on the first round
  as shown -/
  behind : ∀ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
    rs.take 1 = [r] → First.Close.bat t0.st t0.g e r = .ok (row, L, S') →
    P.LayG L ∧
    ∀ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (cu : IoppStage) (id : Nat)
      (st : Statement) (book : TreeBook), p.nums.stages = first :: rest →
      stageAt p 0 first = some cu →
      MaskCase p { t0 with st := S', pass := .claim row L } (ioppFoldShape cu L) id st book →
      PartsP P st book id

/-- A yes of the block's decision holds a yes of the batching on the first round. -/
theorem k12_bat (p : P12) (he : p.early = true) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ (ds : List Fmt.DeclaredRound) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout)
      (S' : Statement), H2U.roundsOfNums p.nums = some ds ∧ rs.take 1 = [r] ∧
      First.Close.bat t0.st t0.g e r = .ok (row, L, S') := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, hfr, hbat, _, _⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  obtain ⟨first', rest', ds', e1', e2', l1, _⟩ := H2K.FrameLens.lens_top (Cl := Unit) guardedProximityTestParts p hp
  obtain rfl := Option.some.inj (e2'.symm.trans e2)
  have hF : tF = t0 := by
    have hfr' : (frontJ p).decide t0 [] [] = .ok tF := (frontK_ok p _ _ _ _ hfr).1
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  have nB : (batAt guardedProximityTestParts p (ds'.zip p.oracles) : Blk').rounds.length = 1 := by
    show (((ds'.zip p.oracles).take 1).map (·.1)).length = 1
    rw [List.length_map, l1]
  rw [nB] at hbat
  obtain ⟨hbat', _, _⟩ := batK_ok p _ _ _ _ _ hbat
  obtain ⟨e, r, row, L, S', hr1, hb, _⟩ := batJ_ok p he _ _ _ _ _ hbat'
  exact ⟨ds', e, r, row, L, S', e2, hr1, hb⟩

/-- The law of the proximity test, of `Block.step`, at the chain of the place and at the batched
row. -/
theorem k12_step_accD (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 : T12)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hpub : pubOk p t0.st.codes = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧ c.rds = l.map WR.rd ∧
          stagesOf c = p.nums.stages ∧
      ∀ (gW : (sgOf a).cIn.Word) (b : c.Bl) (G : Gp (sgOf a))
        (P : GpData G) (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc)
        (g : ℕ → ℕ → Option (List UInt64)) (firstTree : Nat) (tE : T12) (rs : List Fmt.RoundView)
        (cols : List OpenedColumn) (n : Nat),
        StartI p c b P o oF g t0 (rs.map noDigest)
          (regroup ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
              (rs.map (·.drawn))).map (·.length))
            (cols.take ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
              (rs.map (·.drawn))).flatMap id).length)) →
        (proximityTestKind guardedProximityTestParts p : Blk').step firstTree t0 rs cols = .ok (tE, n) →
        ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
          (rs.map noDigest).take 1 = [r] ∧ First.Close.bat t0.st t0.g e r = .ok (row, L, S') ∧
          c.Acc (stmG (sgOf a) row) (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j))
            (frOf (sgOf a) P.aF P.oF P.dF oF) gW b := by
  obtain ⟨a, rest, w0, l, c, hs, hw, hrds, hst, hall⟩ := k12_step_accC X p he ha t0 hp hpub
  refine ⟨a, rest, w0, l, c, hs, hw, hrds, hst, ?_⟩
  intro gW b G P o oF g firstTree tE rs cols n h0 h
  obtain ⟨ds, e, r, row, L, S', hd, hr, hb⟩ :=
    k12_bat p he t0 tE _ _ hp (Prox.step_ok firstTree _ t0 tE rs cols n h).2.2
  refine ⟨e, r, row, L, S', hr, hb, ?_⟩
  refine hall (stmG (sgOf a) row) gW b G P o oF g firstTree tE rs cols n
    ⟨h0.gp, h0.keys, h0.reads, ?_⟩ h
  intro e' r' row' L' S'' hr' hb'
  have hrr : r' = r := by
    rw [hr] at hr'
    exact (List.cons.inj hr').1.symm
  subst hrr
  have hu := bat_unique _ _ _ _ _ _ _ hb hb'
  cases hu
  exact ⟨claimNow_step p c row ds hst hd, h0.behind e' r' row L S' hr' hb'⟩

end H2K.JointK
