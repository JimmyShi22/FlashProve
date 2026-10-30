-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TopG.lean: the law of the proximity test with the first stage's tie paid.

Pays the field `tie` of `StartK` (Johnson/Desc/K12/Law/Top.lean) by `firstReads_keyed`
(Johnson/Desc/K12/Law/FirstRead.lean), for a group of several members in several trees. Statements
and proofs.
Main names:
  `StartG`: what is assumed in front of the test. Public: `stages`, `pub`, `gp` (`GpData.Pub` at the
    chain's first tree's number) and `keys` (the first switch's declared openings, less the first
    tree's number, are the keys of the group's trees in the book's order). On the reading of the
    view: `reads : ReadsK`. On the record: the group's layout is the public one (`GpData.LayG`), and
    each member and the mask have their places in the book and their shapes in the statement
    (`PartsP`, in both arms of `MaskCase`). The claim q is the batched row read in the field.
  `startK_of_G`: `StartG` gives `StartK` at the word of the members' written oracles and the word of
    the first mask's.
  `k12_step_accG`: the test on the plan, `StartG` and a yes of `Block.step` give `c.Acc` at these
    words.
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
import Johnson.Desc.K12.Law.K12Law
import Johnson.Desc.K12.Law.ReadsK

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw (PartsP)

/-- What is assumed in front of the test. The file's head sorts the fields. -/
structure StartG (p : P12) {s : Sg} (c : Chain s) (q : GE × (s.cIn.J → GE)) (b : c.Bl) {G : Gp s}
    (P : GpData G) (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc)
    (g : ℕ → ℕ → Option (List UInt64)) (t0 : T12) (rs : List Fmt.RoundView) (gs : Gs) : Prop where
  /-- public -/
  stages : stagesOf c = p.nums.stages
  /-- public -/
  pub : ∀ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (cu : IoppStage)
    (restI : List IoppStage), p.nums.stages = first :: rest → stageAt p 0 first = some cu →
    stagesAt p 1 rest = some restI → c.Pub t0.st.codes cu restI
  /-- public -/
  gp : P.Pub p.nums.firstTree
  /-- public -/
  keys : ((cutS (laidS p) (s.h + s.g)).flatMap fun r =>
    r.opens.map fun x => x.1.tree - p.nums.firstTree) = P.ts.map P.key
  /-- on the reading of the view -/
  reads : ReadsK p c b P o oF g rs gs
  /-- of whatever the batching returns on the first round as shown: which claim the law speaks of;
  and, on the record, the layout and the places -/
  behind : ∀ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
    rs.take 1 = [r] → First.Close.bat t0.st t0.g e r = .ok (row, L, S') →
    ClaimNow c q row ∧ P.LayG L ∧
    ∀ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (cu : IoppStage) (id : Nat)
      (st : Statement) (book : TreeBook), p.nums.stages = first :: rest →
      stageAt p 0 first = some cu →
      MaskCase p { t0 with st := S', pass := .claim row L } (ioppFoldShape cu L) id st book →
      PartsP P st book id

theorem startK_of_G (p : P12) {s : Sg} (c : Chain s) (q : GE × (s.cIn.J → GE)) (gW : s.cIn.Word)
    (b : c.Bl) {G : Gp s} (P : GpData G) (o : ∀ j, (wRound (P.d j)).Orc)
    (oF : (wRound P.dF).Orc) (g : ℕ → ℕ → Option (List UInt64)) (t0 : T12) (rs : List Fmt.RoundView)
    (gs : Gs) (h : StartG p c q b P o oF g t0 rs gs) :
    StartK p c q (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j))
      (frOf s P.aF P.oF P.dF oF) gW b t0 rs gs := by
  refine ⟨h.stages, h.pub, h.reads.rounds, ?_⟩
  intro first rest cu ds e r row L S' e1 hcu e2 hr hb
  obtain ⟨k1, k3, k4⟩ := h.behind e r row L S' hr hb
  have hl : laidOf p = ds.zip p.oracles := by
    unfold laidOf
    rw [e2]
    rfl
  have hsh := h.reads.shown
  have hgr := h.reads.groups
  have hky := h.keys
  unfold laidS grpsS at hsh hgr
  unfold laidS at hky
  rw [hl] at hsh hgr hky
  refine ⟨k1, hsh, ?_⟩
  cases c with
  | last s e' dL dB fu fs εb =>
    exfalso
    have hs : p.nums.stages = [s.st] := h.stages.symm
    unfold H2U.roundsOfNums at e2
    rw [hs] at e2
    cases e2
  | step s s' hf n0 e' dE dT dS dC fW fZ fG εf εc next =>
    have hst : s.st = first := by
      have h1 := h.stages.trans e1
      exact (List.cons.inj h1).1
    have hk : cu.k = s.h + s.g := by rw [stageAt_k hcu, ← hst]; rfl
    have hh : cu.h = s.h := by
      unfold stageAt at hcu
      cases hi : p.idx[0]? with
      | none => rw [hi] at hcu; cases hcu
      | some i => rw [hi] at hcu; cases hcu; rw [← hst]; rfl
    intro id st book hmc
    rw [hk]
    exact H2K.Sw.firstReads_keyed p _ _ s G P cu L st book id o oF g _ hk hh h.gp k3
      (k4 first rest cu id st book e1 hcu hmc) h.reads.members h.reads.mask hky hgr

/-- The law of the proximity test, of `Block.step`, with the first stage's tie paid. -/
theorem k12_step_accG (p : P12) (he : p.early = true) (ha : p.answers = 1) {s : Sg} (c : Chain s)
    (q : GE × (s.cIn.J → GE)) (gW : s.cIn.Word) (b : c.Bl) {G : Gp s} (P : GpData G)
    (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc) (g : ℕ → ℕ → Option (List UInt64))
    (firstTree : Nat) (t0 tE : T12) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h0 : StartG p c q b P o oF g t0 (rs.map noDigest)
      (regroup ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds (rs.map (·.drawn))).map
          (·.length))
        (cols.take ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
          (rs.map (·.drawn))).flatMap id).length)))
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step firstTree t0 rs cols = .ok (tE, n)) :
    c.Acc q (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j)) (frOf s P.aF P.oF P.dF oF) gW
      b :=
  k12_step_acc p he ha c q _ _ gW b firstTree t0 tE rs cols n hp
    (startK_of_G p c q gW b P o oF g t0 _ _ h0) h

end H2K.JointK
