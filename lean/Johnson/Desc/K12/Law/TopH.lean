-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TopH.lean: the law of the proximity test from the block's own yes.

In `guardedProximityTestParts` the block itself asks the Booleans that Johnson/Desc/K12/Law/TopF.lean takes as
premises: `cutOk` in the front's test on the plan, `pubOk` at the record's codes in the front's
decision, `gpOk` behind the batching. So what is left is two numbers of the place, the block's test
on the plan, a yes of `Block.step`, and the two sentences on the view. Statements and proofs.
Main names:
  `k12_guards`: a yes of the block's decision holds that the plan's count of roots in front of the
    test is the record's, `pubOk` at the record's codes, a return of the batching on the first
    round, and `gpOk` at the record behind it.
  `k12_step_accH`: the statement of `k12_step_accF` without its premises `pubOk`, `cutOk` and
    `gpOk`: `p.early = true`, `p.answers = 1`, the block's test on the plan and a yes of
    `Block.step` give the chain, the batching's return, the plain data D, and, for all written
    rounds and oracles by the book's place and all transcripts, from the two sentences: `c.Acc`. Its
    text was made of that theorem's own text by a program.
Limits: The law of the proximity test is not proved for a view that comes from bytes: the two
sentences (the rounds shown behind "BAT" are the chain's written rounds; every dealt column is the
written tree's, opening by opening) are premises. The chain stands behind the step's yes here. That
is right for a law. A game wants the chain in front of its rounds: there `pubOk` stays a premise
(Johnson/Desc/K12/Law/K12Lemma.lean). It is stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean): the
parts of Johnson/Desc/K12/Join.lean behind guards, with the base case deciding by
Johnson/Desc/Prox/BaseCase.lean. It is not stated of `proximityTestParts`, the parts of Join.lean themselves. No
statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); plain functions of that
program, some with names that begin with `Blk.`, are reached. No soundness is claimed. Nothing here
is about hiding.
-/
import Johnson.Desc.K12.Law.TopF

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok got_ok)
open H2K.Pub (Letters pubOk sgOf writtenOf WR)
open H2K.First (gpOk gpOf gpL gpG gpP Good Plain good_of_ok cutOk)

/-- What a yes of the block's decision holds of its guards. -/
theorem k12_guards (p : P12) (he : p.early = true) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    p.nums.free = t0.roots ∧ pubOk p t0.st.codes = true ∧
    ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
      rs.take 1 = [r] ∧ First.Close.bat t0.st t0.g e r = .ok (row, L, S') ∧
      gpOk p { t0 with st := S', pass := .claim row L } = true := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, hfr, hbat, _, _⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  obtain ⟨first', rest', ds', e1', e2', l1, _⟩ := H2K.FrameLens.lens_top (Cl := Unit) guardedProximityTestParts p hp
  obtain rfl := Option.some.inj (e2'.symm.trans e2)
  obtain ⟨hfr', hfree, hpub⟩ := frontK_ok p _ _ _ _ hfr
  have hF : tF = t0 := by
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
  obtain ⟨hbat', _, hg⟩ := batK_ok p _ _ _ _ _ hbat
  obtain ⟨e, r, row, L, S', hr1, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ hbat'
  exact ⟨hfree, hpub, e, r, row, L, S', hr1, hb, hg⟩

/-- The law of the proximity test, of `Block.step`: the block's own yes pays the Booleans. -/
theorem k12_step_accH (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 : T12)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (firstTree : Nat) (tE : T12) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step firstTree t0 rs cols = .ok (tE, n)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
        ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement)
          (G0 : Group),
          (rs.map noDigest).take 1 = [r] ∧ First.Close.bat t0.st t0.g e r = .ok (row, L, S') ∧
          t0.st.groups[t0.g]? = some G0 ∧ t0.st.layout t0.g = some L ∧
          S' = begun t0.st t0.g G0 ∧
          (
            ∃ (D : Plain) (hok : H2K.First.ok (gpL p a row D) = true),
              gpOf p { t0 with st := S', pass := .claim row L } a L = some D ∧
              ∀ (rad : ℕ → ℕ) (dT : ℕ → PQ.RD) (oT : ∀ z, (wRound (dT z)).Orc),
                (∀ i, PQ.posN (dT (D.mems.get i).t).tree = 2 ^ (D.mems.get i).tsh.logN) →
                PQ.posN (dT D.fresh.t).tree = 2 ^ D.fresh.tsh.logN →
                ∀ (gW : (sgOf a).cIn.Word) (b : c.Bl),
                  (rs.map noDigest).drop 1 = (c.rvs b).map noDigest →
                  Follows (grpsS p (regroup ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
                        (rs.map (·.drawn))).map (·.length))
                      (cols.take ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
                        (rs.map (·.drawn))).flatMap id).length)))
                    (srcFirst c b (laidS p) D.ts fun z x => colW (dT z) (oT z) x) →
                  c.Acc (stmG (sgOf a) row)
                    ((gpG (good_of_ok p a row D hok) rad).word fun j =>
                      ((gpG (good_of_ok p a row D hok) rad).mb j).ofOrc
                        ((gpP (good_of_ok p a row D hok) rad (fun i => dT (D.mems.get i).t)
                          (dT D.fresh.t)).lay j) (dT (D.mems.get j).t) (oT (D.mems.get j).t))
                    (frOf (sgOf a) D.fresh.tsh.logN
                      (gpP (good_of_ok p a row D hok) rad (fun i => dT (D.mems.get i).t)
                        (dT D.fresh.t)).oF (dT D.fresh.t) (oT D.fresh.t))
                    gW b) := by
  obtain ⟨_, _, hdec⟩ := Prox.step_ok firstTree _ t0 tE rs cols n h
  obtain ⟨_, hpub, e0, r0, row0, L0, S0, hr0, hb0, hg0⟩ := k12_guards p he t0 tE _ _ hp hdec
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, hall⟩ :=
    k12_step_accF X p he ha t0 hp hpub (cut_of_planOk p hp)
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, ?_⟩
  obtain ⟨e, r, row, L, S', G0, g1, g2, g3, g4, g5, g6⟩ := hall firstTree tE rs cols n h
  have hrr : r = r0 := by
    rw [hr0] at g1
    exact (List.cons.inj g1).1.symm
  subst hrr
  cases bat_unique _ _ _ _ _ _ _ hb0 g2
  exact ⟨e, r, row0, L0, S0, G0, g1, g2, g3, g4, g5, g6 hg0⟩

end H2K.JointK
