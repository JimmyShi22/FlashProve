-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TopE.lean: the law of the proximity test from three tests that a program runs,
two numbers of the place, and the reading of the view.

Pays the public clauses on the group under test and the clauses on the record by a Boolean, `gpOk`,
with `first_of_ok` (Johnson/Desc/K12/Law/FirstOk.lean, FirstOkLaw.lean). Statement and proof.
Main names:
  `k12_step_accE`: `p.early = true`, `p.answers = 1`, the block's test on the plan and `pubOk p
    t0.st.codes = true` give the chain c (its written rounds are the place's declared rounds behind
    "BAT", its stages the place's) such that a yes of `Block.step` gives a return (row, L, S') of
    the batching on the first round as shown, and, if `gpOk` says yes at the record behind the
    batching, the group's plain data D, made by code of that record, such that for all written
    rounds dM and dF as deep as the book's trees, all written oracles o and oF of these rounds, all
    transcripts b and all g: `ReadsK` gives `c.Acc` at the row read in the field and at the words
    read off o and oF.
Limits: The law of the proximity test is not proved for a view that comes from bytes: `ReadsK`
(Johnson/Desc/K12/Law/ReadsK.lean), and that the written rounds dM and dF are as deep as the book's
trees, are premises. That the premises on the view and the block's yes hold together on any view is
not shown; the two public fields of `StartK` have a member wherever `pubOk` says yes (`pub_of_ok`,
Johnson/Desc/K12/Law/ChainOf.lean). It is stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean): the
parts of Johnson/Desc/K12/Join.lean behind guards, with the base case deciding by
Johnson/Desc/Prox/BaseCase.lean. It is not stated of `proximityTestParts`, the parts of Join.lean themselves.
The chain's radii and error counts and the members' radii are letters: `Chain.Acc` reads none of
them. At the four proximity tests of the two stored example proofs, the full-size one and the
smaller one, `Block.step` of `proximityTestKind guardedProximityTestParts p` said yes, and `pubOk` and `gpOk` were true; the two
were false at forty and forty-eight spoiled inputs [runs; the prints are not in this library]. No
statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); plain functions of that
program, some with names that begin with `Blk.`, are reached. No soundness is claimed. Nothing here
is about hiding.
-/
import Johnson.Desc.K12.Law.TopD
import Johnson.Desc.K12.Law.FirstOkLaw

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters pubOk sgOf writtenOf WR)
open H2K.First (gpOk first_of_ok gpG gpP Good Plain)

/-- The law of the proximity test, of `Block.step`: three Booleans, two numbers, and the reading of
the view. -/
theorem k12_step_accE (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 : T12)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hpub : pubOk p t0.st.codes = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∀ (firstTree : Nat) (tE : T12) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat),
        (proximityTestKind guardedProximityTestParts p : Blk').step firstTree t0 rs cols = .ok (tE, n) →
        ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
          (rs.map noDigest).take 1 = [r] ∧ First.Close.bat t0.st t0.g e r = .ok (row, L, S') ∧
          (gpOk p { t0 with st := S', pass := .claim row L } = true → ∀ (rad : ℕ → ℕ),
            ∃ (D : Plain) (h : Good p.nums.firstTree a row D),
              ∀ (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD),
                (∀ i, PQ.posN (dM i).tree = 2 ^ (D.mems.get i).tsh.logN) →
                PQ.posN dF.tree = 2 ^ D.fresh.tsh.logN →
                ∀ (gW : (sgOf a).cIn.Word) (b : c.Bl)
                  (o : ∀ j, (wRound ((gpP h rad dM dF).d j)).Orc)
                  (oF : (wRound (gpP h rad dM dF).dF).Orc) (g : ℕ → ℕ → Option (List UInt64)),
                  ReadsK p c b (gpP h rad dM dF) o oF g (rs.map noDigest)
                    (regroup ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
                        (rs.map (·.drawn))).map (·.length))
                      (cols.take ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
                        (rs.map (·.drawn))).flatMap id).length)) →
                  c.Acc (stmG (sgOf a) row)
                    ((gpG h rad).word fun j =>
                      ((gpG h rad).mb j).ofOrc ((gpP h rad dM dF).lay j) ((gpP h rad dM dF).d j) (o
                          j))
                    (frOf (sgOf a) (gpP h rad dM dF).aF (gpP h rad dM dF).oF (gpP h rad dM dF).dF
                        oF)
                    gW b) := by
  obtain ⟨a, rest, w0, l, c, hs, hw, hrds, hst, hall⟩ := k12_step_accD X p he ha t0 hp hpub
  refine ⟨a, rest, w0, l, c, hs, hw, hrds, hst, ?_⟩
  intro firstTree tE rs cols n h
  obtain ⟨ds, e, r, row, L, S', hd, hr, hb⟩ :=
    k12_bat p he t0 tE _ _ hp (Prox.step_ok firstTree _ t0 tE rs cols n h).2.2
  refine ⟨e, r, row, L, S', hr, hb, ?_⟩
  intro hok rad
  have hhk : a.h ≤ a.k := by
    obtain ⟨l', hl'⟩ := stagesOf_ne c
    have h1 : (sgOf a).st = a := (List.cons.inj ((hl'.symm.trans hst).trans hs)).1
    have h2 : a.h + (a.k - a.h) = a.k := congrArg (·.k) h1
    omega
  obtain ⟨D, hG, hD⟩ := first_of_ok p { t0 with st := S', pass := .claim row L } a rest row L hs rfl
    hok hhk rad
  refine ⟨D, hG, ?_⟩
  intro dM dF hM hF gW b o oF g hreads
  obtain ⟨p1, ⟨src, p2⟩, _, p4, p5⟩ := hD dM dF hM hF
  obtain ⟨e2, r2, row2, L2, S2, hr2, hb2, hacc⟩ := hall gW b (gpG hG rad) (gpP hG rad dM dF) o oF g
    firstTree tE rs cols n
    ⟨p1, p2.keys, hreads, by
      intro e' r' row' L' S'' hr' hb'
      have hrr : r' = r := by
        rw [hr] at hr'
        exact (List.cons.inj hr').1.symm
      subst hrr
      cases bat_unique _ _ _ _ _ _ _ hb hb'
      refine ⟨p4, ?_⟩
      intro first rest' cu id st book hs' hcu hmc
      have hfa : first = a := (List.cons.inj (hs'.symm.trans hs)).1
      subst hfa
      exact p5 cu id st book hcu hmc⟩ h
  have hrr : r2 = r := by
    rw [hr] at hr2
    exact (List.cons.inj hr2).1.symm
  subst hrr
  cases bat_unique _ _ _ _ _ _ _ hb hb2
  exact hacc

end H2K.JointK
