-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SeatAcc.lean: the law of the proximity test at its seat, the finish of the
first chain.

Carries `k12_step_accE`, `k12_step_accF` and `k12_step_accH` (Johnson/Desc/K12/Law/TopE.lean,
TopF.lean, TopH.lean) to the block `atFinish p` on the first chain's own state
(Johnson/Desc/K12/AtFinish.lean), by `atFinish_step` and `atFinish_planOk`
(Johnson/Desc/K12/SeatLaws.lean). Statements and proofs.
Main names:
  `recAt σ fin`: the record that the seat hands the test, off the chain's state σ at its finish.
  `atFinish_to_k12`: a yes of the seat's step is a yes of the test's step at that record.
  `atFinish_step_accE`, `atFinish_step_accF`, `atFinish_step_accH`: the statements of
    `k12_step_accE`, `k12_step_accF` and `k12_step_accH` to the letter, but for: the record is
    `recAt σ fin`, the test on the plan is the seat's, and the step is the seat's. Their text was
    made of the three theorems' own text by a program.
Limits: The law of the proximity test is not proved for a view that comes from bytes: see
Johnson/Desc/K12/Law/TopE.lean, TopF.lean and TopH.lean. `atFinish p` seats `proximityTestKind guardedProximityTestParts p`. No
statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); plain functions of that
program, some with names that begin with `Blk.`, are reached. No soundness is claimed. Nothing here
is about hiding.
-/
import Johnson.Desc.K12.Law.TopH
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters pubOk sgOf writtenOf WR)
open H2K.First (gpOk gpOf gpL gpG gpP Good Plain good_of_ok cutOk)

/-- The record that the seat hands the test. -/
def recAt (σ : First.S) (fo : First.FinOwn) : T12 :=
  { st := σ.st, book := σ.book, roots := σ.roots, g := fo.fr.group, pass := .nothing, mask :=
      fo.mask }

theorem atFinish_to_k12 (p : P12) (firstTree : Nat) (σ σ' : First.S) (fo : First.FinOwn)
    (hσ : σ.here = .fin fo) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (h : (atFinish p).step firstTree σ rs cols = .ok (σ', n)) :
    ∃ t', (proximityTestKind guardedProximityTestParts p : Blk').step firstTree (recAt σ fo) rs cols = .ok (t', n) := by
  obtain ⟨o', t', ho, _, _, hs, _⟩ := Seat.atFinish_step p firstTree σ σ' rs cols n h
  rw [hσ] at ho
  cases ho
  exact ⟨t', hs⟩

/-- The law of the proximity test at its seat, in the form of `k12_step_accE`. -/
theorem atFinish_step_accE (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1) (σ :
    First.S)
    (fo : First.FinOwn) (hσ : σ.here = .fin fo)
    (hp : (atFinish p).planOk = true) (hpub : pubOk p (recAt σ fo).st.codes = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∀ (firstTree : Nat) (σ' : First.S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat),
        (atFinish p).step firstTree σ rs cols = .ok (σ', n) →
        ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
          (rs.map noDigest).take 1 = [r] ∧ First.Close.bat (recAt σ fo).st (recAt σ fo).g e r = .ok
              (row, L, S') ∧
          (gpOk p { (recAt σ fo) with st := S', pass := .claim row L } = true → ∀ (rad : ℕ → ℕ),
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
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, hall⟩ :=
    k12_step_accE X p he ha (recAt σ fo) (Seat.atFinish_planOk p hp) hpub
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, ?_⟩
  intro firstTree σ' rs cols n h
  obtain ⟨t', ht⟩ := atFinish_to_k12 p firstTree σ σ' fo hσ rs cols n h
  exact hall firstTree t' rs cols n ht

/-- The law of the proximity test at its seat, in the form of `k12_step_accF`. -/
theorem atFinish_step_accF (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1) (σ :
    First.S)
    (fo : First.FinOwn) (hσ : σ.here = .fin fo)
    (hp : (atFinish p).planOk = true) (hpub : pubOk p (recAt σ fo).st.codes = true)
    (hcut : cutOk p = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∀ (firstTree : Nat) (σ' : First.S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat),
        (atFinish p).step firstTree σ rs cols = .ok (σ', n) →
        ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement)
          (G0 : Group),
          (rs.map noDigest).take 1 = [r] ∧ First.Close.bat (recAt σ fo).st (recAt σ fo).g e r = .ok
              (row, L, S') ∧
          (recAt σ fo).st.groups[(recAt σ fo).g]? = some G0 ∧ (recAt σ fo).st.layout (recAt σ fo).g
              = some L ∧
          S' = begun (recAt σ fo).st (recAt σ fo).g G0 ∧
          (gpOk p { (recAt σ fo) with st := S', pass := .claim row L } = true →
            ∃ (D : Plain) (hok : H2K.First.ok (gpL p a row D) = true),
              gpOf p { (recAt σ fo) with st := S', pass := .claim row L } a L = some D ∧
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
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, hall⟩ :=
    k12_step_accF X p he ha (recAt σ fo) (Seat.atFinish_planOk p hp) hpub hcut
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, ?_⟩
  intro firstTree σ' rs cols n h
  obtain ⟨t', ht⟩ := atFinish_to_k12 p firstTree σ σ' fo hσ rs cols n h
  exact hall firstTree t' rs cols n ht

/-- The law of the proximity test at its seat, in the form of `k12_step_accH`: the seat's own yes
pays the Booleans. -/
theorem atFinish_step_accH (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (σ σ' : First.S) (fo : First.FinOwn) (hσ : σ.here = .fin fo)
    (hp : (atFinish p).planOk = true) (firstTree : Nat) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat)
    (h : (atFinish p).step firstTree σ rs cols = .ok (σ', n)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
        ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement)
          (G0 : Group),
          (rs.map noDigest).take 1 = [r] ∧
          First.Close.bat (recAt σ fo).st (recAt σ fo).g e r = .ok (row, L, S') ∧
          (recAt σ fo).st.groups[(recAt σ fo).g]? = some G0 ∧
          (recAt σ fo).st.layout (recAt σ fo).g = some L ∧
          S' = begun (recAt σ fo).st (recAt σ fo).g G0 ∧
          (
            ∃ (D : Plain) (hok : H2K.First.ok (gpL p a row D) = true),
              gpOf p { (recAt σ fo) with st := S', pass := .claim row L } a L = some D ∧
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
  obtain ⟨t', ht⟩ := atFinish_to_k12 p firstTree σ σ' fo hσ rs cols n h
  exact k12_step_accH X p he ha (recAt σ fo) (Seat.atFinish_planOk p hp) firstTree t' rs cols n ht

end H2K.JointK
