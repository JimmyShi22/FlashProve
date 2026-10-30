-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SilentAll.lean: THE SILENT READER (Law/K6SilentCode.lean: k6Silent) ANSWERS
AT ALL FIVE RUNS THAT THE TABLE OF JOINTS OPENS BEHIND THE OUTPUT HEAD's OWN SUB-PROTOCOL: the
head's four (Law/SilentAnswers.lean) and the lookup's "planes". Definitions, statements and proofs.

  PlanesBack       A NAMED PREMISE: the way back of Law/PlanesRoad.lean's PlanesStates.
  planes_answers   the reader answers at "planes", where the tables can be made: the head's readers
                   of the planes answer at every column (the three tables are long enough); the run
                   accepts (Law/SilentPlanes.lean); its three forms name row 0 of the reads' array
                   alone (Law/PlanesCell.lean: planeForms_ents).
  all_answer       MAIN: see its docstring. What the lookup left at the state in front (LeavesReady)
                   rides past the head's hearing by Law/TakesAt.lean's blockAt_takes and
                   Law/KeepsOwed.lean's blockAt_owed.

WHAT IT IS NOT. An implication. NAMED PREMISES THAT NOBODY PAYS HERE: Law/SilentAnswers.lean's ·
PlanesStates · PlanesBack · LeavesReady at the state in front · the planes have no more columns than
each of their three tables is long · the starting form of the sumcheck over the leaves names no
entry. Nothing on what the reader answers. Nothing on soundness.
LETTERS. R stands under "there is" in the tops' conclusions: tied by k6Silent's own answer.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SilentAnswers
import Johnson.Desc.Kinds.Law.SilentPlanes
import Johnson.Desc.Kinds.Law.PlanesCell
import Johnson.Desc.Kinds.Law.KeepsOwed
import Johnson.Desc.Kinds.Law.TakesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Fork Aff HTree)
open VerifiableInference.Desc.First (S HeadOwn)
open Planes

/-- **A NAMED PREMISE**, the way back of PlanesStates (Law/PlanesRoad.lean): an accept of the
lookup's own run at the head's readers is an accept of what the link's sub-protocol number b states
under "planes". -/
def PlanesBack (iU3 lm : Nat) (states : Nat → List (K9.RunOf S)) (b : Nat) : Prop :=
  ∀ run, (states b).find? (fun r => r.1 == "planes") = some ("planes", run) →
    ∀ k t y, K3.planesRun (K3.seatCalls asClaim) lm (callerReaders (planesAt iU3)) k t = .ok y →
      run k t = .ok y

/-- **THE SILENT READER ANSWERS AT "planes"**, where the tables can be made. -/
theorem planes_answers (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (b : Nat)
    (states : Nat → List (K9.RunOf S)) (hSt : PlanesStates (readsOf W) P.h.lmbH states b)
    (hBk : PlanesBack (readsOf W) P.h.lmbH states b) (t e : S) (he : withTables P t = some e)
    (F : Fork) (tr : HTree) (hF : e.fork? = some F) (htr : F.trees[readsOf W]? = some tr)
    (hK : tr.K ≠ 0) (hwide : P.hp.nU.getD 2 0 ≤ tr.K) (hR1 : tr.R = 1)
    (gk : OnBytes.Model.Forest.Heard) (hgk : e.lookHeard? = some gk) (hL : LeavesReady gk F)
    (hok : First.Look.planesOk gk.shape P.h.lmbH = true)
    (hlen : nCols gk P.h.lmbH ≤ (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
      ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH))
    (hbare : gk.leaves.start.ents = #[]) :
    ∃ R, k6Silent P states b "planes" t = some R := by
  obtain ⟨run, hf, _⟩ := hSt
  obtain ⟨a0, cov, x0, tt, ha0, _, _, _, htab, hee⟩ := (withTables_iff P t e).1 he
  have ho : e.here = .head { a0 with t := some tt } := by rw [hee]
  obtain ⟨_, _, e0, e1, eP, _, _, h0, h1, hP, l0, l1, lP, _⟩ := tables_planes htab
  have hB := below_of_width P t (readsOf W) (fun e' F2 tr2 he' hF2 htr2 => by
    obtain rfl := Option.some.inj (he.symm.trans he')
    obtain rfl : F = F2 := Option.some.inj (hF.symm.trans hF2)
    obtain rfl : tr = tr2 := Option.some.inj (htr.symm.trans htr2)
    exact hwide) e _ tt F tr he ho rfl hF htr
  have hr := planesAt_readers (readsOf W) ho hF rfl htr hK
  have hcols : ((F.trees[readsOf W]?).map (·.K)).getD 1 = tr.K := by
    rw [htr]
    rfl
  rw [hcols] at hr
  -- each reader's form: there, and on row 0 of the reads' array
  have one : ∀ (xr : PlaneRead) (u : String × Nat × Nat) (col : Nat),
      tt.tab.find? (fun e => e.1 == (match xr with
        | .bits0 => "bH-bits-0" | .bits1 => "bH-bits-1" | .pin => "bH-pin")) = some u →
      col < u.2.2 →
      (planeEntry tt.tab (readsOf W) tr.K xr col).isSome = true ∧
        Row0 (readsOf W) tr.K ((planeEntry tt.tab (readsOf W) tr.K xr col).getD {}) := by
    intro xr u col hfind hi
    have hm := hB u (List.mem_of_find?_eq_some hfind)
    rw [planeEntry_at hfind hi]
    exact ⟨rfl, row0_entryAt _ _ _ (by omega)⟩
  have hb : ∀ q col, col < nCols gk P.h.lmbH →
      (planeEntry tt.tab (readsOf W) tr.K (if q == 0 then .bits0 else .bits1) col).isSome = true ∧
        Row0 (readsOf W) tr.K ((planeEntry tt.tab (readsOf W) tr.K
          (if q == 0 then .bits0 else .bits1) col).getD {}) := by
    intro q col hc
    by_cases hq : (q == 0) = true
    · rw [if_pos hq]
      exact one .bits0 e0 col h0 (by rw [l0]; omega)
    · rw [if_neg hq]
      exact one .bits1 e1 col h1 (by rw [l1]; omega)
  have hp : ∀ col, col < nCols gk P.h.lmbH →
      (planeEntry tt.tab (readsOf W) tr.K .pin col).isSome = true ∧
        Row0 (readsOf W) tr.K ((planeEntry tt.tab (readsOf W) tr.K .pin col).getD {}) :=
    fun col hc => one .pin eP col hP (by rw [lP]; omega)
  obtain ⟨G, hrun, _⟩ := Part.MaskedSum.hideRun_returns F gk.leaves.first
    (Array.replicate gk.leaves.walk.1.length zeroE) (subE zeroE oneE)
    (by rw [Array.size_replicate]; exact hL.free)
  have hy := planesRun_answers P.h.lmbH (callerReaders (planesAt (readsOf W))) 0 e F G gk _ hF hgk
    hL.planes hr hok (fun q col hc => (hb q col hc).1) (fun col hc => (hp col hc).1) hL.flags hrun
  have hs := hBk run hf 0 e _ hy
  have hrow := planeForms_ents (Q := fun tree row idx => tree = readsOf W ∧ row = 0 ∧ idx < tr.K)
    gk P.h.lmbH _ _ hbare (fun q col hc => (hb q col hc).2) (fun col hc => (hp col hc).2)
  unfold k6Silent
  rw [he]
  show ∃ R, K9.readerOf states b "planes" e = some R
  unfold K9.readerOf
  rw [hf]
  simp only [Option.bind_some]
  rw [hs, hF]
  simp only
  rw [VerifiableInference.OnPublicFiles.fork_putFork e F _ hF]
  simp only [Option.bind_some]
  rw [if_pos]
  · exact ⟨_, rfl⟩
  · rw [List.all_eq_true]
    intro c hc
    obtain ⟨f, hfm, rfl⟩ := List.mem_map.1 hc
    have h1' : f.ents.all (K9.ownRow F) = true := ownRow_of_row0 (hrow f hfm) htr hR1
    show ((asClaim f).runs.isEmpty && (asClaim f).eqFirst.isNone &&
      f.ents.all (K9.ownRow F)) = true
    rw [h1']
    rfl

/-- **THE SILENT READER ANSWERS AT ALL FIVE RUNS BEHIND THE ACCEPT OF THE HEAD's OWN SUB-PROTOCOL.**
s: the verifier's state in front; t: behind. b: the number of the head's own sub-protocol in the
link; bP: the lookup's. -/
theorem all_answer (W : OnBytes.Model.Verify.Public) (l : Nat)
    (blk : VerifiableInference.Desc.Block S Unit) (hb : blockOf W l = some blk) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Sound.below blk).decide s rs gs = .ok t) (hOn : K6On W s) (P : K8.ReadsQuiet.PH)
    (hP : P.h = W.hS) (hB : tabsPlanB P.h P.L P.hp = true) (hRB : readsPlanB P.h P.hp = true)
    (hcov : ∃ cov, t.covered P.h.T P.h.V = .ok cov) (F : Fork) (tr : HTree)
    (hF : t.fork? = some F) (htr : F.trees[readsOf W]? = some tr) (hK : tr.K ≠ 0)
    (hwide : P.hp.nU.getD 2 0 ≤ tr.K) (hR1 : tr.R = 1) (piece b bP : Nat)
    (states : Nat → List (K9.RunOf S))
    (K : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (KB : K6Back W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (hSt : PlanesStates (readsOf W) P.h.lmbH states bP)
    (hBk : PlanesBack (readsOf W) P.h.lmbH states bP) (Fs : Fork) (hFs : s.fork? = some Fs)
    (gk : OnBytes.Model.Forest.Heard) (hgk : s.lookHeard? = some gk) (hL : LeavesReady gk Fs)
    (hzj : W.hS.ls ≤ (OnBytes.Model.Head.zjOf P.L gk 0).size)
    (hok : First.Look.planesOk gk.shape W.hS.lmbH = true) (hbare : gk.cEnd.ents = #[])
    (hc6 : gk.shape.calls.size = 6) (he6 : gk.e.size = 6)
    (hlen : nCols gk P.h.lmbH ≤ (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
      ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH))
    (hlv : gk.leaves.start.ents = #[]) :
    (∀ name, K6Name name → ∃ R, k6Silent P states b name t = some R) ∧
      ∃ R, k6Silent P states bP "planes" t = some R := by
  obtain ⟨Fs', Ft, f1, f2, _, _, hh⟩ := below_ledgers W l blk hb s t rs gs h hOn
  obtain rfl : Fs' = Fs := Option.some.inj (f1.symm.trans hFs)
  obtain rfl : Ft = F := Option.some.inj (f2.symm.trans hF)
  have hgt : t.lookHeard? = some gk := hh.trans hgk
  obtain ⟨hcan, hd⟩ := canonical_of_below blk s t rs gs h
  have hok' : 5 ≤ W.hS.lmbH ∧ W.hS.lmbH ≤ gk.shape.kT + 5 := by
    unfold First.Look.planesOk at hok
    simpa using hok
  have one : ∀ g', s.lookHeard? = some g' → g' = gk := fun g' hg' =>
    Option.some.inj (hg'.symm.trans hgk)
  -- the lookup's leavings ride past the head's hearing
  have hLt : LeavesReady gk Ft := by
    obtain ⟨i, hu, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 : (seatAt W.hS i).ledger s = Fs' := by
      show s.fork?.getD {} = _
      rw [hFs]
      rfl
    have e2 : (seatAt W.hS i).ledger t = Ft := by
      show t.fork?.getD {} = _
      rw [hF]
      rfl
    have hr : readsOf W = i := by
      unfold readsOf
      rw [hu]
      rfl
    have hW : WellLaid Fs' := by
      have h0 : WellLaid ((seatAt W.hS (readsOf W)).ledger s) := hOn.1
      rw [hr, e1] at h0
      exact h0
    obtain ⟨n, _, T⟩ := blockAt_takes W.hS i (workOf W) l s t rs gs
      (by rw [e1]; exact ⟨hW.2.1, hW.2.2, hW.1⟩) hd
    have ho := blockAt_owed W.hS i (workOf W) l s t rs gs hd
    rw [e1, e2] at T ho
    exact hL.takes T ho
  refine ⟨fun name hn => four_answer W l blk hb s t rs gs h hOn P hP hB hRB hcov
    (fun g' hg' => by rw [one g' hg']; exact hzj) hok'.1
    (fun g' hg' => by rw [one g' hg']; exact hok'.2) Ft tr hF htr hK hwide hR1 piece b states K KB
    gk hgt hLt.join hbare hc6 he6 name hn, ?_⟩
  obtain ⟨i, hu, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hr : readsOf W = i := by
    unfold readsOf
    rw [hu]
    rfl
  subst hr
  obtain ⟨e, v, he, _, hFe, hlk, _⟩ := letters_behind W l hd hOn.1 hcan hOn.2.1 P hP hB hRB hcov
    hOn.2.2.1 (fun g' hg' => by rw [one g' hg']; exact hzj) hok'.1
    (fun g' hg' => by rw [one g' hg']; exact hok'.2) Ft tr hF htr hK hwide
  exact planes_answers W P bP states hSt hBk t e he Ft tr hFe htr hK hwide hR1 gk (hlk.trans hgt)
    hLt (by rw [hP]; exact hok) hlen hlv

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.all_answer
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planes_answers
