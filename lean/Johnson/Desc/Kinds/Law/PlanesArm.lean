-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanesArm.lean: THE THIRD OF THE THREE ITEMS "worth" OF THE OUTPUT HEAD's
FOURTH TIE: "planes": Law/PlanesRoad.lean's road WITH THE THREE CLAUSES PAID at the stated function
statedAll (Law/K6StatedPlanes.lean), ACROSS AN ACCEPTING RUN OF THE HEAD's OWN SUB-PROTOCOL, IN THE
SHAPE OF THE TABLE OF JOINTS' FILLING's ARM (Johnson/Desc/First/Look/K3HeadFill.lean: worthHead at
"planes"). Statements and proofs.

  readers_some     where the seat's readers of the planes answer: the state stands in the head's
                   link with tables laid, and the ledger holds the array of the reads, with a
                   column.
  host_statedAll   the three clauses K3HostPlanes in every world with the stated entries, in the
                   form that Law/PlanesRoad.lean asks.
  below_ledgers    across a yes of the strict reading of the head's own sub-protocol, under K6On in
                   front: the two ledgers, the second later and well laid; what the lookup heard
                   stays.
  planes_arm       MAIN: formsT at (b, "planes") at the verifier's state t behind that yes: at the
                   state s in front: for whatever s shows as heard and as its ledger: K3OutPlanes.

WHAT IT IS NOT. An implication. NAMED PREMISES THAT NOBODY PAYS HERE: PlanesStates (what the link's
sub-protocol number b states under "planes") · the reader is the filling k6Silent · the stated
data's cells of the reads' array are statedAll, and its mask row is nu at the masks below the
ledger's number of slots · the array's name in the link's list · the array is at least as wide as
the number of reads in the list of rounds · each of the three tables is at least as long as the
planes have columns · what was heard has the place's shape, lawful. THE READING nu IS A LETTER: that
it is the closed caller's (headNu) is other files' to show. Nothing on soundness.
LETTERS. No letter stands under "there is" in the top's conclusion.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.PlanesRoad
import Johnson.Desc.Kinds.Law.K6StatedPlanes
import Johnson.Desc.Kinds.Law.K6RecordPaid
import Johnson.Desc.Kinds.Law.HeadPlanesHost
import Johnson.Desc.Kinds.Law.PlanesRefuses
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Desc.Kinds.Law.RowPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff World Reading HTree)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (Readers segAt? RunOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (worldOwn)
open VerifiableInference.OnPublicFiles

/-- Where the seat's readers of the planes answer (by Law/PlanesRefuses.lean's planesAt_some). -/
theorem readers_some {iU3 : Nat} {e : S}
    {r : (Nat → Nat → Option Form) × (Nat → Option Form)}
    (h : callerReaders (planesAt iU3) e = some r) :
    ∃ (o : HeadOwn) (F : Fork) (tt : OnBytes.Model.Head.Tables) (tr : HTree),
      e.here = .head o ∧ e.fork? = some F ∧ o.t = some tt ∧ F.trees[iU3]? = some tr ∧
      tr.K ≠ 0 := by
  unfold callerReaders at h
  obtain ⟨at_, h1, _⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, F, tt, tr, k1, k2, k3, k4, k5, _⟩ := planesAt_some iU3 e at_ h1
  exact ⟨o, F, tt, tr, k1, k2, k3, k4, k5⟩

/-- **The three clauses at the stated function, in the form that the road asks.** -/
theorem host_statedAll (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (cells : S → Bound K → NCells) (nuL : S → Bound K → _root_.Fo.Pl → K) (St : Sound.Stated)
    (own : List (Nat × Nat)) (s : S) (rdW : Nat × Nat → Sound.MsgQ) (a : K9.Part)
    (ha : segAt? s = some a) (cU : Nat × String) (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, (St.at1 s (Sound.dataQ own a rdW)).cell cU.1 cU.2 0 pos =
      statedAll W P cells P.h.lmbH nuL s (Sound.dataQ own a rdW) cU 0 pos)
    (hwide : ∀ e F tr, withTables P s = some e → e.fork? = some F →
      F.trees[readsOf W]? = some tr → P.hp.nU.getD 2 0 ≤ tr.K)
    (hlen : ∀ gk, s.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - P.h.lmbH) ≤
        (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
          ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH)) :
    ∀ e a' r gk (Wd : World K), withTables P s = some e → segAt? s = some a' →
      callerReaders (planesAt (readsOf W)) e = some r → e.lookHeard? = some gk →
      Wd.entry = (worldOwn a' [] (St.at1 s (Sound.dataQ own a' rdW))).entry →
      Meaning.Planes.K3HostPlanes gk.shape P.h.lmbH (_root_.Fo.rdL Reading.gl gk.zb0)
        (_root_.Fo.rdL Reading.gl gk.zb1) (nuL s (Sound.dataQ own a rdW))
        (fun f => f.value Reading.gl Wd)
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}) := by
  intro e a' r gk Wd he ha' hr hg hWd
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  obtain ⟨o, F, tt, tr, ho, hF, ht, htr, hK⟩ := readers_some hr
  obtain ⟨a0, cov, x, tt', ha0, _, _, _, htab, hee⟩ := (withTables_iff P s e).1 he
  have htt : tt' = tt := by
    rw [hee] at ho
    have h1 : ({ a0 with t := some tt' } : HeadOwn) = o := by
      simpa using ho
    rw [← h1] at ht
    exact Option.some.inj ht
  subst htt
  obtain ⟨_, _, e0, e1, eP, _, _, h0, h1, hP, l0, l1, lP, _⟩ := tables_planes htab
  have hgs : s.lookHeard? = some gk := by
    rw [← hg, hee]
    unfold S.lookHeard?
    rw [ha0]
  have hl := hlen gk hgs
  obtain ⟨r', hr', H⟩ := hostPlanes_stated W P cells P.h.lmbH nuL s e a (Sound.dataQ own a rdW)
    (St.at1 s (Sound.dataQ own a rdW)) Wd hWd he o ho tt' ht (tabsApart_at P s e o tt' he ho ht) F
    hF tr htr hK (below_of_width P s (readsOf W) hwide e o tt' F tr he ho ht hF htr) gk hg cU hArr
    hcell h0 h1 hP (by rw [l0]; exact hl) (by rw [l1]; exact hl) (by rw [lP]; exact hl)
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
  exact H

/-- Across a yes of the strict reading of the head's own sub-protocol, under K6On in front. -/
theorem below_ledgers (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below b).decide s rs gs = .ok t)
    (hOn : K6On W s) :
    ∃ Fs Ft, s.fork? = some Fs ∧ t.fork? = some Ft ∧ OnBytes.PscRun.Later Fs Ft ∧ WellLaid Ft ∧
      t.lookHeard? = s.lookHeard? := by
  obtain ⟨_, hd⟩ := canonical_of_below b s t rs gs h
  obtain ⟨i, hu, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hL := blockAt_later _ _ _ _ s t rs gs hd
  obtain ⟨a, F1, X, Q, ha, hop, _, rfl⟩ := Came.decide_record _ _ _ _ hd
  have f1 : s.fork? = some a.F := by
    unfold S.fork?
    rw [ha]
    simp [hop]
  have f2 : ({ s with here := .head { a with F := F1, x := some X, squaresP := some Q } } :
      S).fork? = some F1 := by
    unfold S.fork?
    simp [hop]
  have hh : ({ s with here := .head { a with F := F1, x := some X, squaresP := some Q } } :
      S).lookHeard? = s.lookHeard? := by
    unfold S.lookHeard?
    rw [ha]
  have e1 : (seatAt W.hS i).ledger s = a.F := by
    show s.fork?.getD {} = _
    rw [f1]
    rfl
  have e2 : (seatAt W.hS i).ledger
      { s with here := .head { a with F := F1, x := some X, squaresP := some Q } } = F1 := by
    show (S.fork? _).getD {} = _
    rw [f2]
    rfl
  rw [e1, e2] at hL
  have hr : readsOf W = i := by
    unfold readsOf
    rw [hu]
    rfl
  have hW : WellLaid a.F := by
    have h0 : WellLaid ((seatAt W.hS (readsOf W)).ledger s) := hOn.1
    rw [hr, e1] at h0
    exact h0
  exact ⟨a.F, F1, f1, f2, hL, Came.wellLaid_later hW hL, hh⟩

/-- **"planes", IN THE SHAPE OF THE FILLING's ARM.** s: the verifier's state in front of the head's
own sub-protocol; t: behind its yes. -/
theorem planes_arm (W : OnBytes.Model.Verify.Public) (l : Nat) (blk : Block S Unit)
    (hb : blockOf W l = some blk) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below blk).decide s rs gs = .ok t)
    (hOn : K6On W s) (P : K8.ReadsQuiet.PH) (b : Nat) (states : Nat → List (RunOf S))
    (hSt : PlanesStates (readsOf W) P.h.lmbH states b) (Rd : Readers) (St : Sound.Stated)
    (own : List (Nat × Nat)) (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : Rd.forms b "planes" t = k6Silent P states b "planes" t)
    (hf : Sound.formsTQ Rd St own b "planes" t rdW) (cells : S → Bound K → NCells)
    (nuL : S → Bound K → _root_.Fo.Pl → K) (a : K9.Part) (ha : segAt? t = some a)
    (hmask : ∀ j, j < a.F.ns → (St.at1 t (Sound.dataQ own a rdW)).mask j =
      nuL t (Sound.dataQ own a rdW) (.mask j))
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, (St.at1 t (Sound.dataQ own a rdW)).cell cU.1 cU.2 0 pos =
      statedAll W P cells P.h.lmbH nuL t (Sound.dataQ own a rdW) cU 0 pos)
    (hwide : ∀ e F tr, withTables P t = some e → e.fork? = some F →
      F.trees[readsOf W]? = some tr → P.hp.nU.getD 2 0 ≤ tr.K)
    (hlen : ∀ gk, t.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - P.h.lmbH) ≤
        (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
          ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH))
    (fs : OnBytes.Model.Forest.Shape) (hsh : ∀ g, s.lookHeard? = some g → g.shape = fs)
    (hok : FoNums.ok fs = true) (first : Nat) :
    ∀ (g : OnBytes.Model.Forest.Heard) (F' : Fork), s.fork? = some F' → s.lookHeard? = some g →
      K3OutPlanes fs P.h.lmbH first (nuL t (Sound.dataQ own a rdW)) Reading.gl g F' := by
  intro g F' hF' hg
  obtain ⟨Fs, Ft, f1, f2, hL, hWl, hh⟩ := below_ledgers W l blk hb s t rs gs h hOn
  obtain rfl : Fs = F' := Option.some.inj (f1.symm.trans hF')
  obtain rfl := hsh g hg
  refine outPlanes_of_forms W P P.h.lmbH b states hSt Rd St own t rdW hRd hf
    (nuL t (Sound.dataQ own a rdW)) (fun a' ha' j hj => ?_)
    (host_statedAll W P cells nuL St own t rdW a ha cU hArr hcell hwide hlen) g (hh.trans hg) hok
    Fs first fun F hF => ?_
  · obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
    exact hmask j hj
  · obtain rfl : Ft = F := Option.some.inj (f2.symm.trans hF)
    exact ⟨⟨hL.next, hL.ns, hL.keep⟩, ⟨hWl.2.1, hWl.2.2, hWl.1⟩⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.readers_some
#print axioms VerifiableInference.Desc.Kinds.Head.Law.host_statedAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.below_ledgers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planes_arm
