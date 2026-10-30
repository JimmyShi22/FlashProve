-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanesRoad.lean: THE PLANES' ROAD: FROM THE TABLE OF JOINTS' ITEM formsT AT
THE RUN "planes" OF THE LOOKUP ON THE HEAD's CALLS, at the verifier's state behind the head's own
block (the run's three forms are worth 0 in the world of the forms at the stated data:
Johnson/Desc/Sound/FormsQ.lean: formsTQ) TO THE SENTENCE THAT THE TABLE's FILLING HOLDS AT worth m 3
"planes" (Johnson/Top/H/K3RowOut.lean: K3OutPlanes: the library's three claims on the planes are 0
at every list of rounds for which what the lookup heard stands). Statements and proofs.

  PlanesStates     A NAMED PREMISE: what the link's block number b states under "planes" only adds
                   refusals to the lookup's own run at the head's readers of the planes.
  reader_planes    what the reader of that run gives, where it answers: the run's yes, the two
                   ledgers, the forms, the late slots.
  slot_late        the world of the forms reads a slot that is filled in front, or late, as the
                   ledger behind the run has it.
  countK_congr     the claim on the counts hangs on the columns below the planes' number alone.
  outPlanes_of_forms   MAIN: see its docstring.

BY planes_worth (Johnson/Top/H/K3RunsLaw.lean), which needs the run's yes: the reader's
answer holds it.
WHAT IT IS NOT. An implication. NAMED PREMISES THAT NOBODY PAYS HERE: PlanesStates · the reader at
(b, "planes") is the filling k6Silent · hHost: the three clauses K3HostPlanes in the world of the
forms (Law/K6StatedPlanes.lean pays them at the stated function statedAll) · the reading nu at the
masks below the ledger's number of slots is the stated data's mask row · what was heard stands for
rounds from a ledger F0 that the ledger at the state is later than. Nothing on soundness.
LETTERS. No letter stands under "there is" in the top's conclusion.

-/
import Mathlib
import Johnson.Top.H.K3RowOut
import Johnson.Top.H.K3RunsLaw
import Johnson.Top.H.K3OutProof
import Johnson.Top.H.K3SeatFits
import Johnson.Desc.Kinds.Law.K6Silent
import Johnson.Desc.Kinds.Law.RowPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff World Reading)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Readers readerOf lateOf lateAt segAt? RunOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (worldOwn slotW slotW_late slotW_ledger)
open VerifiableInference.OnPublicFiles

/-- **A NAMED PREMISE**: what block number b of the link states under "planes". -/
def PlanesStates (iU3 lm : Nat) (states : Nat → List (RunOf S)) (b : Nat) : Prop :=
  ∃ run, (states b).find? (fun r => r.1 == "planes") = some ("planes", run) ∧
    ∀ k t y, run k t = .ok y →
      K3.planesRun (K3.seatCalls asClaim) lm (callerReaders (planesAt iU3)) k t = .ok y

/-- What the reader of that run gives, where it answers. -/
theorem reader_planes {iU3 lm : Nat} {states : Nat → List (RunOf S)} {b : Nat}
    (hS : PlanesStates iU3 lm states b) {e : S} {R : K9.Read}
    (h : readerOf states b "planes" e = some R) :
    ∃ z F G, K3.planesRun (K3.seatCalls asClaim) lm (callerReaders (planesAt iU3)) 0 e = .ok z ∧
      e.fork? = some F ∧ z.2.fork? = some G ∧ R.forms = z.1.map (·.form) ∧
      R.late = lateOf F G := by
  obtain ⟨run, hf, hr⟩ := hS
  unfold readerOf at h
  rw [hf] at h
  simp only [Option.bind_some] at h
  cases h1 : run 0 e with
  | error x =>
    rw [h1] at h
    exact absurd h (by simp)
  | ok z =>
    cases h2 : e.fork? with
    | none =>
      rw [h1, h2] at h
      exact absurd h (by simp)
    | some F =>
      rw [h1, h2] at h
      simp only at h
      cases h3 : z.2.fork? with
      | none =>
        rw [h3] at h
        exact absurd h (by simp)
      | some G =>
        rw [h3] at h
        simp only [Option.bind_some] at h
        split at h
        · obtain rfl := Option.some.inj h
          exact ⟨z, F, G, hr 0 e z h1, rfl, h3, rfl, rfl⟩
        · exact absurd h (by simp)

/-- What stands in the list of late slots. (The text of mem_lateOf of
Johnson/Top/H0/MergeLaw/LateTie.lean, whose cone does not stand in this file's ground.) -/
theorem mem_late {F G : Fork} {x : Nat × E × E} (h : x ∈ lateOf F G) :
    ¬ OnBytes.PscRun.Filled F x.1 ∧ x.2 = (G.vp.getD x.1 zeroE, G.mf.getD x.1 zeroE) := by
  unfold lateOf at h
  obtain ⟨j, _, hx⟩ := List.mem_filterMap.1 h
  by_cases hc : (!(F.gotF.getD j false) && G.gotF.getD j false) = true
  · rw [if_pos hc] at hx
    obtain rfl := Option.some.inj hx
    obtain ⟨c1, _⟩ := Eq.mp (Bool.and_eq_true _ _) hc
    exact ⟨fun hf => by
      unfold OnBytes.PscRun.Filled at hf
      rw [hf] at c1
      exact absurd c1 (by simp), rfl⟩
  · rw [if_neg hc] at hx
    exact nomatch hx

/-- A slot that is filled in front is not late. -/
theorem late_none {F G : Fork} {j : Nat} (h : OnBytes.PscRun.Filled F j) :
    lateAt (lateOf F G) j = none := by
  unfold lateAt
  cases e : (lateOf F G).find? fun x => x.1 == j with
  | none => rfl
  | some x =>
    have hx : x.1 = j := by simpa using List.find?_some e
    obtain ⟨h0, _⟩ := mem_late (List.mem_of_find?_eq_some e)
    rw [hx] at h0
    exact absurd h h0

/-- The world of the forms reads a slot that is filled in front, or late, as the ledger behind the
run has it. -/
theorem slot_late {F G : Fork} (hL : _root_.Fo.Later F G) (mask : Nat → K) (j : Nat)
    (h : (lateAt (lateOf F G) j).isSome = true ∨ OnBytes.PscRun.Filled F j) :
    slotW F (lateOf F G) mask j =
      Reading.gl.val (G.vp.getD j zeroE) - Reading.gl.val (G.mf.getD j zeroE) * mask j := by
  by_cases hf : OnBytes.PscRun.Filled F j
  · rw [slotW_ledger _ _ _ _ (late_none hf), (hL.keep j hf).2.1,
      (hL.keep j hf).2.2]
  · have h1 : (lateAt (lateOf F G) j).isSome = true := h.resolve_right hf
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h1
    rw [slotW_late _ _ _ _ y hy]
    unfold lateAt at hy
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hy
    have hj : x.1 = j := by simpa using List.find?_some hx
    obtain ⟨_, h3⟩ := mem_late (List.mem_of_find?_eq_some hx)
    rw [h3, hj]

/-- The claim on the counts hangs on the columns below the planes' number alone. -/
theorem countK_congr (h : FoNums.Sh) (lm : Nat) (p p' : Nat → K)
    (hp : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → p col = p' col) :
    Cb.Fo.Pin.countK h lm p = Cb.Fo.Pin.countK h lm p' := by
  unfold Cb.Fo.Pin.countK
  generalize (-((2 ^ h.v - h.padding : ℕ) : K)) = c0
  have key : ∀ (n : Nat) (c : K), (∀ col, col < n → p col = p' col) →
      (List.range n).foldl (fun f col => f + p col) c =
        (List.range n).foldl (fun f col => f + p' col) c := by
    intro n
    induction n with
    | zero => intro c _; rfl
    | succ n ih =>
      intro c hq
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        ih c fun col hc => hq col (Nat.lt_succ_of_lt hc)]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hq n (Nat.lt_succ_self n)]
  exact key _ c0 hp

/-- **THE PLANES' ROAD.** s: the verifier's state behind the head's own block. The item formsT at
the run "planes" holds there of the witness's tables rdW; the reader is the filling k6Silent; what
the link's block states only adds refusals to the lookup's run; the reading nu has the stated data's
mask row at the masks below the ledger's number of slots; the three clauses hold in the world of the
forms. Then, for every ledger F0 than which the state's ledger is later: the library's three claims
on the planes are 0 at every list of rounds for which what the lookup heard stands from F0. -/
theorem outPlanes_of_forms (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (lm b : Nat)
    (states : Nat → List (RunOf S)) (hSt : PlanesStates (readsOf W) lm states b) (Rd : Readers)
    (St : Sound.Stated) (own : List (Nat × Nat)) (s : S) (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : Rd.forms b "planes" s = k6Silent P states b "planes" s)
    (hf : Sound.formsTQ Rd St own b "planes" s rdW) (nu : _root_.Fo.Pl → K)
    (hmask : ∀ a, segAt? s = some a → ∀ j, j < a.F.ns →
      (St.at1 s (Sound.dataQ own a rdW)).mask j = nu (.mask j))
    (hHost : ∀ e a r gk (Wd : World K), withTables P s = some e → segAt? s = some a →
      callerReaders (planesAt (readsOf W)) e = some r → e.lookHeard? = some gk →
      Wd.entry = (worldOwn a [] (St.at1 s (Sound.dataQ own a rdW))).entry →
      Meaning.Planes.K3HostPlanes gk.shape lm (_root_.Fo.rdL Reading.gl gk.zb0)
        (_root_.Fo.rdL Reading.gl gk.zb1) nu (fun f => f.value Reading.gl Wd)
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}))
    (gk : OnBytes.Model.Forest.Heard) (hk : s.lookHeard? = some gk)
    (hok : FoNums.ok gk.shape = true) (F0 : Fork) (first : Nat)
    (hL0 : ∀ F, s.fork? = some F → _root_.Fo.Later F0 F ∧ OnBytes.PscRun.Sized F) :
    K3OutPlanes gk.shape lm first nu Reading.gl gk F0 := by
  intro rs hI
  obtain ⟨a, R, ha, hR, _, hall⟩ := hf
  rw [hRd] at hR
  unfold k6Silent at hR
  obtain ⟨e, he, hRe⟩ := Option.bind_eq_some_iff.1 hR
  obtain ⟨z, F, G, hrun, hF, hG, hforms, hlate⟩ := reader_planes hSt hRe
  obtain ⟨a', tt, ha', hee⟩ := withTables_spec he
  have hFs : s.fork? = some F := by
    rw [← hF, hee]
    unfold S.fork?
    rw [ha']
  have hks : e.lookHeard? = some gk := by
    rw [← hk, hee]
    unfold S.lookHeard?
    rw [ha']
  obtain rfl : a.F = F := Option.some.inj ((seg_fork ha).symm.trans hFs)
  obtain ⟨hLF, hSF⟩ := hL0 _ hFs
  obtain ⟨gk', r, hk', hr, _⟩ := planesRun_at asClaim W lm 0 e z hrun
  obtain rfl : gk' = gk := Option.some.inj (hk'.symm.trans hks)
  obtain ⟨G', hG', _, hLG, _, _, hv⟩ := planes_worth (K3.seatCalls asClaim) (·.form)
    (seatCalls_fits asClaim (·.form) fun _ => rfl) lm (callerReaders (planesAt (readsOf W))) K
    Reading.gl gk' first rs F0 a.F 0 e z.2 z.1 hks hF hI hLF hok hSF hrun
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  have hv' := hv G' (_root_.Fo.Later.refl _) nu
    (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry
  -- each form of the run is worth 0 in the world of the ledger behind the run
  have hz : ∀ c ∈ z.1, c.form.value Reading.gl (G'.worldOf Reading.gl (fun j => nu (.mask j))
      (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry) = 0 := by
    intro c hc
    obtain ⟨hin, h0⟩ := hall c.form (by rw [hforms]; exact List.mem_map_of_mem hc)
    rw [← h0]
    refine (Sound.value_eq (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW)))
      (G'.worldOf Reading.gl (fun j => nu (.mask j))
        (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry) c.form (fun _ _ => rfl)
      fun x hx => ?_).symm
    have h1 : (c.form.slots.toList.all fun x =>
        K9.slotIn own (K9.mergeOf s) R.late a x.1) = true :=
      (Eq.mp (Bool.and_eq_true _ _) hin).2
    have h2 := List.all_eq_true.1 h1 x hx
    unfold K9.slotIn at h2
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h2
    show slotW a.F R.late _ x.1 = _
    rw [hlate, slot_late hLG, hmask a ha x.1 h2.1]
    · rfl
    · rw [← hlate]
      rcases h2.2.2.2 with q | q
      · exact Or.inl q
      · exact Or.inr q.1
  have H := hHost e a r gk' (G'.worldOf Reading.gl (fun j => nu (.mask j))
    (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry) he ha hr hks rfl
  have h3 : ∀ x ∈ z.1.map (fun c => c.form.value Reading.gl
      (G'.worldOf Reading.gl (fun j => nu (.mask j))
        (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry)), x = 0 := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact hz c hc
  rw [hv'] at h3
  have e0 : _root_.Fo.rdL Reading.gl gk'.zb0 = (_root_.Fo.endsOf gk'.shape lm first rs).zb0 :=
    hI.zb0
  have e1 : _root_.Fo.rdL Reading.gl gk'.zb1 = (_root_.Fo.endsOf gk'.shape lm first rs).zb1 :=
    hI.zb1
  have hb : ∀ q col, bitOf (callerReaders (planesAt (readsOf W))) e q col =
      (r.1 q col).getD {} := by
    intro q col
    unfold bitOf
    rw [hr]
    rfl
  have hp : ∀ col, pinOf (callerReaders (planesAt (readsOf W))) e col = (r.2 col).getD {} := by
    intro col
    unfold pinOf
    rw [hr]
    rfl
  have c1 := h3 _ List.mem_cons_self
  have c2 := h3 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have c3 := h3 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [claimLeaves_congr gk'.shape lm first rs nu _
    (_root_.Fo.colsK gk'.shape lm (_root_.Fo.rdL Reading.gl gk'.zb0) nu) (fun col hc => by
      rw [hb]
      exact H.bit0 col hc), e0] at c1
  rw [claimBits_congr gk'.shape lm first rs nu _
    (_root_.Fo.colsK gk'.shape lm (_root_.Fo.rdL Reading.gl gk'.zb1) nu) (fun col hc => by
      rw [hb]
      exact H.bit1 col hc), e1] at c2
  rw [countK_congr gk'.shape lm _ (Cb.Fo.Pin.pinColK lm nu) (fun col hc => by
      rw [hp]
      exact H.pin col hc)] at c3
  exact ⟨c1, c2, c3⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.outPlanes_of_forms
#print axioms VerifiableInference.Desc.Kinds.Head.Law.reader_planes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.slot_late
#print axioms VerifiableInference.Desc.Kinds.Head.Law.countK_congr
