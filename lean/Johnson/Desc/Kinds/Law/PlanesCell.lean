-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanesCell.lean: K6's HALF OF THE EXCHANGE AT THE SENDING OF THE
HEAD's READS, AT THE RUN "planes": the form ArmCellIn (Johnson/Desc/Sound/StatedCellIn.lean): at
every entry that a form of the run names, the committed cell, read behind the sending, is the stated
function statedAll (Law/K6StatedPlanes.lean) at the verifier's state in front. Statements and
proofs.

  EntsAt Q f       every entry that the form f names lies at a place of which Q holds (general in Q
                   where Law/K6FormsInT.lean's Row0 has one Q; by Law/Covered.lean's addMul_ents).
  entsAt_addMul, _scale, _add, _sub, _addSlots, _rowForm   the forms' operations name no new place.
  planeForms_ents  so the three forms of "planes" name the places of the caller's forms alone, where
                   the starting form of the sumcheck over the leaves names no entry.
  readers_silent_planes   where no tables are laid the link's readers ask the filling "silent" at
                   the run "planes".
  armCellIn_planes MAIN: see its docstring.

WHAT IT IS NOT. An implication. THE NAMED PREMISE THAT CARRIES THE CONTENT: hHostC: the three
clauses K3HostPlanes IN THE WORLD OF THE COMMITTED DATA behind the sending (
Law/HeadPlanesTie.lean has them from the tie "the sent reads are the true ones" of the approximate
range proof): not called here. Beside: PlanesStates · the reader is k6Silent · the tables' facts ·
the starting form of the sumcheck over the leaves names no entry. Nothing on soundness.
LETTERS. No letter stands under "there is" in the top's conclusion.

-/
import Mathlib
import Johnson.Desc.Sound.StatedCellIn
import Johnson.Desc.Kinds.Law.PlanesArm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff Ent World Reading HTree)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (Readers segAt? RunOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (worldOwn)
open Planes

/-- Every entry that the form names lies at a place of which Q holds. -/
def EntsAt (Q : Nat → Nat → Nat → Prop) (f : Aff) : Prop :=
  ∀ x ∈ f.ents.toList, Q x.tree x.row x.idx

theorem entsAt_of_empty (Q : Nat → Nat → Nat → Prop) {f : Aff} (h : f.ents = #[]) :
    EntsAt Q f := by
  intro x hx
  rw [h] at hx
  exact absurd hx (by simp)

theorem entsAt_addMul {Q : Nat → Nat → Nat → Prop} {a b : Aff} (ha : EntsAt Q a)
    (hb : EntsAt Q b) (k : E) : EntsAt Q (Aff.addMul a b k) := by
  intro x hx
  rw [addMul_ents] at hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    exact hb z hz

theorem entsAt_scale {Q : Nat → Nat → Nat → Prop} {a : Aff} (ha : EntsAt Q a) (k : E) :
    EntsAt Q (Aff.scale a k) :=
  entsAt_addMul (entsAt_of_empty Q rfl) ha k

theorem entsAt_add {Q : Nat → Nat → Nat → Prop} {a b : Aff} (ha : EntsAt Q a) (hb : EntsAt Q b) :
    EntsAt Q (a + b) := entsAt_addMul ha hb _

theorem entsAt_sub {Q : Nat → Nat → Nat → Prop} {a b : Aff} (ha : EntsAt Q a) (hb : EntsAt Q b) :
    EntsAt Q (a - b) := entsAt_addMul ha hb _

theorem entsAt_addSlots {Q : Nat → Nat → Nat → Prop} {a : Aff} (ha : EntsAt Q a) (first : Nat)
    (form : Array E) : EntsAt Q (OnBytes.Model.addSlots a first form) := by
  unfold OnBytes.Model.addSlots
  rw [← Array.foldl_toList]
  have key : ∀ (l : List E) (p : Nat × Aff), EntsAt Q p.2 →
      EntsAt Q (l.foldl OnBytes.Model.addSlot p).2 := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons y l ih =>
      intro p hp
      rw [List.foldl_cons]
      exact ih _ (entsAt_addMul hp (entsAt_of_empty Q rfl) y)
  exact key _ _ ha

theorem entsAt_rowForm {Q : Nat → Nat → Nat → Prop} (p : OnBytes.Model.Psc) (S0 : E) {kept : Aff}
    (hs : p.start.ents = #[]) (hk : EntsAt Q kept) : EntsAt Q (p.rowForm S0 kept) := by
  unfold OnBytes.Model.Psc.rowForm
  exact entsAt_addMul (entsAt_addMul (entsAt_addSlots (entsAt_of_empty Q rfl) _ _)
    (entsAt_sub (entsAt_of_empty Q rfl) (entsAt_of_empty Q hs)) _) hk _

theorem entsAt_fold {Q : Nat → Nat → Nat → Prop} (step : Aff → Nat → Aff) (n : Nat)
    (hstep : ∀ f col, col < n → EntsAt Q f → EntsAt Q (step f col)) {a : Aff} (ha : EntsAt Q a) :
    EntsAt Q ((List.range n).foldl step a) := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    exact hstep _ n (Nat.lt_succ_self n)
      (ih fun f col hc => hstep f col (Nat.lt_succ_of_lt hc))

/-- **The three forms of "planes" name the places of the caller's forms alone.** -/
theorem planeForms_ents {Q : Nat → Nat → Nat → Prop} (g : OnBytes.Model.Forest.Heard) (lm : Nat)
    (bit : Nat → Nat → Aff) (pin : Nat → Aff) (hs : g.leaves.start.ents = #[])
    (hb : ∀ e col, col < nCols g lm → EntsAt Q (bit e col))
    (hp : ∀ col, col < nCols g lm → EntsAt Q (pin col)) :
    ∀ f ∈ (planeForms g lm bit pin).toList, EntsAt Q f := by
  have hat : ∀ e, EntsAt Q (atForm g lm e bit) := fun e =>
    entsAt_fold _ _ (fun f col hc hf => entsAt_addMul hf (hb e col hc) _) (entsAt_of_empty Q rfl)
  intro f hf
  unfold planeForms at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact entsAt_rowForm _ _ hs (entsAt_scale (hat 0) _)
  · exact entsAt_sub (entsAt_of_empty Q rfl) (hat 1)
  · exact entsAt_fold _ _ (fun f col hc hf => entsAt_add hf (hp col hc)) (entsAt_of_empty Q rfl)

/-- **WHERE NO TABLES ARE LAID THE LINK's READERS ASK "silent" AT THE RUN "planes"** (the like of
Law/K6Silent.lean's readers_silent at the head's four runs): the run itself rejects there: its yes
would have the seat's readers of the planes answer, and these want the tables. -/
theorem readers_silent_planes (iU3 lm b : Nat) (Lk : VerifiableInference.Desc.Link S Claim)
    (hS : PlanesStates iU3 lm (K9.statesOfLink Lk) b) (P : K8.ReadsQuiet.PH)
    (small : S → Option K9.Read) (s : S) (o : HeadOwn) (ho : s.here = .head o)
    (ht : o.t = none) :
    (K9.readersOfLink ⟨small, k6Silent P (K9.statesOfLink Lk)⟩ Lk).forms b "planes" s =
      k6Silent P (K9.statesOfLink Lk) b "planes" s := by
  have hnone : K9.readerOf (K9.statesOfLink Lk) b "planes" s = none := by
    cases hR : K9.readerOf (K9.statesOfLink Lk) b "planes" s with
    | none => rfl
    | some R =>
      exfalso
      obtain ⟨z, _, _, hrun, _⟩ := reader_planes hS hR
      obtain ⟨_, r, _, hr, _⟩ := planesRun_claims (K3.seatCalls asClaim) lm _ 0 s z hrun
      obtain ⟨o', _, tt, _, ho', _, ht', _⟩ := readers_some hr
      rw [ho] at ho'
      obtain rfl : o = o' := by injection ho'
      rw [ht] at ht'
      cases ht'
  show (if ("planes" == "K8.equations") = true then small s
    else match K9.readerOf (K9.statesOfLink Lk) b "planes" s with
      | some R => some R
      | Option.none => k6Silent P (K9.statesOfLink Lk) b "planes" s) = _
  rw [if_neg (by decide), hnone]

/-- **THE HEAD's HALF OF THE EXCHANGE AT THE RUN "planes".** s, a: the verifier's state in front
of the sending of the reads, and its part; b: the part behind it. Where the three clauses hold in
the world of the committed data behind the sending (hHostC): at every entry that a form of the run
names the committed cell is statedAll at the state in front. -/
theorem armCellIn_planes (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (blk : Nat)
    (states : Nat → List (RunOf S)) (hSt : PlanesStates (readsOf W) P.h.lmbH states blk)
    (Rd : Readers) (own own' : List (Nat × Nat)) (s : S) (a b : K9.Part)
    (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : Rd.forms blk "planes" s = k6Silent P states blk "planes" s)
    (cells : S → Bound K → NCells) (nuL : S → Bound K → _root_.Fo.Pl → K) (cU : Nat × String)
    (hArr : a.L.arrayOf[readsOf W]? = some cU) (hArrB : b.L.arrayOf[readsOf W]? = some cU)
    (hwide : ∀ e F tr, withTables P s = some e → e.fork? = some F →
      F.trees[readsOf W]? = some tr → P.hp.nU.getD 2 0 ≤ tr.K)
    (hlen : ∀ gk, s.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - P.h.lmbH) ≤
        (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
          ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH))
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.leaves.start.ents = #[])
    (hHostC : ∀ e r gk, withTables P s = some e →
      callerReaders (planesAt (readsOf W)) e = some r → e.lookHeard? = some gk →
      Meaning.Planes.K3HostPlanes gk.shape P.h.lmbH (_root_.Fo.rdL Reading.gl gk.zb0)
        (_root_.Fo.rdL Reading.gl gk.zb1) (nuL s (Sound.dataQ own a rdW))
        (fun f => f.value Reading.gl (worldOwn b [] (Sound.dataQ own' b rdW)))
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {})) :
    Sound.ArmCellIn Rd own own' blk "planes" s a b rdW
      (statedAll W P cells P.h.lmbH nuL) := by
  intro R hR f hf x hx _ c hc _
  rw [hRd] at hR
  unfold k6Silent at hR
  obtain ⟨e, he, hRe⟩ := Option.bind_eq_some_iff.1 hR
  obtain ⟨z, F, G, hrun, hF, _, hforms, _⟩ := reader_planes hSt hRe
  obtain ⟨gk, r, hg, hr, hz⟩ := planesRun_at asClaim W P.h.lmbH 0 e z hrun
  obtain ⟨o, F', tt, tr, ho, hF', ht, htr, hK⟩ := readers_some hr
  obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
  obtain ⟨a0, cov, x0, tt', ha0, _, _, _, htab, hee⟩ := (withTables_iff P s e).1 he
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
  have hA := tabsApart_at P s e o tt' he ho ht
  have hB := below_of_width P s (readsOf W) hwide e o tt' F tr he ho ht hF htr
  have H := hHostC e r gk he hr hg
  have hr' := planesAt_readers (readsOf W) ho hF ht htr hK
  obtain rfl := Option.some.inj (hr'.symm.trans hr)
  have hcols : ((F.trees[readsOf W]?).map (·.K)).getD 1 = tr.K := by
    rw [htr]
    rfl
  -- the equation, as a property of a place
  let Q : Nat → Nat → Nat → Prop := fun tree row idx =>
    ∀ c : Nat × String, a.L.arrayOf[tree]? = some c →
      (Sound.dataQ own' b rdW).cell c.1 c.2 row idx =
        statedAll W P cells P.h.lmbH nuL s (Sound.dataQ own a rdW) c row idx
  have one : ∀ (xr : PlaneRead) (name : String) (t : String × Nat × Nat) (col : Nat) (v : K),
      (match xr with
        | .bits0 => "bH-bits-0" | .bits1 => "bH-bits-1" | .pin => "bH-pin") = name →
      tt'.tab.find? (fun e => e.1 == name) = some t → col < t.2.2 →
      planesTruth gk P.h.lmbH (nuL s (Sound.dataQ own a rdW)) name col = some v →
      ((planeEntry tt'.tab (readsOf W) (((F.trees[readsOf W]?).map (·.K)).getD 1) xr col).getD
        {}).value Reading.gl (worldOwn b [] (Sound.dataQ own' b rdW)) = v →
      EntsAt Q ((planeEntry tt'.tab (readsOf W) (((F.trees[readsOf W]?).map (·.K)).getD 1) xr
        col).getD {}) := by
    intro xr name t col v hnm hfind hi hv hval
    subst hnm
    have hm : t ∈ tt'.tab := List.mem_of_find?_eq_some hfind
    have hlt : t.2.1 + col < tr.K := by
      have := hB t hm
      omega
    rw [hcols, planeEntry_at (x := xr) hfind hi] at hval ⊢
    have hval' : (Aff.ent (readsOf W) ((t.2.1 + col) / tr.K) ((t.2.1 + col) % tr.K)).value
        Reading.gl (worldOwn b [] (Sound.dataQ own' b rdW)) = v := hval
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, Aff.value_ent] at hval'
    have hcellB : (Sound.dataQ own' b rdW).cell cU.1 cU.2 0 (t.2.1 + col) = v := by
      have h2 : (match b.L.arrayOf[readsOf W]? with
        | some q => (Sound.dataQ own' b rdW).cell q.1 q.2 0 (t.2.1 + col)
        | none => 0) = v := hval'
      rw [hArrB] at h2
      exact h2
    intro y hy
    have hy' : y ∈ (Aff.ent (readsOf W) ((t.2.1 + col) / tr.K)
        ((t.2.1 + col) % tr.K)).ents.toList := hy
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt] at hy'
    obtain rfl : y = { tree := readsOf W, row := 0, idx := t.2.1 + col, coef := oneE } := by
      simpa [Aff.ent] using hy'
    intro c' hc'
    obtain rfl : cU = c' := Option.some.inj (hArr.symm.trans hc')
    show (Sound.dataQ own' b rdW).cell cU.1 cU.2 0 (t.2.1 + col) = _
    rw [hcellB]
    exact (statedAll_at W P cells P.h.lmbH nuL s e (Sound.dataQ own a rdW) cU 0 he o ho tt' ht hA
      gk hg _ t hfind col hi v hv).symm
  have hfm : f ∈ (planeForms gk P.h.lmbH
      (fun q col => ((fun q col => planeEntry tt'.tab (readsOf W)
        (((F.trees[readsOf W]?).map (·.K)).getD 1) (if q == 0 then .bits0 else .bits1) col) q
        col).getD {})
      fun col => (planeEntry tt'.tab (readsOf W) (((F.trees[readsOf W]?).map (·.K)).getD 1) .pin
        col).getD {}).toList := by
    rw [hforms, hz, List.map_map] at hf
    obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hf
    exact hf'
  refine planeForms_ents (Q := Q) gk P.h.lmbH _ _ (hbare gk hgs) (fun q col hcl => ?_)
    (fun col hcl => ?_) f hfm x hx c hc
  · by_cases hq : (q == 0) = true
    · have e' : q = 0 := by simpa using hq
      subst e'
      exact one .bits0 _ e0 col _ rfl h0 (lt_of_lt_of_le hcl (by rw [l0]; exact hl)) rfl
        (H.bit0 col hcl)
    · have e' : (if (q == 0) = true then PlaneRead.bits0 else PlaneRead.bits1) = .bits1 :=
        if_neg hq
      show EntsAt Q ((planeEntry tt'.tab (readsOf W) (((F.trees[readsOf W]?).map (·.K)).getD 1)
        (if (q == 0) = true then PlaneRead.bits0 else PlaneRead.bits1) col).getD {})
      rw [e']
      exact one .bits1 _ e1 col _ rfl h1 (lt_of_lt_of_le hcl (by rw [l1]; exact hl)) rfl
        (H.bit1 col hcl)
  · exact one .pin _ eP col _ rfl hP (lt_of_lt_of_le hcl (by rw [lP]; exact hl)) rfl
      (H.pin col hcl)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.readers_silent_planes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planeForms_ents
#print axioms VerifiableInference.Desc.Kinds.Head.Law.armCellIn_planes
