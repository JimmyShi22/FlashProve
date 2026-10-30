-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05JoinThere.lean: kind K5: THE ONE FORM OF THE LOOKUP's JOIN AT K5's KEY FORMS, MADE
AT THE RECORD BEHIND THE HEARING's LAY, NAMES ONLY WHAT IS THERE: the public test affInT
(Johnson/Desc/First/Batch/FormsIn.lean; imported,
not turned), with no late slot.
Main names:
  `form_there`: GENERAL IN THE FORM: a form whose slots are all filled in a sized ledger G with the
    trees of the ledger in front, and whose entries all lie in the tables' part (Cov,
    Claims/Covered.lean), passes affInT own none [] at the part behind the lay, and each of its
    entries names row 0 of an array with one own row: under U3There (Att/K05FormsMade.lean).
  `cEnd_behind`: THE PLUG: the form that the lookup leaves for the join names slots that are filled in
    the ledger that the lookup left (the lookups' K3Left.cEndFilled); what lies stays (Stays): so
    they are filled behind K5's hearing.
  `cov_joinW`: join's written form names the key forms' entries alone, where g.cEnd names none (the
    lookups' K3Left.cEndEnts).
  `k5_join_there`: **the join's form passes.**
  `lateOf_paid`: marking an owed claim as added turns no mark on a slot: so the run "join" has no late
    slot.
Premises of k5_join_there: those of k5_forms_there but "second"'s return; "keys"' return; the two
facts on g.cEnd; joinF's return.
It stands on join_slots_K05 (Claims/SlotsCoveredKeys.lean) and the base's
keysRun_covered (Claims/CoveredKeys.lean).
Limits: as at Att/K05FormsMade.lean. Nothing on the lookup's run "planes".
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05FormsMade
import Johnson.Desc.First.Att.Claims.SlotsCoveredKeys
import Johnson.Desc.First.Att.Claims.CoveredKeys
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.K9 (maskSeat slotIn atMoment1 entInT affInT lateOf)
open K5Law (SlotsIn Cov cov_ofConst cov_addMul cov_add cov_sub joinW)

section
variable {s : First.S} {a : First.AttOwn} {c : ParC} {G : Fork} {K : ℕ}

/-- **A form whose slots are filled and whose entries lie in the tables' part names only what is
there.** -/
theorem form_there (own : List (ℕ × ℕ)) (zG : Sized G) (U : U3There own s a c)
    (ht : G.trees = a.F.trees) (hK : (G.trees[c.iU3]?).map (·.K) = some K) (o : Option ℕ) {f : Aff}
    (hS : SlotsIn (PscRun.Filled G) f) (hC : Cov c.iU3 K c.nW f) :
    affInT own none [] (partAt s a G o) f = true ∧
      ∀ e ∈ f.ents.toList, e.row = 0 ∧ ∃ T, G.trees[e.tree]? = some T ∧ T.R = 1 := by
  obtain ⟨T, hT, hR, hW⟩ := U.tree
  obtain ⟨b, Ar, hb, hA, hm1, hI, hCz⟩ := U.array
  have hT' : G.trees[c.iU3]? = some T := by rw [ht]; exact hT
  have eK : K = T.K := by
    rw [hT'] at hK
    exact (Option.some.inj hK).symm
  have ents : ∀ e ∈ f.ents.toList, e.tree = c.iU3 ∧ e.row = 0 ∧ e.idx < c.nW := by
    intro e he
    obtain ⟨y, hy, t1, t2, t3⟩ := hC e he
    have hyK : y < K := by rw [eK]; omega
    exact ⟨t1, by rw [t2, Nat.div_eq_of_lt hyK], by rw [t3, Nat.mod_eq_of_lt hyK]; exact hy⟩
  refine ⟨?_, fun e he => ?_⟩
  · unfold affInT
    refine Eq.mpr (Bool.and_eq_true _ _) ⟨List.all_eq_true.2 fun e he => ?_,
      List.all_eq_true.2 fun y hy => ?_⟩
    · obtain ⟨t1, t2, t3⟩ := ents e he
      unfold entInT
      have hb' : (partAt s a G o).L.arrayOf[e.tree]? = some b := by rw [t1]; exact hb
      have hA' : reqArray (partAt s a G o).L.check.rows.layout b.1 b.2 = some Ar := hA
      have hm' : atMoment1 (partAt s a G o) b Ar = true := hm1
      rw [hb']
      simp only [hA', hm', t2, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨hI, by omega⟩
    · exact slotIn_of_fl own (b := partAt s a G o) zG U.mask (hS y hy)
  · obtain ⟨t1, t2, _⟩ := ents e he
    exact ⟨t2, T, by rw [t1]; exact hT', hR⟩

end

/-- **The plug**: what the lookup's form for the join names is filled behind K5's hearing. -/
theorem cEnd_behind {F' G : Fork} {f : Aff} (hc : Fo.FilledA F' f) (st : Stays F' G) :
    SlotsIn (PscRun.Filled G) f := fun x hx => (st x.1 _ _ ⟨(hc x hx).2, rfl, rfl⟩).1

section
variable {iU3 K nW : ℕ}

theorem cov_noEnts {f : Aff} (h : f.ents = #[]) : Cov iU3 K nW f := by
  intro e he
  rw [h] at he
  cases he

theorem cov_getD {KF : Array Aff} (hK : ∀ f ∈ KF.toList, Cov iU3 K nW f) (c : ℕ) :
    Cov iU3 K nW (KF.getD c (Aff.ofConst zeroE)) := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : KF[c]? with
  | none => exact cov_ofConst _
  | some f => exact hK f (Array.mem_toList_iff.2 (Array.mem_of_getElem? h))

/-- Join's written form names the key forms' entries alone, where g.cEnd names none. -/
theorem cov_joinW {g : Forest.Heard} {KF : Array Aff} (hK : ∀ f ∈ KF.toList, Cov iU3 K nW f)
    (hc : g.cEnd.ents = #[]) : Cov iU3 K nW (joinW g KF) := by
  unfold joinW
  refine cov_sub (cov_add ?_ (cov_ofConst _)) (cov_noEnts hc)
  have key : ∀ (l : List ℕ) (s : Aff), Cov iU3 K nW s → Cov iU3 K nW
      (l.foldl (fun (f : Aff) c => Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
        KF.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE)) s) := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons c l ih =>
      intro s hs
      exact ih _ (cov_addMul hs (cov_sub (cov_ofConst _) (cov_getD hK c)) _)
  exact key _ _ (cov_ofConst _)

end

section
variable {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard}
  {G : Fork} {c : ParC} {i : Runs.In} {K : ℕ}

/-- **The join's one form, made behind the lay, names only what is there.** -/
theorem k5_join_there (own : List (ℕ × ℕ)) (hh : hear x (a.F, rs, 0) = some (h, G, [], 0))
    (hz : Sized a.F) (hin : inOf (seatCO c) c (behind s a h G) = some (i, K)) {l₁ : List Aff}
    {j : Runs.JoinsP} (h1 : Runs.firstRun i K = some (l₁, j)) {k3 : Runs.PadIn} {kf : Array Aff}
    (hk : Runs.keysRun i k3 j = some kf) (gf : GeoFits c.geo x) (U : U3There own s a c)
    (o : Option ℕ) {g : Forest.Heard} (hcE : g.cEnd.ents = #[]) (hcF : Fo.FilledA a.F g.cEnd)
    {F : Fork} {t : OnBytes.K.Kc.Tape} {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF g kf F t = some y) :
    affInT own none [] (partAt s a G o) y.1 = true ∧
      ∀ e ∈ y.1.ents.toList, e.row = 0 ∧ ∃ T, G.trees[e.tree]? = some T ∧ T.R = 1 := by
  obtain ⟨eg, eu, hK, g0, l, lk, _, hl, hp, ht⟩ := inOf_behind hin
  obtain ⟨L, _, hs, zG, st, _⟩ := hear_law_paid hh hz
  obtain ⟨_, bl⟩ := hear_below hh hz
  rw [← eg] at hl hp ht gf
  have hS := K5Law.join_slots_K05 (Ps := PscRun.Filled G) (pts_slots hs hp gf)
    (rows_slots (leftP_spec hl) hs (K5Law.points_are hp)) h1 hk (cEnd_behind hcF st) hj
  have hC : Cov c.iU3 K c.nW y.1 := by
    rw [(K5Law.joinF_is hj).1, ← eu]
    exact cov_joinW (K5Law.keysRun_covered (K5Law.len_in ht)
      (rows_cov (leftP_spec hl) hs (K5Law.points_are hp)) h1 hk) hcE
  exact form_there own zG U bl.trees hK o hS hC

end

/-- Marking an owed claim as added turns no mark on a slot. -/
theorem lateOf_paid (F : Fork) (n : ℕ) : lateOf F (F.paid n) = [] := by
  unfold lateOf
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  show (if (!(F.gotF.getD j false) && F.gotF.getD j false) = true then _ else none) = none
  cases F.gotF.getD j false <;> rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.form_there
#print axioms VerifiableInference.Desc.First.Att.P.cEnd_behind
#print axioms VerifiableInference.Desc.First.Att.P.cov_joinW
#print axioms VerifiableInference.Desc.First.Att.P.k5_join_there
#print axioms VerifiableInference.Desc.First.Att.P.lateOf_paid
