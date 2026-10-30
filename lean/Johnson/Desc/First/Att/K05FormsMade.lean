-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05FormsMade.lean: kind K5: EVERY FORM THAT THE RUNS "first" AND "second" GATHER
AT THE RECORD BEHIND THE HEARING's LAY NAMES ONLY WHAT IS THERE: the public test affInT
(FormsIn.lean; imported, not turned), with no late
slot, and its reader's test ownRow (ReaderOf.lean's text, typed here as a Prop on the entry).

Main names:
  `fl_lt`: a filled slot of a sized ledger is below the number of slots.
  `slotIn_of_fl`: so it passes slotIn AT free := none AND late := [], where the mask row's seat is
    there. THESE TWO LETTERS ARE CLOSED HERE, NOT PAID: the table's term is affInT own (mergeOf s)
    R.late: that the reader hands no late slot, and that no slot is masked elsewhere (mergeOf s =
    none), IS A DEBT OF THIS FILE; Att/K05FormsMadeAt.lean pays both at the generic reader.
  `U3There own s a c`: THREE PUBLIC FACTS ON THE RECORD IN FRONT: (tree) the open ledger's array number
    c.iU3 has one own row and at least c.nW columns · (array) the link's list names at c.iU3 an array
    of the layout, of the open segment's second sending, with a row and at least c.nW columns ·
    (mask) the segment's mask row's message is seated.
  `inOf_behind`: what the claims' seat reads at the record behind the lay: leftP and pointsOf at what
    was heard and the ledger behind; the columns of that ledger's array.
  `k5_forms_there`: **for every f that "first" or "second" gathers there: affInT own none [] (no slot
    masked elsewhere; no late slot: see above) holds of f at the part behind the lay; each entry of f names row 0 of the array c.iU3, which has one own
    row.**
Premises: the hearing's return at a sized ledger, with no round left and lead 0 (the seam's form:
decide_lays, Att/K5Shape.lean) · the seat's reading and the two runs return ·
GeoFits (Att/K05PtsSlots.lean: a Bool on public data) · U3There.
It stands on: slots_covered_K05' (Claims/SlotsCovered.lean) at pts_slots and rows_slots;
reads_covered_heard (Att/K05ReadsCovered.lean).
Limits. U3There IS SAID BY NO CLAUSE OF THE TABLE's TERM KNOWN HERE: it is shown of no record here.
That the runs return is not shown here (Att/K05ReturnsLk.lean). "keys" gathers no form; "join" and
"planes" are not spoken of. EMPTY AT: a record at which a run does not return.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05FormsKept
import Johnson.Desc.First.Att.K05PtsSlots
import Johnson.Desc.First.Att.K05ReadsCovered
import Johnson.Desc.First.Att.Claims.SlotsCovered
import Johnson.Desc.First.Att.Claims.AnySeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.K9 (seatAt arrayIn entIn maskSeat lateAt lateOk slotIn atMoment1 entInT
  affInT)
open K5Law (SlotsIn Cov)

theorem fl_lt {G : Fork} (z : Sized G) {j : ℕ} (h : PscRun.Filled G j) : j < G.ns := by
  rw [← z.got]
  by_contra hn
  have h0 : G.gotF.getD j false = false := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hn)]
  have h1 : G.gotF.getD j false = true := h
  rw [h0] at h1
  cases h1

theorem slotIn_of_fl (own : List (ℕ × ℕ)) {b : K9.Part} (z : Sized b.F)
    (hm : (maskSeat own b).isSome = true) {j : ℕ} (h : PscRun.Filled b.F j) : slotIn own none [] b j = true := by
  have hj := fl_lt z h
  have h1 : b.F.gotF.getD j false = true := h
  unfold slotIn
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨hj, hm, by simp, Or.inr ⟨h1, ?_, ?_⟩⟩
  · rw [z.vp]
    exact hj
  · rw [z.mf]
    exact hj

/-- Three public facts on the record in front. -/
structure U3There (own : List (ℕ × ℕ)) (s : First.S) (a : First.AttOwn) (c : ParC) : Prop where
  tree : ∃ T, a.F.trees[c.iU3]? = some T ∧ T.R = 1 ∧ c.nW ≤ T.K
  array : ∃ b Ar, a.L.arrayOf[c.iU3]? = some b ∧
    reqArray a.L.check.rows.layout b.1 b.2 = some Ar ∧
    atMoment1 (partAt s a a.F none) b Ar = true ∧ 0 < Ar.sizeI ∧ c.nW ≤ Ar.sizeC
  mask : (maskSeat own (partAt s a a.F none)).isSome = true

section
variable {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard}
  {G : Fork} {c : ParC} {i : Runs.In} {K : ℕ}

/-- **What the claims' seat reads at the record behind the lay.** -/
theorem inOf_behind (hin : inOf (seatCO c) c (behind s a h G) = some (i, K)) :
    i.g = c.geo ∧ i.iU3 = c.iU3 ∧ (G.trees[c.iU3]?).map (·.K) = some K ∧
      ∃ g l lk, a.g = some g ∧ leftP c.geo g.zk h G = some l ∧ pointsOf c.geo g.zk h l = some i.p ∧
        tablesP c.geo c.mats c.nW lk i.p = some i.t := by
  obtain ⟨e1, e2, _, hp, hK, lk, _, ht⟩ := K5Law.inOf_some _ _ _ _ _ hin
  have hp' : (a.g.bind fun g => (some h).bind fun h' => ptsFrom c.geo g.zk h' G) = some i.p := hp
  obtain ⟨g, hg, hp2⟩ := Option.bind_eq_some_iff.1 hp'
  have hp3 : ptsFrom c.geo g.zk h G = some i.p := hp2
  unfold ptsFrom at hp3
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp3
  obtain ⟨l, hl, hq⟩ := hp3
  exact ⟨e1, e2, hK, g, l, lk, hg, hl, hq, ht⟩

/-- **Every form that "first" or "second" gathers behind the lay names only what is there.** -/
theorem k5_forms_there (own : List (ℕ × ℕ)) (hh : hear x (a.F, rs, 0) = some (h, G, [], 0))
    (hz : Sized a.F) (hin : inOf (seatCO c) c (behind s a h G) = some (i, K)) {l₁ l₂ : List Aff}
    {j : Runs.JoinsP} (h1 : Runs.firstRun i K = some (l₁, j)) (h2 : Runs.secondRun i K = some l₂)
    (gf : GeoFits c.geo x) (U : U3There own s a c) (o : Option ℕ) :
    ∀ f ∈ l₁ ++ l₂, affInT own none [] (partAt s a G o) f = true ∧
      ∀ e ∈ f.ents.toList, e.row = 0 ∧ ∃ T, G.trees[e.tree]? = some T ∧ T.R = 1 := by
  obtain ⟨eg, eu, hK, g, l, lk, _, hl, hp, ht⟩ := inOf_behind hin
  obtain ⟨L, _, hs, zG, _, _⟩ := hear_law_paid hh hz
  obtain ⟨_, bl⟩ := hear_below hh hz
  rw [← eg] at hl hp ht gf
  have hS := K5Law.slots_covered_K05' (Ps := PscRun.Filled G) (pts_slots hs hp gf)
    (rows_slots (leftP_spec hl) hs (K5Law.points_are hp)) h1 h2
  have hC := reads_covered_heard hh hz hl hp ht h1 h2
  obtain ⟨T, hT, hR, hW⟩ := U.tree
  obtain ⟨b, Ar, hb, hA, hm1, hI, hCz⟩ := U.array
  have hT' : G.trees[c.iU3]? = some T := by rw [bl.trees]; exact hT
  have eK : K = T.K := by
    rw [hT'] at hK
    exact (Option.some.inj hK).symm
  intro f hf
  have ents : ∀ e ∈ f.ents.toList, e.tree = c.iU3 ∧ e.row = 0 ∧ e.idx < c.nW := by
    intro e he
    obtain ⟨y, hy, t1, t2, t3⟩ := hC f hf e he
    have hyK : y < K := by rw [eK]; omega
    exact ⟨t1.trans eu, by rw [t2, Nat.div_eq_of_lt hyK], by rw [t3, Nat.mod_eq_of_lt hyK]; exact hy⟩
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
    · exact slotIn_of_fl own (b := partAt s a G o) zG U.mask (hS f hf y hy)
  · obtain ⟨t1, t2, _⟩ := ents e he
    exact ⟨t2, T, by rw [t1]; exact hT', hR⟩

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.slotIn_of_fl
#print axioms VerifiableInference.Desc.First.Att.P.inOf_behind
#print axioms VerifiableInference.Desc.First.Att.P.k5_forms_there
