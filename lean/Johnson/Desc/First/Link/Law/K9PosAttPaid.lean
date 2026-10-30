-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9PosAttPaid.lean: THE TEST `posPlanB`
(Johnson/Desc/First/Link/K9PosAsk.lean: every table of a segment's plan ends inside
the array of the third vector) ACCEPTS AT THE TWELVE ATTENTION SEGMENTS: a theorem in the goals'
scope alone, BY THE MAKE OF THE PLAN: no entry test, no head, no opening of the maker, no numeral
but "twelve groups". The end is the clause at l = 2 g + 1 of the sentence `PosAsked Z`
(Johnson/Desc/First/Link/Law/K9PosAskLaw.lean), written out. One definition and statements with
their proofs; nothing is evaluated.

How. The test lays the tables one behind the other by their WRITTEN numbers of entries
(`attTriples`, `placeB`). So a table ends at or below the sum of all entries (`place_end`); a
table's columns times its stretches of rows are at most its written entries (`entries_le`: the
five sorts of Johnson/Desc/First/Link/Law/AttTabEntries.lean, over the planner's own list of
matrices: `plan_mats`, Johnson/Road/Lane5AttLabel.lean); the sum is at most
`Attention.Shape.tableElems` (`sum_le`), which is the plan's nW (`plan_nW`), which is the array's
number of columns (`ofPlan_u3_tree`, Johnson/Desc/First/Att/Claims/OfPlan.lean).

  `place_end`   the law on `placeB`
  `sum_repB`, `mem_repB`, `sum_parts`, `sum_att`, `mem_att`   the list `attTriples`: its sum and
      its members
  `nKF`, `units_fold`, `units_le`   the units of the scores are at most the count in tableElems
  `sum_le`, `entries_le`   as above
  `posPlan_att`   general in the plan: where `Attention.plan` returns A0, at every structure with
      A0's matrices and every number of columns from A0.nW on, the test's body accepts
  `posAsked_att`   **MAIN**

What is not claimed. Nothing on tiling. Nothing on soundness.

-/
import Johnson.Desc.First.Link.K9PosAsk
import Johnson.Desc.First.Link.Law.K9NuPaid
import Johnson.Desc.First.Link.Law.AttTabEntries
import Johnson.Road.Lane5AttLabel

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks

open OnBytes OnBytes.Model
open OnBytes.Model.Stages (SubPlanH LinkH)
open OnBytes.Road.L5 (fixed plan_mats jp_ok bind_ok)
open VerifiableInference.Desc.First.Att.P (planIs_public)

/-! ## 1 Tables laid one behind the other -/

/-- A table of placeB ends at or below the sum of all entries. -/
theorem place_end : ∀ (L : List (ℕ × ℕ × ℕ)) (p : ℕ) (t : ℕ × ℕ × ℕ), t ∈ placeB L p →
    ∃ e, (t.1, t.2.1, e) ∈ L ∧ t.2.2 + e ≤ p + (L.map (·.2.2)).sum
  | [], _, _, h => by cases h
  | a :: L, p, t, h => by
    rcases List.mem_cons.1 h with rfl | h
    · refine ⟨a.2.2, List.mem_cons_self, ?_⟩
      show p + a.2.2 ≤ p + (a.2.2 + (L.map (·.2.2)).sum)
      omega
    · obtain ⟨e, he, hle⟩ := place_end L (p + a.2.2) t h
      refine ⟨e, List.mem_cons_of_mem _ he, ?_⟩
      show t.2.2 + e ≤ p + (a.2.2 + (L.map (·.2.2)).sum)
      omega

theorem sum_repB (l : List (ℕ × ℕ × ℕ)) : ∀ k, ((repB k l).map (·.2.2)).sum =
    k * (l.map (·.2.2)).sum
  | 0 => by simp [repB]
  | k + 1 => by
    show ((l ++ repB k l).map (·.2.2)).sum = _
    rw [List.map_append, List.sum_append, sum_repB l k, Nat.succ_mul, Nat.add_comm]

theorem mem_repB {l : List (ℕ × ℕ × ℕ)} {x : ℕ × ℕ × ℕ} : ∀ {k}, x ∈ repB k l → x ∈ l
  | 0, h => by cases h
  | k + 1, h => by
    rcases List.mem_append.1 (show x ∈ l ++ repB k l from h) with h | h
    · exact h
    · exact mem_repB h

theorem sum_parts (a b : ℕ) : ∀ n, (((List.range n).flatMap fun q => [(q, a, b)]).map
    (·.2.2)).sum = n * b
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, sum_parts a b n]
    simp [Nat.succ_mul]

/-- The entries of an attention segment's tables, added up. -/
theorem sum_att (S : Attention.Shape) (k : ℕ) : ((attTriples S k).map (·.2.2)).sum =
    3 * (S.cf.NAs * (S.kAs / S.cf.NAs)) + (k + 6) * S.fillH + S.fillO * S.T / 2 ^ S.cf.la +
      (2 * k + 5) * (S.fillQ * S.T / 2 ^ S.cf.la) + 3 * S.kbA := by
  unfold attTriples
  simp only [List.map_append, List.sum_append, sum_repB, sum_parts, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

/-- Which tables there are. -/
theorem mem_att {S : Attention.Shape} {k : ℕ} {x : ℕ × ℕ × ℕ} (h : x ∈ attTriples S k) :
    (∃ q < S.cf.NAs, x = (q, 2 ^ S.cf.lmS, S.kAs / S.cf.NAs)) ∨ x = (S.cf.NAs, S.T, S.fillH) ∨
      x = (S.cf.NAs + 1, 2 ^ S.cf.la, S.fillO * S.T / 2 ^ S.cf.la) ∨
      x = (S.cf.NAs + 3, 2 ^ S.cf.la, S.fillQ * S.T / 2 ^ S.cf.la) ∨
      x = (S.cf.NAs + 2, 2 ^ S.cf.lmb, S.kbA) := by
  unfold attTriples at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at h
  have hr : ∀ {l : List (ℕ × ℕ × ℕ)} {k}, x ∈ repB k l → x ∈ l := fun h => mem_repB h
  rcases h with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h
  all_goals first
    | exact .inl ⟨_, hq, rfl⟩
    | exact .inr (.inl h)
    | exact .inr (.inr (.inl h))
    | exact .inr (.inr (.inr (.inl h)))
    | exact .inr (.inr (.inr (.inr h)))
    | (have h2 := hr h
       simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at h2
       first
         | exact .inr (.inl h2)
         | exact .inr (.inr (.inr (.inl h2))))

/-! ## 2 The units of the scores -/

/-- The count nKF in `Attention.Shape.tableElems`. -/
def nKF (S : Attention.Shape) : ℕ :=
  S.calls.foldl (fun n c => if c.kind == .kfd then n + c.segs.length else n) 0

theorem units_fold : ∀ (l : List Attention.ACall) (k n : ℕ),
    ((l.zipIdx k).flatMap fun x =>
      if x.1.kind == Attention.Table.kfd then
        ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => x.1.holds s).map
          fun s => (x.2, x.1, s)
      else []).length + n ≤
      l.foldl (fun n c => if c.kind == .kfd then n + c.segs.length else n) n
  | [], _, n => by simp
  | c :: l, k, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, List.foldl_cons]
    have ih := units_fold l (k + 1) (if c.kind == .kfd then n + c.segs.length else n)
    have hc : ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.holds s).length ≤
        c.segs.length := held_le c
    by_cases hk : (c.kind == Attention.Table.kfd) = true
    · simp only [hk, if_true, List.length_map] at ih ⊢
      omega
    · simp only [hk, if_false, List.length_nil, Bool.false_eq_true] at ih ⊢
      omega

theorem units_le (S : Attention.Shape) : unitsB S ≤ nKF S := by
  unfold unitsB nKF Attention.unitsOf
  rw [← Array.foldl_toList]
  have h := units_fold S.calls.toList 0 0
  simpa using h

theorem sum_le (S : Attention.Shape) :
    ((attTriples S (unitsB S)).map (·.2.2)).sum ≤ S.tableElems := by
  rw [sum_att]
  have hk := units_le S
  have h1 : S.cf.NAs * (S.kAs / S.cf.NAs) ≤ S.kAs := Nat.mul_div_le _ _
  have h2 : (unitsB S + 6) * S.fillH ≤ (nKF S + 6) * S.fillH :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (2 * unitsB S + 5) * (S.fillQ * S.T / 2 ^ S.cf.la) ≤
      (2 * nKF S + 5) * (S.fillQ * S.T / 2 ^ S.cf.la) := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 3 * S.kAs + (nKF S + 6) * S.fillH + S.fillO * S.T / 2 ^ S.cf.la +
    (2 * nKF S + 5) * (S.fillQ * S.T / 2 ^ S.cf.la) + 3 * S.kbA
  omega

/-! ## 3 A table's entries -/

theorem fixed_m (M : TMat) : (fixed M).m = M.m := by
  unfold fixed
  split <;> rfl

theorem fixed_k (M : TMat) : (fixed M).k = M.k := by
  unfold fixed
  split <;> rfl

/-- The matrix's columns times its stretches of rows are at most the table's written entries. -/
theorem entries_le (S : Attention.Shape) (i : Attention.In) {k : ℕ} {x : ℕ × ℕ × ℕ}
    (h : x ∈ attTriples S k) :
    ((((Attention.matrices S i).map fixed).getD x.1 {}).k *
      ((((Attention.matrices S i).map fixed).getD x.1 {}).m / x.2.1)) ≤ x.2.2 := by
  rcases mem_att h with ⟨q, hq, rfl⟩ | rfl | rfl | rfl | rfl
  · exact att_tab_as fixed fixed_m fixed_k S i hq
  · exact att_tab_ah fixed fixed_m fixed_k S i
  · exact att_tab_ao fixed fixed_m fixed_k S i
  · exact att_tab_qa fixed fixed_m fixed_k S i
  · exact att_tab_bA fixed fixed_m fixed_k S i

/-! ## 4 The clause -/

/-- The test's yes at a segment with an attention plan's structure and ledger. -/
theorem posPlan_att {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A0 : Attention.Plan} (h0 : Attention.plan settings i cf = .ok A0) {tl : HTailF2} {cols : ℕ}
    (hm : tl.mats = A0.seam.tl.mats) (hc : A0.nW ≤ cols) :
    (!(attPlaced A0.S).isEmpty && (attPlaced A0.S).all (tableIn tl cols)) = true := by
  rw [Bool.and_eq_true]
  constructor
  · have hne : attTriples A0.S (unitsB A0.S) ≠ [] := by
      intro e
      unfold attTriples at e
      simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_and] at e
    unfold attPlaced
    cases hL : attTriples A0.S (unitsB A0.S) with
    | nil => exact absurd hL hne
    | cons a L => rfl
  · refine List.all_eq_true.2 fun t ht => ?_
    obtain ⟨e, he, hle⟩ := place_end _ 0 t ht
    have h1 := entries_le A0.S A0.inp he
    have h2 := sum_le A0.S
    have h3 := plan_nW h0
    unfold tableIn
    rw [hm, plan_mats h0]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    refine .inr ?_
    have h1' : (((Attention.matrices A0.S A0.inp).map fixed).getD t.1 {}).k *
        ((((Attention.matrices A0.S A0.inp).map fixed).getD t.1 {}).m / t.2.1) ≤ e := h1
    omega

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}

/-- **The clauses of PosAsked Z at the twelve attention segments**
(Johnson/Desc/First/Link/Law/K9PosAskLaw.lean), written out. -/
theorem posAsked_att (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub o Pb.pol ly Pb.KL = .ok Z)
    (hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X) {g : ℕ} (hg : g < 12) :
    ∃ X, Z.p.built.links[2 * g + 1]? = some X ∧ posPlanB Z.p.X (2 * g + 1) X = true := by
  obtain ⟨k4, kN, _, hAll⟩ := _root_.Meaning.scope_plans hS hR hpub
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4, kN] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨declared, hd⟩ := OnBytes.Road.K4.Names.built_declared hB
  obtain ⟨_, hat⟩ := OnBytes.L5.LinksOrder.declareLinks_at _ _ _ _ _ hd
  obtain ⟨a, ha, _⟩ := hAll g hg
  obtain ⟨hp, hgp⟩ := _root_.Meaning.planG_there hpub C hg
  have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
      ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hgp]
    rfl
  have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
      ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, ha]
    rfl
  obtain ⟨_, q1⟩ := p0 g _ _ s0 t0
  obtain ⟨ar, har⟩ := hat (2 * g + 1) _ q1
  obtain ⟨A0, pf, h0, e⟩ := planIs_public hpub g a ha
  obtain ⟨h30, _⟩ := thirdA _ _ _ A0 h0
  obtain ⟨i0, T, hT, _, hK, _⟩ := _root_.K5Law.ofPlan_u3_tree ⟨_, _, _, A0, pf, h0, e⟩
  have h3 : a.seam.tl.ix.U.getD 2 none = some 0 := by
    rw [e]
    exact h30
  have eS : a.S = A0.S := by rw [e]
  have eM : a.seam.tl.mats = A0.seam.tl.mats := by rw [e]
  have eW : a.nW = A0.nW := by rw [e]
  have eC : colsB a.seam.Fp 0 = a.nW := by
    unfold colsB
    rw [i0] at hT
    rw [hT]
    exact hK
  refine ⟨_, har, ?_⟩
  unfold posPlanB triplesAt
  rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, ha]
  show (!(attPlaced a.S).isEmpty && (attPlaced a.S).all
    (tableIn a.seam.tl (colsB a.seam.Fp ((a.seam.tl.ix.U.getD 2 none).getD 0)))) = true
  rw [h3, eS]
  exact posPlan_att h0 eM (by
    show A0.nW ≤ colsB a.seam.Fp 0
    rw [eC, eW])

end

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.place_end
#print axioms VerifiableInference.Desc.K9Asks.sum_att
#print axioms VerifiableInference.Desc.K9Asks.mem_att
#print axioms VerifiableInference.Desc.K9Asks.units_le
#print axioms VerifiableInference.Desc.K9Asks.sum_le
#print axioms VerifiableInference.Desc.K9Asks.entries_le
#print axioms VerifiableInference.Desc.K9Asks.posPlan_att
#print axioms VerifiableInference.Desc.K9Asks.posAsked_att
