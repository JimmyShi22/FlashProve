-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsAny.lean: K08Claims AT ANY TABLE OF CELLS: the law of EquationsForms.lean
with the cells a free function A (array, row, column), not the reading of a lay; the single equations as the
list rowsTail of gaps, not as forms on a lay's entries.

Statements and proofs. WHY: the world in which kind K9's lemma is stated reads its cells off the bound data by
a function that is no lay's reading; K08Raw is general in A already. THE PROOF IS k08_claims' OWN, LINE BY LINE,
made of it by program: the places that turn: the letters that are introduced; RawRows' table; the last step,
which there goes on from gaps to forms by batch_rowsForm and here stops; and, for A0, five terms that go on
from A0 to the returned ledger by the three premises. No routine of `verify-on-bytes` is
named. USED OF THE FILES UNDER OnBytes/, ON RECORDS AND PLAIN DATA ALONE: what EquationsForms.lean's head
lists, and rowsTail, Rising, batchOf.
Main names:
  **K08Any** (a closed Prop), **k08_any**: from the two yeses, one coefficient a slot, Fits and RawRows at A:
    the list rowsTail has rising exponents, each from the plan's number of claims on and below that
    number + topOf; the list of claims is four and then as many as there are matrices and reads; and behind
    the four the total grows by batchOf at the batching element, at A, of that list.
  **K08AnyAt**, **k08_any_at**: the same with the list added to ANY ledger A0 that has the returned ledger's
    frame of arrays, batching element and plan's number, and one coefficient a slot (for a step that gathers
    several runs' lists and adds them behind the last run). k08_any is its case A0 := the returned ledger.
  eq_split: the list is four claims and then NM + the number of reads: from the list's yes alone.
  K08AnyTests, k08_any_tests: the same with RawRows replaced as in K08Tests: testsP's yes behind the adding,
    ReadsRaw at A, two premises on public numbers.
Limits: those of K08Claims and K08Tests.

-/
import Johnson.Desc.First.TailClaims.EquationsTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows Finset
open OnBytes.Tie.Pv.Tail (ReadsRaw UnitRow)

/-- **K08Claims at any table of cells.** -/
def K08Any : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (A : Nat → Nat → Nat → K)
    (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 G : Fork)
    (look cls : List Claim),
    F.LS.size = F.ns → equations front tl funs F = .ok (tl', F1, cls) →
    addAll F1 (look ++ cls) = some G → Fits tl →
    RawRows W tl F1 funs (ρ.val F.theta) A →
    Rising (rowsTail ρ tl funs F.planClaimsF) ∧
    (∀ r ∈ rowsTail ρ tl funs F.planClaimsF,
      F.planClaimsF ≤ r.1 ∧ r.1 < F.planClaimsF + topOf tl funs) ∧
    ∃ (four rest : List Claim) (X X4 : Fork), cls = four ++ rest ∧ four.length = 4 ∧
      rest.length = tl.NM + (readsList tl funs).length ∧ addAll F1 look = some X ∧
      addAll X four = some X4 ∧ addAll X4 rest = some G ∧
      G.total ρ W = X4.total ρ W +
        batchOf (ρ.val F.theta) A (rowsTail ρ tl funs F.planClaimsF)

/-- **K08Claims at any table of cells, the list added to any ledger A0 that has the returned ledger's frame of
arrays, batching element and plan's number, and one coefficient a slot.** -/
def K08AnyAt : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (A : Nat → Nat → Nat → K)
    (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 A0 G : Fork)
    (look cls : List Claim),
    F.LS.size = F.ns → equations front tl funs F = .ok (tl', F1, cls) →
    A0.LS.size = A0.ns → treesFrame A0.trees = treesFrame F1.trees → A0.theta = F1.theta →
    A0.planClaimsF = F1.planClaimsF →
    addAll A0 (look ++ cls) = some G → Fits tl →
    RawRows W tl F1 funs (ρ.val F.theta) A →
    Rising (rowsTail ρ tl funs F.planClaimsF) ∧
    (∀ r ∈ rowsTail ρ tl funs F.planClaimsF,
      F.planClaimsF ≤ r.1 ∧ r.1 < F.planClaimsF + topOf tl funs) ∧
    ∃ (four rest : List Claim) (X X4 : Fork), cls = four ++ rest ∧ four.length = 4 ∧
      rest.length = tl.NM + (readsList tl funs).length ∧ addAll A0 look = some X ∧
      addAll X four = some X4 ∧ addAll X4 rest = some G ∧
      G.total ρ W = X4.total ρ W +
        batchOf (ρ.val F.theta) A (rowsTail ρ tl funs F.planClaimsF)

theorem k08_any_at : K08AnyAt := by
  intro K _ ρ W A front tl tl' funs F F1 A0 G look cls hs h hsA hfrA hthA hplA hadd hfit hV
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    obtain ⟨tlx, Fx, arr⟩ := x
    have h' := Except.ok.inj h
    have htl : tlx = tl' := congrArg Prod.fst h'
    have hFx : Fx = F1 := congrArg (fun y => y.2.1) h'
    have hcl : arr.toList = cls := congrArg (fun y => y.2.2) h'
    rw [← hFx] at hV hfrA hthA hplA
    rw [← hcl] at hadd
    rw [eqAll_split] at e
    obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 e
    rw [(eq_must_ok h1).2] at k1
    obtain ⟨u2, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
    rw [(eq_must_ok h2).2] at k2
    obtain ⟨z, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
    rw [(eq_ask_ok h3).2] at k3
    obtain ⟨u4, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
    rw [(eq_test_ok h4).2] at k4
    obtain ⟨g', t5, h5, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
    rw [(eq_get_ok h5).2] at k5
    obtain ⟨u6, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
    rw [(eq_must_ok h6).2] at k6
    unfold eqRest at k6
    obtain ⟨before, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
    obtain ⟨hbef, et7⟩ := eq_claims_ok h7
    rw [et7] at k7
    obtain ⟨tla, s1, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
    obtain ⟨tlb, s2, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
    obtain ⟨o1, n1, a1⟩ := tame_keys tl _ _ _ _ h8
    obtain ⟨o2, n2, a2⟩ := tame_counts tla _ _ _ _ h9
    -- a first look at the tail, for the list alone
    obtain ⟨tl1, hW, h44, hlaid, etl, hall, n3, e3, l3, _⟩ :=
      eqTail_total ρ W F before tlb tlx funs front s2 (Fx, arr) k9
    have hF2 : Fx = s2.1 := congrArg Prod.fst e3
    have harr : arr = s2.2 ++ n3.toArray := congrArg Prod.snd e3
    have hs2 : s2.2 = (n1 ++ n2).toArray := by
      rw [a2, a1]
      simp
    have hl : arr.toList = (n1 ++ n2) ++ n3 := by
      rw [harr, hs2]
      simp
    have hlen : (n1 ++ n2).length = 4 := by
      have q : front + (n1 ++ n2).length - (front + 0) = 4 := by
        rw [hbef, hs2] at h44
        exact h44
      omega
    rw [hl, addAll_append] at hadd
    obtain ⟨X, hX, hadd2⟩ := Option.bind_eq_some_iff.1 hadd
    rw [addAll_append] at hadd2
    obtain ⟨X4, hX4, hG⟩ := Option.bind_eq_some_iff.1 hadd2
    have os : OnlySide F Fx := by
      rw [hF2]
      exact o1.trans o2
    obtain ⟨oX, _, sX⟩ := addAll_keeps look A0 X hsA hX
    obtain ⟨o4, _, s4⟩ := addAll_keeps (n1 ++ n2) X X4 sX hX4
    -- the tail again, against X4
    obtain ⟨tl1', hW', _, _, _, _, n3', e3', _, push⟩ :=
      eqTail_total ρ W X4 before tlb tlx funs front s2 (Fx, arr) k9
    have htl1 : tl1' = tl1 := congrArg Prod.fst (Except.ok.inj (hW'.symm.trans hW))
    have hn3 : n3' = n3 := by
      have q : s2.2 ++ n3'.toArray = s2.2 ++ n3.toArray :=
        (congrArg Prod.snd e3').symm.trans harr
      have q' := congrArg Array.toList q
      simpa using q'
    rw [htl1, hn3] at push
    have fr : Fr X4 s2.1 := by
      unfold Fr
      rw [← hF2]
      exact ((o4.trees.trans oX.trees).trans hfrA).symm
    obtain ⟨hk, _, htot⟩ := push fr X4 G ⟨rfl, rfl, s4, rfl⟩ hG
    obtain ⟨hP1, e1, hgam1⟩ := eqWeights_spec tlb tl1 front s2 s2 hW
    have th4 : X4.theta = F.theta := ((o4.theta.trans oX.theta).trans hthA).trans os.theta
    have pl4 : X4.planClaimsF = F.planClaimsF := ((o4.plan.trans oX.plan).trans hplA).trans os.plan
    have thG : G.theta = F.theta := hk.theta.trans th4
    have plG : G.planClaimsF = F.planClaimsF := hk.plan.trans pl4
    have hP1' : Powered tl1 X4.theta := by
      rw [th4, ← os.theta, hF2]
      exact hP1
    have hV' : RawRows W tl G funs (ρ.val G.theta) A := by
      rw [thG]
      exact rawRows_cols hV fun t =>
        colsU_frame G Fx (((hk.frame.trans o4.trees).trans oX.trees).trans hfrA) t
    obtain ⟨hr, hb, eNM, eReads, ht⟩ := spread_of_total ρ W (eqKeys_spec tl tla _ _ _ h8)
      (eqCounts_spec tla tlb _ _ _ h9) hP1' e1 hgam1 etl hall hk htot hfit _ hV'
    rw [plG] at hr hb ht
    rw [thG] at ht
    exact ⟨hr, hb, n1 ++ n2, n3, X, X4, hcl.symm.trans hl, hlen, by rw [l3, eNM, eReads], hX, hX4,
      hG, ht⟩

theorem k08_any : K08Any := by
  intro K _ ρ W A front tl tl' funs F F1 G look cls hs h hadd hfit hV
  have os := eq_side h
  exact k08_any_at K ρ W A front tl tl' funs F F1 F1 G look cls hs h
    (by rw [os.LS, os.ns]; exact hs) rfl rfl rfl hadd hfit hV

/-- **The same, with RawRows replaced as in K08Tests.** -/
def K08AnyTests : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (A : Nat → Nat → Nat → K)
    (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 G Fc : Fork)
    (look cls : List Claim) (ls : Array E) (nU : Array Nat),
    F.LS.size = F.ns → equations front tl funs F = .ok (tl', F1, cls) →
    addAll F1 (look ++ cls) = some G → Fits tl →
    testsP nU { tl' with lsTail := ls } G = .ok Fc →
    ReadsRaw ρ { tl' with lsTail := ls } funs Fc W A →
    (Fc.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2 →
    (∀ x ∈ readsList tl funs, UnitRow Fc (uOf tl x.1) ∧
      ∀ d, d < (tl.mats.getD x.1.mat {}).k → posOf tl x.1 x.2 d < colsU F1 (uOf tl x.1)) →
    Rising (rowsTail ρ tl funs F.planClaimsF) ∧
    (∀ r ∈ rowsTail ρ tl funs F.planClaimsF,
      F.planClaimsF ≤ r.1 ∧ r.1 < F.planClaimsF + topOf tl funs) ∧
    ∃ (four rest : List Claim) (X X4 : Fork), cls = four ++ rest ∧ four.length = 4 ∧
      rest.length = tl.NM + (readsList tl funs).length ∧ addAll F1 look = some X ∧
      addAll X four = some X4 ∧ addAll X4 rest = some G ∧
      G.total ρ W = X4.total ρ W +
        batchOf (ρ.val F.theta) A (rowsTail ρ tl funs F.planClaimsF)

theorem k08_any_tests : K08AnyTests := by
  intro K _ ρ W A front tl tl' funs F F1 G Fc look cls ls nU hs h hadd hfit ht hW hrows hU
  have hth : Fc.theta = F.theta := (coef_theta (tests_ok ht).2.1).trans (eq_link hs h hadd).2.2.1
  exact k08_any K ρ W A front tl tl' funs F F1 G look cls hs h hadd hfit
    (k08_raw K ρ W A front tl tl' funs F F1 Fc cls ls h hth (tests_ok ht).2.2 hW hrows hU)

/-- **The list is four claims and then as many as there are matrices and reads**: from the list's yes alone: no
adding is asked. (ρ and W are handed on to eqTail_total and play no part.) -/
theorem eq_split {K : Type} [Field K] (ρ : Reading K) (W : World K) {front : Nat} {tl tl' : HTailF2}
    {funs : Array HFun} {F F1 : Fork} {cls : List Claim}
    (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∃ four rest : List Claim, cls = four ++ rest ∧ four.length = 4 ∧
      rest.length = tl.NM + (readsList tl funs).length := by
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    obtain ⟨tlx, Fx, arr⟩ := x
    have h' := Except.ok.inj h
    have htl : tlx = tl' := congrArg Prod.fst h'
    have hFx : Fx = F1 := congrArg (fun y => y.2.1) h'
    have hcl : arr.toList = cls := congrArg (fun y => y.2.2) h'
    rw [eqAll_split] at e
    obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 e
    rw [(eq_must_ok h1).2] at k1
    obtain ⟨u2, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
    rw [(eq_must_ok h2).2] at k2
    obtain ⟨z, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
    rw [(eq_ask_ok h3).2] at k3
    obtain ⟨u4, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
    rw [(eq_test_ok h4).2] at k4
    obtain ⟨g', t5, h5, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
    rw [(eq_get_ok h5).2] at k5
    obtain ⟨u6, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
    rw [(eq_must_ok h6).2] at k6
    unfold eqRest at k6
    obtain ⟨before, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
    obtain ⟨hbef, et7⟩ := eq_claims_ok h7
    rw [et7] at k7
    obtain ⟨tla, s1, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
    obtain ⟨tlb, s2, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
    obtain ⟨o1, n1, a1⟩ := tame_keys tl _ _ _ _ h8
    obtain ⟨o2, n2, a2⟩ := tame_counts tla _ _ _ _ h9
    -- a first look at the tail, for the list alone
    obtain ⟨tl1, hW, h44, hlaid, etl, hall, n3, e3, l3, _⟩ :=
      eqTail_total ρ W F before tlb tlx funs front s2 (Fx, arr) k9
    have hF2 : Fx = s2.1 := congrArg Prod.fst e3
    have harr : arr = s2.2 ++ n3.toArray := congrArg Prod.snd e3
    have hs2 : s2.2 = (n1 ++ n2).toArray := by
      rw [a2, a1]
      simp
    have hl : arr.toList = (n1 ++ n2) ++ n3 := by
      rw [harr, hs2]
      simp
    have hlen : (n1 ++ n2).length = 4 := by
      have q : front + (n1 ++ n2).length - (front + 0) = 4 := by
        rw [hbef, hs2] at h44
        exact h44
      omega
    obtain ⟨_, e1, _⟩ := eqWeights_spec tlb tl1 front s2 s2 hW
    have ea := eqKeys_spec tl tla _ _ _ h8
    have eb := eqCounts_spec tla tlb _ _ _ h9
    have sNM : tlx.NM = tl.NM := carry4 (fun t => t.NM) ea rfl eb rfl e1 rfl etl rfl
    have sNM1 : tlx.NM = tl1.NM := (congrArg (fun t => t.NM) etl).trans rfl
    have sR : readsList tlx funs = readsList tl funs :=
      carry4 (fun t => readsList t funs) ea rfl eb rfl e1 rfl etl rfl
    have sR1 : readsList tlx funs = readsList tl1 funs :=
      (congrArg (fun t => readsList t funs) etl).trans rfl
    exact ⟨n1 ++ n2, n3, hcl.symm.trans hl, hlen, by rw [l3, ← sNM1, sNM, ← sR1, sR]⟩

/-- What the run leaves of the record that the single equations read: rowsTail is the same at the
returned record. -/
theorem eq_rowsTail {K : Type} [Field K] (ρ : Reading K) (n : Nat) {front : Nat} {tl tl' : HTailF2}
    {funs : Array HFun} {F F1 : Fork} {cls : List Claim}
    (h : equations front tl funs F = .ok (tl', F1, cls)) :
    rowsTail ρ tl' funs n = rowsTail ρ tl funs n :=
  eq_same (fun t => rowsTail ρ t funs n) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)

theorem eq_topOf {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork} {cls : List Claim}
    (h : equations front tl funs F = .ok (tl', F1, cls)) : topOf tl' funs = topOf tl funs :=
  eq_same (fun t => topOf t funs) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_any_at
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_any
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_any_tests
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_split
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_rowsTail
