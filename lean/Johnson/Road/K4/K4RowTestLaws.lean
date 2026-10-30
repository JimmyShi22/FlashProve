-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/K4RowTestLaws.lean: THE LAWS OF THE ROW k4RowB, ASKED BY NO LIST
(Johnson/Road/K4/K4RowTest.lean): what its accept proves, what its rejection rejects, and general
laws on bent inputs that it rejects. Thirteen statements with their proofs. No
evaluation.

  `k4RowAt_iff`: the row's accept, opened: there is a group; at each g below X.NGr there is X.G's
    entry; frontB accepts at it where g < 2; rowB accepts at it (THE ROW ASKS rowLightB: the same
    Bool, by rowLight_eq, Johnson/Road/K4/PendLightBack.lean).
  **`k4RowAt_full`**: WHEREVER publicOf RETURNS, WITHOUT THE HEAD: the row's accept says that
    both tests accept at EVERY group below X.NGr (an "if and only if").
  LAW 1: **`k4Row_two`**: hA · k4RowB Zp = true ⟹ K4NamedTwo hA (what stays a test of the nine
    named tests of K4's row: Johnson/Road/K4/K4NamedPaid.lean). The head gives "X.NGr = 12"
    (Meaning.scope_plans); the constant's d1.lin is Zp.first.lin by its make; frontB at the groups
    2 to 11 comes of group 1's (frontB_from_one, Johnson/Road/K4/FrontLater.lean).
  LAW 2: **`k4Row_rejects`**: where the row rejects there is no group at all, or there is a group
    below X.NGr that has no entry, or at whose entry rowB rejects, or frontB where g < 2. WHAT THAT
    MEANS FOR A RUN: `front_dead`: where frontB rejects, behind EVERY hearing of K4's that returns
    (at that shape of the lookup) the listing of its forms does not return · `row_dead`: where rowB
    rejects, behind every such hearing the routine wsPending does not return.
    (Contrapositives of frontB_of_return, rowB_of_return: Johnson/Road/K4/Total/PlanMember.lean,
    PlanRow.lean.) SO THE ROW REFUSES NO PUBLIC FILES AT WHICH A HEARING COULD BE FOLLOWED BY THE
    RETURN OF ITS OWN TWO RUNS (for front: see Limits).
  WHAT IT REJECTS, AS GENERAL LAWS (theorems, not tests that could fail): `k4RowAt_none`: no group
    at all: rejected · `k4RowAt_short`: a group without an entry: rejected · `k4RowAt_bendClaims`:
    WHEREVER THE ROW ACCEPTS it rejects the bend "one claim more" (by `wsPending_claims`,
    `rowB_claims`: the routine compares the number of claims) ·
    `frontB_noReads`, `k4RowAt_bendReads`: the list of the vectors' arrays emptied: rejected.
  The bends bendShort and bendLimb are for the evaluator.
Limits. AT PUBLIC PARAMETERS THAT ARE NOT publicOf's RETURN THE ROW ASKS LESS
(frontB at a group from 2 on is not asked). THE ROW's ACCEPT IS A PREMISE HERE: NO
ENTRY TEST ASKS IT; under the head it is a theorem (`k4Row_of_head`, K4RowOfHead.lean). front_dead
speaks at a heard shape fo.shape; the row asks at the layout's own y.fo: that the two are one at a
hearing is another sub-protocol's law. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE
(AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). K04_law, the law of
K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4NamedPaid
import Johnson.Road.K4.K4RowTestBends
import Johnson.Road.K4.Total.PlanMember
import Johnson.Road.K4.Total.PlanRow
import Johnson.Road.K4.PendLightBack
import Johnson.Road.K4.FrontLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Params (exc_guard exc_guard_not)
open OnBytes.Maker (WholeD)
open OnBytes.Desc.First.K4 (front hear engFl)
open OnBytes.Desc.First.K4.Total (rowB frontB planOwn planWo frontB_of_return rowB_of_return)

/-- **The row's accept, opened.** -/
theorem k4RowAt_iff {X : Verify.Public} {lin : Params.LinShape} :
    k4RowAt X lin = true ↔ 0 < X.NGr ∧ ∀ g, g < X.NGr → ∃ hp, X.G[g]? = some hp ∧
      (g < 2 → frontB false X.layers hp g X.layers.y.fo = true) ∧
      rowB X.layers g hp.NCL lin = true := by
  unfold k4RowAt
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun g hg => ?_⟩
    have t := h g (List.mem_range.2 hg)
    cases e : X.G[g]? with
    | none =>
      rw [e] at t
      cases t
    | some hp =>
      rw [e] at t
      have t' : ((decide (2 ≤ g) || frontB false X.layers hp g X.layers.y.fo) &&
          Pend.rowLightB X.layers g hp.NCL lin) = true := t
      rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Pend.rowLight_eq] at t'
      exact ⟨hp, rfl, fun h2 => t'.1.resolve_left (by omega), t'.2⟩
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun g hg => ?_⟩
    obtain ⟨hp, e, t1, t2⟩ := h g (List.mem_range.1 hg)
    rw [e]
    show ((decide (2 ≤ g) || frontB false X.layers hp g X.layers.y.fo) &&
      Pend.rowLightB X.layers g hp.NCL lin) = true
    rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Pend.rowLight_eq]
    refine ⟨?_, t2⟩
    by_cases h2 : 2 ≤ g
    · exact Or.inl h2
    · exact Or.inr (t1 (by omega))

/-- **Wherever publicOf returns the row's accept is both tests' accept at every group.** -/
theorem k4RowAt_full {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL lay = .ok X) {lin : Params.LinShape} :
    k4RowAt X lin = true ↔ 0 < X.NGr ∧ ∀ g, g < X.NGr → ∃ hp, X.G[g]? = some hp ∧
      frontB false X.layers hp g X.layers.y.fo = true ∧ rowB X.layers g hp.NCL lin = true := by
  constructor
  · intro hr
    obtain ⟨h0, hall⟩ := k4RowAt_iff.1 hr
    refine ⟨h0, fun g hg => ?_⟩
    obtain ⟨hp, e, t1, t2⟩ := hall g hg
    refine ⟨hp, e, ?_, t2⟩
    by_cases h2 : g < 2
    · exact t1 h2
    · obtain ⟨hp₁, e₁, s1, _⟩ := hall 1 (by omega)
      exact frontB_from_one_public h false _ e₁ (s1 (by omega)) g (by omega) hp e
  · rintro ⟨h0, hall⟩
    refine k4RowAt_iff.2 ⟨h0, fun g hg => ?_⟩
    obtain ⟨hp, e, t1, t2⟩ := hall g hg
    exact ⟨hp, e, fun _ => t1, t2⟩

/-- **LAW 2: what a rejection rejects.** -/
theorem k4Row_rejects {Z : ProofFile.Pub} (h : k4RowB Z = false) :
    Z.p.X.NGr = 0 ∨ ∃ g, g < Z.p.X.NGr ∧ (Z.p.X.G[g]? = none ∨ ∃ hp, Z.p.X.G[g]? = some hp ∧
      ((g < 2 ∧ frontB false Z.p.X.layers hp g Z.p.X.layers.y.fo = false) ∨
        rowB Z.p.X.layers g hp.NCL Z.first.lin = false)) := by
  by_contra hn
  have ht : k4RowAt Z.p.X Z.first.lin = true := by
    refine k4RowAt_iff.2 ⟨Nat.pos_of_ne_zero fun e0 => hn (Or.inl e0), fun g hg => ?_⟩
    cases e : Z.p.X.G[g]? with
    | none => exact absurd (Or.inr ⟨g, hg, Or.inl e⟩) hn
    | some hp =>
      cases t2 : rowB Z.p.X.layers g hp.NCL Z.first.lin with
      | false => exact absurd (Or.inr ⟨g, hg, Or.inr ⟨hp, e, Or.inr t2⟩⟩) hn
      | true =>
        refine ⟨hp, rfl, fun h2 => ?_, t2⟩
        by_contra hne
        have t1 : frontB false Z.p.X.layers hp g Z.p.X.layers.y.fo = false := by simpa using hne
        exact hn (Or.inr ⟨g, hg, Or.inr ⟨hp, e, Or.inl ⟨h2, t1⟩⟩⟩)
  have hf : k4RowAt Z.p.X Z.first.lin = false := h
  rw [ht] at hf
  cases hf

section Run
variable {P : Layer.Pub} {hp : Layer.HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
  {t u : Tape} {o : Layer.Own}

/-- Where frontB rejects: behind every hearing that returns, the listing does not return. -/
theorem front_dead {rows : Bool} (hB : frontB rows P hp g fo.shape = false)
    (h : hear engFl P hp g fo F t = some (o, G, u)) (a b : Aff) : front rows P g o a b = none := by
  cases e : front rows P g o a b with
  | none => rfl
  | some l =>
    have hr : (front rows P g o a b).isSome = true := by
      rw [e]
      rfl
    rw [frontB_of_return h hr] at hB
    cases hB

/-- Where rowB rejects: behind every hearing that returns, `wsPending` does not return. -/
theorem row_dead {n : Nat} {lin : Params.LinShape} (hB : rowB P g n lin = false)
    (h : hear engFl P hp g fo F t = some (o, G, u)) :
    (wsPending P.wsLay o.wo n lin).toOption = none := by
  cases e : (wsPending P.wsLay o.wo n lin).toOption with
  | none => rfl
  | some l =>
    have hr : (wsPending P.wsLay o.wo n lin).toOption.isSome = true := by
      rw [e]
      rfl
    rw [rowB_of_return h hr] at hB
    cases hB

end Run

/-- A general law: no group of layers at all rejects. -/
theorem k4RowAt_none {X : Verify.Public} {lin : Params.LinShape} (e : X.NGr = 0) :
    k4RowAt X lin = false := by
  cases h : k4RowAt X lin with
  | false => rfl
  | true =>
    have h0 := (k4RowAt_iff.1 h).1
    omega

/-- A general law: a group without an entry rejects. -/
theorem k4RowAt_short {X : Verify.Public} {lin : Params.LinShape} {g : ℕ} (hg : g < X.NGr)
    (e : X.G[g]? = none) : k4RowAt X lin = false := by
  cases h : k4RowAt X lin with
  | false => rfl
  | true =>
    obtain ⟨hp, e', _⟩ := (k4RowAt_iff.1 h).2 g hg
    rw [e] at e'
    cases e'

/-- The routine wsPending compares the number of claims. -/
theorem wsPending_claims {lay : WsLay} {o : WsForkOut} {n : Nat} {S : Params.LinShape}
    {p : WsPending} (h : wsPending lay o n S = .ok p) : o.recs.length = n := by
  unfold wsPending at h
  dsimp only at h
  replace h := exc_guard h
  have k := exc_guard_not h
  by_contra hne
  exact k (by simp [hne])

/-- So rowB accepts at one number of claims at most. -/
theorem rowB_claims {P : Layer.Pub} {g n : Nat} {lin : Params.LinShape}
    (h : rowB P g n lin = true) : ∃ w₀, planWo P g = some w₀ ∧ w₀.recs.length = n := by
  unfold rowB at h
  cases hw : planWo P g with
  | none =>
    rw [hw] at h
    cases h
  | some w₀ =>
    rw [hw] at h
    have h' : (wsPending P.wsLay w₀ n lin).toOption.isSome = true := h
    cases hp : wsPending P.wsLay w₀ n lin with
    | error e =>
      rw [hp] at h'
      cases h'
    | ok p => exact ⟨w₀, rfl, wsPending_claims hp⟩

/-- **A general law: wherever the row accepts, one claim more is rejected.** -/
theorem k4RowAt_bendClaims {X : Verify.Public} {lin : Params.LinShape}
    (h : k4RowAt X lin = true) : k4RowAt (bendClaims X) lin = false := by
  obtain ⟨h0, hall⟩ := k4RowAt_iff.1 h
  obtain ⟨hp, e, _, t2⟩ := hall 0 h0
  cases hb : k4RowAt (bendClaims X) lin with
  | false => rfl
  | true =>
    obtain ⟨hp', e', _, t2'⟩ := (k4RowAt_iff.1 hb).2 0 h0
    have e'' : (bendClaims X).G[0]? = some { hp with NCL := hp.NCL + 1 } := by
      show (X.G.modify 0 _)[0]? = _
      rw [Array.getElem?_modify, if_pos rfl, e]
      rfl
    obtain rfl : { hp with NCL := hp.NCL + 1 } = hp' := Option.some.inj (e''.symm.trans e')
    have t3 : rowB X.layers 0 (hp.NCL + 1) lin = true := t2'
    obtain ⟨w, hw, l1⟩ := rowB_claims t2
    obtain ⟨w', hw', l2⟩ := rowB_claims t3
    obtain rfl : w = w' := Option.some.inj (hw.symm.trans hw')
    omega

/-- A general law, at every plan: without the array of the reads the first test rejects. -/
theorem frontB_noReads (rows : Bool) (P : Layer.Pub) {hp : Layer.HPlan2} (g : ℕ)
    (sh : Forest.Shape) (e : hp.tl.ix.U = #[]) : frontB rows P hp g sh = false := by
  unfold frontB planOwn
  rw [e]
  rfl

/-- So the row rejects at the bend bendReads, wherever X has a first group. -/
theorem k4RowAt_bendReads {X : Verify.Public} {lin : Params.LinShape} (h0 : 0 < X.NGr)
    {hp : Layer.HPlan2} (e : X.G[0]? = some hp) : k4RowAt (bendReads X) lin = false := by
  cases h : k4RowAt (bendReads X) lin with
  | false => rfl
  | true =>
    obtain ⟨hp', e', t1, _⟩ := (k4RowAt_iff.1 h).2 0 h0
    have e'' : (bendReads X).G[0]? =
        some { hp with tl := { hp.tl with ix := { hp.tl.ix with U := #[] } } } := by
      show (X.G.modify 0 _)[0]? = _
      rw [Array.getElem?_modify, if_pos rfl, e]
      rfl
    obtain rfl := Option.some.inj (e''.symm.trans e')
    have t1' := t1 (by omega)
    rw [frontB_noReads false _ 0 _ rfl] at t1'
    cases t1'

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **LAW 1: THE ROW PROVES WHAT STAYS A TEST OF THE NINE.** -/
theorem k4Row_two (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (h : k4RowB Zp = true) :
    K4NamedTwo hA := by
  obtain ⟨_, kN, _, _⟩ := Meaning.scope_plans hA.scope hA.reads hA.pubOne
  have h' : k4RowAt (P5J.At.X Zp) Zp.first.lin = true := h
  have H : ∀ g, g < 12 → ∀ hp, (P5J.At.X Zp).G[g]? = some hp →
      frontB false (P5J.At.X Zp).layers hp g (P5J.At.X Zp).layers.y.fo = true ∧
        rowB (P5J.At.X Zp).layers g hp.NCL Zp.first.lin = true := by
    intro g hg hp e
    obtain ⟨hp', e', t1, t2⟩ := (k4RowAt_iff.1 h').2 g (by rw [kN]; exact hg)
    obtain rfl : hp = hp' := Option.some.inj (e.symm.trans e')
    refine ⟨?_, t2⟩
    by_cases h2 : g < 2
    · exact t1 h2
    · obtain ⟨hp₁, e₁, s1, _⟩ := (k4RowAt_iff.1 h').2 1 (by rw [kN]; omega)
      exact frontB_from_one hA e₁ (s1 (by omega)) g (by omega) hg hp e
  exact { front := fun g hg hp e => (H g hg hp e).1, row := fun g hg hp e => (H g hg hp e).2 }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4RowAt_iff
#print axioms OnBytes.Road.K4.k4RowAt_full
#print axioms OnBytes.Road.K4.k4Row_rejects
#print axioms OnBytes.Road.K4.front_dead
#print axioms OnBytes.Road.K4.row_dead
#print axioms OnBytes.Road.K4.k4RowAt_none
#print axioms OnBytes.Road.K4.k4RowAt_short
#print axioms OnBytes.Road.K4.wsPending_claims
#print axioms OnBytes.Road.K4.rowB_claims
#print axioms OnBytes.Road.K4.k4RowAt_bendClaims
#print axioms OnBytes.Road.K4.frontB_noReads
#print axioms OnBytes.Road.K4.k4RowAt_bendReads
#print axioms OnBytes.Road.K4.k4Row_two
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#check @OnBytes.Road.K4.k4RowAt_iff
#check @OnBytes.Road.K4.k4RowAt_full
#check @OnBytes.Road.K4.k4Row_rejects
#check @OnBytes.Road.K4.k4Row_two
#check @OnBytes.Road.K4.front_dead
#check @OnBytes.Road.K4.row_dead
#check @OnBytes.Road.K4.k4RowAt_none
#check @OnBytes.Road.K4.k4RowAt_short
#check @OnBytes.Road.K4.k4RowAt_bendClaims
#check @OnBytes.Road.K4.k4RowAt_bendReads
