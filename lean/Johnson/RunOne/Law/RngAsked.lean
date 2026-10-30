-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngAsked.lean: AT A KEY FILE's RANGES' TEST EVERY TEST WITH CODE THAT THE KIND K12's LAW TAKES AS A PREMISE IS HAD FROM THE BLOCK's OWN YES. Statements and proofs; the block is Johnson/Desc/Key/Ranges.lean's.
OBJECT. `rangesTest laid back N`, `asksOnRecord`, `asksOnPlan` (Johnson/Desc/Key/Ranges.lean): their decision and their test on the plan, taken apart clause by clause.
USER. Johnson/RunOne/Law/RngHolds.lean, K12Grows.lean, and through them every law of ours on the ranges' test.
LETTERS. The state, the two halves, the type of claims and N are free. Premises: the block's yes, the asking's return, or the yes of the test on the plan.

What is said.
  `bindE_ok`, `mapE_ok`, `needD_ok`: what a returning step says.
  `asksRecord_ok`: where the asking returns: the group, its layout and a first stage are there, and the five tests say yes. `asksRecord_mask`: and the record names the message that holds the first fold's mask.
  `asksPlan_ok`: the test on the plan, clause by clause.
  `four_of_ok`: the four numbers as equations.
  `gpAll_row`, `gpOk_row`, `labelsOk_row`: the two tests on the record behind the batching read of the batched row only whether it has a kept form.
  `decide_ok`: WHERE THE BLOCK's decide RETURNS: enter returned a record t0; the asking returned; the variant's decide returned tE at t0; leave returned.
  `planOk_ok`: WHERE THE BLOCK's TEST ON THE PLAN SAYS YES: the variant's does; early = true; answers = 1; cutOk; spendOk.
  `asked_at_bat`: AT THE ROW THAT THE KIND's BATCHING RETURNS: where the asking has returned at t0 and `bat t0.st t0.g e r` returns (row, L, S') with no kept form: pubOk at the record's codes; combineAt at S', at L and the rows in their fixed order;
    the four equations; gpOk and labelsOk AT THE RECORD BEHIND THE BATCHING AS THE LAW NAMES IT ({ t0 with st := S', pass := .claim row L }).
`trial_asks_bites`, `trial_asks_rows`: the asking does not return where pubOk says no, nor where a row that the batching would take lies off the group's tables: THESE ARE `asksRecord_ok` READ BACKWARDS: they show no record at which a test says no: runs do (the
sheets' controls). (Of a block that says no to all: Limits.)
Limits. That the tests say yes anywhere is a run's word (they have, at both stored key files). "No kept form" is a premise of `asked_at_bat`: the variant's own guard behind its batching asks it; that lemma is not this file's. The tests' laws (what each yes
gives) are not this file's. THE READING (that the view is the written transcript's) IS NO TEST AND IS NOT ASKED: it stays owed. A block that says no to all meets every statement here: they are of the form "where it returns". Nothing on soundness.

-/
import Johnson.Desc.Key.Ranges
import Johnson.RunOne.Law.RngBat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngAsked
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.Key
open VerifiableInference.Desc (Block need)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.First.Close (bat)

/-! ## 1 What a returning step says -/

theorem bindE_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapE_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem needD_ok {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-! ## 2 The asking -/

/-- **Where the asking returns.** -/
theorem asksRecord_ok {p : P12} {t : T12} {u : Unit} (h : asksOnRecord p t = .ok u) :
    ∃ G L a rest, t.st.groups[t.g]? = some G ∧ t.st.layout t.g = some L ∧ p.nums.stages = a :: rest ∧
      H2K.Pub.pubOk p t.st.codes = true ∧
      Means.combineAt (begun t.st t.g G) t.g ⟨L, runRows t.st G⟩ = true ∧ layoutIsStage a L = true ∧
      H2K.First.gpOk p (behindBatching t G L) = true ∧ H2K.First.labelsOk p (behindBatching t G L) = true := by
  unfold asksOnRecord at h
  split at h
  · rename_i G L a rest hG hL hs
    obtain ⟨_, _, h⟩ := RngBat.bind_ok h
    obtain ⟨_, h1, k1⟩ := RngBat.bind_ok h
    obtain ⟨_, h2, k2⟩ := RngBat.bind_ok k1
    obtain ⟨_, h3, k3⟩ := RngBat.bind_ok k2
    obtain ⟨_, h4, k4⟩ := RngBat.bind_ok k3
    exact ⟨G, L, a, rest, hG, hL, hs, needD_ok h1, needD_ok h2, needD_ok h3, needD_ok h4, needD_ok k4⟩
  · cases h

/-- Where the asking returns, the record names the message that holds the first fold's mask. -/
theorem asksRecord_mask {p : P12} {t : T12} {u : Unit} (h : asksOnRecord p t = .ok u) :
    ∃ id, t.mask = some id := by
  unfold asksOnRecord at h
  split at h
  · obtain ⟨_, h0, _⟩ := RngBat.bind_ok h
    exact Option.isSome_iff_exists.1 (needD_ok h0)
  · cases h

theorem asksPlan_ok {p : P12} (h : asksOnPlan p = true) :
    p.early = true ∧ p.answers = 1 ∧ H2K.First.cutOk p = true ∧ H2K.Pub.spendOk p = true := by
  unfold asksOnPlan at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem four_of_ok {a : Fmt.M1.Stage} {L : GroupLayout} (h : layoutIsStage a L = true) :
    L.k = a.h + (a.k - a.h) ∧ L.h = a.h ∧ 2 ^ L.logEll = a.C.l ∧ 2 ^ L.logEllZk = a.Z.l := by
  unfold layoutIsStage at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ## 3 The two tests behind the batching read of the row only whether it has a kept form -/

theorem gpAll_row (p : P12) (t : T12) (row row' : GroupRow) (L : GroupLayout)
    (h : row.kept.isEmpty = row'.kept.isEmpty) :
    H2K.First.gpAll p { t with pass := .claim row L } = H2K.First.gpAll p { t with pass := .claim row' L } := by
  unfold H2K.First.gpAll
  cases p.nums.stages with
  | nil => rfl
  | cons a rest =>
    show (match H2K.First.gpOf p { t with pass := .claim row L } a L with
      | some D => H2K.First.gpL p a row D
      | none => _) = (match H2K.First.gpOf p { t with pass := .claim row' L } a L with
      | some D => H2K.First.gpL p a row' D
      | none => _)
    have e : H2K.First.gpOf p { t with pass := .claim row L } a L =
        H2K.First.gpOf p { t with pass := .claim row' L } a L := rfl
    rw [e]
    cases H2K.First.gpOf p { t with pass := .claim row' L } a L with
    | none => rfl
    | some D =>
      show H2K.First.gpL p a row D = H2K.First.gpL p a row' D
      unfold H2K.First.gpL
      rw [h]

theorem gpOk_row (p : P12) (t : T12) (row row' : GroupRow) (L : GroupLayout)
    (h : row.kept.isEmpty = row'.kept.isEmpty) :
    H2K.First.gpOk p { t with pass := .claim row L } = H2K.First.gpOk p { t with pass := .claim row' L } := by
  unfold H2K.First.gpOk
  rw [gpAll_row p t row row' L h]

theorem labelsOk_row (p : P12) (t : T12) (row row' : GroupRow) (L : GroupLayout) :
    H2K.First.labelsOk p { t with pass := .claim row L } = H2K.First.labelsOk p { t with pass := .claim row' L } := by
  unfold H2K.First.labelsOk H2K.First.labelsL
  cases p.nums.stages with
  | nil => rfl
  | cons a rest => rfl

/-! ## 4 The block's yes -/

section
variable {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ} {N : H2U.PlaceNums}

/-- **Where the block's decide returns.** -/
theorem decide_ok {s s' : σ} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (rangesTest (Cl := Cl) laid back N).decide s rs gs = .ok s') :
    ∃ t0 tE, rangesRecord laid s = .ok t0 ∧ asksOnRecord (rangesParams N) t0 = .ok () ∧
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl).decide t0 rs gs = .ok tE ∧ back s tE = .ok s' := by
  have h' : (enterAndAsk laid (rangesParams N) s).bind (fun t =>
      ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl).decide t rs gs).bind (back s)) = .ok s' := h
  obtain ⟨t0, h1, h2⟩ := bindE_ok h'
  obtain ⟨tE, h3, h4⟩ := bindE_ok h2
  unfold enterAndAsk at h1
  obtain ⟨t1, h5, h6⟩ := bindE_ok h1
  obtain ⟨u, h7, h8⟩ := mapE_ok h6
  subst h8
  exact ⟨t1, tE, h5, h7, h3, h4⟩

/-- **Where the block's test on the plan says yes.** -/
theorem planOk_ok (h : (rangesTest (Cl := Cl) laid back N).planOk = true) :
    (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl).planOk = true ∧ (rangesParams N).early = true ∧
      (rangesParams N).answers = 1 ∧ H2K.First.cutOk (rangesParams N) = true ∧ H2K.Pub.spendOk (rangesParams N) = true := by
  have h' : (((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl).planOk &&
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl).claims.isEmpty &&
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl).after.isEmpty) && asksOnPlan (rangesParams N)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact ⟨h'.1.1.1, asksPlan_ok h'.2⟩

end

/-- **AT THE ROW THAT THE KIND's BATCHING RETURNS.** -/
theorem asked_at_bat {p : P12} {t0 : T12} (ha : asksOnRecord p t0 = .ok ()) {e : Fmt.Entry} {r : Fmt.RoundView}
    {row : GroupRow} {L : GroupLayout} {S' : Statement} (hb : bat t0.st t0.g e r = .ok (row, L, S'))
    (h0 : row.kept = #[]) :
    ∃ G a rest, t0.st.groups[t0.g]? = some G ∧ p.nums.stages = a :: rest ∧ S' = begun t0.st t0.g G ∧
      H2K.Pub.pubOk p t0.st.codes = true ∧ Means.combineAt S' t0.g ⟨L, runRows t0.st G⟩ = true ∧
      (L.k = a.h + (a.k - a.h) ∧ L.h = a.h ∧ 2 ^ L.logEll = a.C.l ∧ 2 ^ L.logEllZk = a.Z.l) ∧
      H2K.First.gpOk p { t0 with st := S', pass := .claim row L } = true ∧
      H2K.First.labelsOk p { t0 with st := S', pass := .claim row L } = true := by
  obtain ⟨G, L', a, rest, hG, hL, hs, a1, a2, a3, a4, a5⟩ := asksRecord_ok ha
  obtain ⟨G', t, hG', hL', rfl, _, _, _⟩ := RngBat.bat_says hb
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  obtain rfl : L = L' := Option.some.inj (hL'.symm.trans hL)
  refine ⟨G', a, rest, hG, hs, rfl, a1, a2, four_of_ok a3, ?_, ?_⟩
  · have e1 : row.kept.isEmpty = ({} : GroupRow).kept.isEmpty := by rw [h0]
    exact (gpOk_row p { t0 with st := begun t0.st t0.g G' } row {} L e1).trans a4
  · exact (labelsOk_row p { t0 with st := begun t0.st t0.g G' } row {} L).trans a5

/-! ## 5 Trials -/

/-- `asksRecord_ok` read backwards: the asking does not return where pubOk says no. -/
theorem trial_asks_bites {p : P12} {t : T12} (h : H2K.Pub.pubOk p t.st.codes = false) (u : Unit) :
    asksOnRecord p t ≠ .ok u := fun hk => by
  obtain ⟨_, _, _, _, _, _, _, a1, _⟩ := asksRecord_ok hk
  rw [h] at a1
  cases a1

/-- Nor where a row that the batching would take lies off the group's tables. -/
theorem trial_asks_rows {p : P12} {t : T12} {G : Group} {L : GroupLayout} (hG : t.st.groups[t.g]? = some G)
    (hL : t.st.layout t.g = some L)
    (h : Means.combineAt (begun t.st t.g G) t.g ⟨L, runRows t.st G⟩ = false) (u : Unit) :
    asksOnRecord p t ≠ .ok u := fun hk => by
  obtain ⟨G', L', _, _, hG', hL', _, _, a2, _⟩ := asksRecord_ok hk
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  obtain rfl : L' = L := Option.some.inj (hL'.symm.trans hL)
  rw [h] at a2
  cases a2

end Johnson.RunOne.Law.RngAsked

#print axioms Johnson.RunOne.Law.RngAsked.asksRecord_ok
#print axioms Johnson.RunOne.Law.RngAsked.asksRecord_mask
#print axioms Johnson.RunOne.Law.RngAsked.gpOk_row
#print axioms Johnson.RunOne.Law.RngAsked.decide_ok
#print axioms Johnson.RunOne.Law.RngAsked.planOk_ok
#print axioms Johnson.RunOne.Law.RngAsked.asked_at_bat
#print axioms Johnson.RunOne.Law.RngAsked.trial_asks_bites
#print axioms Johnson.RunOne.Law.RngAsked.trial_asks_rows
