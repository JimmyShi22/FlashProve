-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/CutKit.lean: helper lemmas on the splitting step and on the two steps that follow it.
  1. The splitting step (Rom/SpecCut.lean): an answer is split between two oracles, the first and
     the second oracle of o; `cutSpec` is the split family.
  2. The expansion from a state (Rom/StateFirst.lean): an oracle is unchanged (`plain`) or a chain
     oracle, whose long answer is replaced by a state of two hash blocks, and hash block j of
     the old answer becomes dr (state, j) for one new oracle dr; conditions: `HidFree`,
     `PlainOnly`.
  3. The step to one hash function (Rom/Family.lean), by a query encoding (`OracleCoding`); condition:
     `LocalTo`.
Most of the lemmas derive the three steps' conditions from facts over the family S before the
splitting.

  `wholeOnly_of_localTo`  An extractor that reads only entries at one-block oracles (`LocalTo`)
                          reads only entries at oracles that are not split, if no oracle with a
                          one-block answer is split.

Notation:
  `lam`: `ℕ`; `Dg lam`: `Fin lam → Bool` (Rom/NeedA.lean): a hash block
  `C2 x`: `Link lam ((cutSpec S C).Rng x)` (Rom/StateFirst.lean): how an oracle with answers in R is
    treated: `plain`, or `chain K e` with `e : R ≃ (Fin K → Dg lam) × Dg lam × Dg lam`
  in `stSpec (cutSpec S C) lam C2` (Rom/StateFirst.lean: the second family): `.inl (.inl o)`,
    `.inl (.inr o)`: the first and the second oracle of o; `.inr u`: the oracle dr
  `m`, `m'`: `OracleCoding _ lam` (Rom/Family.lean): query encodings; `m.blocks o`: `ℕ`, with
    `m.rng o : S.Rng o ≃ (Fin (m.blocks o) → Fin lam → Bool)`
  `LocalTo E m` (Rom/Family.lean): the extractor reads only entries at oracles whose answer is one
    hash block
  `single m tr` (Rom/Family.lean): the entries of a trace at oracles whose answer is one hash block
  `HidFree C2 A` (Rom/StateFirst.lean): the three algorithms do not read the last block of a chain
    answer
  `PlainOnly C2 E` (Rom/StateFirst.lean): the extractor reads only entries at unchanged oracles
  `c.FactorsBy ag` (Rom/OverOneN.lean): the program reads an answer only up to a relation ag on
    answers; `ag`: `∀ o, S.Dom o → S.Rng o → S.Rng o → Prop`
  `extSt C2 E`: `Gen.Extractor (stSpec _ lam C2) I X W IVK Pf` (Rom/StateFirst.lean)
  `plainOf C2 tr` (Rom/StateFirst.lean): the entries of a trace of the first family (here
    `cutSpec S C`) at unchanged oracles; `plainTr C2 tr`: the entries at unchanged oracles, as
    entries of the first family
  `wCut C need u o q r`: `ℕ` (Rom/SpecCut.lean): what a typed query costs over `cutSpec S C`, if a
    query there costs u
  `wCh C2 x q`: `ℕ` (Rom/StateFirst.lean): the weight of a query: 1 at a chain oracle, 0 at an
    unchanged one
-/
import Rom.CutDown

set_option autoImplicit false

namespace Rom
open ZKCP

variable {S : OSpec} (C : ∀ o, OCut (S.Rng o)) {I X W IVK Pf α : Type}

theorem single_wholeOf {lam : ℕ} (m : OracleCoding S lam)
    (h : ∀ o, m.blocks o = 1 → (C o).isWhole = true) (tr : Trace S) :
    single m (wholeOf C tr) = single m tr := by
  unfold single wholeOf
  rw [List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  by_cases h1 : m.blocks e.1 = 1
  · simp [h1, h e.1 h1]
  · simp [h1]

theorem wholeOnly_of_localTo {lam : ℕ} (m : OracleCoding S lam)
    (h : ∀ o, m.blocks o = 1 → (C o).isWhole = true)
    (E : Gen.Extractor S I X W IVK Pf) (hE : LocalTo E m) : WholeOnly C E :=
  ⟨fun v tr => by rw [hE.1 v tr, hE.1 v (wholeOf C tr), single_wholeOf C m h],
    fun v tr x π tr' => by
      rw [hE.2 v tr x π tr', hE.2 v (wholeOf C tr) x π (wholeOf C tr'),
        single_wholeOf C m h, single_wholeOf C m h]⟩

/-- The splitting step's condition from a relation ag on answers: under h (an answer as the rule
`need` shows it, `shownCut C need o q r`, is the answer r itself or is related to it by ag), an
algorithm that reads its answers up to ag (`FactorsBy ag`) meets `ReadsCut`. -/
theorem readsCut_of {need : NeedCut C} {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}
    (h : ∀ o q r, shownCut C need o q r = r ∨ ag o q r (shownCut C need o q r)) :
    ∀ c : OComp S α, c.FactorsBy ag → c.ReadsCut C need
  | .pure _, _ => trivial
  | .sample _ k, hc => fun r => readsCut_of h (k r) (hc r)
  | .query o q k, hc => ⟨fun r r' e => by
      rw [e]
      rcases h o q r with e1 | e1
      · rw [e1]
      · exact hc.1 r _ e1, fun r => readsCut_of h (k r) (hc.2 r)⟩

/-! ## For the expansion from a state, after the splitting -/

/-- What an algorithm does not read, it does not read after the splitting either: under h1 and h2,
if c reads its answers up to ag (`FactorsBy ag`), `c.cut` reads the parts up to ag'. Here h1 asks
that first parts related by ag' are equal, and h2 that if ag' relates two second parts, ag relates
the two answers that they form with any common first part. (So `HidFree` of the scheme after the
splitting comes from a fact on the scheme over S.) -/
theorem factorsBy_cut {need : NeedCut C} {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}
    {ag' : ∀ x, (cutSpec S C).Dom x → (cutSpec S C).Rng x → (cutSpec S C).Rng x → Prop}
    (h1 : ∀ (o : S.ι) (q : S.Dom o) (a a' : (C o).Front), ag' (.inl o) q a a' → a = a')
    (h2 : ∀ (o : S.ι) (q : S.Dom o) (a : (C o).Front) (b b' : (C o).Rest),
      ag' (.inr o) q b b' → ag o q ((C o).join a b) ((C o).join a b')) :
    ∀ c : OComp S α, c.FactorsBy ag → (c.cut C need).FactorsBy ag'
  | .pure _, _ => trivial
  | .sample _ k, hc => fun r => factorsBy_cut h1 h2 (k r) (hc r)
  | .query o q k, hc => by
    refine ⟨fun a a' e => by rw [h1 o q a a' e], fun a => ?_⟩
    show (if ((C o).isWhole || !need o q a) = true then (k ((C o).alone a)).cut C need
      else
        OComp.query (S := cutSpec S C) (.inr o) q fun b =>
          (k ((C o).join a b)).cut C need).FactorsBy ag'
    by_cases hs : ((C o).isWhole || !need o q a) = true
    · rw [if_pos hs]
      exact factorsBy_cut h1 h2 _ (hc.2 _)
    · rw [if_neg hs]
      exact ⟨fun b b' e => congrArg (fun z => OComp.cut C need z) (hc.1 _ _ (h2 o q a b b' e)),
        fun b => factorsBy_cut h1 h2 _ (hc.2 _)⟩

theorem OCut.back_none {R : Type} : ∀ c : OCut R, c.isWhole = false → ∀ a, c.back a = none
  | .cut _ _ _ _ _ _ _, _, _ => rfl

theorem wholeTr_plainOf {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C).Rng x))
    (h : ∀ o, (C o).isWhole = true → (C2 (.inl o)).isPlain = true) (tr : Trace (cutSpec S C)) :
    wholeTr C (plainOf C2 tr) = wholeTr C tr := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    obtain ⟨x, q, a⟩ := e
    have e1 : plainOf C2 (⟨x, q, a⟩ :: tr) =
      if (C2 x).isPlain = true then ⟨x, q, a⟩ :: plainOf C2 tr
      else plainOf C2 tr := List.filter_cons
    rw [e1]
    by_cases hp : (C2 x).isPlain = true
    · rw [if_pos hp, wholeTr_cons, wholeTr_cons, ih]
    · rw [if_neg hp, wholeTr_cons, ih]
      cases x with
      | inr o => rfl
      | inl o =>
        have hw : (C o).isWhole = false := by
          cases hh : (C o).isWhole
          · rfl
          · exact absurd (h o hh) hp
        show _ = (((C o).back a).map fun r => (⟨o, q, r⟩ : QA S)).toList ++ _
        rw [(C o).back_none hw a]
        rfl

/-- The extractor over the split family reads only entries at unchanged oracles, if the first oracle
of every oracle that is not split is unchanged. -/
theorem plainOnly_extCut {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C).Rng x))
    (h : ∀ o, (C o).isWhole = true → (C2 (.inl o)).isPlain = true)
    (E : Gen.Extractor S I X W IVK Pf) : PlainOnly C2 (extCut C E) :=
  ⟨fun v tr => by
      show E.Ei v (wholeTr C tr) = E.Ei v (wholeTr C (plainOf C2 tr)); rw [wholeTr_plainOf C C2 h],
   fun v tr x π tr' => by show E.Ew v (wholeTr C tr) x π (wholeTr C tr') = E.Ew v (wholeTr C (plainOf C2 tr)) x π (wholeTr C (plainOf C2 tr')); rw [wholeTr_plainOf C C2 h, wholeTr_plainOf C C2 h]⟩

/-! ## For the step to one hash function, after the splitting and the expansion; at the end, the
weight of the expansion step's added error terms (`wCut_zero`, `wCut_one`) -/

/-- the number of hash blocks of lam > 0 bits is determined by the number of answers -/
theorem blocks_eq_of_equiv {lam : ℕ} (hl : 0 < lam) {a b : ℕ}
    (e : (Fin a → Fin lam → Bool) ≃ (Fin b → Fin lam → Bool)) : a = b := by
  have h := Fintype.card_congr e
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at h
  have h2 : (2 ^ lam : ℕ) ^ a = (2 ^ lam) ^ b := h
  exact Nat.pow_right_injective (a := 2 ^ lam) (by
    have : 2 ^ 1 ≤ 2 ^ lam := Nat.pow_le_pow_right (by omega) hl
    omega) h2

theorem OCut.front_eq {R : Type} : ∀ c : OCut R, c.isWhole = true → c.Front = R
  | .whole, _ => rfl

theorem Link.ans_eq {lam : ℕ} {R : Type} : ∀ c : Link lam R, c.isPlain = true → c.Ans = R
  | .plain, _ => rfl

/-- Any query encoding of the family after the splitting and the expansion gives an oracle that is
not split, and whose first oracle is unchanged, as many hash blocks as any query encoding of S, if
lam > 0: both count the same answers. -/
theorem blocks_whole {lam : ℕ} (hl : 0 < lam) (C2 : ∀ x, Link lam ((cutSpec S C).Rng x))
    (m : OracleCoding S lam) (m' : OracleCoding (stSpec (cutSpec S C) lam C2) lam) (o : S.ι)
    (hw : (C o).isWhole = true) (hp : (C2 (.inl o)).isPlain = true) :
    m'.blocks (.inl (.inl o)) = m.blocks o := by
  have e1 : (stSpec (cutSpec S C) lam C2).Rng (.inl (.inl o)) = S.Rng o :=
    ((C2 (.inl o)).ans_eq hp).trans ((C o).front_eq hw)
  exact blocks_eq_of_equiv hl
    (((m'.rng (.inl (.inl o))).symm.trans (Equiv.cast e1)).trans (m.rng o))

/-- what the extractor after the splitting and the expansion reads of one entry -/
def readCS {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C).Rng x)) :
    QA (stSpec (cutSpec S C) lam C2) → List (QA S)
  | ⟨.inl (.inl o), q, a⟩ =>
    (((C2 (.inl o)).back a).bind fun a' => ((C o).back a').map fun r => (⟨o, q, r⟩ : QA S)).toList
  | ⟨.inl (.inr _), _, _⟩ => []
  | ⟨.inr _, _, _⟩ => []

theorem wholeTr_plainTr_cons {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C).Rng x))
    (e : QA (stSpec (cutSpec S C) lam C2)) (tr : Trace (stSpec (cutSpec S C) lam C2)) :
    wholeTr C (plainTr C2 (e :: tr)) = readCS C C2 e ++ wholeTr C (plainTr C2 tr) := by
  obtain ⟨x, q, a⟩ := e
  cases x with
  | inr u => rfl
  | inl y =>
    have e1 : plainTr C2 (⟨.inl y, q, a⟩ :: tr) =
        (((C2 y).back a).map fun r => (⟨y, q, r⟩ : QA (cutSpec S C))).toList ++ plainTr C2 tr := by
      show List.filterMap _ (_ :: _) = _
      rw [List.filterMap_cons]
      cases h : (C2 y).back a <;> simp only [h, Option.map_none, Option.map_some] <;> rfl
    rw [e1]
    cases h : (C2 y).back a with
    | none =>
      cases y with
      | inl o => show _ = (((C2 (.inl o)).back a).bind _).toList ++ _; rw [h]; rfl
      | inr o => rfl
    | some a' =>
      show wholeTr C (⟨y, q, a'⟩ :: plainTr C2 tr) = _
      rw [wholeTr_cons]
      cases y with
      | inl o => show _ = (((C2 (.inl o)).back a).bind _).toList ++ _; rw [h]; rfl
      | inr o => rfl

/-- an entry that is read is at the first oracle of an oracle that is not split -/
theorem mem_readCS {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C).Rng x))
    {e : QA (stSpec (cutSpec S C) lam C2)} {z : QA S} (h : z ∈ readCS C C2 e) :
    e.1 = .inl (.inl z.1) ∧ (C z.1).isWhole = true := by
  obtain ⟨x, q, a⟩ := e
  cases x with
  | inr u => exact nomatch h
  | inl y =>
    cases y with
    | inr o => exact nomatch h
    | inl o =>
      have h' : z ∈
          (((C2 (.inl o)).back a).bind fun a' =>
            ((C o).back a').map fun r => (⟨o, q, r⟩ : QA S)).toList := h
      rw [Option.mem_toList] at h'
      obtain ⟨a', -, h2⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨r, h3, rfl⟩ := Option.map_eq_some_iff.1 h2
      refine ⟨rfl, ?_⟩
      cases hw : (C o).isWhole
      · rw [(C o).back_none hw a'] at h3
        exact nomatch h3
      · rfl

theorem single_readCS {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C).Rng x)) (m : OracleCoding S lam)
    (m' : OracleCoding (stSpec (cutSpec S C) lam C2) lam)
    (hm : ∀ o, (C o).isWhole = true → m'.blocks (.inl (.inl o)) = m.blocks o)
    (tr : Trace (stSpec (cutSpec S C) lam C2)) :
    single m (wholeTr C (plainTr C2 (single m' tr))) = single m (wholeTr C (plainTr C2 tr)) := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    have e2 : single m (wholeTr C (plainTr C2 (e :: tr))) =
        single m (readCS C C2 e) ++ single m (wholeTr C (plainTr C2 tr)) := by
      rw [wholeTr_plainTr_cons]
      exact List.filter_append _ _
    rw [e2]
    by_cases hb : m'.blocks e.1 = 1
    · have e1 : single m' (e :: tr) = e :: single m' tr := by simp [single, hb]
      rw [e1, wholeTr_plainTr_cons]
      show List.filter _ (_ ++ _) = _
      rw [List.filter_append]
      exact congrArg _ ih
    · have e1 : single m' (e :: tr) = single m' tr := by simp [single, hb]
      have e3 : single m (readCS C C2 e) = [] := by
        refine List.filter_eq_nil_iff.2 fun z hz => ?_
        obtain ⟨h1, h2⟩ := mem_readCS C C2 hz
        have : m.blocks z.1 ≠ 1 := fun h => hb (by rw [h1, hm z.1 h2, h])
        simpa using this
      rw [e1, ih, e3]
      rfl

/-- If E reads only entries at one-block oracles of m, and the query encoding m' of the family after
the splitting and the expansion gives every oracle that is not split as many hash blocks as m, then
the extractor after these two steps reads only entries at one-block oracles of m'. -/
theorem localTo_extSt_extCut {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C).Rng x)) (m : OracleCoding S lam)
    (m' : OracleCoding (stSpec (cutSpec S C) lam C2) lam)
    (hm : ∀ o, (C o).isWhole = true → m'.blocks (.inl (.inl o)) = m.blocks o)
    (E : Gen.Extractor S I X W IVK Pf) (hE : LocalTo E m) :
    LocalTo (extSt C2 (extCut C E)) m' :=
  ⟨fun v tr => by
      show E.Ei v (wholeTr C (plainTr C2 tr)) = E.Ei v (wholeTr C (plainTr C2 (single m' tr)))
      rw [hE.1 v (wholeTr C (plainTr C2 tr)),
        hE.1 v (wholeTr C (plainTr C2 (single m' tr))), single_readCS C C2 m m' hm],
   fun v tr x π tr' => by
      show E.Ew v (wholeTr C (plainTr C2 tr)) x π (wholeTr C (plainTr C2 tr')) =
        E.Ew v (wholeTr C (plainTr C2 (single m' tr))) x π (wholeTr C (plainTr C2 (single m' tr')))
      rw [hE.2 v (wholeTr C (plainTr C2 tr)) x π (wholeTr C (plainTr C2 tr')),
        hE.2 v (wholeTr C (plainTr C2 (single m' tr))) x π (wholeTr C (plainTr C2 (single m' tr'))),
        single_readCS C C2 m m' hm, single_readCS C C2 m m' hm]⟩

/-- With the first oracle unchanged: a query whose second part is not queried counts 0 in the weight
of the expansion step's added error terms. -/
theorem wCut_zero (C1 : ∀ o, OCut (S.Rng o)) {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C1).Rng x))
    (need : NeedCut C1) (o : S.ι) (q : S.Dom o) (r : S.Rng o) (hp : (C2 (.inl o)).isPlain = true)
    (hs : need o q ((C1 o).front r) = false) :
    wCut C1 need (wCh C2) o q r = 0 := by
  unfold wCut wCh
  simp [hp, hs]

/-- With the first oracle unchanged and the second a chain oracle: a query to a split oracle whose
second part is queried counts 1. -/
theorem wCut_one (C1 : ∀ o, OCut (S.Rng o)) {lam : ℕ} (C2 : ∀ x, Link lam ((cutSpec S C1).Rng x))
    (need : NeedCut C1) (o : S.ι) (q : S.Dom o) (r : S.Rng o) (hp : (C2 (.inl o)).isPlain = true)
    (hc : (C2 (.inr o)).isPlain = false) (hw : (C1 o).isWhole = false)
    (hs : need o q ((C1 o).front r) = true) :
    wCut C1 need (wCh C2) o q r = 1 := by
  unfold wCut wCh
  simp [hp, hs, hc, hw]

end Rom
