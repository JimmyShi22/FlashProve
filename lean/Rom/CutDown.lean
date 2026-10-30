-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/CutDown.lean: the splitting step (an answer split between two oracles: `OCut`, `cutSpec`,
Rom/SpecCut.lean): a family of oracle functions and its split form (`cutFam`) are the same thing,
and uniform corresponds to uniform. Structure as in Rom/Prefix.lean and Rom/ExitDown.lean. A whole
oracle is one that is not split; its second oracle is trivial.

  `joinFam_cutFam`, `cutFam_joinFam`
                                 `joinFam` is inverse to `cutFam`.
  `runEager_downCut`, `queryBound_downCut`
                                 The run and the query bound of `downCut` (an algorithm over the
                                 split family as an algorithm over the family); `upTrCut`,
                                 `withTrace_downCut`, `wholeOf_upTrCut`: the same with traces.
-/
import Rom.CutRun
import Rom.Prefix
import Rom.ExitDown

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Rom

namespace OCut
variable {R : Type}

theorem rest_join : ∀ (c : OCut R) (a : c.Front) (b : c.Rest), c.rest (c.join a b) = b
  | .whole, _, _ => rfl
  | .cut _ _ _ _ _ e _, a, b => congrArg Prod.snd (e.apply_symm_apply (a, b))

/-- an answer is the pair of its parts -/
def equiv (c : OCut R) : R ≃ c.Front × c.Rest where
  toFun r := (c.front r, c.rest r)
  invFun x := c.join x.1 x.2
  left_inv r := c.join_parts r
  right_inv x := Prod.ext (c.front_join x.1 x.2) (c.rest_join x.1 x.2)

end OCut

variable {S : OSpec} (C : ∀ o, OCut (S.Rng o)) {α β : Type}

/-- the family whose answers are joined from the parts -/
def joinFam (g : Fam (cutSpec S C)) : Fam S := fun o q => (C o).join (g (.inl o) q) (g (.inr o) q)

theorem joinFam_cutFam (F : Fam S) : joinFam C (cutFam C F) = F := by
  funext o q
  exact (C o).join_parts (F o q)

theorem cutFam_joinFam (g : Fam (cutSpec S C)) : cutFam C (joinFam C g) = g := by
  funext x q
  cases x with
  | inl o => exact (C o).front_join _ _
  | inr o => exact (C o).rest_join _ _

/-- the two oracles for a query -/
def nameOf (k : Σ _ : (Σ o, S.Dom o), Bool) : Σ x : (cutSpec S C).ι, (cutSpec S C).Dom x :=
  match k.2 with
  | false => ⟨.inl k.1.1, k.1.2⟩
  | true => ⟨.inr k.1.1, k.1.2⟩

theorem nameOf_injective : Function.Injective (nameOf C) := by
  rintro ⟨⟨o, q⟩, b⟩ ⟨⟨o', q'⟩, b'⟩ h
  cases b <;> cases b' <;> simp only [nameOf, Sigma.mk.injEq, reduceCtorEq, false_and] at h
  · obtain ⟨h1, h⟩ := h
    obtain rfl := Sum.inl.inj h1
    obtain rfl := eq_of_heq h
    rfl
  · obtain ⟨h1, h⟩ := h
    obtain rfl := Sum.inr.inj h1
    obtain rfl := eq_of_heq h
    rfl

/-- the two parts at a query, joined -/
def joinAt (p : Σ o, S.Dom o) (x : (b : Bool) → (cutSpec S C).Rng (nameOf C ⟨p, b⟩).1) :
    S.Rng p.1 :=
  (C p.1).join (x false) (x true)

theorem map_joinAt (p : Σ o, S.Dom o) :
    (Measure.infinitePi fun b : Bool => unifM (cutSpec S C) (nameOf C ⟨p, b⟩).1).map (joinAt C p) =
      unifM S p.1 := by
  rw [Measure.infinitePi_eq_pi]
  refine Measure.ext_of_singleton fun r => ?_
  have hpre : joinAt C p ⁻¹' {r} =
      {fun b => match b with | false => (C p.1).front r | true => (C p.1).rest r} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext b
      cases b
      · exact (congrArg (C p.1).front h ▸
          ((C p.1).front_join (x false) (x true)).symm : x false = (C p.1).front r)
      · exact (congrArg (C p.1).rest h ▸
          ((C p.1).rest_join (x false) (x true)).symm : x true = (C p.1).rest r)
    · rintro rfl
      exact (C p.1).join_parts r
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton r), hpre,
    Measure.pi_singleton, Fintype.prod_bool]
  unfold unifM
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply,
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_congr (C p.1).equiv,
    Fintype.card_prod, Nat.cast_mul, mul_comm]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))).symm

theorem measurable_joinFam : Measurable (joinFam C) := by
  refine measurable_pi_iff.2 fun o => measurable_pi_iff.2 fun q => ?_
  have h1 : Measurable fun g : Fam (cutSpec S C) => g (.inl o) q :=
    (measurable_pi_apply (q : (cutSpec S C).Dom (.inl o))).comp
      (measurable_pi_apply (Sum.inl o : (cutSpec S C).ι))
  have h2 : Measurable fun g : Fam (cutSpec S C) => g (.inr o) q :=
    (measurable_pi_apply (q : (cutSpec S C).Dom (.inr o))).comp
      (measurable_pi_apply (Sum.inr o : (cutSpec S C).ι))
  have h3 : Measurable
      fun x : (cutSpec S C).Rng (.inl o) × (cutSpec S C).Rng (.inr o) => (C o).join x.1 x.2 :=
    measurable_of_finite _
  exact h3.comp (h1.prodMk h2)

/-- Joining uniform functions over the split family gives a uniform family. -/
theorem U_map_joinFam : (U (cutSpec S C)).map (joinFam C) = U S := by
  let r0 := (MeasurableEquiv.piCurry
    fun (x : (cutSpec S C).ι) (_ : (cutSpec S C).Dom x) => (cutSpec S C).Rng x).symm
  let r1 : Flat (cutSpec S C) →
      ((k : Σ _ : (Σ o, S.Dom o), Bool) → (cutSpec S C).Rng (nameOf C k).1) :=
    fun f k => f (nameOf C k)
  let r2 := MeasurableEquiv.piCurry fun (p : Σ o, S.Dom o) (b : Bool) =>
    (cutSpec S C).Rng (nameOf C ⟨p, b⟩).1
  let r3 : ((p : Σ o, S.Dom o) → (b : Bool) → (cutSpec S C).Rng (nameOf C ⟨p, b⟩).1) → Flat S :=
    fun x p => joinAt C p (x p)
  let r4 := MeasurableEquiv.piCurry fun (o : S.ι) (_ : S.Dom o) => S.Rng o
  have hr1 : Measurable r1 := measurable_pi_iff.2 fun k => measurable_pi_apply (nameOf C k)
  have hr3 : Measurable r3 :=
    measurable_pi_iff.2 fun p => (measurable_of_finite (joinAt C p)).comp (measurable_pi_apply p)
  have h0 : (U (cutSpec S C)).map r0 =
      Measure.infinitePi fun p : (Σ x : (cutSpec S C).ι, (cutSpec S C).Dom x) =>
        unifM (cutSpec S C) p.1 := by
    rw [U_eq_map_curry, Measure.map_map r0.measurable (MeasurableEquiv.measurable _)]
    simp only [r0, MeasurableEquiv.symm_comp_self, Measure.map_id]
  have h1 : (Measure.infinitePi fun p : (Σ x : (cutSpec S C).ι, (cutSpec S C).Dom x) =>
        unifM (cutSpec S C) p.1).map r1 =
      Measure.infinitePi fun k => unifM (cutSpec S C) (nameOf C k).1 :=
    infinitePi_map_reindex (nameOf C) (nameOf_injective C) fun p => unifM (cutSpec S C) p.1
  have h2 : (Measure.infinitePi fun k : (Σ _ : (Σ o, S.Dom o), Bool) =>
        unifM (cutSpec S C) (nameOf C k).1).map r2 =
      Measure.infinitePi fun p : (Σ o, S.Dom o) =>
        Measure.infinitePi fun b : Bool => unifM (cutSpec S C) (nameOf C ⟨p, b⟩).1 :=
    Measure.infinitePi_map_piCurry (X := fun (p : Σ o, S.Dom o) (b : Bool) =>
          (cutSpec S C).Rng (nameOf C ⟨p, b⟩).1)
      (fun p b => unifM (cutSpec S C) (nameOf C ⟨p, b⟩).1)
  have h3 : (Measure.infinitePi fun p : (Σ o, S.Dom o) =>
        Measure.infinitePi fun b : Bool => unifM (cutSpec S C) (nameOf C ⟨p, b⟩).1).map r3 =
      Measure.infinitePi fun p : (Σ o, S.Dom o) => unifM S p.1 := by
    have h := Measure.infinitePi_map_pi
      (μ := fun p : (Σ o, S.Dom o) =>
          Measure.infinitePi fun b : Bool => unifM (cutSpec S C) (nameOf C ⟨p, b⟩).1)
      (f := fun p => joinAt C p) (fun p => measurable_of_finite _)
    simpa only [map_joinAt] using h
  calc (U (cutSpec S C)).map (joinFam C)
      = (((((U (cutSpec S C)).map r0).map r1).map r2).map r3).map r4 := by
        rw [Measure.map_map hr1 r0.measurable,
          Measure.map_map r2.measurable (hr1.comp r0.measurable),
          Measure.map_map hr3 (r2.measurable.comp (hr1.comp r0.measurable)),
          Measure.map_map r4.measurable (hr3.comp (r2.measurable.comp (hr1.comp r0.measurable)))]
        rfl
    _ = U S := by rw [h0, h1, h2, h3, ← U_eq_map_curry]

/-- Under hφ: integrals over the split families are integrals over the families. -/
theorem lintegral_cutFam (φ : Fam (cutSpec S C) → ℝ≥0∞)
    (hφ : Measurable fun F : Fam S => φ (cutFam C F)) :
    ∫⁻ g, φ g ∂(U (cutSpec S C)) = ∫⁻ F, φ (cutFam C F) ∂(U S) := by
  rw [← U_map_joinFam C, lintegral_map hφ (measurable_joinFam C)]
  simp only [cutFam_joinFam]

/-! ### An algorithm over the split family is an algorithm over the family -/

namespace OCut
variable {R : Type}

/-- the one answer of the trivial oracle of a whole oracle; none at a split one -/
def idle : (c : OCut R) → Option c.Rest
  | .whole => some ()
  | .cut _ _ _ _ _ _ _ => none

theorem rest_of_idle : ∀ (c : OCut R) (b : c.Rest), c.idle = some b → ∀ r, c.rest r = b
  | .whole, _, _, _ => rfl

theorem idle_isSome : ∀ c : OCut R, c.idle.isSome = c.isWhole
  | .whole => rfl
  | .cut _ _ _ _ _ _ _ => rfl

theorem back_front : ∀ (c : OCut R) (r : R), c.back (c.front r) = if c.isWhole then some r else none
  | .whole, _ => rfl
  | .cut _ _ _ _ _ _ _, _ => rfl

end OCut

/-- One query for a part, over the family: one query for the whole answer, of which the part is
kept. The trivial oracle of a whole oracle is answered without a query: else the trace over the
family would hold an entry at a whole oracle that the trace over the split family does not show. -/
def askPart :
    (x : (cutSpec S C).ι) → (cutSpec S C).Dom x → ((cutSpec S C).Rng x → OComp S β) → OComp S β
  | .inl o, q, K => .query o q fun r => K ((C o).front r)
  | .inr o, q, K =>
      match (C o).idle with
      | some b => K b
      | none => .query o q fun r => K ((C o).rest r)

/-- The same algorithm over the family. -/
def downCut : OComp (cutSpec S C) α → OComp S α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => downCut (k r)
  | .query x q k => askPart C x q fun r => downCut (k r)

/-- the entry, if any, that a query for a part adds to the trace over the family F -/
def upE (F : Fam S) : (x : (cutSpec S C).ι) → (cutSpec S C).Dom x → List (QA S)
  | .inl o, q => [⟨o, q, F o q⟩]
  | .inr o, q => if (C o).isWhole then [] else [⟨o, q, F o q⟩]

theorem askPart_idle {o : S.ι} {b : (C o).Rest} (hi : (C o).idle = some b)
    (q : S.Dom o) (K : (C o).Rest → OComp S β) :
    askPart C (.inr o) q K = K b := by
  show (match (C o).idle with
    | some b => K b
    | none => OComp.query o q fun r => K ((C o).rest r)) = _
  rw [hi]

theorem askPart_rest {o : S.ι} (hi : (C o).idle = none) (q : S.Dom o) (K : (C o).Rest → OComp S β) :
    askPart C (.inr o) q K = OComp.query o q fun r => K ((C o).rest r) := by
  show (match (C o).idle with
    | some b => K b
    | none => OComp.query o q fun r => K ((C o).rest r)) = _
  rw [hi]

theorem upE_idle {o : S.ι} {b : (C o).Rest} (hi : (C o).idle = some b) (F : Fam S) (q : S.Dom o) :
    upE C F (.inr o) q = [] := by
  have hw := (C o).idle_isSome
  rw [hi] at hw
  show (if (C o).isWhole then [] else _) = _
  rw [← hw]
  rfl

theorem upE_rest {o : S.ι} (hi : (C o).idle = none) (F : Fam S) (q : S.Dom o) :
    upE C F (.inr o) q = [⟨o, q, F o q⟩] := by
  have hw := (C o).idle_isSome
  rw [hi] at hw
  show (if (C o).isWhole then _ else _) = _
  rw [← hw]
  rfl

theorem runEager_askPart (F : Fam S) (x : (cutSpec S C).ι)
    (q : (cutSpec S C).Dom x) (K : (cutSpec S C).Rng x → OComp S β) :
    (askPart C x q K).runEager F = (K (cutFam C F x q)).runEager F := by
  cases x with
  | inl o => rfl
  | inr o =>
    cases hi : (C o).idle with
    | some b =>
      rw [askPart_idle C hi]
      exact congrArg (fun z => (K z).runEager F) ((C o).rest_of_idle b hi (F o q)).symm
    | none =>
      rw [askPart_rest C hi]
      rfl

theorem withTrace_askPart (F : Fam S) (x : (cutSpec S C).ι)
    (q : (cutSpec S C).Dom x) (K : (cutSpec S C).Rng x → OComp S β) :
    (askPart C x q K).withTrace.runEager F =
      ((K (cutFam C F x q)).withTrace.runEager F).map fun out => (out.1, upE C F x q ++ out.2) := by
  cases x with
  | inl o =>
    show (((K ((C o).front (F o q))).withTrace.bind fun out =>
        OComp.pure (out.1, (⟨o, q, F o q⟩ : QA S) :: out.2)).runEager F) = _
    rw [OComp.runEager_bind]
    rfl
  | inr o =>
    cases hi : (C o).idle with
    | some b =>
      rw [askPart_idle C hi, upE_idle C hi]
      show (K b).withTrace.runEager F =
        ((K ((C o).rest (F o q))).withTrace.runEager F).map fun out => (out.1, [] ++ out.2)
      rw [(C o).rest_of_idle b hi (F o q)]
      exact (PMF.map_id _).symm
    | none =>
      rw [askPart_rest C hi, upE_rest C hi]
      show (((K ((C o).rest (F o q))).withTrace.bind fun out =>
          OComp.pure (out.1, (⟨o, q, F o q⟩ : QA S) :: out.2)).runEager F) = _
      rw [OComp.runEager_bind]
      rfl

theorem queryBound_askPart (x : (cutSpec S C).ι) (q : (cutSpec S C).Dom x)
    (K : (cutSpec S C).Rng x → OComp S β) (t : ℕ) (h : ∀ r, (K r).QueryBound t) :
    (askPart C x q K).QueryBound (t + 1) := by
  cases x with
  | inl o => exact fun r => h _
  | inr o =>
    cases hi : (C o).idle with
    | some b =>
      rw [askPart_idle C hi]
      exact (h b).mono (Nat.le_succ t)
    | none =>
      rw [askPart_rest C hi]
      exact fun r => h _

theorem runEager_downCut (F : Fam S) (c : OComp (cutSpec S C) α) :
    (downCut C c).runEager F = c.runEager (cutFam C F) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [downCut, OComp.runEager, ih]
  | query x q k ih => exact (runEager_askPart C F x q _).trans (ih _)

theorem queryBound_downCut (c : OComp (cutSpec S C) α) :
    ∀ t, c.QueryBound t → (downCut C c).QueryBound t := by
  induction c with
  | pure a => intro t _; trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query x q k ih =>
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t => exact queryBound_askPart C x q _ t fun r => ih r t (h r)

/-! ### Traces -/

/-- The trace over the family that belongs to a trace over the split family, when the family is F:
each entry is the whole answer; a query to a trivial oracle adds none. -/
def upTrCut (F : Fam S) : Trace (cutSpec S C) → Trace S
  | [] => []
  | e :: tr => upE C F e.1 e.2.1 ++ upTrCut F tr

theorem withTrace_downCut (F : Fam S) (c : OComp (cutSpec S C) α) :
    (downCut C c).withTrace.runEager F =
      (c.withTrace.runEager (cutFam C F)).map fun out => (out.1, upTrCut C F out.2) := by
  induction c with
  | pure a =>
    show PMF.pure (a, ([] : Trace S)) = (PMF.pure (a, ([] : Trace (cutSpec S C)))).map _
    rw [PMF.pure_map]
    rfl
  | sample n k ih => simp only [downCut, OComp.withTrace, OComp.runEager, ih, PMF.map_bind]
  | query x q k ih =>
    show (askPart C x q fun r => downCut C (k r)).withTrace.runEager F =
      (((k (cutFam C F x q)).withTrace.bind fun out =>
          OComp.pure (out.1, (⟨x, q, cutFam C F x q⟩ : QA (cutSpec S C)) :: out.2)).runEager
        (cutFam C F)).map _
    rw [withTrace_askPart, ih, OComp.runEager_bind, PMF.map_comp, PMF.map_bind]
    simp only [OComp.runEager, PMF.pure_map]
    rfl

/-- `wholeTr` of e :: tr: the entry at a whole oracle that e shows, if any, then `wholeTr` of tr -/
theorem wholeTr_cons (e : QA (cutSpec S C)) (tr : Trace (cutSpec S C)) :
    wholeTr C (e :: tr) = (match e with
      | ⟨.inl o, q, a⟩ => (((C o).back a).map fun r => (⟨o, q, r⟩ : QA S)).toList
      | ⟨.inr _, _, _⟩ => []) ++ wholeTr C tr := by
  obtain ⟨x, q, a⟩ := e
  cases x with
  | inl o =>
    show List.filterMap _ (_ :: _) = _
    rw [List.filterMap_cons]
    cases h : (C o).back a <;> simp only [h, Option.map_none, Option.map_some] <;> rfl
  | inr o => rfl

/-- On a trace with the true answers, the entries at whole oracles over the family are those read
off the trace over the split family. -/
theorem wholeOf_upTrCut (F : Fam S) (tr : Trace (cutSpec S C)) :
    wholeOf C (upTrCut C F tr) = wholeTr C (retr (cutFam C F) tr) := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    obtain ⟨x, q, r⟩ := e
    have e1 : retr (cutFam C F) (⟨x, q, r⟩ :: tr) =
        ⟨x, q, cutFam C F x q⟩ :: retr (cutFam C F) tr := rfl
    have e2 : wholeOf C (upTrCut C F (⟨x, q, r⟩ :: tr)) =
        wholeOf C (upE C F x q) ++ wholeOf C (upTrCut C F tr) :=
      List.filter_append _ _
    rw [e1, e2, wholeTr_cons, ih]
    congr 1
    cases x with
    | inl o =>
      show List.filter _ [_] =
        (((C o).back ((C o).front (F o q))).map fun r => (⟨o, q, r⟩ : QA S)).toList
      rw [OCut.back_front, List.filter_cons]
      cases (C o).isWhole <;> rfl
    | inr o =>
      show List.filter _ (if (C o).isWhole then [] else [_]) = []
      cases hw : (C o).isWhole
      · show List.filter _ [_] = []
        rw [List.filter_cons]
        show (if (C o).isWhole = true then _ else _) = _
        rw [hw]
        rfl
      · rfl

end Rom
