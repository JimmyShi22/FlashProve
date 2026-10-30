-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/OwnRecordKept.lean: "the step leaves own as it was": one sentence,
said of the steps on the chain's shape that stand between the layers' own rounds and the rows
"front" and "back" of the link's batching: where the step returns, the shape after has the component
own of the shape before. General in every parameter (the link, the plan, the group, the numbers): no
link is named. Nothing is evaluated.

Why. BackRunCover.lean and FrontRunCover.lean have a premise on that component (it comes of a
hearing). The step of the layers' own rounds sets it; these laws carry it to the rows.

  StepKeepsOwn, OptionStepKeepsOwn, RowRunKeepsOwn, WholeStepKeepsOwn   the sentence, at the four
                          types of step: on the chain's shape with an error message; in Option; a
                          row's run (its claims beside); on the whole shape.
  stepKeepsOwn_ofOption, wholeStepKeepsOwn_ofStep, wholeStepKeepsOwn_ofOption   from one type to the
                          next.
  commitStepG_keepsOwn, commitG_keepsOwn, layersG_keepsOwn, eqGO_keepsOwn   the pieces.
  **readsGS_keepsOwn, drawStep_keepsOwn, commitGS_keepsOwn, digitsG_keepsOwn**   the four members
                          after the layers' own rounds.
  **drawG_keepsOwn**      the batching's draw.
  **objectsG_keepsOwn, guestsG_keepsOwn, k4RunG_keepsOwn, equationsRunCovered_keepsOwn**   the rows'
                          runs (k4RunG at every listing).
  readsA_keepsOwn, digitsA_keepsOwn   the two members that also apply sendForms to the second
                          component of the whole shape.

Limits. From a return alone. Nothing on any other component. That a step returns is not said.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.FrontRunCover
import Johnson.AtFull.Shape.Lines.Layers.ReadsEquationsCover
import Johnson.AtFull.Shape.TabLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc.First.Shape

/-- Where the step returns, own is as it was. -/
def StepKeepsOwn (g : ChainSh → Except String ChainSh) : Prop := ∀ a b, g a = .ok b → b.own = a.own

/-- The sentence for a step in Option. -/
def OptionStepKeepsOwn (g : ChainSh → Option ChainSh) : Prop := ∀ a b, g a = some b → b.own = a.own

/-- The sentence for a row's run, its claims beside. -/
def RowRunKeepsOwn (g : Nat → ChainSh → Except String (List ClaimSh × ChainSh)) : Prop :=
  ∀ n a y, g n a = .ok y → y.2.own = a.own

/-- The sentence for a step on the whole shape. -/
def WholeStepKeepsOwn (g : ShA → Except String ShA) : Prop := ∀ x y, g x = .ok y → y.1.own = x.1.own

/-- From a step in Option to the same step with an error message. -/
theorem stepKeepsOwn_ofOption {g : ChainSh → Option ChainSh} (h : OptionStepKeepsOwn g) :
    StepKeepsOwn (optE g) := by
  intro a b e
  unfold optE at e
  split at e
  · rename_i u hu
    obtain rfl := Except.ok.inj e
    exact h a u hu
  · cases e

/-- From a step on the chain's shape to its lift to the whole shape. -/
theorem wholeStepKeepsOwn_ofStep {G : ChainSh → Except String ChainSh} (h : StepKeepsOwn G) :
    WholeStepKeepsOwn (liftQ G) := by
  intro x y e
  unfold liftQ at e
  cases hG : G x.1 with
  | error w =>
    rw [hG] at e
    cases e
  | ok a =>
    rw [hG] at e
    obtain rfl : (a, x.2) = y := Except.ok.inj e
    exact h x.1 a hG

/-- From a step in Option to its lift to the whole shape. -/
theorem wholeStepKeepsOwn_ofOption {g : ChainSh → Option ChainSh} (h : OptionStepKeepsOwn g) :
    WholeStepKeepsOwn (liftO g) :=
  wholeStepKeepsOwn_ofStep (stepKeepsOwn_ofOption h)

/-! ## The commitment's step and the quiet step after the reads -/

/-- commitStepG keeps own. -/
theorem commitStepG_keepsOwn (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) : OptionStepKeepsOwn (commitStepG P link moment arrays) := by
  intro a b h
  unfold commitStepG at h
  split at h
  · split at h
    · split at h
      · cases h
      · obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1 h
        rfl
    · cases h
  · cases h

/-- commitG keeps own. -/
theorem commitG_keepsOwn (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) : OptionStepKeepsOwn (commitG P link moment arrays) := by
  intro a b h
  unfold commitG at h
  split at h
  · exact commitStepG_keepsOwn P link moment arrays a b h
  · cases h

/-- commitGS keeps own. -/
theorem commitGS_keepsOwn (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) : OptionStepKeepsOwn (commitGS P link moment arrays) := by
  intro a b h
  unfold commitGS at h
  split at h
  · cases h
  · exact commitG_keepsOwn P link moment arrays a b h

/-- The quiet step after the reads keeps own. -/
theorem layersG_keepsOwn (t : TailSh) :
    OptionStepKeepsOwn (VerifiableInference.Desc.K8.ReadsQuiet.layersG t) := by
  intro a b h
  unfold VerifiableInference.Desc.K8.ReadsQuiet.layersG at h
  split at h
  · cases h
  · split at h
    · obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl
    · cases h

/-! ## The members after the layers' own rounds -/

/-- readsGS keeps own. -/
theorem readsGS_keepsOwn (P : VerifiableInference.Desc.K1.Par) (link : Nat) (arrays : Option (List
    Nat))
    (t : TailSh) : OptionStepKeepsOwn (readsGS P link arrays t) := by
  intro a b h
  unfold readsGS at h
  split at h
  · cases h
  · obtain ⟨c, hc, hb⟩ := Option.bind_eq_some_iff.1 h
    exact (layersG_keepsOwn t c b hb).trans (commitG_keepsOwn P link 1 arrays a c hc)

/-- drawStep keeps own. -/
theorem drawStep_keepsOwn (p : VerifiableInference.Desc.First.K8.Par) : StepKeepsOwn (drawStep p) :=
    by
  intro a b h
  unfold drawStep drawGS at h
  split at h
  · cases h
  · unfold VerifiableInference.Desc.First.K8.drawG at h
    split at h
    · cases h
    · split at h
      · obtain rfl := Except.ok.inj h
        rfl
      · cases h

/-- digitsG keeps own. -/
theorem digitsG_keepsOwn (h : OnBytes.Model.Forest.Shape) (first used claims : Nat) :
    StepKeepsOwn (ProofFile.Honest.K3.Law.AtThr.digitsG h first used claims) := by
  intro a b e
  unfold ProofFile.Honest.K3.Law.AtThr.digitsG at e
  split at e
  · obtain rfl := Except.ok.inj e
    unfold ProofFile.Honest.K3.Law.AtThr.digitsU
    split <;> rfl
  · cases e

/-! ## The batching's draw and the rows' runs -/

/-- The batching's draw keeps own. -/
theorem drawG_keepsOwn (rows : Nat) : StepKeepsOwn (VerifiableInference.Desc.K9.Shape.drawG rows) :=
    by
  intro a b h
  unfold VerifiableInference.Desc.K9.Shape.drawG at h
  split at h
  · split at h
    · obtain rfl := Except.ok.inj h
      rfl
    · cases h
  · cases h

/-- The run objectsG keeps own. -/
theorem objectsG_keepsOwn (d : Bool) : RowRunKeepsOwn (ProofFile.Honest.K3.Shape.objectsG d) := by
  intro n a y h
  unfold ProofFile.Honest.K3.Shape.objectsG at h
  split at h
  · obtain rfl := Except.ok.inj h
    rfl
  · cases h

/-- The run guestsG keeps own. -/
theorem guestsG_keepsOwn : RowRunKeepsOwn ProofFile.Honest.K3.Shape.guestsG := by
  intro n a y h
  obtain rfl : (([] : List ClaimSh), a) = y := Except.ok.inj h
  rfl

/-- k4RunG keeps own, at every listing. -/
theorem k4RunG_keepsOwn (fG : OwnSh → LedSh → Option (List AffSh × LedSh)) :
    RowRunKeepsOwn fun _ a => OnBytes.Desc.First.K4.Rt.k4RunG fG a := by
  intro n a y h
  have h' : OnBytes.Desc.First.K4.Rt.k4RunG fG a = .ok y := h
  unfold OnBytes.Desc.First.K4.Rt.k4RunG at h'
  split at h'
  · cases h'
  · split at h'
    · split at h'
      · obtain rfl := Except.ok.inj h'
        rfl
      · cases h'
    · cases h'

/-- eqGO keeps own. -/
theorem eqGO_keepsOwn (front : Nat) :
    StepKeepsOwn (VerifiableInference.Desc.First.K8.Honest.eqGO front) := by
  intro a b h
  unfold VerifiableInference.Desc.First.K8.Honest.eqGO at h
  split at h
  · split at h
    · split at h
      · obtain rfl := Except.ok.inj h
        rfl
      · cases h
    · cases h
  · cases h

/-- The light run "K8.equations" keeps own. -/
theorem equationsRunCovered_keepsOwn : RowRunKeepsOwn
    VerifiableInference.Desc.First.K8.Honest.equationsRunCovered := by
  intro n a y h
  unfold VerifiableInference.Desc.First.K8.Honest.equationsRunCovered at h
  cases ht : VerifiableInference.Desc.First.K8.Honest.eqGO n a with
  | error e =>
    rw [ht] at h
    cases h
  | ok t =>
    rw [ht] at h
    have h' : (match VerifiableInference.Desc.First.K8.Honest.equationClaimsCovered a t with
      | some cs => (.ok (cs, t) : Except String (List ClaimSh × ChainSh))
      | none => .error "K8.equations: the claims' shapes cannot be said") = .ok y := h
    split at h'
    · obtain rfl := Except.ok.inj h'
      exact eqGO_keepsOwn n a t ht
    · cases h'

/-! ## The two members that also apply sendForms -/

/-- readsA keeps own where its step does. -/
theorem readsA_keepsOwn {G : ChainSh → Option ChainSh} (h : OptionStepKeepsOwn G)
    (P : VerifiableInference.Desc.K1.Par) : WholeStepKeepsOwn (readsA G P) := by
  intro x y e
  unfold readsA at e
  split at e
  · rename_i u hu
    obtain rfl := Except.ok.inj e
    exact h x.1 u hu
  · cases e

/-- digitsA keeps own. -/
theorem digitsA_keepsOwn (P : VerifiableInference.Desc.K1.Par) (l : Nat) (digits : Option (List
    Nat)) :
    WholeStepKeepsOwn (digitsA P l digits) := by
  intro x y e
  unfold digitsA at e
  split at e
  · rename_i u hu
    obtain rfl := Except.ok.inj e
    exact commitGS_keepsOwn P l 2 digits x.1 u hu
  · cases e

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.StepKeepsOwn
#print axioms Johnson.AtFull.Shape.OptionStepKeepsOwn
#print axioms Johnson.AtFull.Shape.RowRunKeepsOwn
#print axioms Johnson.AtFull.Shape.WholeStepKeepsOwn
#print axioms Johnson.AtFull.Shape.stepKeepsOwn_ofOption
#print axioms Johnson.AtFull.Shape.wholeStepKeepsOwn_ofStep
#print axioms Johnson.AtFull.Shape.wholeStepKeepsOwn_ofOption
#print axioms Johnson.AtFull.Shape.commitStepG_keepsOwn
#print axioms Johnson.AtFull.Shape.commitG_keepsOwn
#print axioms Johnson.AtFull.Shape.commitGS_keepsOwn
#print axioms Johnson.AtFull.Shape.layersG_keepsOwn
#print axioms Johnson.AtFull.Shape.readsGS_keepsOwn
#print axioms Johnson.AtFull.Shape.drawStep_keepsOwn
#print axioms Johnson.AtFull.Shape.digitsG_keepsOwn
#print axioms Johnson.AtFull.Shape.drawG_keepsOwn
#print axioms Johnson.AtFull.Shape.objectsG_keepsOwn
#print axioms Johnson.AtFull.Shape.guestsG_keepsOwn
#print axioms Johnson.AtFull.Shape.k4RunG_keepsOwn
#print axioms Johnson.AtFull.Shape.eqGO_keepsOwn
#print axioms Johnson.AtFull.Shape.equationsRunCovered_keepsOwn
#print axioms Johnson.AtFull.Shape.readsA_keepsOwn
#print axioms Johnson.AtFull.Shape.digitsA_keepsOwn
