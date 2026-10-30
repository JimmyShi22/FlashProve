-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/ModelTieAtFiles.lean: the model's tie at the protocol: requests and the served set.

1.  The index of any weights is in range, and whatever is served is in range.
2.  A request that can be served, with the model's own output, builds an instance that is served at the index of the weights, and the
    request reads back from it.
3.  A request that is refused at some weights is not served there, if it builds an instance.
4.  There is an instance that no request builds. At that instance as the fallback, a refused request that builds nothing is
    not served either.
Nothing here is about the provers.
-/
import VerifiableInference.Final.TheSeam
import VerifiableInference.RequestOutcome
import VerifiableInference.AtEveryRequestGuards
import E2E.CompleteAsIOPServedLaws
import Johnson.FrontRoad.AtWeights
import Johnson.FrontRoad.TieServed
import Johnson.Flat.MatrixOfImage

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation.Seam
open AtPublicFiles.AtFiles VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles readFiles InScope settingsOfRead valid_of_read)
open FlashProve (committerCoinCountLessOne backThe backB homeR build_home_of_built)
open OnBytes.FrontRoad (okThe inRange_backThe backTok)
open VerifiableInference (canServe_and_modelOutput_iff CanServe requestOfTokens tokensOfRequest
  requestOfTokens_some indexOfWeights weightsOfIndex_indexOfWeights settingsAreValid ModelWeights Token)
open IntegerModel (requestOf requestOf_some tokenZero)
open VerifiableInference.AtEveryRequest (requestOutcome requestOutcome_eq_served_iff served_iff_canServe)
open LPFD.Full (XF)

variable (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)

/-- The index of any weights is in range. -/
theorem range_at (s : IntegerTransformer.Settings) (w : ModelWeights s) : okThe Z (backThe Z s w) :=
  inRange_backThe Z s w

section General
variable (b : PublicFiles → ℕ)

-- In a variable b Lean need not evaluate the number committerCoinCountLessOne Z when it compares the index types of the two inputs.
theorem served_inRange_gen (i : (homeR b Z).Index) (x : (homeR b Z).Instance) (h : ServedRequest b Z hr i x) :
    Flat.InRange i := by
  obtain ⟨w, -, -, hi, -⟩ := h
  rw [hi]
  exact inRange_backThe Z _ w

theorem tie_gen (scope : InScope Z = true) (w : ModelWeights (settingsOfRead pp)) (p o : List Token)
    (hd : CanServe (settingsOfRead pp) w p o) (hm : VerifierAndGoals.ModelOutput (settingsOfRead pp) w p o) :
    ∃ x : (homeR b Z).Instance, Flat.buildReq (p, o) [] = some x ∧
      ServedRequest b Z hr (backB b Z (settingsOfRead pp) w) x ∧ backTok b Z x = (p, o) := by
  obtain ⟨x, hx, -⟩ := Meaning.true_of_served scope hr w p o hd hm
  obtain ⟨hform, hres⟩ := (canServe_and_modelOutput_iff (valid_of_read hr) w p o).1 ⟨hd, hm⟩
  have hb := build_home_of_built b Z hx
  have hb' := (congrFun (congrFun (FlashProve.build_home b Z) (p, o)) []).symm.trans hb
  exact ⟨_, hb', ⟨w, p, o, rfl, hform, hres, hb⟩, Flat.buildReq_reads hb'⟩

end General

/-- The builder of the verifier's input. -/
theorem build_input : (inputAt Z).buildInstance = Flat.buildReq := rfl

/-- What is served is in range. -/
theorem servedInRange_at (i : FullSizeMatrix) (x : XF) (h : servedAt Z hr i x) : okThe Z i :=
  served_inRange_gen Z hr committerCoinCountLessOne i x h

/-- **A request that can be served builds an instance that is served, and reads back from it.** -/
theorem tie_at (scope : InScope Z = true) (w : ModelWeights (settingsOfRead pp)) (p o : List Token)
    (hd : CanServe (settingsOfRead pp) w p o) (hm : VerifierAndGoals.ModelOutput (settingsOfRead pp) w p o) :
    ∃ x : XF, (inputAt Z).buildInstance (p, o) [] = some x ∧ servedAt Z hr (backThe Z (settingsOfRead pp) w) x ∧
      backTok committerCoinCountLessOne Z x = (p, o) :=
  Exists.elim (tie_gen Z hr committerCoinCountLessOne scope w p o hd hm) fun x h =>
    ⟨x, (congrFun (congrFun (build_input Z) (p, o)) []).trans h.1, h.2.1, h.2.2⟩

/-- At valid settings weights are read back from their matrix. -/
theorem backThe_injective {s : IntegerTransformer.Settings} (hv : settingsAreValid s = true)
    {w w' : ModelWeights s} (h : backThe Z s w = backThe Z s w') : w = w' := by
  have h1 : VerifierAndGoals.Fit.backO hv w = VerifierAndGoals.Fit.backO hv w' := by
    unfold backThe at h
    rwa [dif_pos hv, dif_pos hv] at h
  have h2 : indexOfWeights hv w = indexOfWeights hv w' := Flat.matrixOf_injective h1
  rw [← weightsOfIndex_indexOfWeights hv w, ← weightsOfIndex_indexOfWeights hv w', h2]

/-- The same, for the index of the home input, in a variable bound. -/
theorem backB_injective (b : PublicFiles → ℕ) {s : IntegerTransformer.Settings} (hv : settingsAreValid s = true)
    {w w' : ModelWeights s} (h : backB b Z s w = backB b Z s w') : w = w' := by
  have h0 : @Eq FullSizeMatrix (backB b Z s w) (backB b Z s w') := h
  have h1 : @Eq FullSizeMatrix (backThe Z s w) (backThe Z s w') := h0
  exact backThe_injective Z hv h1

theorem refused_built_gen (b : PublicFiles → ℕ) (w : ModelWeights (settingsOfRead pp)) (p o : List Token)
    (x : XF) (hb : Flat.buildReq (p, o) [] = some x)
    (href : requestOutcome (settingsOfRead pp) w (p, o) = .refused) :
    ¬ ServedRequest b Z hr (backB b Z (settingsOfRead pp) w) x := by
  intro h
  obtain ⟨w', p', o', hi, hform, hres, hb'⟩ := h
  have hb2 : Flat.buildReq (p', o') [] = some x :=
    (congrFun (congrFun (FlashProve.build_home b Z) (p', o')) []).symm.trans hb'
  have e3 : (p', o') = (p, o) := (Flat.buildReq_reads hb2).symm.trans (Flat.buildReq_reads hb)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e3
  have hw : w = w' := backB_injective Z b (valid_of_read hr) hi
  subst hw
  have hs : requestOutcome (settingsOfRead pp) w (p', o') = .served :=
    (requestOutcome_eq_served_iff _ _ _).2 ⟨hform, hres⟩
  rw [hs] at href
  cases href

/-- **A refused request that builds an instance is not served there.** -/
theorem refused_built (w : ModelWeights (settingsOfRead pp)) (p o : List Token) (x : XF)
    (hb : (inputAt Z).buildInstance (p, o) [] = some x)
    (href : requestOutcome (settingsOfRead pp) w (p, o) = .refused) :
    ¬ servedAt Z hr (backThe Z (settingsOfRead pp) w) x :=
  refused_built_gen Z hr committerCoinCountLessOne w p o x
    ((congrFun (congrFun (build_input Z) (p, o)) []).symm.trans hb) href

/-- A well-formed request whose window holds a token past its own two: no request builds it at no padding. -/
def unbuiltRequest : Inst.Model.Instance Inst.Model.ppref :=
  ⟨fun t => if t.val = 3 then ⟨1, by decide⟩ else tokenZero, tokenZero, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

theorem unbuiltRequest_wf : Flat.WellFormed unbuiltRequest := ⟨Nat.zero_lt_one, fun _ => rfl⟩

/-- **The fallback instance.** -/
def fallbackInstance : XF := ⟨unbuiltRequest, unbuiltRequest_wf⟩

/-- **No request builds it.** -/
theorem fallback_not_built (p o : List Token) : Flat.buildReq (p, o) [] ≠ some fallbackInstance := by
  intro h
  have h2 := Flat.buildReq_some h
  obtain ⟨prompt, output, pad, -, -, hpad, hq⟩ := requestOfTokens_some h2
  have hp0 : pad = [] := (Option.some.inj hpad).symm
  subst hp0
  obtain ⟨hc, hrr, hee, -⟩ := requestOf_some hq
  have h0 : (0 : ℕ) = prompt.length - 1 := hrr
  have h1 : (1 : ℕ) = prompt.length - 1 + output.length := hee
  have hl : (prompt ++ output ++ []).length ≤ 3 := by
    simp only [List.length_append, List.length_nil]
    omega
  unfold requestOf at hq
  rw [dif_pos hc] at hq
  have h3 := congrArg (fun x : Inst.Model.Instance Inst.Model.ppref => (x.prompt ⟨3, by decide⟩).val)
    (Option.some.inj hq)
  have h4 : ((prompt ++ output ++ []).getD 3 tokenZero).val = 1 := h3
  rw [List.getD_eq_default _ _ hl] at h4
  exact absurd h4 (by decide)

/-- **Nothing is served at an instance that no request builds.** -/
theorem unserved_of_neverBuilt (x₀ : XF) (h : ∀ p o, Flat.buildReq (p, o) [] ≠ some x₀) (i : FullSizeMatrix) :
    ¬ servedAt Z hr i x₀ := by
  intro hs
  have h' : ServedRequest committerCoinCountLessOne Z hr i x₀ := hs
  obtain ⟨-, p, o, -, -, -, hb⟩ := h'
  exact h p o hb

/-- **A refused request is not served**, at any fallback instance that no request builds. -/
theorem refusedIsUnserved_of (x₀ : XF) (h : ∀ p o, Flat.buildReq (p, o) [] ≠ some x₀)
    (w : ModelWeights (settingsOfRead pp)) (request : List Token × List Token)
    (href : requestOutcome (settingsOfRead pp) w request = .refused) :
    ¬ servedAt Z hr (backThe Z (settingsOfRead pp) w) (OnBytes.FrontRoad.instOf (inputAt Z) x₀ request) := by
  unfold OnBytes.FrontRoad.instOf
  cases hb : (inputAt Z).buildInstance request [] with
  | none => exact unserved_of_neverBuilt Z hr x₀ h _
  | some x => exact refused_built Z hr w request.1 request.2 x hb href

/-- One such instance: a test that the premise can be met. -/
theorem fallback_unserved (i : FullSizeMatrix) : ¬ servedAt Z hr i fallbackInstance :=
  unserved_of_neverBuilt Z hr fallbackInstance fallback_not_built i

theorem refusedIsUnserved (w : ModelWeights (settingsOfRead pp)) (request : List Token × List Token)
    (href : requestOutcome (settingsOfRead pp) w request = .refused) :
    ¬ servedAt Z hr (backThe Z (settingsOfRead pp) w)
      (OnBytes.FrontRoad.instOf (inputAt Z) fallbackInstance request) :=
  refusedIsUnserved_of Z hr fallbackInstance fallback_not_built w request href

/-- **A served request builds an instance that is served at the index of the weights.** -/
theorem servedIsServed (scope : InScope Z = true) (w : ModelWeights (settingsOfRead pp))
    (request : List Token × List Token)
    (h : requestOutcome (settingsOfRead pp) w request = .served) :
    ∃ x : XF, (inputAt Z).buildInstance request [] = some x ∧
      servedAt Z hr (backThe Z (settingsOfRead pp) w) x := by
  obtain ⟨p, o⟩ := request
  have hc := (served_iff_canServe (valid_of_read hr) w (p, o)).1 h
  obtain ⟨x, hb, hs, -⟩ := tie_at Z hr scope w p o hc.1 hc.2
  exact ⟨x, hb, hs⟩

/-- **The outcome and the relation are one**: at any fallback instance that no request builds, a request is served exactly if its instance
is served at the index of the weights. -/
theorem outcome_served_iff (scope : InScope Z = true) (x₀ : XF)
    (h : ∀ p o, Flat.buildReq (p, o) [] ≠ some x₀) (w : ModelWeights (settingsOfRead pp))
    (request : List Token × List Token) :
    requestOutcome (settingsOfRead pp) w request = .served ↔
      servedAt Z hr (backThe Z (settingsOfRead pp) w) (OnBytes.FrontRoad.instOf (inputAt Z) x₀ request) := by
  constructor
  · intro hs
    obtain ⟨x, hb, hv⟩ := servedIsServed Z hr scope w request hs
    unfold OnBytes.FrontRoad.instOf
    rw [hb]
    exact hv
  · intro hv
    cases e : requestOutcome (settingsOfRead pp) w request with
    | served => rfl
    | refused => exact absurd hv (refusedIsUnserved_of Z hr x₀ h w request e)

end VerifiableInference.Compilation.Seam

#print axioms VerifiableInference.Compilation.Seam.range_at
#print axioms VerifiableInference.Compilation.Seam.servedInRange_at
#print axioms VerifiableInference.Compilation.Seam.tie_at
#print axioms VerifiableInference.Compilation.Seam.backThe_injective
#print axioms VerifiableInference.Compilation.Seam.build_input
#print axioms VerifiableInference.Compilation.Seam.refused_built
#print axioms VerifiableInference.Compilation.Seam.fallback_not_built
#print axioms VerifiableInference.Compilation.Seam.unserved_of_neverBuilt
#print axioms VerifiableInference.Compilation.Seam.refusedIsUnserved_of
#print axioms VerifiableInference.Compilation.Seam.fallback_unserved
#print axioms VerifiableInference.Compilation.Seam.refusedIsUnserved
#print axioms VerifiableInference.Compilation.Seam.servedIsServed
#print axioms VerifiableInference.Compilation.Seam.outcome_served_iff
