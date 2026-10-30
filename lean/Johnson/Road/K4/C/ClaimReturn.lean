-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimReturn.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: ONE CLAIM RETURNS AND
PASSES THE MERGE's TWO TESTS ON A CLAIM: the verifier's function claim
(OnBytes/Model/LayerPanels.lean), for a kind of weight matrix that the layer has, returns where the
rule for the factors returns on each group of the unit a factor that fits the group; the claim's
unit is then a unit of the layout of the weights, and the claim has the sizes that the layout asks
(wsClaimShape, OnBytes/Model/Weights.lean). That the unit is found, and which groups it has, is the
library's (unitOf_eq, ask_of_kind, unitsFrom_get, unitOK_of_layout:
Johnson/Road/FormsKeysWLay.lean). Statements and proofs. General in the sizes.

  `mapM_fits`      factors that fit, group by group.
  **`claim_some`**   the claim.

Not shown here. That the hypotheses hold at any plan or layout of the weights: no example is shown
here. AT A LAYOUT OF THE WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS, whose shape
agrees with the library's parameters (SizedW). Kinds 0 to 11 alone. Public data alone: whether a
claim IS THERE and how long its parts are; nothing on its elements. No property is claimed.
-/
import Johnson.Road.K4.C.ReadersReturn
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv)
open Inst.Model (Params)
open Inst.Model.Layout renaming first → firstLib

/-- Factors that fit, group by group: the list of them is there, is as long as the list of groups,
and passes the test on the pairs. -/
theorem mapM_fits {fac : WsGrp → Option WsFac} : ∀ (l : List WsGrp),
    (∀ G ∈ l, ∃ f, fac G = some f ∧ f.fits G = true) →
    ∃ fs, l.mapM fac = some fs ∧ fs.length = l.length ∧
      ((fs.zip l).all fun y => y.1.fits y.2) = true
  | [], _ => ⟨[], rfl, rfl, rfl⟩
  | G :: l, h => by
    obtain ⟨f, hf, hfit⟩ := h G List.mem_cons_self
    obtain ⟨fs, h1, h2, h3⟩ := mapM_fits l fun G' hG' => h G' (List.mem_cons_of_mem _ hG')
    refine ⟨f :: fs, ?_, ?_, ?_⟩
    · rw [List.mapM_cons, hf, h1]
      rfl
    · rw [List.length_cons, List.length_cons, h2]
    · rw [List.zip_cons_cons, List.all_cons, hfit, h3]
      rfl

/-- **ONE CLAIM RETURNS, ON A UNIT OF THE LAYOUT, WITH THE SIZES THAT THE LAYOUT ASKS.**
CONDITIONAL: on the layout of the weights (Z, hlw), on a layer of the model (hl), on a kind that the
layer has (hX), and on the rule for the factors (hfac): on each group of the layer's asked unit of
that kind, placed, whose numbers fit each other, it returns a factor that fits. -/
theorem claim_some {c : ClaimEnv} {s : WsShape} {P : Params} {lk : ℕ} (Z : SizedW s P)
    (hlw : wsLayOf s true lk = .ok c.wsLay) {lam X i : ℕ} (hl : c.v.lay lam < P.layers)
    (hX : (kindsOf (c.v.lay lam))[i]? = some X) {fac : WsGrp → Option WsFac}
    (hfac : ∀ a ∈ layerAsks (shapeOf s true) (c.v.lay lam), a.X = X →
      ∀ G ∈ placeP a.g lk 0, GrpOK G → ∃ f, fac G = some f ∧ f.fits G = true) :
    ∃ cl, c.claim X lam fac = some cl ∧ cl.ui < c.wsLay.U.size ∧
      (wsClaimShape c.wsLay cl).isOk = true := by
  have hu := (unitOf_eq Z hlw).1 _ hl i X hX
  obtain ⟨a, ha, hm, eX, -⟩ := ask_of_kind Z hlw hl hX
  obtain ⟨-, h2, -, -⟩ := wsLayOf_units hlw
  obtain ⟨o, hU⟩ : ∃ o, c.wsLay.U[firstLib P (c.v.lay lam) + i]? = some (unitP lk o a) :=
    ⟨_, by rw [← Array.getElem?_toList, h2]; exact unitsFrom_get lk _ 0 _ a ha⟩
  have hok : UnitOK lk (unitP lk o a) :=
    ((unitOK_of_layout hlw).2 _ (Array.mem_of_getElem? hU)).1
  obtain ⟨fs, f1, f2, f3⟩ := mapM_fits (placeP a.g lk 0)
    fun G hG => hfac a hm eX G hG (hok.grp G hG)
  refine ⟨{ ui := firstLib P (c.v.lay lam) + i, f := fs }, ?_, ?_, ?_⟩
  · unfold ClaimEnv.claim
    rw [hu]
    show (do
      let u ← c.wsLay.U[firstLib P (c.v.lay lam) + i]?
      let f ← u.g.mapM fac
      pure ({ ui := firstLib P (c.v.lay lam) + i, f := f } : WsClaim)) = _
    rw [hU]
    show (do
      let f ← (placeP a.g lk 0).mapM fac
      pure ({ ui := firstLib P (c.v.lay lam) + i, f := f } : WsClaim)) = _
    rw [f1]
    rfl
  · exact (Array.getElem?_eq_some_iff.mp hU).1
  · unfold wsClaimShape
    show (match c.wsLay.U[firstLib P (c.v.lay lam) + i]? with
      | none => throw "internal-claim-unit"
      | some u =>
        if (fs.length == u.g.length && ((fs.zip u.g).all fun y => y.1.fits y.2)) = true then
          pure ()
        else throw "internal-claim-factors" : Except String Unit).isOk = true
    rw [hU]
    show (if (fs.length == (placeP a.g lk 0).length &&
        ((fs.zip (placeP a.g lk 0)).all fun y => y.1.fits y.2)) = true then pure ()
      else throw "internal-claim-factors" : Except String Unit).isOk = true
    rw [f2, f3, beq_self_eq_true]
    rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.mapM_fits
#print axioms OnBytes.Road.K4.C.claim_some
