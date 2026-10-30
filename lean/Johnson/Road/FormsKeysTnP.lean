-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTnP.lean: the sum that a weight claim of the verifier speaks of is the
functional of a tensor claim of the library.

claimVal (Johnson/Road/FormsKeysWm.lean) writes what a claim of the verifier on the matrix W of
weights says: the sum over all tuples of indices of the product of what the claim's factors weigh
the indices with, times the weight, read in W at the verifier's cells. The library has the like:
TClaim.Tn (Inst/Model/Common/TensorClaim.lean): a unit by its number, one factor for each
coordinate, the entry read in W at the library's places. This file shows that the two are one
number, if the claim's unit is the library's unit and each factor weighs each index of its group as
the library's factor does.

What is compared with what: claimVal, a definition of these files on the verifier's records, with
the library's TClaim.Tn; through layout_eq (Johnson/Road/FormsKeysWLay.lean), which says that the
verifier's cell is the library's place.

Main theorems: sumIdx_boxSum, claimVal_Tn, claimVal_Tn_of_layout.

What is not claimed. That claimVal is what the verifier's settling of a claim on W comes to is shown
in Johnson/Road/FormsKeysFac.lean. Which factors the claims of a layer sub-proof have is looked at
in other files. The program does not import this file.
-/
import Johnson.Road.FormsKeysWLay
import Inst.Model.Common.TensorClaim

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading WsShape WsGrp WsUnit WsLay WsFac WsClaim wsLayOf)
open Inst.Model (Params TClaim entryW boxSum)

variable {K : Type} [Field K] (ρ : Reading K)

/-- Each factor of the verifier weighs each index of its group as the function beside it does. -/
def FacsAre (fg : List (WsFac × WsGrp)) (fs : List (ℕ → K)) : Prop :=
  List.Forall₂ (fun xg f => ∀ v, v < xg.2.R → facAt ρ xg.1 xg.2 v = f v) fg fs

/-- The verifier's sum over the tuples of indices is the library's, if the factors agree on the
groups' indices. -/
theorem sumIdx_boxSum : ∀ (fg : List (WsFac × WsGrp)) (fs : List (ℕ → K)) (F : List ℕ → K),
    FacsAre ρ fg fs → sumIdx ρ fg F = boxSum (fg.map fun xg => coordOf xg.2) fs F
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | (x, g) :: fg, f :: fs, F, h => by
    cases h with
    | cons h1 h2 =>
      show ∑ v ∈ range g.R, facAt ρ x g v * sumIdx ρ fg (fun idx => F (v :: idx)) =
        ∑ i ∈ range g.R, f i * boxSum (fg.map fun xg => coordOf xg.2) fs fun is => F (i :: is)
      refine sum_congr rfl fun v hv => ?_
      rw [h1 v (mem_range.mp hv), sumIdx_boxSum fg fs _ h2]

/-- One claim. If unit u of the verifier's layout, which the claim c names, has the coordinates, the
number of digits and the cells of the library's unit U with the number n, and the claim's factors
agree with the functions fs on the groups' indices, then the sum that the claim speaks of is the
functional of the library's tensor claim ⟨n, U, fs⟩ on the same matrix. -/
theorem claimVal_Tn {lay : WsLay} {W : Wm K} {c : WsClaim} {u : WsUnit} {P : Params} {lk n : ℕ}
    {U : Inst.Model.Layout.UnitS} {fs : List (ℕ → K)} (hu : lay.U[c.ui]? = some u)
    (hco : u.g.map coordOf = U.coords) (hlen : c.f.length = u.g.length) (hnl : u.nlw = U.nU)
    (hcell : ∀ q idx, cellOf u q idx =
      Inst.Model.Layout.place lk (Inst.Model.Layout.units P) n U q idx)
    (hf : FacsAre ρ (c.f.zip u.g) fs) :
    claimVal ρ lay W c = (⟨n, U, fs⟩ : TClaim K).Tn P lk W := by
  have e1 : ((c.f.zip u.g).map fun xg => coordOf xg.2) = U.coords := by
    rw [← hco]
    have e2 : ((c.f.zip u.g).map fun xg => coordOf xg.2) =
        ((c.f.zip u.g).map Prod.snd).map coordOf := by
      rw [List.map_map]
      rfl
    rw [e2, List.map_snd_zip (by omega)]
  have e3 : wgtOf u W = fun i => entryW P lk W n U i := by
    funext idx
    unfold wgtOf entryW
    rw [hnl]
    refine sum_congr rfl fun q _ => ?_
    rw [hcell]
  unfold claimVal
  rw [hu]
  show sumIdx ρ (c.f.zip u.g) (wgtOf u W) = boxSum U.coords fs fun i => entryW P lk W n U i
  rw [sumIdx_boxSum ρ _ _ _ hf, e1, e3]

/-- The same on the verifier's own layout of the weights: for a shape that agrees with the library's
parameters in the nine numbers of SizedW, a layout that wsLayOf returns, and a claim on a unit whose
number the library's list has. Asked of the claim: one factor for each group, and that the factors
agree with fs. -/
theorem claimVal_Tn_of_layout {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) (W : Wm K) {c : WsClaim} {U : Inst.Model.Layout.UnitS}
    (hU : (Inst.Model.Layout.units P)[c.ui]? = some U) {fs : List (ℕ → K)}
    (hf : ∀ u, lay.U[c.ui]? = some u → c.f.length = u.g.length ∧ FacsAre ρ (c.f.zip u.g) fs) :
    claimVal ρ lay W c = (⟨c.ui, U, fs⟩ : TClaim K).Tn P lk W := by
  obtain ⟨-, -, -, hall⟩ := layout_eq Z h
  obtain ⟨u, hu, -, hnl, -, -, hco, -, -, hcell⟩ := hall c.ui U hU
  obtain ⟨hlen, hfa⟩ := hf u hu
  exact claimVal_Tn ρ hu hco hlen hnl hcell hfa

#print axioms sumIdx_boxSum
#print axioms claimVal_Tn
#print axioms claimVal_Tn_of_layout

end OnBytes.Road
