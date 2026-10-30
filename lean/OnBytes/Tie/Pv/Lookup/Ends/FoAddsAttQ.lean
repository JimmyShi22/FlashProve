-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttQ.lean.
The attention sub-proof: the routines that only make a form add no claim.

States Fo.Quiet of uEnt (OnBytes/Model/Look.lean) and of these routines of
OnBytes/Model/AttentionClaimsA.lean: u3at, weighted, plane, shV, xl, overG, readDenominator,
readMaximum, readIndexBit, readHead, readGroup, lessPieces. For weighted, overG and lessPieces the
premise is that the routine handed in is Quiet at every argument. callKR and callKFD of that file
return a form too, and they do add claims (OnBytes/Tie/Pv/Lookup/Ends/FoAddsAtt.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAdds
import OnBytes.Model.AttentionClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

theorem quiet_uEnt (t x : ℕ) : Quiet (uEnt t x) := by
  unfold uEnt
  quiet

theorem quiet_u3at (h : Attention.Heard) (t i : ℕ) : Quiet (u3at h t i) := by
  unfold u3at
  refine Quiet.bind ?_ fun _ => quiet_uEnt _ _
  quiet

theorem quiet_weighted (n : ℕ) (w : Array E) (f : ℕ → SubM Aff) (hf : ∀ i, Quiet (f i)) :
    Quiet (weighted n w f) := by
  unfold weighted
  exact Quiet.foldlM (fun _ i => (hf i).bind fun _ => Quiet.pure _) _ _

theorem quiet_plane (h : Attention.Heard) (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    Quiet (plane h t x lam a z isD) := by
  unfold plane
  exact quiet_weighted _ _ _ fun _ => quiet_u3at _ _ _

theorem quiet_shV (h : Attention.Heard) (t off nl J lam j : ℕ) : Quiet (shV h t off nl J lam j) :=
    by
  unfold shV
  exact quiet_weighted _ _ _ fun _ => quiet_u3at _ _ _

theorem quiet_xl (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) :
    Quiet (xl h t X lam hd zc) := by
  unfold xl
  dsimp only
  split
  · split
    · exact quiet_weighted _ _ _ fun _ => quiet_weighted _ _ _ fun _ => quiet_u3at _ _ _
    · quiet
  · quiet

theorem quiet_overG (h : Attention.Heard) (zg : Array E) (f : ℕ → SubM Aff)
    (hf : ∀ i, Quiet (f i)) : Quiet (overG h zg f) := by
  unfold overG
  exact quiet_weighted _ _ _ hf

theorem quiet_readDenominator (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    Quiet (readDenominator h t zg lam a) := by
  unfold readDenominator
  exact quiet_overG _ _ _ fun _ => quiet_shV _ _ _ _ _ _ _

theorem quiet_readMaximum (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    Quiet (readMaximum h t zg lam a) := by
  unfold readMaximum
  exact quiet_overG _ _ _ fun _ => quiet_shV _ _ _ _ _ _ _

theorem quiet_readIndexBit (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a k : ℕ) :
    Quiet (readIndexBit h t zg lam a k) := by
  unfold readIndexBit
  exact quiet_overG _ _ _ fun _ => quiet_shV _ _ _ _ _ _ _

theorem quiet_readHead (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    Quiet (readHead h t X zg zc lam a) := by
  unfold readHead
  exact quiet_overG _ _ _ fun _ => quiet_xl _ _ _ _ _ _

theorem quiet_readGroup (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    Quiet (readGroup h t X zg zc lam) := by
  unfold readGroup
  exact quiet_overG _ _ _ fun _ => quiet_xl _ _ _ _ _ _

theorem quiet_lessPieces (start : Aff) (pw : Array PW) (f : PW → SubM Aff)
    (hf : ∀ w, Quiet (f w)) : Quiet (lessPieces start pw f) := by
  unfold lessPieces
  exact Quiet.arrayFoldlM (fun _ w => (hf w).bind fun _ => Quiet.pure _) _ _

end Fo
