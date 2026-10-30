-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttKf.lean.
The attention sub-proof: the key forms that it hands to the lookup's join, as closed terms.

Attention.claims (OnBytes/Model/Attention.lean) makes the calls' key forms in claim3, claim4 and
claim5, which also add claims, and hands them to Forest.join. What these three routines return does
not depend on the run.

States:
  kfKR, kfKFD: the key form of a call of kind KR, of kind KFD, as plain folds. (Kind R16: kfR16 in
    OnBytes/Tie/Pv/Lookup/Ends/FoAttKfAt.lean.)
  joins3, joins4, joins5: the record of key forms behind claim3, claim4, claim5, as plain folds.
  callKR_gives, callKFD_gives, claim3_gives, claim4_gives, claim5_gives: every run that returns,
    returns these. (The three in turn: claims345_gives in the same other file.)
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that a run returns, or
that a key form reads the extension of the call's key vector. Nothing is said of what the runs do to
the state.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoGives
import OnBytes.Model.AttentionClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

/-- The key form of call q, a call of kind KR. -/
def kfKR (h : Attention.Heard) (q : ℕ) : Aff :=
  h.planes.toList.foldl (fun v pc => if pc.call == q then v + keyKR pc else v) (Aff.ofConst zeroE)

/-- The key form of call c, which has the number q, a call of kind KFD. -/
def kfKFD (h : Attention.Heard) (q : ℕ) (c : ACall) : Aff :=
  h.scores.toList.zipIdx.foldl
    (fun v x => if x.1.call == q then v + keyKFD (h.S.shd c.sh) x.1 else v)
    (padTerm c (h.g.zk.getD q #[]))

theorem callKR_gives (h : Attention.Heard) (q : ℕ) : Returns (callKR h q) (kfKR h q) := by
  unfold callKR kfKR
  refine gives_foldlMA _ _ (fun v pc => ?_) _ _
  exact gives_ite (gives_then fun _ => gives_pure _) (gives_pure _)

theorem callKFD_gives (h : Attention.Heard) (q : ℕ) (c : ACall) :
    Returns (callKFD h q c) (kfKFD h q c) := by
  unfold callKFD kfKFD
  refine gives_foldlM _ _ (fun v x => ?_) _ _
  exact gives_ite (gives_then fun _ => gives_pure _) (gives_pure _)

/-- The key forms behind claim 3. -/
def joins3 (h : Attention.Heard) (j : Joins) : Joins :=
  h.S.calls.toList.zipIdx.foldl
    (fun j x => if x.1.kind == .kr then j.set x.2 (kfKR h x.2) else j) j

/-- The key forms behind claim 4. -/
def joins4 (h : Attention.Heard) (j : Joins) : Joins :=
  h.S.calls.toList.zipIdx.foldl
    (fun j x => if x.1.kind == .kfd then j.set x.2 (kfKFD h x.2 x.1) else j) j

/-- The key forms behind claim 5. -/
def joins5 (h : Attention.Heard) (j : Joins) : Joins :=
  (joinR16 h.S h.d j).set h.d.qWH (keyWH h.d)

theorem claim3_gives (h : Attention.Heard) (j : Joins) : Returns (claim3 h j) (joins3 h j) := by
  unfold claim3 joins3
  refine gives_foldlM _ _ (fun j x => ?_) _ _
  exact gives_ite (gives_bind (callKR_gives h x.2) (gives_pure _)) (gives_pure _)

theorem claim4_gives (h : Attention.Heard) (j : Joins) : Returns (claim4 h j) (joins4 h j) := by
  unfold claim4 joins4
  refine gives_foldlM _ _ (fun j x => ?_) _ _
  exact gives_ite (gives_bind (callKFD_gives h x.2 x.1) (gives_pure _)) (gives_pure _)

theorem claim5_gives (h : Attention.Heard) (j : Joins) : Returns (claim5 h j) (joins5 h j) := by
  unfold claim5 joins5
  repeat' (first | exact gives_pure _ | (refine gives_then fun _ => ?_))

end Fo
