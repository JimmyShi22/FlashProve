-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/QuietHead.lean: the routines of the check of the output head's sub-proof that make its
tables, its forms and its claims do not touch the channel; each as a function on the ledger alone.

OnBytes/K/Kc/Quiet.lean says what "quiet" means and what `still` is: the program's own routine, run
from one fixed empty context of a run on a view, with the context dropped. This file proves that the
following routines are quiet, by the rules of that file along each routine's text, and names their
functions on the ledger:
 - `flatTables`: the head's tables of reads (`Model.Head.tablesOf`, OnBytes/Model/HeadTables.lean);
 - `flatWeightsClaim`: the one claim on the committed weights (`Model.Head.weightsClaim`);
 - the walk's own groups of claims, in the walk's order (OnBytes/Model/Head.lean):
   `flatObjects` (the lookup's claims that read mask entries alone), `flatClaimSquares`,
   `flatClaimLedger`, `flatClaimStream`, `flatClaimJoin`, `flatClaimPolicy`, `flatClaimPlanes`,
   `flatClaimLogits`.
For each, `still_iff` (OnBytes/K/Kc/Quiet.lean) then says: a run on a view from a state F and any
context succeeds with the value a and the state G exactly if the function at F is some (a, G); and
`still_same`: the context is left as it was but for kept values. The statements stand below under
names of their own (`lawTables` and so on).

What a claim routine does to the ledger: it adds forms to the sub-proof's one equation
(`Model.Fork.lin`); it tests public numbers, and in `weightsClaim` one value (a checked token is an
entry of the vocabulary). WHICH forms are added is not said here in closed form: the function is the
program's text.

Not claimed. Nothing on the dry run. Nothing on soundness. The program does not import this file.
-/
import OnBytes.K.Kc.Quiet
import OnBytes.Model.Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM)

/-! ## The steps on the state, the lookup's claims, the routines that make forms, the claims -/

/-- SubM.hide is quiet. -/
instance quiet_hide (j : Nat) (a b : E) : Quiet (SubM.hide j a b) := by
  unfold SubM.hide
  infer_instance

/-- SubM.kap is quiet. -/
instance quiet_kap : Quiet (SubM.kap) := by
  unfold SubM.kap
  infer_instance

/-- SubM.push is quiet. -/
instance quiet_push (w : E) (a : Model.Aff) : Quiet (SubM.push w a) := by
  unfold SubM.push
  infer_instance

/-- SubM.lin is quiet. -/
instance quiet_lin (f : Model.Aff) : Quiet (SubM.lin f) := by
  unfold SubM.lin
  infer_instance

/-- SubM.setPlanClaims is quiet. -/
instance quiet_setPlanClaims (n : Nat) : Quiet (SubM.setPlanClaims n) := by
  unfold SubM.setPlanClaims
  infer_instance

/-- SubM.claims is quiet. -/
instance quiet_claims : Quiet (SubM.claims) := by
  unfold SubM.claims
  infer_instance

/-- SubM.allTaken is quiet. -/
instance quiet_allTaken : Quiet (SubM.allTaken) := by
  unfold SubM.allTaken
  infer_instance

/-- SubM.paid is quiet. -/
instance quiet_paid (i : Nat) : Quiet (SubM.paid i) := by
  unfold SubM.paid
  infer_instance

/-- SubM.settle is quiet. -/
instance quiet_settle (n : Nat) : Quiet (SubM.settle n) := by
  unfold SubM.settle
  infer_instance

/-- pscRow is quiet: it reads no round. -/
instance quiet_pscRow (p : Model.Psc) (S0 : E) (kept : Model.Aff) :
    Quiet (Model.pscRow p S0 kept) := by
  unfold Model.pscRow
  infer_instance

/-- layerObject is quiet. -/
instance quiet_layerObject (o : Model.Level) : Quiet (Model.layerObject o) := by
  unfold Model.layerObject
  infer_instance

/-- An entry of a stored vector. -/
instance quiet_uEnt (t x : Nat) :
    Quiet (Model.uEnt t x) := by
  unfold Model.uEnt
  infer_instance

/-- The lookup's claims that read mask entries alone. -/
instance quiet_objects (g : Model.Forest.Heard) :
    Quiet (Model.Forest.objects g) := by
  unfold Model.Forest.objects
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _
    | refine quiet_foldlM _ ?_ _ _
    | refine quiet_forMA _ ?_ _

/-- Marking the claims on the planes. -/
instance quiet_planesAdded (g : Model.Forest.Heard) :
    Quiet (Model.Forest.planesAdded g) := by
  unfold Model.Forest.planesAdded
  infer_instance

/-- Marking the claim on the key vectors. -/
instance quiet_joinAdded (g : Model.Forest.Heard) :
    Quiet (Model.Forest.joinAdded g) := by
  unfold Model.Forest.joinAdded
  infer_instance

/-- The guard on the padding. -/
instance quiet_paddingLaid (g : Model.Forest.Heard) (laid : Array Nat) :
    Quiet (Model.Forest.paddingLaid g laid) := by
  unfold Model.Forest.paddingLaid
  infer_instance

/-- The claim on the key vectors. -/
instance quiet_join (g : Model.Forest.Heard) (KF : Array Model.Aff) :
    Quiet (Model.Forest.join g KF) := by
  unfold Model.Forest.join
  infer_instance

/-- The planes' value at a point, if reading a column is quiet. -/
instance quiet_planesAt (g : Model.Forest.Heard) (lm e : Nat) (bit : Nat → Nat → SubM Model.Aff)
    [∀ a b, Quiet (bit a b)] :
    Quiet (Model.Forest.planesAt g lm e bit) := by
  unfold Model.Forest.planesAt
  infer_instance

/-- The three claims that read the planes. -/
instance quiet_planeClaims (g : Model.Forest.Heard) (lm : Nat) (bit : Nat → Nat → SubM Model.Aff)
    (pin : Nat → SubM Model.Aff) [∀ a b, Quiet (bit a b)] [∀ a, Quiet (pin a)] :
    Quiet (Model.Forest.planeClaims g lm bit pin) := by
  unfold Model.Forest.planeClaims
  infer_instance

/-- Adding these three claims. -/
instance quiet_planeLins (g : Model.Forest.Heard) (lm : Nat) (bit : Nat → Nat → SubM Model.Aff)
    (pin : Nat → SubM Model.Aff) [∀ a b, Quiet (bit a b)] [∀ a, Quiet (pin a)] :
    Quiet (Model.Forest.planeLins g lm bit pin) := by
  unfold Model.Forest.planeLins
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _
    | refine quiet_foldlM _ ?_ _ _
    | refine quiet_forMA _ ?_ _

/-- Head.tabAt is quiet. -/
instance quiet_tabAt (R : Model.Head.Run) (n : String) :
    Quiet (Model.Head.tabAt R n) := by
  unfold Model.Head.tabAt
  infer_instance

/-- Head.U3at is quiet. -/
instance quiet_U3at (R : Model.Head.Run) (t i : Nat) :
    Quiet (Model.Head.U3at R t i) := by
  unfold Model.Head.U3at
  infer_instance

/-- Head.segOf is quiet. -/
instance quiet_segOf (R : Model.Head.Run) (sn : String) :
    Quiet (Model.Head.segOf R sn) := by
  unfold Model.Head.segOf
  infer_instance

/-- Head.ewOf is quiet. -/
instance quiet_ewOf (R : Model.Head.Run) (sn : String) :
    Quiet (Model.Head.ewOf R sn) := by
  unfold Model.Head.ewOf
  infer_instance

/-- Head.ewh is quiet. -/
instance quiet_ewh (R : Model.Head.Run) (sn : String) :
    Quiet (Model.Head.ewh R sn) := by
  unfold Model.Head.ewh
  infer_instance

/-- Head.Sl is quiet. -/
instance quiet_Sl (R : Model.Head.Run) (sn : String) (OFF nl J : Nat) :
    Quiet (Model.Head.Sl R sn OFF nl J) := by
  unfold Model.Head.Sl
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.xbA is quiet. -/
instance quiet_xbA (R : Model.Head.Run) (t kh : Nat) :
    Quiet (Model.Head.xbA R t kh) := by
  unfold Model.Head.xbA
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.sh2 is quiet. -/
instance quiet_sh2 (R : Model.Head.Run) (t j : Nat) :
    Quiet (Model.Head.sh2 R t j) := by
  unfold Model.Head.sh2
  infer_instance

/-- Head.rowAt is quiet. -/
instance quiet_rowAt (R : Model.Head.Run) (P : String) :
    Quiet (Model.Head.rowAt R P) := by
  unfold Model.Head.rowAt
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.row5At is quiet. -/
instance quiet_row5At (R : Model.Head.Run) (P : String) :
    Quiet (Model.Head.row5At R P) := by
  unfold Model.Head.row5At
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.gapAt is quiet. -/
instance quiet_gapAt (R : Model.Head.Run) (P : String) (i : Nat) (wsum : E) :
    Quiet (Model.Head.gapAt R P i wsum) := by
  unfold Model.Head.gapAt
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.ztSeg is quiet. -/
instance quiet_ztSeg (R : Model.Head.Run) (sn : String) :
    Quiet (Model.Head.ztSeg R sn) := by
  unfold Model.Head.ztSeg
  infer_instance

/-- Head.middleDigit is quiet. -/
instance quiet_middleDigit (R : Model.Head.Run) (sn : String) (wR : E) :
    Quiet (Model.Head.middleDigit R sn wR) := by
  unfold Model.Head.middleDigit
  infer_instance

/-- Head.lowDigit is quiet. -/
instance quiet_lowDigit (R : Model.Head.Run) (sn : String) (wR : E) :
    Quiet (Model.Head.lowDigit R sn wR) := by
  unfold Model.Head.lowDigit
  infer_instance

/-- Head.LINE is quiet. -/
instance quiet_LINE (R : Model.Head.Run) (sn : String) :
    Quiet (Model.Head.LINE R sn) := by
  unfold Model.Head.LINE
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _
    | refine quiet_foldlM _ ?_ _ _
    | refine quiet_forMA _ ?_ _
    | refine quiet_forML _ ?_ _
    | refine quiet_mapMA _ ?_ _
    | split

/-- Head.keyForm is quiet. -/
instance quiet_keyForm (R : Model.Head.Run) (q : Nat) (laid : Array Nat) :
    Quiet (Model.Head.keyForm R q laid) := by
  unfold Model.Head.keyForm
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_
    | refine quiet_forInS _ ?_ _ _

/-- Head.weightsClaim is quiet. -/
instance quiet_weightsClaim (R : Model.Head.Run) (wsLay : Model.WsLay) :
    Quiet (Model.Head.weightsClaim R wsLay) := by
  unfold Model.Head.weightsClaim
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _
    | refine quiet_foldlM _ ?_ _ _
    | refine quiet_forMA _ ?_ _
    | refine quiet_forML _ ?_ _
    | refine quiet_mapMA _ ?_ _
    | split

/-- Head.claimSquares is quiet. -/
instance quiet_claimSquares (R : Model.Head.Run) :
    Quiet (Model.Head.claimSquares R) := by
  unfold Model.Head.claimSquares
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.claimLedger5 is quiet. -/
instance quiet_claimLedger5 (R : Model.Head.Run) :
    Quiet (Model.Head.claimLedger5 R) := by
  unfold Model.Head.claimLedger5
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _

/-- Head.claimLedger4 is quiet. -/
instance quiet_claimLedger4 (R : Model.Head.Run) :
    Quiet (Model.Head.claimLedger4 R) := by
  unfold Model.Head.claimLedger4
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.claimLedger is quiet. -/
instance quiet_claimLedger (R : Model.Head.Run) :
    Quiet (Model.Head.claimLedger R) := by
  unfold Model.Head.claimLedger
  infer_instance

/-- Head.claimStream is quiet. -/
instance quiet_claimStream (R : Model.Head.Run) :
    Quiet (Model.Head.claimStream R) := by
  unfold Model.Head.claimStream
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.claimJoin is quiet. -/
instance quiet_claimJoin (R : Model.Head.Run) :
    Quiet (Model.Head.claimJoin R) := by
  unfold Model.Head.claimJoin
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.claimPolicy is quiet. -/
instance quiet_claimPolicy (R : Model.Head.Run) :
    Quiet (Model.Head.claimPolicy R) := by
  unfold Model.Head.claimPolicy
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.claimPlanes is quiet. -/
instance quiet_claimPlanes (R : Model.Head.Run) :
    Quiet (Model.Head.claimPlanes R) := by
  unfold Model.Head.claimPlanes
  infer_instance

/-- Head.claimLogits is quiet. -/
instance quiet_claimLogits (R : Model.Head.Run) :
    Quiet (Model.Head.claimLogits R) := by
  unfold Model.Head.claimLogits
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_

/-- Head.noteConstant is quiet. -/
instance quiet_noteConstant (group : String) :
    Quiet (Model.Head.noteConstant group) := by
  unfold Model.Head.noteConstant
  infer_instance

/-- Head.tablesOf is quiet. -/
instance quiet_tablesOf (h : Model.Head.Shape) (L : Model.Head.HL) (hp : Model.Head.HPlanH2)
    (cov : Model.Head.Covered) (x : Model.Head.Heard) :
    Quiet (Model.Head.tablesOf h L hp cov x) := by
  unfold Model.Head.tablesOf
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInR _ _ _ ?_
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _
    | refine quiet_foldlM _ ?_ _ _
    | refine quiet_forMA _ ?_ _
    | refine quiet_forML _ ?_ _
    | refine quiet_mapMA _ ?_ _
    | split

/-! ## The functions on the ledger, and their laws -/

section Laws

variable (R : Model.Head.Run)

/-- The head's tables of reads. -/
def flatTables (h : Model.Head.Shape) (L : Model.Head.HL) (hp : Model.Head.HPlanH2)
    (cov : Model.Head.Covered) (x : Model.Head.Heard) : Fork → Option (Model.Head.Tables × Fork) :=
  still (Model.Head.tablesOf h L hp cov x)

/-- The one claim on the committed weights. -/
def flatWeightsClaim (wsLay : Model.WsLay) : Fork → Option (Model.WsClaim × Fork) :=
  still (Model.Head.weightsClaim R wsLay)

/-- The lookup's claims that read mask entries alone. -/
def flatObjects (g : Model.Forest.Heard) : Fork → Option (Unit × Fork) :=
  still (Model.Forest.objects g)

def flatClaimSquares : Fork → Option (Unit × Fork) := still (Model.Head.claimSquares R)
def flatClaimLedger : Fork → Option (Unit × Fork) := still (Model.Head.claimLedger R)
def flatClaimStream : Fork → Option (Unit × Fork) := still (Model.Head.claimStream R)
def flatClaimJoin : Fork → Option (Unit × Fork) := still (Model.Head.claimJoin R)
def flatClaimPolicy : Fork → Option (Unit × Fork) := still (Model.Head.claimPolicy R)
def flatClaimPlanes : Fork → Option (Unit × Fork) := still (Model.Head.claimPlanes R)
def flatClaimLogits : Fork → Option (Unit × Fork) := still (Model.Head.claimLogits R)

/-- What it means that g is the routine m, in runs on a view: both directions, from any context;
and the context is left but for kept values. -/
def LawStill {α : Type} (m : SubM α) (g : Fork → Option (α × Fork)) : Prop :=
  ∀ (F G : Fork) (C : Ctx) (a : α), C.ch.dry = false →
    ((∃ D, (m F).Yields C (a, G) D) ↔ g F = some (a, G)) ∧
      ∀ D, (m F).Yields C (a, G) D → Blk.SameButNotes C D

theorem lawStill {α : Type} (m : SubM α) [Quiet m] : LawStill m (still m) :=
  fun F G C a hd => ⟨still_iff m F G C a hd, fun _ r => still_same m hd r⟩

theorem lawTables (h : Model.Head.Shape) (L : Model.Head.HL) (hp : Model.Head.HPlanH2)
    (cov : Model.Head.Covered) (x : Model.Head.Heard) :
    LawStill (Model.Head.tablesOf h L hp cov x) (flatTables h L hp cov x) := lawStill _

theorem lawWeightsClaim (wsLay : Model.WsLay) :
    LawStill (Model.Head.weightsClaim R wsLay) (flatWeightsClaim R wsLay) := lawStill _

theorem lawObjects (g : Model.Forest.Heard) :
    LawStill (Model.Forest.objects g) (flatObjects g) := lawStill _

theorem lawClaimSquares : LawStill (Model.Head.claimSquares R) (flatClaimSquares R) := lawStill _
theorem lawClaimLedger : LawStill (Model.Head.claimLedger R) (flatClaimLedger R) := lawStill _
theorem lawClaimStream : LawStill (Model.Head.claimStream R) (flatClaimStream R) := lawStill _
theorem lawClaimJoin : LawStill (Model.Head.claimJoin R) (flatClaimJoin R) := lawStill _
theorem lawClaimPolicy : LawStill (Model.Head.claimPolicy R) (flatClaimPolicy R) := lawStill _
theorem lawClaimPlanes : LawStill (Model.Head.claimPlanes R) (flatClaimPlanes R) := lawStill _
theorem lawClaimLogits : LawStill (Model.Head.claimLogits R) (flatClaimLogits R) := lawStill _

end Laws

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.lawTables
#print axioms OnBytes.K.Kc.lawWeightsClaim
#print axioms OnBytes.K.Kc.lawObjects
#print axioms OnBytes.K.Kc.lawClaimSquares
#print axioms OnBytes.K.Kc.lawClaimLedger
#print axioms OnBytes.K.Kc.lawClaimStream
#print axioms OnBytes.K.Kc.lawClaimJoin
#print axioms OnBytes.K.Kc.lawClaimPolicy
#print axioms OnBytes.K.Kc.lawClaimPlanes
#print axioms OnBytes.K.Kc.lawClaimLogits
