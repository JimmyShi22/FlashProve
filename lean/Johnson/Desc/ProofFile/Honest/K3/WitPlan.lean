-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitPlan.lean: the honest side of the kind "lookup" (K3): a filling
of the letters `Sources` (Honest/K3/Wit.lean) that goes by the public part's own numbers, so at any
number of groups; and that at the full size it is the filling of Honest/K3/WitFill.lean, conditional
on one public hypothesis. Definitions with code, and theorems.

Terms. Honest/K3/GLOSSARY.md: see there sources, filling, cells, link, public part and full size. In
this file: WitFill.lean reads a matrix by a label that is found by written numbers (twelve groups;
the head is segment 24). Here a matrix of a link's list is named by the verifier's own plan: entry a
of the list of matrices of the link's smallness test (`TMat.name`, OnBytes/Model/Frame.lean), and a
link's number is made of the public part's flag for attention links and its number of groups, as the
verifier's own split of the links has it (`First.Look.lookAt`, Johnson/Desc/First/Look/LookAt.lean).

What is defined and shown.
  `nameAt`, `atMats`, `planG`, `planA`, `planH`: the readings of the library's names, of a list of
    matrices.
  `inG`, `inA`, `inH`: the library's keys and bits at them, of the structures that these terms read.
  `stepOf`, `linkG`, `linkA`, `linkH`, `tlOf`: the links' numbers; the structure of a link's
    smallness test. They write out the split of `First.Look.lookAt`; `tlOf` writes out the library's
    `First.Look.tlAt` (Johnson/Desc/First/Look/Laid.lean), with the empty structure where that
    returns nothing: the tie is `tlOf_eq_tlAt` (Honest/K3/Law/TiesSealed.lean). A tie at the digits
    is `lookAt_digits` (Honest/K3/Law/SiteShapes.lean): where `lookAt X i true` returns a place, its
    shape is that of `tlOf X i`.
  `planSources`: the filling.
  `PlanLabels`, `planSources_eq`: the public hypothesis; conditionally on it, at the full size the
    filling is that of WitFill.lean. On the way: `step_full`, `atMats_eq`, `planG_eq`, `planA_eq`,
    `planH_eq`, `tlOf_eq`.

Hypotheses that remain.
  `B`: `PlanLabels X`, public: attention links stand between the layers'; twelve groups; at each of
    the 25 links entry a of the plan's list bears the label that `labelAt`
    (Johnson/HonestTrace/FromCells.lean) gives the number a, and the list ends where the labels end.
  `hk`, `hg`: the link is below 25; the group is below 12.

Users. Honest/K3/WitDigits.lean, Honest/K3/WitFillToy.lean [not in this library] and
Honest/K3/WitRiderToy.lean [not in this library] import this file.

Limits. `PlanLabels` is a hypothesis here; the trace's files prove the labels of the plans'
entries in the goals' scope, in files that this one does not import. Evaluated in part:
Honest/K3/Law/WitOwnerMember.lean [not in this library]: `labelsOk`, a test with code for it,
accepts at one synthetic public part at the full size's numbers. What stays open: that public part
is synthetic. No theorem is stated at another size than the full one. ZZ is a letter; the head's
public data depend on the instance through a letter. A borrowed matrix is read at the borrower's
link under the borrower's name. Where the public part has no attention links (`stepOf` = 1)
`linkA X g` is `linkG X (g + 1)`: there the filling's field for attention would read the next
group's layers' list (at the last group: the head's), and has no meaning.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.HonestTrace (fromG fromA fromH fsAt labelAt atNo)
open OnBytes.Road (Hd.shapeA)

/-! ## 1 The readings -/

/-- The name of matrix number a of a plan's list; none beyond the list. -/
def nameAt (mats : Array OnBytes.Model.TMat) (a : ℕ) : Option String := (mats[a]?).map (·.name)

/-- The cell (r, c) of matrix number a of the link's list, read by the plan's name, in the extension
field; 0 beyond the list. -/
def atMats (mats : Array OnBytes.Model.TMat) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (link a r c : ℕ) : Cb.Gl.E :=
  match nameAt mats a with
  | some s => algebraMap Cb.Gl.F Cb.Gl.E (cell link s r c)
  | none => 0

def planG (mats : Array OnBytes.Model.TMat) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) : OnBytes.Ends.G.NameG → Cb.Gl.E
  | .cell a r c => atMats mats cell link a r c
  | .w r c => algebraMap Cb.Gl.F Cb.Gl.E (entry r c)

def planA (mats : Array OnBytes.Model.TMat) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (link : ℕ) :
    OnBytes.Ends.NameA → Cb.Gl.E := fun n => atMats mats cell link n.M n.r n.c

def planH (mats : Array OnBytes.Model.TMat) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) : OnBytes.Ends.H.NameH → Cb.Gl.E
  | .cell a r c => atMats mats cell link a r c
  | .w r c => algebraMap Cb.Gl.F Cb.Gl.E (entry r c)

/-! ## 2 The library's keys and bits at them -/

def inG (P : OnBytes.Model.Layer.Pub) (g link : ℕ) (mats : Array OnBytes.Model.TMat) (C : Cells)
    (W : Weights) : LookIn :=
  ⟨fun theta n => OnBytes.Ends.G.keyG P g (planG mats C.cell W.entry link) theta n,
   fun u j => OnBytes.Ends.G.bitsG P.y (planG mats C.cell W.entry link) (u * 32 + j)⟩

def inA (S : OnBytes.Attention.Shape) (fs : OnBytes.Model.Forest.Shape) (link : ℕ)
    (mats : Array OnBytes.Model.TMat) (C : Cells) : LookIn :=
  ⟨fun theta n => OnBytes.Ends.A.keyA S fs (planA mats C.cell link) theta n,
   fun u j => OnBytes.Ends.A.bitsA S fs (planA mats C.cell link) (u * 32 + j)⟩

def inH (P : OnBytes.Ends.H.PubH) (link : ℕ) (mats : Array OnBytes.Model.TMat) (C : Cells)
    (W : Weights) : LookIn :=
  ⟨fun theta n => OnBytes.Ends.H.keyH P (planH mats C.cell W.entry link) theta n,
   fun u j => OnBytes.Ends.H.bitsH P.h P.L.fs (planH mats C.cell W.entry link) (u * 32 + j)⟩

/-! ## 3 The links -/

/-- 2 where attention links stand between the layers' links; else 1. -/
def stepOf (X : OnBytes.Model.Verify.Public) : ℕ := if X.p4 then 2 else 1

def linkG (X : OnBytes.Model.Verify.Public) (g : ℕ) : ℕ := stepOf X * g
def linkA (X : OnBytes.Model.Verify.Public) (g : ℕ) : ℕ := stepOf X * g + 1
def linkH (X : OnBytes.Model.Verify.Public) : ℕ := stepOf X * X.NGr

/-- The structure of the smallness test of a link, by the verifier's own split of the links; the
empty structure where the public part has no such plan. -/
def tlOf (X : OnBytes.Model.Verify.Public) (link : ℕ) : OnBytes.Model.HTailF2 :=
  if link == linkH X then X.H.tl
  else if link % stepOf X == 0 then ((X.G[link / stepOf X]?).map (·.tl)).getD {}
  else ((X.A[link / stepOf X]?).map (·.seam.tl)).getD {}

/-! ## 4 The filling -/

/-- **The filling by the public part's own numbers.** The letters are as in `fullSources`. -/
def planSources {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH)
    (zzOf : ℕ → Cells → List Int → ℕ → ℕ → Cb.Gl.F) : Sources W₀ Xi Tr' :=
  { cells := cells
    weights := weights
    layers := fun g => inG X.layers g (linkG X g) (tlOf X (linkG X g)).mats
    attention := fun g => inA (Hd.shapeA X g) (fsAt X g) (linkA X g) (tlOf X (linkA X g)).mats
    head := fun x => inH (pubH x) (linkH X) (tlOf X (linkH X)).mats
    digits := fun link C ts => lookZ (tlOf X link) (zzOf link C ts) }

/-! ## 5 At the full size -/

/-- **The public hypothesis.** -/
structure PlanLabels (X : OnBytes.Model.Verify.Public) : Prop where
  p4 : X.p4 = true
  groups : X.NGr = 12
  names : ∀ k < 25, ∀ a, nameAt (tlOf X k).mats a = labelAt X k a

section
variable {X : OnBytes.Model.Verify.Public}

theorem step_full (B : PlanLabels X) : stepOf X = 2 := by
  unfold stepOf
  rw [B.p4]
  rfl

theorem atMats_eq (B : PlanLabels X) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) {k : ℕ} (hk : k < 25)
    (a r c : ℕ) : atMats (tlOf X k).mats cell k a r c = atNo X cell k a r c := by
  unfold atMats atNo
  rw [B.names k hk a]
  cases labelAt X k a <;> rfl

theorem planG_eq (B : PlanLabels X) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) {g : ℕ} (hg : g < 12) :
    planG (tlOf X (linkG X g)).mats cell entry (linkG X g) = fromG X cell entry g := by
  have e : linkG X g = 2 * g := by unfold linkG; rw [step_full B]
  rw [e]
  funext n
  cases n with
  | cell a r c => exact atMats_eq B cell (by omega) a r c
  | w r c => rfl

theorem planA_eq (B : PlanLabels X) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) {g : ℕ} (hg : g < 12) :
    planA (tlOf X (linkA X g)).mats cell (linkA X g) = fromA X cell g := by
  have e : linkA X g = 2 * g + 1 := by unfold linkA; rw [step_full B]
  rw [e]
  funext n
  exact atMats_eq B cell (by omega) n.M n.r n.c

theorem planH_eq (B : PlanLabels X) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) :
    planH (tlOf X (linkH X)).mats cell entry (linkH X) = fromH X cell entry := by
  have e : linkH X = 24 := by unfold linkH; rw [step_full B, B.groups]
  rw [e]
  funext n
  cases n with
  | cell a r c => exact atMats_eq B cell (by omega) a r c
  | w r c => rfl

theorem tlOf_eq (B : PlanLabels X) (link : ℕ) : tlOf X link = tlAt X link := by
  have e : linkH X = 24 := by unfold linkH; rw [step_full B, B.groups]
  unfold tlOf tlAt
  rw [e, step_full B]
  by_cases h1 : link = 24
  · simp [h1]
  · by_cases h2 : link % 2 = 0 <;> simp [h1, h2]

/-- **At the full size, at the groups below 12, the two fillings are one.** Conditional on
`PlanLabels X` (public). No instance of these hypotheses is exhibited in this file. The trace's
files prove the plans' labels in the goals' scope, in files that this one does not import. -/
theorem planSources_eq {W₀ Xi Tr' : Type} (B : PlanLabels X) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH)
    (zzOf : ℕ → Cells → List Int → ℕ → ℕ → Cb.Gl.F) :
    (∀ g < 12, (planSources X cells weights pubH zzOf).layers g =
        (fullSources X cells weights pubH zzOf).layers g) ∧
      (∀ g < 12, (planSources X cells weights pubH zzOf).attention g =
        (fullSources X cells weights pubH zzOf).attention g) ∧
      (planSources X cells weights pubH zzOf).head = (fullSources X cells weights pubH zzOf).head ∧
      (planSources X cells weights pubH zzOf).digits =
        (fullSources X cells weights pubH zzOf).digits := by
  refine ⟨fun g hg => ?_, fun g hg => ?_, ?_, ?_⟩
  · funext C W
    show inG X.layers g (linkG X g) (tlOf X (linkG X g)).mats C W = lookG X g C W
    unfold inG lookG
    rw [planG_eq B C.cell W.entry hg]
    rfl
  · funext C
    show inA (Hd.shapeA X g) (fsAt X g) (linkA X g) (tlOf X (linkA X g)).mats C = lookA X g C
    unfold inA lookA
    rw [planA_eq B C.cell hg]
  · funext x C W
    show inH (pubH x) (linkH X) (tlOf X (linkH X)).mats C W = lookH X (pubH x) C W
    unfold inH lookH
    rw [planH_eq B C.cell W.entry]
  · funext link C ts
    show lookZ (tlOf X link) (zzOf link C ts) = lookZ (tlAt X link) (zzOf link C ts)
    rw [tlOf_eq B]

end

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.step_full
#print axioms ProofFile.Honest.K3.atMats_eq
#print axioms ProofFile.Honest.K3.planG_eq
#print axioms ProofFile.Honest.K3.planA_eq
#print axioms ProofFile.Honest.K3.planH_eq
#print axioms ProofFile.Honest.K3.tlOf_eq
#print axioms ProofFile.Honest.K3.planSources_eq
