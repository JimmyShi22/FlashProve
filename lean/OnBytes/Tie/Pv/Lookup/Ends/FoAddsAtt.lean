-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAddsAtt.lean.
The attention sub-proof: how many claims the routines claim3 to claim8 and their parts add.

States, each as Fo.Adds with the number as a term in the record of what was heard:
  linPlanes (one for each plane of the plane claim), callKR (cntKR), claim3 (cnt3), endValues (2),
  unitKFD (cntUnit), callKFD (cntKFD), claim4 (cnt4), endValuesE (2), claim5 (cnt5), valueProduct,
  claim6 (cnt6), claim7 (cnt7), claim8 (cnt8).
  Adds.qbind, AddsR.qbind, AddsR.abind, AddsR.yield: further rules for putting routines together.
Limit: a number of claims pins no claim (the head of OnBytes/Tie/Pv/Lookup/Ends/FoAdds.lean).
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns, or which claims are added.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsAttQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

section
variable {α β : Type}

theorem Adds.qbind {x : SubM α} {f : α → SubM β} {n : ℕ} (hx : Quiet x) (hf : ∀ a, Adds (f a) n) :
    Adds (x >>= f) n := (Adds.bind hx hf).cast (Nat.zero_add n)

theorem AddsR.qbind {x : SubM α} {f : α → SubM β} {n : ℕ} {post : β → Prop} (hx : Quiet x)
    (hf : ∀ a, AddsR (f a) n post) : AddsR (x >>= f) n post :=
  (AddsR.bind hx fun a _ => hf a).cast (Nat.zero_add n)

theorem AddsR.abind {x : SubM α} {f : α → SubM β} {n m : ℕ} {post : β → Prop} (hx : Adds x n)
    (hf : ∀ a, AddsR (f a) m post) : AddsR (x >>= f) (n + m) post :=
  AddsR.bind hx fun a _ => hf a

/-- The end of a loop's body. -/
theorem AddsR.yield {σ : Type} (s : σ) :
    AddsR (Pure.pure (ForInStep.yield s) : SubM (ForInStep σ)) 0 fun r => ∃ b, r = .yield b :=
  AddsR.pure _ ⟨s, rfl⟩

end

theorem adds_linPlanes (h : Attention.Heard) (pc : PlaneClaim) : Adds (linPlanes h pc) pc.np := by
  unfold linPlanes
  refine (Adds.forM (k := fun _ => 1) (fun x => ?_) _).cast ?_
  · exact Adds.qbind (quiet_lessPieces _ _ _ fun _ => quiet_plane _ _ _ _ _ _ _) fun _ => Adds.lin _
  · rw [sum_const, List.length_range, Nat.mul_one]

/-- The claims that call q, of kind KR, adds. -/
def cntKR (h : Attention.Heard) (q : ℕ) : ℕ :=
  (h.planes.toList.map fun pc => if pc.call == q then pc.np else 0).sum

theorem adds_callKR (h : Attention.Heard) (q : ℕ) : Adds (callKR h q) (cntKR h q) := by
  unfold callKR cntKR
  refine Adds.arrayFoldlM (k := fun pc : PlaneClaim => if pc.call == q then pc.np else 0)
    (fun v pc => ?_) _ _
  exact Adds.ite ((Adds.bind (adds_linPlanes h pc) fun _ => Adds.pure _).cast (Nat.add_zero _))
    (Adds.pure _)

def cnt3 (h : Attention.Heard) : ℕ :=
  (h.S.calls.toList.zipIdx.map fun x => if x.1.kind == .kr then cntKR h x.2 else 0).sum

theorem adds_claim3 (h : Attention.Heard) (j : Joins) : Adds (claim3 h j) (cnt3 h) := by
  unfold claim3 cnt3
  refine Adds.foldlM (k := fun x : ACall × ℕ => if x.1.kind == Table.kr then cntKR h x.2 else 0)
    (fun j x => ?_) _ _
  exact Adds.ite ((Adds.bind (adds_callKR h x.2) fun _ => Adds.pure _).cast (Nat.add_zero _))
    (Adds.pure _)

theorem adds_endValues (h : Attention.Heard) (k : Score) (tb : ScoreTables) (rc : Array E) (b : ℕ)
    (w : PW) : Adds (endValues h k tb rc b w) 2 := by
  unfold endValues
  exact Adds.qbind (quiet_readHead _ _ _ _ _ _ _) fun _ => Adds.bind (n := 1) (m := 1) (Adds.lin _)
    fun _ => Adds.qbind (quiet_readGroup _ _ _ _ _ _) fun _ => Adds.lin _

/-- The claims of one unit of a call of kind KFD. -/
def cntUnit (h : Attention.Heard) (k : Score) : ℕ :=
  ((h.planes[k.claim]?).map (·.np)).getD 0 + (2 + 2 * k.pw.size)

theorem adds_unitKFD (h : Attention.Heard) (i : ℕ) (k : Score) :
    Adds (unitKFD h i k) (cntUnit h k) := by
  unfold unitKFD cntUnit
  refine Adds.qbind (Quiet.getO _) fun tb => ?_
  refine (AddsR.bind (AddsR.getO _) fun pc hpc => ?_).cast (Nat.zero_add _)
  rw [hpc]
  show Adds _ (pc.np + (2 + 2 * k.pw.size))
  refine Adds.bind (adds_linPlanes h pc) fun _ => ?_
  refine Adds.qbind (quiet_lessPieces _ _ _ fun _ => quiet_readMaximum _ _ _ _ _) fun _ => ?_
  refine (Adds.bind (n := 1) (Adds.lin _) fun _ => Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.forM (k := fun _ => 2) (fun x => adds_endValues _ _ _ _ _ _) _).cast ?_
  rw [sum_const, List.length_zipIdx, Array.length_toList]
  omega

/-- The claims that call q, of kind KFD, adds. -/
def cntKFD (h : Attention.Heard) (q : ℕ) : ℕ :=
  (h.scores.toList.zipIdx.map fun x => if x.1.call == q then cntUnit h x.1 else 0).sum

theorem adds_callKFD (h : Attention.Heard) (q : ℕ) (c : ACall) :
    Adds (callKFD h q c) (cntKFD h q) := by
  unfold callKFD cntKFD
  refine Adds.foldlM (k := fun x : Score × ℕ => if x.1.call == q then cntUnit h x.1 else 0)
    (fun v x => ?_) _ _
  exact Adds.ite ((Adds.bind (adds_unitKFD h x.2 x.1) fun _ => Adds.pure _).cast (Nat.add_zero _))
    (Adds.pure _)

def cnt4 (h : Attention.Heard) : ℕ :=
  (h.S.calls.toList.zipIdx.map fun x => if x.1.kind == .kfd then cntKFD h x.2 else 0).sum

theorem adds_claim4 (h : Attention.Heard) (j : Joins) : Adds (claim4 h j) (cnt4 h) := by
  unfold claim4 cnt4
  refine Adds.foldlM (k := fun x : ACall × ℕ => if x.1.kind == Table.kfd then cntKFD h x.2 else 0)
    (fun j x => ?_) _ _
  exact Adds.ite ((Adds.bind (adds_callKFD h x.2 x.1) fun _ => Adds.pure _).cast (Nat.add_zero _))
    (Adds.pure _)

theorem adds_endValuesE (h : Attention.Heard) (b : ℕ) (w : PW) : Adds (endValuesE h b w) 2 := by
  unfold endValuesE
  exact Adds.qbind (quiet_readDenominator _ _ _ _ _) fun _ =>
    Adds.bind (n := 1) (m := 1) (Adds.lin _) fun _ =>
      Adds.qbind (quiet_readHead _ _ _ _ _ _ _) fun _ => Adds.lin _

def cnt5 (h : Attention.Heard) : ℕ := 3 + h.S.cf.lt + 3 + 2 * h.S.NP

theorem adds_claim5 (h : Attention.Heard) (j : Joins) : Adds (claim5 h j) (cnt5 h) := by
  unfold claim5 cnt5
  refine Adds.qbind (quiet_lessPieces _ _ _ fun _ => quiet_readDenominator _ _ _ _ _) fun _ => ?_
  refine Adds.qbind (quiet_lessPieces _ _ _ fun _ => quiet_readHead _ _ _ _ _ _ _) fun _ => ?_
  refine Adds.qbind (quiet_lessPieces _ _ _ fun _ => quiet_readHead _ _ _ _ _ _ _) fun _ => ?_
  refine Adds.qbind (quiet_lessPieces _ _ _ fun _ => quiet_readHead _ _ _ _ _ _ _) fun _ => ?_
  refine Adds.qbind (quiet_lessPieces _ _ _ fun _ => quiet_readHead _ _ _ _ _ _ _) fun _ => ?_
  refine (Adds.bind (n := 1) (Adds.lin _) fun _ => Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (Adds.forIn (k := fun _ => 1) (fun k s => ?_) _ _) fun _ =>
    Adds.bind (n := 1) (Adds.lin _) fun _ => Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (Adds.forIn (k := fun _ => 2) (fun b s => ?_) _ _) fun _ => Adds.pure _).cast ?_
  · exact AddsR.qbind (quiet_lessPieces _ _ _ fun _ => quiet_readIndexBit _ _ _ _ _ _) fun _ =>
      (AddsR.abind (Adds.lin _) fun _ => AddsR.yield _).cast (Nat.add_zero 1)
  · exact (AddsR.abind (adds_endValuesE _ _ _) fun _ => AddsR.yield _).cast (Nat.add_zero 2)
  · rw [sum_const, sum_const, List.length_range, List.length_range]
    omega

theorem adds_valueProduct (h : Attention.Heard) (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool)
    (tV : ℕ) : Adds (valueProduct h sc tS pt isD tV) (1 + 2 * h.S.NP) := by
  unfold valueProduct
  refine (Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (Adds.forIn (k := fun _ => 2) (fun b s => ?_) _ _) fun _ => Adds.pure _).cast ?_
  · exact AddsR.qbind (quiet_plane _ _ _ _ _ _ _) fun _ =>
      AddsR.qbind (quiet_plane _ _ _ _ _ _ _) fun _ =>
      AddsR.abind (n := 1) (m := 1) (Adds.lin _) fun _ =>
      AddsR.qbind (quiet_readGroup _ _ _ _ _ _) fun _ =>
      (AddsR.abind (Adds.lin _) fun _ => AddsR.yield _).cast (Nat.add_zero 1)
  · rw [sum_const, List.length_range]
    omega

def cnt6 (h : Attention.Heard) : ℕ := 1 + 2 * (1 + 2 * h.S.NP)

theorem adds_claim6 (h : Attention.Heard) : Adds (claim6 h) (cnt6 h) := by
  unfold claim6 cnt6
  refine (Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (adds_valueProduct _ _ _ _ _ _) fun _ => adds_valueProduct _ _ _ _ _ _).cast ?_
  omega

def cnt7 (h : Attention.Heard) : ℕ :=
  h.S.NP + 1 + h.S.NP + 1 + h.S.Lam + h.S.NP * h.S.cf.lt

theorem adds_claim7 (h : Attention.Heard) : Adds (claim7 h) (cnt7 h) := by
  unfold claim7 cnt7
  refine (Adds.bind (Adds.forIn (k := fun _ => 1) (fun b s => ?_) _ _) fun _ =>
    Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (Adds.forIn (k := fun _ => 1) (fun b s => ?_) _ _) fun _ =>
    Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (Adds.forIn (k := fun _ => 1) (fun b s => ?_) _ _) fun _ =>
    Adds.bind (Adds.forIn (k := fun _ => h.S.cf.lt) (fun b s => ?_) _ _) fun _ =>
    Adds.pure _).cast ?_
  · exact AddsR.qbind (quiet_readMaximum _ _ _ _ _) fun _ =>
      (AddsR.abind (Adds.lin _) fun _ => AddsR.yield _).cast (Nat.add_zero 1)
  · exact AddsR.qbind (quiet_readHead _ _ _ _ _ _ _) fun _ =>
      (AddsR.abind (Adds.lin _) fun _ => AddsR.yield _).cast (Nat.add_zero 1)
  · exact AddsR.qbind (quiet_readGroup _ _ _ _ _ _) fun _ =>
      (AddsR.abind (Adds.lin _) fun _ => AddsR.yield _).cast (Nat.add_zero 1)
  · refine (AddsR.abind (Adds.forIn (k := fun _ => 1) (fun k s => ?_) _ _) fun _ =>
      AddsR.yield _).cast ?_
    · exact AddsR.qbind (quiet_readIndexBit _ _ _ _ _ _) fun _ =>
        (AddsR.abind (Adds.lin _) fun _ => AddsR.yield _).cast (Nat.add_zero 1)
    · show _ = h.S.cf.lt
      rw [sum_const, List.length_range]
      omega
  · simp only [sum_const, List.length_range]
    ring

def cnt8 (h : Attention.Heard) : ℕ := 1 + 2 * h.S.NP

theorem adds_claim8 (h : Attention.Heard) : Adds (claim8 h) (cnt8 h) := by
  unfold claim8 cnt8
  refine (Adds.bind (n := 1) (Adds.lin _) fun _ =>
    Adds.bind (Adds.forIn (k := fun _ => 2) (fun b s => ?_) _ _) fun _ => Adds.pure _).cast ?_
  · refine AddsR.abind (n := 1) (m := 1) (Adds.lin _) fun _ => ?_
    refine AddsR.qbind (Quiet.foldlM (fun _ _ =>
      (quiet_readIndexBit _ _ _ _ _ _).bind fun _ => Quiet.pure _) _ _) fun _ => ?_
    exact (AddsR.abind (Adds.lin _) fun _ => AddsR.yield _).cast (Nat.add_zero 1)
  · rw [sum_const, List.length_range]
    omega

end Fo
