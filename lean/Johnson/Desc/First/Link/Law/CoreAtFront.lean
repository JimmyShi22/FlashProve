-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CoreAtFront.lean: `OkCore` (OkOne.lean) AT EVERY STATE REACHED IN FRONT
OF A LINK's BATCHING, WITH NONE OF ITS EIGHT CLAUSES LEFT AS A PREMISE. A structure and three
theorems: a joining.
Why. CoreAtBatch.lean keeps seven fields; two of them are heavy: led (the ledger's sizes at EVERY
state reached one step earlier) and pos (the clause itself). FourOfPromise.lean has four and ents4
from the ledger at the state itself; PosAtBatch.lean has pos from one closed sentence on the plan.
CoreAtBatch.lean stands beside this file.
  `OkCoreLess c Xl tlD s`: WHAT IS LEFT. From the table's promise, at the state s: part: K9's part
    is there; ledger: a ledger is open and has its sizes. Closed, at the built segment Xl: static,
    dig, fits. plan: every sub-protocol of the first chain passes its test on the plan.
  `core_layers_front`, `core_att_front`, `core_head_front`: **`OkCore nU tlD (fixed9 (phiAll u ψ)
    a.1.2)` at a reached at 28 g + 9, at 14 (2 g + 1) + 9 (g < 12), at 347**, from `OkCoreLess` and
    H: `PosPlan` (PosAtBatch.lean) of the built segment at the sort's own skeleton of the list of
    tables: a closed sentence.
Limits. A JOINING: NOTHING IS PAID BY THIS FILE. `OkCoreLess` and H are shown of nothing here. THE
CORE IS NOT THE WHOLE DEBT OF A LINK: the sorts' own clauses, and what the payers of the fields that
stand under Ok ask of it (OkOne.lean's head), stand beside it. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OkOne
import Johnson.Desc.First.Link.Law.FitsAtBatch
import Johnson.Desc.First.Link.Law.FourOfPromise
import Johnson.Desc.First.Link.Law.PosAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized)
open OnBytes.Tie.Pv.Tail.Port (Fits)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.Walk.Tied (Reach rchAt_raw)
open ProofFile (Cl)

/-- **WHAT IS LEFT OF `OkCore` AT A STATE IN FRONT OF A BATCHING.** -/
structure OkCoreLess (c : Chain S Cl) (Xl : LinkH) (tlD : HTailF2) (s : S) : Prop where
  /-- from the table's promise, at the state: K9's part is there -/
  part : (atS.get? s).isSome = true
  /-- from the table's promise, at the state: a ledger is open and has its sizes -/
  ledger : ∃ G', s.fork? = some G' ∧ Sized G'
  /-- closed, at the built segment -/
  static : StaticOk Xl.tl Xl.Fp
  dig : DigStatic tlD Xl.tl Xl.Fp
  fits : Fits Xl.tl
  /-- every sub-protocol of the first chain passes its test on the plan -/
  plan : ∀ b ∈ c.blocksInOrder, b.planOk = true

variable {β : Type} {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`OkCore` IN FRONT OF A LAYERS' LINK's BATCHING.** -/
theorem core_layers_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (28 * g + 9) a)
    (nU : Array ℕ) (tlD u : HTailF2) (ψ : S → β) (Lf : OkCoreLess c Xl tlD a.1.2)
    (H : PosPlan Xl.tl Xl.Fp (layShapes Bs.G₀.W.layers g)) :
    OkCore nU tlD (fixed9 (phiAll u ψ) a.1.2) := by
  have hx : ((2 * g, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩
  have e : 28 * g + 9 = 14 * (2 * g) + 9 := by omega
  have h' : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * ((2 * g, 4, 2) : ℕ × ℕ × ℕ).1 + ((2 * g, 4, 2) : ℕ × ℕ × ℕ).2.1 + 3 +
        ((2 * g, 4, 2) : ℕ × ℕ × ℕ).2.2) a := e ▸ h
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 9) (a.1.1, a.1.2) := by
    rw [← e]
    exact rchAt_raw h
  have K := ok_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) tlD Lf.part Lf.static
    Lf.dig
  have Q := four_of_promise hS hR O Lf.plan (by omega : 2 * g < 24) hr Lf.ledger pi8 (phiAll u ψ) u
    (fun _ => rfl)
  exact ⟨(snap_there_of_part u ψ a.1.2 Lf.part).1, (snap_there_of_part u ψ a.1.2 Lf.part).2,
    K.1.2, fits_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) Lf.fits, K.2,
    pos_layers hS hR O hg e3 a h pi8 (phiAll u ψ) u (fun _ => rfl) H, Q.1, Q.2⟩

/-- **`OkCore` IN FRONT OF AN ATTENTION LINK's BATCHING.** -/
theorem core_att_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * (2 * g + 1) + 9) a)
    (nU : Array ℕ) (tlD u : HTailF2) (ψ : S → β) (Lf : OkCoreLess c Xl tlD a.1.2)
    (H : ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S))) :
    OkCore nU tlD (fixed9 (phiAll u ψ) a.1.2) := by
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩
  have h' : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ).1 + ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ).2.1 + 3 +
        ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ).2.2) a := h
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (a.1.1, a.1.2) := rchAt_raw h
  have K := ok_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) tlD Lf.part Lf.static
    Lf.dig
  have Q := four_of_promise hS hR O Lf.plan (by omega : 2 * g + 1 < 24) hr Lf.ledger pi8
    (phiAll u ψ) u (fun _ => rfl)
  exact ⟨(snap_there_of_part u ψ a.1.2 Lf.part).1, (snap_there_of_part u ψ a.1.2 Lf.part).2,
    K.1.2, fits_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) Lf.fits, K.2,
    pos_att hS hR O hg e3 a h pi8 (phiAll u ψ) u (fun _ => rfl) H, Q.1, Q.2⟩

/-- **`OkCore` IN FRONT OF THE HEAD's BATCHING.** -/
theorem core_head_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      347 a)
    (nU : Array ℕ) (tlD u : HTailF2) (ψ : S → β) (Lf : OkCoreLess c Xl tlD a.1.2)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs)) :
    OkCore nU tlD (fixed9 (phiAll u ψ) a.1.2) := by
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches := by decide
  have h' : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * ((24, 5, 3) : ℕ × ℕ × ℕ).1 + ((24, 5, 3) : ℕ × ℕ × ℕ).2.1 + 3 +
        ((24, 5, 3) : ℕ × ℕ × ℕ).2.2) a := h
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (a.1.1, a.1.2) := rchAt_raw h
  have K := ok_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) tlD Lf.part Lf.static
    Lf.dig
  have Q := four_of_promise_head hS hR O Lf.plan hr Lf.ledger pi8 (phiAll u ψ) u (fun _ => rfl)
  exact ⟨(snap_there_of_part u ψ a.1.2 Lf.part).1, (snap_there_of_part u ψ a.1.2 Lf.part).2,
    K.1.2, fits_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) Lf.fits, K.2,
    pos_head hS hR O e3 a h pi8 (phiAll u ψ) u (fun _ => rfl) H, Q.1, Q.2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.core_layers_front
#print axioms VerifiableInference.Desc.LinkJoin.core_att_front
#print axioms VerifiableInference.Desc.LinkJoin.core_head_front
