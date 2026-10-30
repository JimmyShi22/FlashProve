-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlannedAtRch.lean: `planned_at_draw` AND `planned_at_batch`
(PlannedAtDraw.lean) AT THE PICKED «REACHED» (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean), AND WHAT
THEY GIVE FOR THE TEST `sortsB`. Theorems. No text already in the library turns.

  `planned_draw_rch`, `planned_batch_rch`: in scope, at `IM.Open … secondHashFunction`: at every a with
    RchAt ‹the proof file's description› k a, k the draw's number | the batching's entry's number of
    link l: readTl g a.1.2 = some (g Xl.tl), Xl the built link number l, g any `Planned` reading.
  `planned_five`: the five fields that `sortsB` reads are such a reading (four times rfl).
  `sorts_at_batch`: **so: sortsB sh Xl.tl = true ⊢ SortsAt sh a.1.2 at every state reached at the
    batching's entry's number**: a Bool on the plan pays it.
Limits. IN FRONT OF the batching: the batching's own step, and the runs behind it, are not treated
here (the runs: `rests_sorts`, TotalMoves.lean). In scope, at secondHashFunction alone. No member. Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.PlannedAtDraw
import Johnson.Desc.First.Link.Law.SortsFive
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (readTl)
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open ProofFile (Cl)

variable {α : Type} {g : HTailF2 → α}
  {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem planned_draw_rch (hg : Planned g) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ P1K8S.places) {Xl : LinkH} (e3 : Bs.G₀.built[x.1]? = some Xl)
    {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2 + 2) a) : readTl g a.1.2 = some (g Xl.tl) :=
  planned_at_draw hg hS hR O hx e3 a.1 (rchAt_raw h)

theorem planned_batch_rch (hg : Planned g) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a) : readTl g a.1.2 = some (g Xl.tl) :=
  planned_at_batch hg hS hR O hx e3 a.1 (rchAt_raw h)

theorem planned_five : Planned five :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- **A Bool on the plan pays `SortsAt` in front of the batching.** -/
theorem sorts_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {sh : List Look} (hB : sortsB sh Xl.tl = true)
    {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a) : SortsAt sh a.1.2 :=
  sortsAt_of_five (planned_batch_rch planned_five hS hR O hx e3 a h) hB

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.planned_draw_rch
#print axioms VerifiableInference.Desc.LinkJoin.planned_batch_rch
#print axioms VerifiableInference.Desc.LinkJoin.planned_five
#print axioms VerifiableInference.Desc.LinkJoin.sorts_at_batch
