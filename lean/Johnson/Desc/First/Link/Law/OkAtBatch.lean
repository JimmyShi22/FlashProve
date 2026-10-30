-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OkAtBatch.lean: THE STATIC HALF OF THE PROMISE Ok (`OkK8`, OkJoin.lean)
AND ITS CLAUSE okDig (`DigStatic`, RestStatic.lean) AT EVERY STATE THAT IS REACHED AT THE BATCHING's
ENTRY's NUMBER, AT ALL THE LINKS OF THE IOP AS WRITTEN IN LEAN, IN THE GOALS' SCOPE. Theorems.
  `planned_g9`, `planned_gD`: the seven and the nine readings are of the planned fields alone
    (`Planned`, PlannedAtDraw.lean): each of its four fields by unfolding. `of_readTl`.
  `ok_at_batch`: **at a state a that is reached (`RchAt`) at the number 14 l + i + 3 + n of a
    written stretch (l, i, n), Xl the built link l: `OkK8 π (fixed9 φ a.1.2)`, and okDig's body
    there.** That the structure's planned readings are Xl.tl's is no premise: it is
    `planned_batch_rch` (PlannedAtRch.lean) at the two readings.
That the snapshot's arrays have the looks of Xl's planned ledger is none either: it is
`part_at_batch` (AtBatchOpen.lean).
  `part_of_onA`, `ok_at_batch_onA`: the same under the book-keeping in front of the batching
    (`k9OnA`, Johnson/Desc/First/Batch/Law/Borders.lean), which says that the part is open.
PREMISES THAT STAY. At the one reached state: h0 (kind K9's part is open). Of the plan: H1
(`StaticOk Xl.tl Xl.Fp`) and H2 (`DigStatic tlD Xl.tl Xl.Fp`).
Limits. h0 is shown of no state here, H1, H2 of no plan. The other clauses of Ok are not here.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OkDigAt
import Johnson.Desc.First.Link.Law.PlannedAtRch
import Johnson.Desc.First.Link.Law.AtBatchOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (readTl)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-- The seven readings are of the planned fields alone. -/
theorem planned_g9 : Planned g9 :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- So are the nine. -/
theorem planned_gD : Planned gD :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- What a reading of the state's structure says of the structure that is there. -/
theorem of_readTl {β : Type} {g : HTailF2 → β} {s : S} {v : β} (h : readTl g s = some v) :
    ∀ tl, s.tl? = some tl → g tl = v := fun tl htl => by
  unfold readTl at h
  rw [htl] at h
  exact Option.some.inj h

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE STATIC HALF OF Ok, AND THE CLAUSE okDig, AT EVERY STATE THAT IS REACHED AT THE BATCHING's
ENTRY's NUMBER, AT ALL THE LINKS.** -/
theorem ok_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (tlD : HTailF2)
    (h0 : (atS.get? a.1.2).isSome = true)
    (H1 : StaticOk Xl.tl Xl.Fp) (H2 : DigStatic tlD Xl.tl Xl.Fp) :
    OkK8 π (fixed9 φ a.1.2) ∧
      ∀ tlb v, (π (fixed9 φ a.1.2).1).1 = some tlb → (fixed9 φ a.1.2).2 = some v →
        DigStatic tlD tlb v.F :=
  have h2 : ∀ p, atS.get? a.1.2 = some p →
      (pubOf p).F.trees.toList.map look = Xl.Fp.trees.toList.map look :=
    fun p hp => (part_at_batch hS hR O hx e3 a h p hp).2
  ⟨okK8_at π φ u hπ a.1.2 Xl.tl Xl.Fp h0
      (of_readTl (planned_batch_rch planned_g9 hS hR O hx e3 a h)) h2 H1,
    okDig_at π φ u hπ a.1.2 tlD Xl.tl Xl.Fp
      (of_readTl (planned_batch_rch planned_gD hS hR O hx e3 a h)) h2 H2⟩

/-- The book-keeping in front of the batching says that kind K9's part is open. -/
theorem part_of_onA (s : S) (h : k9OnA s = true) : (atS.get? s).isSome = true := by
  unfold k9OnA at h
  cases e : atS.get? s with
  | none =>
    rw [e] at h
    exact nomatch h
  | some _ => rfl

/-- **THE SAME UNDER THE BOOK-KEEPING IN FRONT OF THE BATCHING.** -/
theorem ok_at_batch_onA (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (tlD : HTailF2)
    (hA : k9OnA a.1.2 = true) (H1 : StaticOk Xl.tl Xl.Fp) (H2 : DigStatic tlD Xl.tl Xl.Fp) :
    OkK8 π (fixed9 φ a.1.2) ∧
      ∀ tlb v, (π (fixed9 φ a.1.2).1).1 = some tlb → (fixed9 φ a.1.2).2 = some v →
        DigStatic tlD tlb v.F :=
  ok_at_batch hS hR O hx e3 a h π φ u hπ tlD (part_of_onA a.1.2 hA) H1 H2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.planned_g9
#print axioms VerifiableInference.Desc.LinkJoin.planned_gD
#print axioms VerifiableInference.Desc.LinkJoin.ok_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.ok_at_batch_onA
