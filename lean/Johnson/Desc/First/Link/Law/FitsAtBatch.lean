-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FitsAtBatch.lean: THE THREE TAKES' FIELD okEq (PayLayers.lean,
PayAttention.lean, PayHead.lean: at what is fixed before the draw the approximate range proof's
structure has "the shapes fit the matrices": `Fits`, OnBytes/Tie/Pv/Tail/EndSame.lean) AT EVERY
STATE THAT IS REACHED AT THE BATCHING's ENTRY's NUMBER, AT ALL THE LINKS, IN THE GOALS' SCOPE: from
one sentence on the built link. A definition and theorems: by the road of OkAtBatch.lean.
  `gF tl`: the three planned readings that `Fits` reads: the number of matrices, the shapes, the
    matrices. `gF_blank`, `planned_gF`: none is one of the fourteen written fields; the reading is
    of the planned fields alone (`Planned`, PlannedAtDraw.lean). `fits_congr`: by
    `Fits.of_same`.
  `OkFits π q`: the clause. `okFits_at`: at `fixed9 φ s`, where the structure's three readings are
    tlP's and `Fits tlP`. `fits_at_batch`: **`OkFits π (fixed9 φ a.1.2)` at a state a that is
    reached (`RchAt`) at the number 14 l + i + 3 + n of a written stretch, from `Fits Xl.tl`, Xl the
    built link l.** `fits_at_batch_B`: from a yes of the test with code (`fitsB`,
    Johnson/Desc/First/TailClaims/EquationsSheet.lean).
  `okEq_of`: okEq's own text, where Ok gives `OkFits pi8`. Behind it three `example`s: Lean's own
    check that this is each Take's field.
Limits. `Fits Xl.tl` is shown of no plan here. Ok's lower bound is owed elsewhere (`hready`).
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Link.Law.PayHead
import Johnson.Desc.First.TailClaims.EquationsSheet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (Fits)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank fitsB fitsB_ok)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Att.P (ParC Heard)
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-- **What `Fits` reads of the approximate range proof's structure.** -/
def gF (tl : HTailF2) := (tl.NM, tl.shp, tl.mats)

/-- It reads none of the fourteen written fields. -/
theorem gF_blank (u tl : HTailF2) : gF (blank u tl) = gF tl := rfl

/-- The three readings are of the planned fields alone. -/
theorem planned_gF : Planned gF :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- `Fits` hangs on the three readings alone. -/
theorem fits_congr {tl tl' : HTailF2} (h : gF tl = gF tl') (H : Fits tl') : Fits tl := by
  unfold gF at h
  simp only [Prod.mk.injEq] at h
  exact H.of_same h.1 h.2.1 h.2.2

section
variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- **The clause.** -/
def OkFits (q : α × Option Pub9) : Prop := ∀ tlb, (π q.1).1 = some tlb → Fits tlb

/-- At what is fixed at a state. -/
theorem okFits_at (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (s : S) (tlP : HTailF2)
    (h1 : ∀ tl, s.tl? = some tl → gF tl = gF tlP) (H : Fits tlP) : OkFits π (fixed9 φ s) := by
  intro tlb e1
  have e1' : s.tl?.map (blank u) = some tlb := (congrArg Prod.fst (hπ s)).symm.trans e1
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 e1'
  exact fits_congr ((gF_blank u tl).trans (h1 tl htl)) H

end

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE CLAUSE AT EVERY STATE THAT IS REACHED AT THE BATCHING's ENTRY's NUMBER, AT ALL THE
LINKS.** -/
theorem fits_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (H : Fits Xl.tl) :
    OkFits π (fixed9 φ a.1.2) :=
  okFits_at π φ u hπ a.1.2 Xl.tl (of_readTl (planned_batch_rch planned_gF hS hR O hx e3 a h)) H

/-- The same from a yes of the test with code. -/
theorem fits_at_batch_B (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (H : fitsB Xl.tl = true) :
    OkFits π (fixed9 φ a.1.2) :=
  fits_at_batch hS hR O hx e3 a h π φ u hπ (fitsB_ok H)

/-! ## The Takes' field -/

variable {β : Type}

/-- **okEq's own text**, where Ok gives the clause. -/
theorem okEq_of (Ok : Q β → Prop) (h : ∀ q, Ok q → OkFits pi8 q) :
    ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb → Fits tlb :=
  fun q tlb hq e => h q hq tlb e

/-- Lean's own check that this is the layers' Take's field. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (Fu : S → Prop) (nU : Array ℕ)
    (L : Link S Claim) (p : Par)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) :
    ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb → Fits tlb :=
  A.okEq

/-- And attention's. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (Fu : S → Prop) (nU : Array ℕ)
    (L : Link S Claim) (rd : Phi β → Option (Forest.Heard × Heard)) (c : ParC)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) :
    ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb → Fits tlb :=
  A.okEq

/-- And the head's. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (Fu : S → Prop) (nU : Array ℕ)
    (L : Link S Claim) (h : OnBytes.Model.Head.Shape) (iU3 l piece : ℕ) (p : Kinds.Head.Par)
    (kap : Phi β → Option Seen)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : HeadTake L u ψ Ok Fu h iU3 l piece p kap nU ent tm4 t3 l3) :
    ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb → Fits tlb :=
  A.okEq

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.planned_gF
#print axioms VerifiableInference.Desc.LinkJoin.fits_congr
#print axioms VerifiableInference.Desc.LinkJoin.fits_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.fits_at_batch_B
#print axioms VerifiableInference.Desc.LinkJoin.okEq_of
