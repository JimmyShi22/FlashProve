-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CoreAtBatch.lean: `OkCore` (OkOne.lean) AT EVERY STATE REACHED IN FRONT
OF A LINK's BATCHING: each clause laid in from the theorem that has it; what no theorem has stays a
field of one named structure. A structure and two theorems: a joining.
Why. OkOne.lean makes every field that begins "Ok q" a projection, and so lays all their weight on
one debt a link: Ok of what is fixed, at the states in front of the batching. Several files show
clauses of it at reached states. Here they are joined: so that WHAT IS STILL OPEN IS A
LEAN STRUCTURE, NOT A PAGE.
  `OkCoreLeft c Z Xl tlD u ψ kd z s`: WHAT IS LEFT. part: K9's part is there at s (PartAtBatch.lean
    has it from the table's promise). static, dig, fits: three closed sentences on the built segment
    Xl. plan: every sub-protocol of the first chain passes its test on the plan. led: at every state
    reached at number kd, in front of the lookup on the digits, a ledger is open and has its sizes.
    pos: `OkCore`'s clause pos itself: no theorem is laid in for it here: PosAtBatch.lean
    has it, from one closed sentence on the plan (PosPlan, a premise there, shown of no plan).
  `core_at_batch`: **`OkCore nU tlD (fixed9 (phiAll u ψ) a.1.2)` at a reached at 14 l + 9, l < 24.**
    `core_at_head`: **the like at 347.** The term, field by field: snap, there:
    `snap_there_of_part`; static, dig: `ok_at_batch` (OkAtBatch.lean); fits: `fits_at_batch`
    (FitsAtBatch.lean); four, ents4: `four_at_batch`, `four_at_head` (FourAtBatch.lean); pos: the
    structure's.
Limits. A JOINING: NOTHING IS PAID BY THIS FILE. OVERTAKEN: CoreAtFront.lean has `OkCore` at the
same border from less (`OkCoreLess`); SortsAtBatch.lean alone imports this file. `OkCoreLeft` is
shown of no state here. The parameter nU of `OkCore` is read by none of its fields. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.OkOne
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.FitsAtBatch
import Johnson.Desc.First.Link.Law.FourAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized)
open OnBytes.Tie.Pv.Tail.Port (readsList uOf posOf colsU Fits)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.Walk.Tied (RchAt Reach rchAt_raw)
open ProofFile (Cl)

variable {β : Type}

/-- **WHAT IS LEFT OF `OkCore` AT A STATE IN FRONT OF A BATCHING.** -/
structure OkCoreLeft (c : Chain S Cl) (Z : ProofFile.Pub) (Xl : LinkH) (tlD u : HTailF2) (ψ : S → β)
    (kd : ℕ) (z : ProofFile.InstPub) (s : S) : Prop where
  /-- K9's part is there -/
  part : (atS.get? s).isSome = true
  /-- closed, at the built segment -/
  static : StaticOk Xl.tl Xl.Fp
  dig : DigStatic tlD Xl.tl Xl.Fp
  fits : Fits Xl.tl
  /-- every sub-protocol of the first chain passes its test on the plan -/
  plan : ∀ b ∈ c.blocksInOrder, b.planOk = true
  /-- in front of the lookup on the digits a ledger is open and has its sizes -/
  led : ∀ t, Reach 0 c.blocksInOrder (ProofFile.startS Z) kd (z, t) → ∃ G, t.fork? = some G ∧ Sized G
  /-- `OkCore`'s clause pos itself -/
  pos : ∀ tlb funs v, pi8 (fixed9 (phiAll u ψ) s).1 = (some tlb, some funs) →
    (fixed9 (phiAll u ψ) s).2 = some v → ∀ x ∈ readsList tlb funs,
      ∀ d, d < (tlb.mats.getD x.1.mat {}).k → posOf tlb x.1 x.2 d < colsU v.F (uOf tlb x.1)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **`OkCore` AT EVERY STATE REACHED IN FRONT OF THE BATCHING OF A LINK l < 24.** -/
theorem core_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 24)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * l + 9) a)
    (nU : Array ℕ) (tlD u : HTailF2) (ψ : S → β)
    (Lf : OkCoreLeft c Z Xl tlD u ψ (14 * l + 8) a.1.1 a.1.2) :
    OkCore nU tlD (fixed9 (phiAll u ψ) a.1.2) := by
  have hx : (l, 4, 2) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ l = 24), if_neg (by omega : ¬ l = 24)]⟩
  have h' : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * (l, 4, 2).1 + (l, 4, 2).2.1 + 3 + (l, 4, 2).2.2) a := h
  have K := ok_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) tlD Lf.part Lf.static
    Lf.dig
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (a.1.1, a.1.2) := rchAt_raw h
  have Q := four_at_batch hS hR O Lf.plan hl hr Lf.led pi8 (phiAll u ψ) u (fun _ => rfl)
  exact ⟨(snap_there_of_part u ψ a.1.2 Lf.part).1, (snap_there_of_part u ψ a.1.2 Lf.part).2,
    K.1.2, fits_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) Lf.fits, K.2, Lf.pos,
    Q.1, Q.2⟩

/-- **THE LIKE IN FRONT OF THE HEAD's BATCHING.** -/
theorem core_at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 a)
    (nU : Array ℕ) (tlD u : HTailF2) (ψ : S → β)
    (Lf : OkCoreLeft c Z Xl tlD u ψ 345 a.1.1 a.1.2) :
    OkCore nU tlD (fixed9 (phiAll u ψ) a.1.2) := by
  have hx : (24, 5, 3) ∈ P1K8S.stretches := by decide
  have h' : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * (24, 5, 3).1 + (24, 5, 3).2.1 + 3 + (24, 5, 3).2.2) a := h
  have K := ok_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) tlD Lf.part Lf.static
    Lf.dig
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (a.1.1, a.1.2) := rchAt_raw h
  have Q := four_at_head hS hR O Lf.plan hr Lf.led pi8 (phiAll u ψ) u (fun _ => rfl)
  exact ⟨(snap_there_of_part u ψ a.1.2 Lf.part).1, (snap_there_of_part u ψ a.1.2 Lf.part).2,
    K.1.2, fits_at_batch hS hR O hx e3 a h' pi8 (phiAll u ψ) u (fun _ => rfl) Lf.fits, K.2, Lf.pos,
    Q.1, Q.2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.core_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.core_at_head
