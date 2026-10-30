-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/K4HeardAtReads.lean: k4_heard_at_front (Johnson/Desc/First/Link/Law/K4AtFront.lean) AT THE BORDER 28 g + 5, IN FRONT OF A LAYERS' SEGMENT's READS, where the
thread stands. Its proof is that law's, from K4's step on. What it says is less: the hearing's return is the state's own?; no pads' names and no later ledger.

  k4_own_at_reads   the statement. Its tokens, heard record, ledger and tape stand under "there are", tied to nothing: the state's own? is SOME return of hearFl at the plan. It serves a caller who spends what holds of
                    every return (OwnHeardS, K1/TieStateAtHead.lean); it cannot say which values the return holds

NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.First.Link.Law.K4AtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (hearFl)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (reach_pred kept_atS)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **In front of a layers' segment's reads the state's own? is a return of K4's hearing.** -/
theorem k4_own_at_reads (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : Q}
    {s₅ : S} (r5 : Reach 0 c.blocksInOrder start (28 * g + 5) (z, s₅)) :
    ∃ (x : Bool × OnBytes.Desc.First.K4.Par) (tokv : _) (fo : Forest.Heard) (F₄ : Fork) (o : Own)
      (G : Fork) (t u : Tape),
      x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none ∧ x.2.g = g ∧
      x.2.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[g]? = some x.2.hp ∧
      hearFl { x.2.P with tokv := tokv } x.2.hp x.2.g fo F₄ t = some (o, G, u) ∧
      s₅.own? = some o := by
  obtain ⟨Lk, b, x, e1, e2, hx, hla, -, a2, a3, a4, -⟩ := IM.k4_of hS hR O g hg
  obtain ⟨z', s₄, s'', b₀, e, r4, hb, hy⟩ := reach_pred (k := 28 * g + 4) r5
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[28 * g + 4]? = some b := by
    have k := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega : 2 * g ≤ 24) 2] at k
    rw [show 28 * g + 4 = 14 * (2 * g) + 2 + 2 by omega]
    exact k
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' := ((IM.k4_yes hla s₄ _ rs gs).1 hd).1
  obtain ⟨a, fo, o, G, ha, hfo, hG, -, ho, -, -, -, -, hofo, -, t, u, hh⟩ := kept_atS hd'
  exact ⟨x, _, fo, a.F, o, G, t, u, hx, a2, a3, a4, hh, ho⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k4_own_at_reads
