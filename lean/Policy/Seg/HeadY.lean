-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/HeadY.lean

The last segment: the families of the head with the cost ledger (Policy/Seg/Head.lean) and the
identity "y = 0 if e < 1,024" as one more family.

Statements with their proofs, after Cm/TargetSegHeadY.lean, whose family `TS.idY` is used as it
stands. `withY_holds`, `withY_wf`, `withY_places`: for every segment S over `Gl.F`, `Gl.E` the
conditions of `withY S` hold if and only if S's hold and y = 0 modulo `Gl.p` if e < 1,024; it is
well formed if S is; it reads no place that S does not read. `headPolY_wf`, `headPolY_places`,
`headPolY_holds_int`: `segHeadPolY s pol` is well formed at `TS.fmtRef`; it reads places of
`reads Hd.main 24` alone; for integer cells t with `ReadsAtMain t M` its conditions at M are
`HeadCl` at t and the clause on y.

Limits: the coefficient of `TS.idY` reads the reply y. Nothing on bounds of cells or on protocols.
-/
import Policy.Seg.HeadProofs

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

/-- The conditions of a segment with the identity on y in front: the segment's own, and y = 0 modulo
`Gl.p` if e < T. -/
theorem withY_holds (S : SegSpec XI Gl.F Gl.E) (Φ : IdxFmt Gl.F) (x : XI) (W : ℕ → ℕ → Gl.F)
    (A : ℕ → ℕ → ℕ → Gl.E) :
    (withY S).Holds Φ x W A ↔
    S.Holds Φ x W A ∧ (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Gl.p) = 0) := by
  have hy : (∀ b < 2 ^ TS.idY.v, TS.idY.val Φ x W A b = 0) ↔
      (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Gl.p) = 0) := by
    constructor
    · intro h he
      have h0 := h 0 (by positivity)
      rw [TS.idY_val, if_pos he] at h0
      exact (TS.natE_iff _).1 h0
    · intro h b _
      rw [TS.idY_val]
      split_ifs with he
      · exact (TS.natE_iff _).2 (h he)
      · rfl
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun f hf => h1 f (List.mem_cons_of_mem _ hf), h2⟩,
      hy.1 (h1 TS.idY (List.mem_cons_self ..))⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun f hf => ?_, h2⟩
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hy.2 h3
    · exact h1 f hf

theorem withY_wf {S : SegSpec XI Gl.F Gl.E} {Φ : IdxFmt Gl.F} (h : S.WF Φ) : (withY S).WF Φ :=
  ⟨fun f hf => by
      rcases List.mem_cons.1 hf with rfl | hf
      · exact TS.idY_wf Φ
      · exact h.1 f hf,
    h.2⟩

theorem withY_places (S : SegSpec XI Gl.F Gl.E) : ∀ q ∈ (withY S).places, q ∈ S.places := by
  rintro q (⟨f, hf, hq⟩ | h)
  · rcases List.mem_cons.1 hf with rfl | hf
    · rw [TS.idY_places] at hq
      exact absurd hq (Set.notMem_empty q)
    · exact Or.inl ⟨f, hf, hq⟩
  · exact Or.inr h

theorem headPolY_wf (s : Cm.Scales) (pol : AcceptancePolicy) : (segHeadPolY s pol).WF TS.fmtRef :=
  withY_wf (headPol_wf s pol)

theorem headPolY_places (s : Cm.Scales) (pol : AcceptancePolicy) :
    ∀ q ∈ (segHeadPolY s pol).places, q ∈ reads Hd.main 24 := fun q hq =>
  headPol_places s pol q (withY_places _ q hq)

/-- For integer cells t with `ReadsAtMain t M`: the last segment's conditions hold at the integer
matrices M and the integer index matrix Wz if and only if the head's clauses `HeadCl` hold at t and
y = 0 modulo `Gl.p` if e < T. -/
theorem headPolY_holds_int (s : Cm.Scales) (pol : AcceptancePolicy) (x : XI) (Wz : Mat) (M : ℕ → ℕ → ℕ → ℤ)
    (t : Head.Cells ℤ) (h : ReadsAtMain t M) :
    (segHeadPolY s pol).Holds TS.fmtRef x (fun y c => ((Wz y c : ℤ) : Gl.F))
        (Partition.castM (E := Gl.E) M) ↔
      HeadCl s.nf pol Wz x t ∧ (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Gl.p) = 0) :=
  (withY_holds _ _ _ _ _).trans (and_congr_left' (headPol_holds_int s pol x Wz M t h))

end Policy
