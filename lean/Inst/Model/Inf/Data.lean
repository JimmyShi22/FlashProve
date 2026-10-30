-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Inf/Data.lean: the serializer of requests as bit strings, and a fixed index, at the
  model's sizes.

  * `sxM` serializes a request x = (tokens, y, r, e) (`Instance`, Inst/Model/Program.lean: y is the
    announced token, r ≤ t < e are the covered positions, Inst/Model/ProgramR.lean): the 1,024
    tokens, then y, in 18 bits each (202,048 ≤ 2^18), then r and e in 11 bits each (1,025 ≤ 2^11).
    No length is written, since the number of tokens is fixed.
  * `i0M` is the index whose weights are all 0. It is well formed.
  Notation:
    index: `Index ppref` (Inst/Model/Program.lean): the type of indices: the well-formed weights
      (`Weights.WF`).
    `Box r c lo hi W` (Inst/Model/Program.lean): a `Prop`: an r × c matrix with entries in [lo, hi],
      and 0 outside; `Two`: a `Prop`: a matrix of two-byte weights.
    `LayerW.WF`, `LayerW.IsZero` (Inst/Model/Program.lean): each a `Prop` on the matrices of a
      layer; `IsZero`: the all-zero layer: the form of every layer beyond the last one.
-/
import Inst.Model.Program
import Iop.Ser

set_option autoImplicit false

namespace Inst.Model.Inf

open Iop

/-! ## Requests as bit strings -/

/-- The serializer of a function on `Fin n`: its values one after the other, each by `A`. -/
def serFn {α : Type} (A : Ser α) : (n : ℕ) → Ser (Fin n → α)
  | 0 => Ser.ofEquiv (Equiv.equivPUnit.{1, 1} (Fin 0 → α)) Ser.unit
  | n + 1 => Ser.ofEquiv (Fin.consEquiv fun _ : Fin (n + 1) => α).symm (Ser.prod A (serFn A n))

theorem length_put_serFn {α : Type} (A : Ser α) (w : ℕ) (h : ∀ a, (A.put a).length = w) :
    ∀ (n : ℕ) (v : Fin n → α), ((serFn A n).put v).length = n * w
  | 0, _ => by simp [serFn, Ser.ofEquiv, Ser.unit]
  | n + 1, v => by
      show ((Ser.prod A (serFn A n)).put _).length = _
      rw [Ser.length_put_prod, h, length_put_serFn A w h n]
      ring

/-- A request as the tuple of its four fields. -/
def instEquiv (P : Params) :
    Instance P ≃ ((Fin P.T → Fin P.V) × Fin P.V) × (Fin (P.T + 1) × Fin (P.T + 1)) :=
  ⟨fun x => ((x.prompt, x.y), (x.rF, x.eF)), fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

/-- The serializer of requests at the model's sizes. -/
def sxM : Ser (Instance ppref) :=
  Ser.ofEquiv (instEquiv ppref)
    (Ser.prod (Ser.prod (serFn (Ser.fin ppref.V) ppref.T) (Ser.fin ppref.V))
      (Ser.prod (Ser.fin (ppref.T + 1)) (Ser.fin (ppref.T + 1))))

/-- Every request is serialized in 1,025 · 18 + 2 · 11 = 18,472 bits. -/
theorem length_put_sxM (x : Instance ppref) : (sxM.put x).length = 18472 := by
  have hw : Nat.clog 2 ppref.V = 18 := by decide +kernel
  have hr : Nat.clog 2 (ppref.T + 1) = 11 := by decide +kernel
  show ((Ser.prod (Ser.prod (serFn (Ser.fin ppref.V) ppref.T) (Ser.fin ppref.V))
        (Ser.prod (Ser.fin (ppref.T + 1)) (Ser.fin (ppref.T + 1)))).put _).length = _
  rw [Ser.length_put_prod, Ser.length_put_prod, Ser.length_put_prod,
    length_put_serFn _ 18 (fun a => (Ser.length_put_fin _ a).trans hw), Ser.length_put_fin,
    Ser.length_put_fin, Ser.length_put_fin, hw, hr]
  rfl

/-! ## A fixed index -/

theorem box_zero (r c : ℕ) {lo hi : ℤ} (h1 : lo ≤ 0) (h2 : 0 ≤ hi) :
    Box r c lo hi fun _ _ => 0 := fun j x => by
  split_ifs
  · exact ⟨h1, h2⟩
  · rfl

theorem two_zero (r c : ℕ) : Two r c fun _ _ => 0 := box_zero r c (by norm_num) (by norm_num)

/-- The layer whose weights are all 0. -/
def layer0 : LayerW :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

theorem layer0_wf (P : Params) (L : ℕ) : layer0.WF P L := by
  refine ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, ?_⟩
  split_ifs
  · refine ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, fun e => ?_⟩
    split_ifs <;> exact ⟨two_zero _ _, two_zero _ _, two_zero _ _⟩
  · exact ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _,
      fun e => ⟨two_zero _ _, two_zero _ _, two_zero _ _⟩⟩

theorem layer0_isZero : layer0.IsZero :=
  ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _,
    two_zero _ _, fun _ => ⟨two_zero _ _, two_zero _ _, two_zero _ _⟩⟩

/-- The index whose weights are all 0. -/
def i0M : Index ppref :=
  ⟨⟨fun _ => layer0, fun _ _ => 0, fun _ _ => 0⟩, fun L => by split_ifs <;> [exact layer0_wf ppref L; exact layer0_isZero], box_zero _ _ (by norm_num) (by norm_num), two_zero _ _⟩

end Inst.Model.Inf
