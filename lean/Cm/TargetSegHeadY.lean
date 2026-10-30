-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegHeadY.lean: the last segment: the plain head's families (Cm/TargetSegHead.lean) and the
identity "y = 0 if e < 1,024" as one more family.

Definitions, small statements and proofs.
Why: by a
reading, in this protocol's technical report (lean/CREDITS.md) it is an identity of the last
segment: a summand that is a coefficient alone. Cb/Req/ReqSpec.lean allows a term without atoms.
Placed here, a zerocheck checks it and nothing of it is left to a test.

Main names:
  `idY`: the family on no variable with one term without atoms, whose coefficient is y if e < 1,024
    and 0 otherwise (read in `Gl.E`).
  `headY_holds`: the conditions of `segHeadY np` (the last segment) hold ⇔ the head's hold, and
    y = 0 modulo `Gl.p` (Cb/Gl/GlField.lean) if e < 1,024.
  `headY_wf`, `headY_places`: `segHeadY np` is well formed at `fmtRef`; every place that it reads
    is among those that the cells' layout says the head reads (`reads Hd.plain 24`); `idY` reads no
    place.

Limits: the coefficient reads the reply y: this is the last segment, where the technical report
allows that. That no earlier segment's coefficient reads y is not said here:
Cm/TargetSegNoReply.lean: `Spec.no_reply` (for k < 24 all coefficient tables of segment k are the
same at two requests with the same prompt).

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetSegHeadAsm
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All

/-- the identity "y = 0 if e < T": a term without atoms -/
def idY : Cb.Fam XI Cb.Gl.E :=
  ⟨0, 0,
    fun _ => .base (.cell fun _ => ⟨0, []⟩),
    [⟨fun x _ => if x.e < ppref.T then ((x.y.val : ℕ) : Cb.Gl.E) else 0, []⟩]⟩

/-- The last segment. -/
def segHeadY (np : NormPar) : SegSpec XI Cb.Gl.F Cb.Gl.E :=
  { segHead np with idn := idY :: (segHead np).idn }

theorem natE_iff (n : ℕ) : ((n : ℕ) : Cb.Gl.E) = 0 ↔ ((n : ℕ) : ZMod Cb.Gl.p) = 0 := by
  rw [← map_natCast (algebraMap Cb.Gl.F Cb.Gl.E) n, map_eq_zero]

theorem idY_val (Φ : IdxFmt Cb.Gl.F) (x : XI) (W : ℕ → ℕ → Cb.Gl.F)
    (A : ℕ → ℕ → ℕ → Cb.Gl.E) (b : ℕ) :
    idY.val Φ x W A b = if x.e < ppref.T then ((x.y.val : ℕ) : Cb.Gl.E) else 0 := by
  simp only [idY, Fam.val, Term.val, List.map_cons, List.map_nil, List.prod_nil, List.sum_cons,
    List.sum_nil, mul_one, add_zero]

theorem headY_holds (np : NormPar) (Φ : IdxFmt Cb.Gl.F) (x : XI)
    (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    (segHeadY np).Holds Φ x W A ↔
    (segHead np).Holds Φ x W A ∧ (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Cb.Gl.p) = 0) := by
  have hy : (∀ b < 2 ^ idY.v, idY.val Φ x W A b = 0) ↔
      (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Cb.Gl.p) = 0) := by
    constructor
    · intro h he
      have h0 := h 0 (by positivity)
      rw [idY_val, if_pos he] at h0
      exact (natE_iff _).1 h0
    · intro h b _
      rw [idY_val]
      split_ifs with he
      · exact (natE_iff _).2 (h he)
      · rfl
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun f hf => h1 f (List.mem_cons_of_mem _ hf), h2⟩,
      hy.1 (h1 idY (List.mem_cons_self ..))⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun f hf => ?_, h2⟩
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hy.2 h3
    · exact h1 f hf

theorem idY_wf (Φ : IdxFmt Cb.Gl.F) : idY.WF Φ :=
  ⟨fun t ht j hj => by
      rcases List.mem_singleton.1 ht with rfl
      exact absurd hj (List.not_mem_nil),
    fun j hj => absurd hj (Nat.not_lt_zero j)⟩

theorem idY_places : idY.places = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)

theorem headY_wf (np : NormPar) : (segHeadY np).WF fmtRef :=
  ⟨fun f hf => by
      rcases List.mem_cons.1 hf with rfl | hf
      · exact idY_wf fmtRef
      · exact (head_wf np).1 f hf,
    (head_wf np).2⟩

theorem headY_places (np : NormPar) : ∀ q ∈ (segHeadY np).places, q ∈ reads Hd.plain 24 := by
  rintro q (⟨f, hf, hq⟩ | h)
  · rcases List.mem_cons.1 hf with rfl | hf
    · rw [idY_places] at hq
      exact absurd hq (Set.notMem_empty q)
    · exact head_places np q (Or.inl ⟨f, hf, hq⟩)
  · exact head_places np q (Or.inr h)

end Cm.Seg.TS
