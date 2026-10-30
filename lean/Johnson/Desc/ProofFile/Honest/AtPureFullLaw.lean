-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureFullLaw.lean: THREE STATEMENTS THAT HOLD BY UNFOLDING the
definitions of Honest/AtPureFull.lean: what the honest prover's trace at the full size is, where it
is there. Statements and proofs.

  `fullTrace_some`     where the trace is there, it is the full-size trace with its planes
                      (`OnBytes.HonestTrace.theTrace`) at an instance that the bytes are read as and
                      that the index serves
  `fullTrace_served`   and it is there at every such instance
  `fullReaders_cells`  the cells' reader is that trace read by the sub-proof's number and the
                      matrix's label (`cellOf`) at the public part's own structure

What they are for. A law on the full-size trace speaks of `theTrace X i x` under `ServesAt X i x`; a
law on the honest side speaks of `H.trace w₀ ξ = some ω`. The first statement carries the second's
hypothesis to the first's.

Limits. They are general in the reader `instOf`, a letter here; the filling lays `ProofFile.instOf`, whose
laws stand in Johnson/Desc/ProofFile/InstOf.lean. Nothing on a run, a coin or a measure. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Inst.Model (Instance ppref)
open OnBytes.HonestTrace (Tr theTrace ServesAt cellOf)

/-- Where the trace is there, it is the full-size trace with its planes, at an instance that the
bytes are read as and that the index serves. -/
theorem fullTrace_some {instOf : Inst → Option (Instance ppref)} {Z : Pub} {i : Cm.Idx} {ξ : Inst}
    {T : Tr} (h : fullTrace instOf Z i ξ = some T) :
    ∃ x, instOf ξ = some x ∧ ServesAt Z.p.X i x ∧ T = theTrace Z.p.X i x := by
  classical
  unfold fullTrace at h
  cases hx : instOf ξ with
  | none =>
    rw [hx] at h
    have h' : (none : Option Tr) = some T := h
    cases h'
  | some x =>
    rw [hx] at h
    have h' : (if ServesAt Z.p.X i x then some (theTrace Z.p.X i x) else none) = some T := h
    by_cases hs : ServesAt Z.p.X i x
    · rw [if_pos hs] at h'
      exact ⟨x, rfl, hs, (Option.some.inj h').symm⟩
    · rw [if_neg hs] at h'
      cases h'

/-- And it is there at every such instance. -/
theorem fullTrace_served {instOf : Inst → Option (Instance ppref)} {Z : Pub} {i : Cm.Idx}
    {ξ : Inst} {x : Instance ppref} (hx : instOf ξ = some x) (hs : ServesAt Z.p.X i x) :
    fullTrace instOf Z i ξ = some (theTrace Z.p.X i x) := by
  classical
  unfold fullTrace
  rw [hx]
  show (if ServesAt Z.p.X i x then some (theTrace Z.p.X i x) else none) = _
  rw [if_pos hs]

/-- The cells' reader is the trace read by the sub-proof's number and the matrix's label. -/
theorem fullReaders_cells (Z : Pub) (i : Cm.Idx) (rc : FullRc) (T : Tr) :
    (fullReaders Z i rc T).cells = ⟨cellOf Z.p.X T⟩ := rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.fullTrace_some
#print axioms ProofFile.Honest.fullTrace_served
#print axioms ProofFile.Honest.fullReaders_cells
