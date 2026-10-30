-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/SemClaims.lean: two lists of deferred claims (`Ledger`, Blocks/Form.lean) in a row, and the
list after the step `join`. They serve claims on the cells of matrices that wait for the partial
evaluations: with them many claims are added to the ledger at once.

Why: in the reduction part of a segment a claim is about true values: it says that the value of a
form plus certain contractions of the cells is 0. A contraction becomes a form in sent entries only
when the partial evaluations have been sent, and a segment of the model has some hundreds of such
claims. The idea is to write every claim as a form from the start, over the entries sent so far and
the entries of the partial evaluations to come (N ⊕ PEnt C R), and to evaluate it, as long as these
have not been sent, at the virtual entries: the true contractions of the cells. Then nothing has to
be transported claim by claim: if the partial evaluations that are sent are the contractions of the
cells, the entries that were sent are the virtual entries, and every form, every list of forms and
every ledger has the same value and the same truth.
 * `Ledger.append`: two ledgers in a row; the terms of the second are shifted. `true_append`,
   `wf_append`. `HLed.append`: the honest prover's memory of two ledgers in a row, with `Of.append`,
   `Good.append`, `len_append`.
 * `PEnt C R`: the entries of the partial evaluations.
 * The step of a segment. `join led x`: the ledger so far, transported to the larger type of
   entries, then the waiting claims x (a ledger over N ⊕ PEnt C R).

Notation: `Mx`: a type: its elements μ are the matrices; `R μ`, `C μ`: types: by the doc comment of
`PEnt`, q : `R μ` is the number of a partial evaluation of the matrix μ and c : `C μ` an entry of
it; `m`: `Mx → ℕ`: it occurs only in the types of the variables `cells`, `w`; `Ledger.push`
(Blocks/Form.lean): the deferred claims transported along a map of entries.
Limits: this file does not define the virtual entries, and it does not prove that the entries that
were sent are the virtual entries, nor soundness of the step `join`.
-/
import Blocks.HLed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Finset

/-! ## 1. Two ledgers in a row -/

namespace Ledger

variable {N E : Type}

/-- The terms of a REL, with the numbers of the opened forms raised by k. -/
def shift (k : ℕ) (ts : List (E × ℕ × ℕ)) : List (E × ℕ × ℕ) :=
  ts.map fun t => (t.1, k + t.2.1, k + t.2.2)

/-- Two ledgers in a row. The terms of the second name its own opened forms, which now come after
those of the first. -/
def append (x x' : Ledger N E) : Ledger N E :=
  ⟨x.lin ++ x'.lin, x.opn ++ x'.opn, x.rel ++ x'.rel.map fun r => (r.1, shift x.opn.length r.2)⟩

theorem wf_append {x x' : Ledger N E} (h : x.wf = true) (h' : x'.wf = true) :
    (x.append x').wf = true := by
  rw [wf_iff] at h h' ⊢
  intro r hr t ht
  have hlen : (x.append x').opn.length = x.opn.length + x'.opn.length := by simp [append]
  rw [hlen]
  rcases List.mem_append.mp hr with hr | hr
  · have := h r hr t ht
    omega
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    have := h' r' hr' t' ht'
    exact ⟨by show x.opn.length + t'.2.1 < _; omega, by show x.opn.length + t'.2.2 < _; omega⟩

variable [Fintype N] [CommRing E]

/-- If the first is well formed: the two ledgers in a row are true iff each of them is. -/
theorem true_append {x : Ledger N E} (h : x.wf = true) (x' : Ledger N E) (y : N → E) :
    (x.append x').True y ↔ x.True y ∧ x'.True y := by
  rw [wf_iff] at h
  have hold : ∀ i < x.opn.length, (x.append x').opv y i = x.opv y i := fun i hi => by
    unfold opv append
    rw [List.getD_append _ _ _ _ hi]
  have hnew : ∀ i, (x.append x').opv y (x.opn.length + i) = x'.opv y i := fun i => by
    unfold opv append
    rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have h1 : ∀ r ∈ x.rel, termSum ((x.append x').opv y) r.2 = termSum (x.opv y) r.2 := fun r hr => by
    unfold termSum
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [hold _ (h r hr t ht).1, hold _ (h r hr t ht).2]
  have h2 : ∀ ts : List (E × ℕ × ℕ),
      termSum ((x.append x').opv y) (shift x.opn.length ts) = termSum (x'.opv y) ts := fun ts => by
    unfold termSum shift
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    show t.1 * (x.append x').opv y (x.opn.length + t.2.1) *
        (x.append x').opv y (x.opn.length + t.2.2) = _
    rw [hnew, hnew]
  constructor
  · rintro ⟨a, b⟩
    refine ⟨⟨fun f hf => a f (List.mem_append_left _ hf), fun r hr => ?_⟩,
      fun f hf => a f (List.mem_append_right _ hf),
      fun r hr => ?_⟩
    · rw [← h1 r hr]
      exact b r (List.mem_append_left _ hr)
    · rw [← h2 r.2]
      exact b (r.1, shift x.opn.length r.2)
        (List.mem_append_right _
          (List.mem_map_of_mem
            (f := fun r : Form N E × List (E × ℕ × ℕ) => (r.1, shift x.opn.length r.2)) hr))
  · rintro ⟨⟨a, b⟩, a', b'⟩
    refine ⟨fun f hf => ?_, fun r hr => ?_⟩
    · rcases List.mem_append.mp hf with hf | hf
      · exact a f hf
      · exact a' f hf
    · rcases List.mem_append.mp hr with hr | hr
      · rw [h1 r hr]
        exact b r hr
      · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
        show Form.val y r'.1 = termSum ((x.append x').opv y) (shift x.opn.length r'.2)
        rw [h2]
        exact b' r' hr'

end Ledger

namespace HLed

variable {N E : Type}

/-- The honest prover's memory of two ledgers in a row. -/
def append (h h' : HLed E) : HLed E :=
  ⟨h.nl + h'.nl, h.ov ++ h'.ov, h.tm ++ h'.tm.map (Ledger.shift h.ov.length)⟩

theorem len_append (h h' : HLed E) :
    (h.append h').len = (h.len.1 + h'.len.1, h.len.2.1 + h'.len.2.1, h.len.2.2 + h'.len.2.2) := by
  simp [len, append]

variable [Fintype N] [CommRing E] {h h' : HLed E} {led led' : Ledger N E} {y : N → E}

theorem Of.append (H : h.Of led y) (H' : h'.Of led' y) : (h.append h').Of (led.append led') y := by
  refine ⟨?_, ?_, ?_⟩
  · show (led.lin ++ led'.lin).length = h.nl + h'.nl
    rw [List.length_append, H.1, H'.1]
  · show (led.opn ++ led'.opn).map (fun f => Form.val y f) = h.ov ++ h'.ov
    rw [List.map_append, H.2.1, H'.2.1]
  · show (led.rel ++ led'.rel.map fun r => (r.1, Ledger.shift led.opn.length r.2)).map
        (fun r => r.2) =
      h.tm ++ h'.tm.map (Ledger.shift h.ov.length)
    have hl : led.opn.length = h.ov.length := by rw [← H.2.1, List.length_map]
    rw [List.map_append, H.2.2, List.map_map, ← H'.2.2, List.map_map, hl]
    rfl

theorem Good.append (H : h.Good led y) (H' : h'.Good led' y) :
    (h.append h').Good (led.append led') y :=
  ⟨H.1.append H'.1,
    Ledger.wf_append H.2.1 H'.2.1,
    (Ledger.true_append H.2.1 led' y).mpr ⟨H.2.2, H'.2.2⟩⟩

end HLed

/-! ## 2. Entries -/

namespace Sem

variable {Mx : Type} {m : Mx → ℕ} {C R : Mx → Type} {N E : Type}

/-- The entries of the partial evaluations: entry c of the partial evaluation number q of the matrix
μ. -/
abbrev PEnt (C R : Mx → Type) : Type := Σ μ, R μ × C μ

variable [CommRing E]


variable [Fintype N] [DecidableEq N] [Fintype Mx] [DecidableEq Mx] [∀ μ, Fintype (C μ)]
  [∀ μ, DecidableEq (C μ)] [∀ μ, Fintype (R μ)] [∀ μ, DecidableEq (R μ)]



/-! ## 3. The step of a segment: the partial evaluations have been sent, the waiting claims enter
the ledger -/

/-- The ledger after the step: the ledger so far, transported to the larger type of entries, then
the waiting claims. -/
def join (led : Ledger N E) (x : Ledger (N ⊕ PEnt C R) E) : Ledger (N ⊕ PEnt C R) E :=
  (led.push Sum.inl).append x

variable {cells : ∀ μ, Fin (m μ) → C μ → E} {w : ∀ μ, R μ → Fin (m μ) → E} {y' : N ⊕ PEnt C R → E}


end Sem

end Blocks

