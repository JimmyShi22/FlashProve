-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerPlanesAt.lean: the test «the planes' cells lie in the list's matrix»
as one function of the public record and a link's number, and the law: at every record that
Verify.publicOf returns it says yes at every link at which the lookup on the calls has a place.
Statements and proofs. No soundness is claimed.

Why. A test stays in a running text only where a file can make it fire. This file shows of this test
that no file can: at whatever record publicOf returns, the test says yes wherever placeAt returns.
It is stated at the letters at which the block on the proof file's first chain is seated: the place
that lookAt makes, the parameters
that placeAt makes of it, the record of the smallness test that tlAt gives.

Main names:
  `planeCellsB_eq`: the five comparisons of Johnson/Desc/First/Look/PlanesIn.lean (definitions
    alone, without Mathlib: what a running text can name) are planesAtB: by rfl.
  `planes_at`: publicOf = ok X, lookAt X i false = some x ⊢ tlAt and iBAt return, and planesAtB says
    yes at what they return, x.fs and x.lm. `shape_at`: there the kind's own parameters make x.fs.
  `planesInAt_true | planesInAt_digits | planesInAt_law`: PlanesIn.lean's planesInAt X i digits is
    `some true` wherever placeAt X i digits returns: at the digits trivially: nothing is asked
    there.
  `planeCellsB_no_matrix | planeCellsB_few_columns`: the test can say no.
  `planes_seated`: the same at placeAt's parameters: at p.shape's own record and p.lm.

Limits. One direction: from publicOf's equation. The lookup on the calls alone: nothing on the
digits'. That matrix iBAt is the planes' matrix of the programs is the library's word (its own tests
name these numbers), no theorem on the programs. Nothing on the cells that the keys read.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtPlan
import Johnson.Desc.First.Look.PlanesIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The running text's five comparisons ARE the callers' test: by the definitions. -/
theorem planeCellsB_eq (tl : HTailF2) (fs : Forest.Shape) (lm iB : ℕ) :
    planeCellsB tl fs lm iB = planesAtB tl fs lm iB := rfl

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ} {x : Place}

/-- **THE LAW, at the place.** -/
theorem planes_at (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x) :
    ∃ tl iB, tlAt X i = some tl ∧ iBAt X i = some iB ∧ planesAtB tl x.fs x.lm iB = true := by
  by_cases hn : i = (if X.p4 then 2 else 1) * X.NGr
  · subst hn
    obtain ⟨ht, hp⟩ := head_planes h e
    refine ⟨X.H.tl, X.hS.NHf + 2, ht, ?_, hp⟩
    unfold iBAt
    dsimp only
    rw [if_pos (by simp)]
  · by_cases h0 : i % (if X.p4 then 2 else 1) = 0
    · obtain ⟨tl, ht, hp⟩ := lay_planes h e hn h0
      refine ⟨tl, _, ht, ?_, hp⟩
      unfold iBAt
      dsimp only
      rw [if_neg (by simpa using hn), if_pos (by simpa using h0)]
    · obtain ⟨a, tl, hg, ht, hp⟩ := att_planes h e hn h0
      refine ⟨tl, _, ht, ?_, hp⟩
      unfold iBAt
      dsimp only
      rw [if_neg (by simpa using hn), if_neg (by simpa using h0), hg]
      rfl

/-- There the kind's own parameters make the place's record. -/
theorem shape_at (set : Params.Setting) (h : Verify.publicOf pol KL layout = .ok X)
    (e : lookAt X i false = some x) : (P.ofPlace set false x).shape = some x.fs := by
  by_cases hn : i = (if X.p4 then 2 else 1) * X.NGr
  · subst hn
    exact head_shape set h e
  · by_cases h0 : i % (if X.p4 then 2 else 1) = 0
    · exact lay_shape set h e hn h0
    · exact att_shape set h e hn h0

/-- **THE LAW, at the parameters at which the block is seated.** -/
theorem planes_seated (h : Verify.publicOf pol KL layout = .ok X) {p : P}
    (e : placeAt X i false = some p) :
    ∃ fs tl iB, p.shape = some fs ∧ tlAt X i = some tl ∧ iBAt X i = some iB ∧
      planesAtB tl fs p.lm iB = true := by
  unfold placeAt at e
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨tl, iB, ht, hi, hp⟩ := planes_at h hx
  exact ⟨x.fs, tl, iB, shape_at _ h hx, ht, hi, hp⟩

/-- **THE LAW, of the one function**, at the calls. -/
theorem planesInAt_true (h : Verify.publicOf pol KL layout = .ok X) {p : P}
    (e : placeAt X i false = some p) : planesInAt X i false = some true := by
  obtain ⟨fs, tl, iB, hs, ht, hi, hp⟩ := planes_seated h e
  unfold planesInAt
  rw [e, ht, hi]
  show some (match p.shape with
    | some fs => planeCellsB tl fs p.lm iB
    | none => false) = some true
  rw [hs]
  show some (planesAtB tl fs p.lm iB) = some true
  rw [hp]

/-- At the digits nothing is asked: so this says nothing. -/
theorem planesInAt_digits (X : Verify.Public) (i : ℕ) : planesInAt X i true = some true := rfl

/-- **THE LAW, IN THE VERY TERM THAT WOULD STAND IN THE BLOCK's TEST ON THE PLAN**: wherever the
lookup has parameters at all. At the digits trivially. -/
theorem planesInAt_law (h : Verify.publicOf pol KL layout = .ok X) (digits : Bool) {p : P}
    (e : placeAt X i digits = some p) : planesInAt X i digits = some true := by
  cases digits with
  | true => rfl
  | false => exact planesInAt_true h e

end

/-! ### the test can say no -/

/-- Where the list has no matrix of that number. -/
theorem planeCellsB_no_matrix {tl : HTailF2} {iB : ℕ} (h : tl.NM ≤ iB) (fs : Forest.Shape)
    (lm : ℕ) : planeCellsB tl fs lm iB = false := by
  unfold planeCellsB
  rw [decide_eq_false (Nat.not_lt.2 h)]
  simp

/-- Where the matrix has too few columns. -/
theorem planeCellsB_few_columns {tl : HTailF2} {fs : Forest.Shape} {lm iB : ℕ}
    (h : (tl.mats.getD iB {}).k < fs.NC * 2 ^ (fs.kT + 5 - lm)) :
    planeCellsB tl fs lm iB = false := by
  unfold planeCellsB
  rw [decide_eq_false (Nat.not_le.2 h)]
  simp

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.planes_at
#print axioms VerifiableInference.Desc.First.Look.shape_at
#print axioms VerifiableInference.Desc.First.Look.planesInAt_true
#print axioms VerifiableInference.Desc.First.Look.planesInAt_law
#print axioms VerifiableInference.Desc.First.Look.planes_seated
#print axioms VerifiableInference.Desc.First.Look.planeCellsB_no_matrix
#print axioms VerifiableInference.Desc.First.Look.planeCellsB_few_columns
