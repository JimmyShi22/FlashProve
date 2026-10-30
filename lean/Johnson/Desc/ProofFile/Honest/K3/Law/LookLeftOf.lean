-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/LookLeftOf.lean: the honest side of the kind "lookup" (K3).
What the lookup leaves, put together from what the walk along the verifier's text yields. Three
definitions, three theorems.

Terms. Honest/K3/GLOSSARY.md ("course", "lawful", "world, worth").

What is shown.
  `RowsWorth`, `LateRow`: the two sentences that the walk carries beside the conclusion of
    `LookHeard`: each heard row is worth 0 if its stage's summand sums as it should; the leaves'
    late row is worth eps (1 - cf).
  `Left`: what the lookup leaves: the conclusion of `LookLeft` (Honest/K3/Law/Statements.lean),
    under a name. `lookLeft_iff` holds it against that statement's text.
  `lookLeft_of`: conditional on `Lawful`, on one part of keys, and on these two sentences: `Left`.

Hypotheses that remain, in `lookLeft_of`. `Lawful` (`hLaw`); one part of keys (`hp`); `RowsWorth`
and `LateRow` (`h1`, `h2`); besides `Fit` (`hF`), `Cut` (`C`), the hearing's return (`hh`),
`HeardIs` (`hH`) and the invariant behind the last stage (`hI`). Other files deliver them.

Users. This file is imported by Honest/K3/Law/LookOne.lean, Honest/K3/Law/SeatedWorth.lean and
Honest/K3/Law/Thread/ExchangeRows.lean.

Limits. It proves the conclusion of `LookLeft` at a face with one part of keys alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Steps
import Johnson.Desc.ProofFile.Honest.K3.Law.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Reading Aff Fork ofNat)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV planesV eqPairs)

variable {W : Type}

/-- Each heard row is worth 0 in the world of every later ledger, if the summands of all stages
with end values sum as they should. -/
def RowsWorth (R : Course W) (g : HeardV) (G : Fork) : Prop :=
  (∀ s ∈ stages R.f, 0 < s.tail R.f →
    Sums R s (rd (R.claimed s)) (rd (endTerm R.factor s (R.shown s)))) →
  ∀ y ∈ g.rows.toList, ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H →
    MasksAre R mask → y.value Reading.gl (H.worldOf Reading.gl mask entry) = 0

/-- The leaves' row, made late, is worth eps (1 - cf), if the leaves' summand sums to cf. -/
def LateRow (R : Course W) (g : HeardV) (G : Fork) : Prop :=
  ∀ cf : GE, Sums R .leaves (rd (R.claimed .leaves)) cf →
    ∀ (F' G' H : Fork) (y : Aff) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
      Sized F' → Later G F' → MaskedSum.row g.leaves oneE {} F' = some (y, G') → Later G' H →
      MasksAre R mask →
      y.value Reading.gl (H.worldOf Reading.gl mask entry) = rd g.leaves.eps * (1 - cf)

/-- **What the lookup leaves**: the conclusion of `LookLeft`, under a name. -/
def Left (R : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE) (g : HeardV)
    (G : Fork) : Prop :=
  (∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H → MasksAre R mask →
    (∀ y ∈ g.rows.toList, y.value Reading.gl (H.worldOf Reading.gl mask entry) = 0) ∧
    (∀ y ∈ R.f.parts.zipIdx, (R.form (.key y.2 y.1)).value Reading.gl
        (H.worldOf Reading.gl mask entry) =
      rd R.pts.alpha - keys y.2 (R.pts.keyPt y.2 y.1))) ∧
  (∀ (F' G' H : Fork) (cl : List PlaneClaim) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
    Sized F' → Later G F' → planesV R.f g F' = some (cl, G') → Later G' H → MasksAre R mask →
    ∀ y ∈ cl, y.lead.value Reading.gl (H.worldOf Reading.gl mask entry) +
      rd y.scalar * planes y.pairs = 0)

/-- `Left` is the conclusion of the statement `LookLeft`: this theorem fails to compile if one of
the two texts changes. -/
theorem lookLeft_iff : LookLeft ↔
    ∀ (W : Type) (R : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE)
      (F G : Fork) (x : List Fmt.RoundView) (g : HeardV),
      Fit R → Inv R 0 F → R.rounds = some x → hearV R.f F x = some (g, G) → Lawful R planes keys →
      Left R planes keys g G := Iff.rfl

theorem mem_bits (f : LFace) : Stage.bits ∈ stages f := by
  unfold stages
  simp

/-- **Conditional on `Lawful`, on one part of keys, and on what the walk yields: what the lookup
leaves.** -/
theorem lookLeft_of (R : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE)
    (F G : Fork) (x : List Fmt.RoundView) (g : HeardV) (v : Nat) (hp : R.f.parts = [v]) (hF : Fit R)
    (C : Cut R x) (hh : hearV R.f F x = some (g, G)) (hH : HeardIs R g)
    (hI : Inv R (stages R.f).length G) (h1 : RowsWorth R g G) (h2 : LateRow R g G)
    (hLaw : Lawful R planes keys) : Left R planes keys g G := by
  have hall : ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H →
      MasksAre R mask → ∀ s' ∈ stages R.f, ∀ j, j < s'.tail R.f →
      (H.worldOf Reading.gl mask entry).slot (R.endSlot s' + j) = rd (R.T s' j) := by
    intro H mask entry hl hM s' hs' j hj
    exact hI.ends H mask entry hl hM s' (by rw [List.take_length]; exact hs') j hj
  have P : PointsAgree R.f g R.a.base (R.t.heard ++ R.ds) := by
    have := pointsAgree_of_hearV R.f v hp F G x g R.t.heard [] hh
    rw [C.drawn, List.append_nil, hF.base] at this
    exact this
  refine ⟨fun H mask entry hl hM => ⟨fun y hy => h1 hLaw.sums y hy H mask entry hl hM, ?_⟩, ?_⟩
  · intro y hy
    rw [← hLaw.keyEnds y hy]
    exact formWorth W R _ (.key y.2 y.1) hF.ok (Or.inr ⟨y, hy, rfl⟩)
      (fun s' hs' j hj => hall H mask entry hl hM s' (List.mem_of_mem_take hs') j hj)
  · intro F' G' H cl mask entry hS hGF hpl hl hM y hy
    cases hr : MaskedSum.row g.leaves oneE {} F' with
    | none => simp [planesV, hr] at hpl
    | some z =>
      obtain ⟨y0, G0⟩ := z
      simp only [planesV, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpl
      obtain ⟨rfl, rfl⟩ := hpl
      have hlater : Later G H := hGF.trans ((MaskedSum.row_keeps hr).trans hl)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · have e := h2 _ hLaw.leaves F' G0 H y0 mask entry hS hGF hr hl hM
        show y0.value Reading.gl (H.worldOf Reading.gl mask entry) +
          rd (mulE g.leaves.eps (R.f.leaf g.theta g.alpha g.zb0)) *
            planes (eqPairs (R.f.mu + R.f.d) g.zb0) = 0
        rw [P.theta, P.alpha, P.zb0, e]
        have em : rd (mulE g.leaves.eps (R.f.leaf R.pts.theta R.pts.alpha R.zb0)) =
            rd g.leaves.eps * rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) := Reading.gl.mul _ _
        show rd g.leaves.eps * (1 - (1 + rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) *
            planes (eqPairs (R.f.mu + R.f.d) R.zb0))) +
          rd (mulE g.leaves.eps (R.f.leaf R.pts.theta R.pts.alpha R.zb0)) *
            planes (eqPairs (R.f.mu + R.f.d) R.zb0) = 0
        rw [em]
        ring
      · have e := hall H mask entry hlater hM .bits (mem_bits R.f) 0 (show 0 < 1 by omega)
        show (Aff.slot g.sBit).value Reading.gl (H.worldOf Reading.gl mask entry) +
          rd (subE zeroE oneE) * planes (eqPairs (R.f.mu + R.f.d) g.zb1) = 0
        rw [Aff.value_slot, hH.sBit, P.zb1]
        have e' : (H.worldOf Reading.gl mask entry).slot (R.endSlot .bits) = rd (R.T .bits 0) := e
        have es : rd (subE zeroE oneE) = 0 - 1 :=
          (Reading.gl.sub _ _).trans (by rw [Reading.gl.zero, Reading.gl.one])
        rw [e', hLaw.bits, es]
        show planes (eqPairs (R.f.mu + R.f.d) R.zb1) +
          (0 - 1) * planes (eqPairs (R.f.mu + R.f.d) R.zb1) = 0
        ring
      · show (Aff.ofConst (subE zeroE (ofNat R.f.count))).value Reading.gl
            (H.worldOf Reading.gl mask entry) + rd oneE * planes (countPairs R.f) = 0
        have e1 : rd oneE = 1 := Reading.gl.one
        rw [Aff.value_ofConst, Reading.gl.sub, Reading.gl.zero, e1, hLaw.count]
        show 0 - rd (ofNat R.f.count) + 1 * rd (ofNat R.f.count) = 0
        ring

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.lookLeft_iff
#print axioms ProofFile.Honest.K3.Law.mem_bits
#print axioms ProofFile.Honest.K3.Law.lookLeft_of
