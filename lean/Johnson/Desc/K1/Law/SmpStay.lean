-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SmpStay.lean: a relation on statements: the codes stay, and every message that
is sampled stands behind at its number, with its shape, its mark and its sample rows. It follows
from two relations together, "a statement only grows" (Johnson/Desc/Grows.lean) and "a sampled
message's sample rows stay" (Johnson/Desc/Ground/Begin.lean): so every plain function of the ground
keeps it, and the beginning of a proximity test too.

Main names: SmpStay, SmpStay.refl, SmpStay.trans, smpStay_of, groundKeeps_smpStay,
beginRun_smpStay.

What is not claimed. Nothing on a message that is not sampled, on groups, open rows, pads or
ledgers. Nothing on a step that writes the statement by another road than these functions. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.Ground.Begin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Ground

/-- The codes stay; every sampled message of A stands in B with its shape, mark and sample rows. -/
def SmpStay (A B : Statement) : Prop :=
  B.codes = A.codes ∧ ∀ (i : Nat) (x : OnBytes.Oracle), A.oracles[i]? = some x →
    x.sampled = true → ∃ x' : OnBytes.Oracle, B.oracles[i]? = some x' ∧ x'.shape = x.shape ∧
      x'.sampled = true ∧ x'.sampleRows = x.sampleRows

theorem SmpStay.refl (A : Statement) : SmpStay A A :=
  ⟨rfl, fun _ x h s => ⟨x, h, rfl, s, rfl⟩⟩

theorem SmpStay.trans {A B C : Statement} (h : SmpStay A B) (k : SmpStay B C) : SmpStay A C := by
  refine ⟨k.1.trans h.1, fun i x hx s => ?_⟩
  obtain ⟨y, hy, a1, a2, a3⟩ := h.2 i x hx s
  obtain ⟨z, hz, b1, b2, b3⟩ := k.2 i y hy a2
  exact ⟨z, hz, b1.trans a1, b2, b3.trans a3⟩

/-- **It follows from the two relations together.** -/
theorem smpStay_of {A B : Statement} (g : Grows A B) (k : SampleKept A B) : SmpStay A B := by
  refine ⟨g.1, fun i x hx s => ?_⟩
  obtain ⟨x', hx', s', r'⟩ := k i x hx s
  obtain ⟨x'', hx'', o⟩ := g.2.2 i x hx
  have e : x'' = x' := Option.some.inj (hx''.symm.trans hx')
  rw [e] at o
  exact ⟨x', hx', o.1, s', r'⟩

/-- **Every plain function of the ground keeps it.** -/
theorem groundKeeps_smpStay : GroundKeeps SmpStay where
  refl := SmpStay.refl
  trans := fun h k => h.trans k
  newGroup := fun d d' c m n h =>
    smpStay_of (groundKeeps_grows.newGroup d d' c m n h) (groundKeeps_kept.newGroup d d' c m n h)
  recv := fun f d d' s i h =>
    smpStay_of (groundKeeps_grows.recv f d d' s i h) (groundKeeps_kept.recv f d d' s i h)
  admit := fun d d' o r h =>
    smpStay_of (groundKeeps_grows.admit d d' o r h) (groundKeeps_kept.admit d d' o r h)
  join := fun d d' g o k h =>
    smpStay_of (groundKeeps_grows.join d d' g o k h) (groundKeeps_kept.join d d' g o k h)
  addRow := fun d d' g r h =>
    smpStay_of (groundKeeps_grows.addRow d d' g r h) (groundKeeps_kept.addRow d d' g r h)
  takeMask := fun d d' o n h =>
    smpStay_of (groundKeeps_grows.takeMask d d' o n h) (groundKeeps_kept.takeMask d d' o n h)
  closeLedger := fun d d' o h =>
    smpStay_of (groundKeeps_grows.closeLedger d d' o h) (groundKeeps_kept.closeLedger d d' o h)
  spendAsMask := fun d d' o h =>
    smpStay_of (groundKeeps_grows.spendAsMask d d' o h) (groundKeeps_kept.spendAsMask d d' o h)
  adopt := fun d d' s g i h =>
    smpStay_of (groundKeeps_grows.adopt d d' s g i h) (groundKeeps_kept.adopt d d' s g i h)
  elsewhere := fun d d' m o t h =>
    smpStay_of (groundKeeps_grows.elsewhere d d' m o t h)
      (groundKeeps_kept.elsewhere d d' m o t h)

/-- The beginning of a proximity test keeps it. -/
theorem beginRun_smpStay {L : Type} (d d' : DState L) (g : Nat) (inp : RunInput)
    (h : beginRunP d g = some (inp, d')) : SmpStay d.st d'.st :=
  smpStay_of (beginRunP_grows d d' g inp h) (beginRun_kept d d' g inp h)

/-- A try: a statement that has lost a sampled message is not behind. -/
theorem not_smpStay_lost (A B : Statement) (i : Nat) (x : OnBytes.Oracle)
    (hx : A.oracles[i]? = some x) (hs : x.sampled = true) (hB : B.oracles[i]? = none) :
    ¬ SmpStay A B := by
  intro h
  obtain ⟨x', hx', _⟩ := h.2 i x hx hs
  rw [hB] at hx'
  cases hx'

end VerifiableInference.Desc.K1
