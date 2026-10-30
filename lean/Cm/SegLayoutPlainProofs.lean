-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegLayoutPlainProofs.lean: the proof of the statement of Cm/SegLayoutPlain.lean, as it is stated
there.
-/
import Cm.SegLayoutPlain
import Cm.SegLayoutProofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm
open Seg Inst.Model Inst.Model.All

theorem lay_below_plain : Spec.lay_below_plain := by
  intro B T
  constructor
  · intro hB n hn
    cases n with
    | ff g c =>
      have := hB.ff g hn.1 c hn.2.1
      rw [vFF_eq, ownFF_own hn.2.2] at this
      exact this
    | att g c =>
      have := hB.att g hn.1 c hn.2.1
      rw [vAtt_eq, ownAtt_own hn.2.2] at this
      exact this
    | hf φ i => exact hB.hf i hn.2 φ hn.1
    | hd φ i => exact hB.hd i hn.2 φ hn.1
    | hr φ i => exact hB.hr i hn.2 φ hn.1
  · intro hN
    exact
      { ff := fun g hg c hc => by rw [vFF_eq]; exact hN _ (ownFF_valid _ hg hc)
        att := fun g hg c hc => by rw [vAtt_eq]; exact hN _ (ownAtt_valid _ hg hc)
        hf := fun i hi φ hφ => hN (.hf φ i) ⟨hφ, hi⟩
        hd := fun i hi φ hφ => hN (.hd φ i) ⟨hφ, hi⟩
        hr := fun i hi φ hφ => hN (.hr φ i) ⟨hφ, hi⟩ }

end Cm
