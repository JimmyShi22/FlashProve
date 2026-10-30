-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPLangsProofs.lean: the statements of Cm/TargetPLangs.lean, proved: applications.

The content of the proofs is in other files. Languages, `TP.sub`, `TP.admits` at a variable prime:
Cm/TargetPRelProofs.lean. The index's side (the entries of an index hold it; `heldB` reads the
layout): Cm/TargetLangsProofs.lean. The configuration's properties: Cb/Obj/LdObjectConfProofs.lean,
Cb/Obj/LdObjectConfMore.lean. The code's side with room, the placing: Cm/TargetLangsGl.lean. The
guards: `lawful_sRef` (Cm/Rel2Guards.lean), and the facts on true requests of Cm/RelTrue.lean, which
`Cm.TP.trace_iff`, `Cm.TP.lang_yes` and `Cm.TP.lang_no` carry.

Main names:
  `target_p_prime`: the characteristic of a finite field is a prime.
  `targetGl_big`: 2^61 - 1 ≤ 2^64 - 2^32 + 1.

Limits: what the head of Cm/TargetPLangs.lean lists as not said is not said here either.
-/
import Cm.TargetPLangs
import Cm.TargetPRelProofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Iop Prob Hiop Blocks Cb Cb.Ood
open Inst.Model.Layout (kRef hRef)

theorem target_p_prime (F : Type) [Field F] [Fintype F] (p : ℕ) [CharP F p] : p.Prime :=
  CharP.char_is_prime F p

theorem target_p_256 {p : ℕ} (h : 2 ^ 61 - 1 ≤ p) : 256 ≤ p := le_trans (by norm_num) h

theorem targetGl_big : 2 ^ 61 - 1 ≤ Gl.p := by
  show 2 ^ 61 - 1 ≤ Code.pGold
  rw [Code.pGold_eq]
  norm_num

attribute [local irreducible] targetHeld targetBody

theorem target_p_langs : Spec.target_p_langs := fun F _ _ _ _ _ p _ hB s h _ _ =>
  have hp := target_p_prime F p
  have h3 : ∀ (i : Idx) (x : Instance ppref) (w : Trace),
      TP.Rno p s i x w → TP.Ryes p s i x (trace2 s i x) :=
    fun i x w hR => (TP.trace_iff p hp hB s h i x).2 (TP.forces p hp hB s h i x w hR)
  ⟨fun i x w hR => ⟨_, h3 i x w hR⟩, fun i x w hR => TP.sub p s i x _ (h3 i x w hR), h3⟩

theorem target_p_true : Spec.target_p_true := fun F _ _ _ _ _ p _ hB s h _ _ i x =>
  ⟨TP.lang_no p (target_p_prime F p) hB s h i x, TP.lang_yes p (target_p_prime F p) hB s h i x⟩

theorem target_p_model : Spec.target_p_model := by
  intro F E _ _ _ _ p _ hB s h Cf₀ pl hinj
  have h3 : ∀ i, targetHeld Cf₀ pl (targetBody Cf₀ pl i) = some i :=
    targetHeld_body Cf₀ pl p (target_p_256 hB) hinj
  have h4 : ∀ a a' : Cf₀.Row × Cf₀.J₀ → F,
      (∀ r l, a (r, Cf₀.lay l) = a' (r, Cf₀.lay l)) → targetHeld Cf₀ pl a = targetHeld Cf₀ pl a' :=
    targetHeld_reads Cf₀ pl
  exact { sub := TP.sub p s, admits := TP.admits p (target_p_prime F p) hB s h,
          held := h3, reads := h4 }

theorem target_p_code {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (p : ℕ)
    (s : Scales) (Cf₀ : LdCf F E) (pl : TargetEnt → Cf₀.Row × Cf₀.Lay) (L : ℕ) (h : Cf₀.CodeOK L) :
    (targetCfP Cf₀ pl p s).CodeOK L :=
  ⟨h.core, h.rad, h.list, h.evades⟩

theorem target_p_props :
    Spec.target_p_props := fun F E _ _ _ _ _ p _ hB s h Cf₀ pl L b hinj hC hPB hb =>
  ldCf_props F E (targetCfP Cf₀ pl p s) L b
    (ldCm_ok F E (targetCfP Cf₀ pl p s) L (target_p_code p s Cf₀ pl L hC)
      (target_p_model F E p hB s h Cf₀ pl hinj))
    hPB hb

/-- The guards at the protocol's prime: (a) is `lawful_sRef`; (b) to (e) are facts on true requests
(Cm/RelTrue.lean), carried by `TP.trace_iff`, `TP.lang_yes` and `TP.lang_no` at this prime. -/
theorem target_p_guards : Spec.target_p_guards :=
  have hp : Gl.p.Prime := target_p_prime Gl.F Gl.p
  ⟨lawful_sRef,
   fun s h rF eF hre =>
     ⟨Idx.ofIndex ScalesSanity.iZero, RequestGuards2.xz rF eF, rfl, rfl,
       (TP.trace_iff Gl.p hp targetGl_big s h _ _).2 (true_zero h.toPP rF eF hre)⟩,
   fun s h =>
     ⟨Idx.ofIndex ScalesSanity.iZero, fun x _ hr he hw hT =>
       false_zero _ _ x hr he hw ((TP.lang_no Gl.p hp targetGl_big s h _ x).1 hT)⟩,
   let ⟨i, i', x, _, _, _, d, e⟩ := true_layer
   ⟨i, i', x, (TP.lang_yes Gl.p hp targetGl_big sRef lawful_sRef i x).2 d,
     fun hT => e ((TP.lang_no Gl.p hp targetGl_big sRef lawful_sRef i' x).1 hT)⟩,
   let ⟨i, q, q', y, a, d, e⟩ := true_earlier
   ⟨i, q, q', y, a, (TP.lang_yes Gl.p hp targetGl_big sRef lawful_sRef i _).2 d,
     fun hT => e ((TP.lang_no Gl.p hp targetGl_big sRef lawful_sRef i _).1 hT)⟩⟩

end Cm
