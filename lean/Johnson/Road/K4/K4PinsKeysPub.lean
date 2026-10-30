-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsKeysPub.lean: FOUR FIELDS OF `KeysFit` (Johnson/Road/K4/K4PinsKeys.lean) ARE
NO DEBTS WHERE `PublicSteps` AND `RefPub` STAND: the numbers of the plan's trees are the library's
at the reference sizes · eight calls · the library's bounds on the shape · a group has four layers.
Calls of the library's lemmas.
One theorem. No draw, no count.

  **`keysFit_of_pub`**: `KeysFit X p q`, from: `PublicSteps pol KL X` · `RefPub X p.g` · the plan's
    public parameters are X's layers' with some tokens · X's plan of group p.g is p.hp · q's shape,
    scale file and group are X's and p's.

CALLED: `lines_calls` (Johnson/Road/FormsKeysCaller.lean) · `treesFit_of_layout`
(Johnson/Road/FormsKeysLookT.lean) · `fo_of_layout` (Johnson/Road/FormsKeysShape.lean) · `steps_ok`
(Johnson/Road/K4/RefPubSteps.lean) · `laySizes_of_layout` (Johnson/Road/K4/PlanSizes.lean).

OBJECT: none of its own. USER: K4PinsKeysAt.lean; meant: `k4_own_end` (K4PinsEnd.lean), whose
structure `K4PlanFit` has `KeysFit` as a field. LETTERS: X, p, q, pol, KL, tk: free.

Limits. K04_law IS NOT PROVED BY THIS. `PublicSteps` and `RefPub` stay premises.
-/
import Johnson.Road.K4.K4PinsKeys
import Johnson.Road.K4.RefPubSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model.Layer (Env)
open OnBytes.Model.Verify (Public layerShape)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First.Look (LayPub)
open Inst.Model.FFSeg (Dim)

/-- **`KeysFit` where `PublicSteps` and `RefPub` stand.** -/
theorem keysFit_of_pub {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat} {q : LayPub}
    (St : PublicSteps pol KL X) (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (h1 : q.h = layerShape X.P) (h2 : q.sc = X.layers.sc)
    (h3 : q.g = p.g) : KeysFit X p q := by
  obtain ⟨s0, HL, _, _⟩ := B.lines p.hp hG
  have PL := HL tk
  rw [← hP] at PL
  obtain ⟨h8, Hc⟩ := OnBytes.Road.lines_calls PL.hN
  have ey : p.P.y = X.layers.y := by rw [hP]
  refine ⟨?_, ?_, ?_, h1, h2, h3, ?_⟩
  · exact OnBytes.Road.treesFit_of_layout (v := ⟨p.P.y, p.P.sc, p.g, 0, 0, [], #[]⟩) PL.hy PL.S
      PL.Z PL.hc h8 fun cc => by
        obtain ⟨cd, a1, a2⟩ := Hc cc
        exact ⟨cd, a1, a2, PL.hfl cc⟩
  · rw [(OnBytes.Road.fo_of_layout PL.hy).2.1, (OnBytes.Road.fo_of_layout PL.hy).2.2, h8]
  · rw [ey]
    exact steps_ok St
  · rw [← ey, (laySizes_of_layout PL.hy).Lam, ← PL.Z.lL]
    rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.keysFit_of_pub
