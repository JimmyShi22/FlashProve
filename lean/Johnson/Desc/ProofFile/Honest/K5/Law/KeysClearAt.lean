-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KeysClearAt.lean: CONDITIONAL: NO KEY FORM OF AN ATTENTION
SEGMENT (kind K5) NAMES A SLOT OUTSIDE THE WINDOW THAT THE KIND's HEARING TOOK: in the form of a
premise of other authors' law on the lookup's run "join" (KeysClear, Honest/K3/Good/Live/Runs.lean).
One statement with its proof: two calls.

  keysClear_att   CONDITIONAL: **KeysClear (keysOfO A) t j**, at j < k or k5End x k ≤ j

The premises. gf: GeoFits (geoOf A.S) x: public · hI: HeldLive x k t
(Johnson/Desc/K5/Honest/Law/LiveState.lean) · hj: j lies in front of the window or behind it.
Called: keysOfO_win (Johnson/Desc/K5/Honest/Law/KeysWindow.lean) · clear_of_pred
(Honest/K3/Good/Live/Bridges.lean).

Limits. Conditional. That a reached state has HeldLive is not proved here. KeysClear speaks of every
form that the reader returns: where it returns nothing the statement says nothing. No call of the
law whose premise this is stands here. All Limits of KeysWindow.lean hold here too. Through its
imports the file stands above the library's folder ThirdParty/. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.KeysWindow
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Bridges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest.Window
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.First.Att.P (geoOf GeoFits keysOfO)
open ProofFile.Honest.K3.Good.Live (KeysClear clear_of_pred)

/-- **NO KEY FORM OF AN ATTENTION SEGMENT NAMES A SLOT OUTSIDE THE WINDOW.** CONDITIONAL: GeoFits;
HeldLive at the state; j lies in front of the window or behind it. -/
theorem keysClear_att (A : OnBytes.Attention.Plan) {x : Params.AttentionRounds} {k : ℕ}
    {t : First.S} (gf : GeoFits (geoOf A.S) x) (hI : HeldLive x k t) {j : ℕ}
    (hj : j < k ∨ k5End x k ≤ j) : KeysClear (keysOfO A) t j := fun KF hk a ha =>
  clear_of_pred (keysOfO_win A gf hI hk a (Array.mem_toList_iff.2 ha))
    (fun w => by
      have w1 : k ≤ j := w.1
      have w2 : j < k5End x k := w.2
      omega)

end H2K5.Honest.Window

#print axioms H2K5.Honest.Window.keysClear_att
