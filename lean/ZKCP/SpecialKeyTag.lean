-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/SpecialKeyTag.lean: the two forms of "a tag in the key" agree.

A scheme with batches over the one oracle gives a scheme of ZKCP/Defs.lean, with one request in each
call (`oneOf`, ZKCP/SpecialAny.lean; `extOf`, `simOf`, ZKCP/SpecialDefs.lean). Putting the tag into
the key (ZKCP/GenKeyTag.lean, ZKCP/KeyTag.lean) before or after that step gives the same terms:
  `oneOf_tagKey`                  oneOf (G.tagKey t) = (oneOf G).tagKey t
  `extOf_tagKey`, `simOf_tagKey`  the same for the extractor and the simulator, by definition
  `oneOf_tagKey_V_of_ne`          so V of oneOf (G.tagKey t) on a key that names another tag is
                                  "false"

Beside the tool `ofRom_bind` it proves nothing else.
-/
import ZKCP.SpecialAny
import ZKCP.KeyTag
import ZKCP.GenKeyTag

set_option autoImplicit false

namespace ZKCP.SpecialAny

open Rom (rom toRom ofRom)
open ZKCP.Special

variable {lam : ℕ} {I X W PP IVK ISK Pf T : Type}

theorem ofRom_bind {α β : Type} (c : Rom.OComp (rom lam) α) (g : α → Rom.OComp (rom lam) β) :
    ofRom (c.bind g) = (ofRom c).bind fun a => ofRom (g a) := by
  induction c with
  | pure a => rfl
  | query o q k ih => simp only [Rom.OComp.bind, ofRom, OComp.bind, ih]
  | sample n k ih => simp only [Rom.OComp.bind, ofRom, OComp.bind, ih]

theorem extOf_tagKey (E : Gen.Extractor (rom lam) I X W IVK Pf) :
    extOf (E.tagKey (T := T)) = (extOf E).tagKey := rfl

theorem simOf_tagKey (Sim : Gen.Simulator (rom lam) PP IVK X Pf) (t : T) :
    simOf (Sim.tagKey t) = (simOf Sim).tagKey t := rfl

variable [DecidableEq T]

/-- The tag before or after the step to one request in each call: the same scheme. -/
theorem oneOf_tagKey (G : Gen.Arg (rom lam) I X W IVK ISK Pf) (t : T) :
    oneOf (G.tagKey t) = (oneOf G).tagKey t := by
  have hC : (oneOf (G.tagKey t)).C = ((oneOf G).tagKey t).C := funext fun i => ofRom_bind (G.C i) _
  have hV : (oneOf (G.tagKey t)).V =
      ((oneOf G).tagKey t).V := funext fun v => funext fun x => funext fun π => by
    show ofRom (if v.1 = t then G.V v.2 x π else .pure false) =
      if v.1 = t then ofRom (G.V v.2 x π) else .pure false
    split <;> rfl
  have hP : (oneOf (G.tagKey t)).P = ((oneOf G).tagKey t).P := rfl
  calc
    oneOf (G.tagKey t) = ⟨(oneOf (G.tagKey t)).C, (oneOf (G.tagKey t)).P, (oneOf (G.tagKey t)).V⟩ :=
      rfl
    _ = ⟨((oneOf G).tagKey t).C, ((oneOf G).tagKey t).P, ((oneOf G).tagKey t).V⟩ := by
      rw [hC, hP, hV]
    _ = (oneOf G).tagKey t := rfl

theorem oneOf_tagKey_V_of_ne (G : Gen.Arg (rom lam) I X W IVK ISK Pf) (t : T) {t' : T} (h : t' ≠ t)
    (ivk : IVK) (x : X) (π : Pf) :
    (oneOf (G.tagKey t)).V (t', ivk) x π = .pure false := by
  rw [oneOf_tagKey]
  exact tagKey_V_of_ne _ t h ivk x π

end ZKCP.SpecialAny
