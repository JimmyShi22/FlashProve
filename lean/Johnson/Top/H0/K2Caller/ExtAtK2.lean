-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/ExtAtK2.lean: code switching: AT A PLACE OF THE KIND K2 THE TABLE OF JOINTS'
EXTRACTOR (extQ · extQAt, Johnson/Desc/Sound/BordersFill.lean) LAYS PADS ALONE: no member's message
and no token. Two equations with their proofs. General in the numbers N, the list of segments and
the place. NO SUB-PROTOCOL IMPORTS THIS FILE.
  extQ_k2     p.kind = .K2: extQ … N links p a y behind w is extAt … [] (minePadAt ms N links p)
              false none a y w
  extQAt_k2   the same at sub-protocol number k of a list of places, where the place there is of
              the kind: the right side of the fourth tie's premise on the piece's extractor
CALLED: mineAt_K2 · laysTok_K2 (Johnson/Desc/Sound/MembersAtB.lean).
LIMITS. That a piece's extractor IS the table's (EachExtQ) and that the place at a number is of the
kind are premises or others' closed facts. No soundness is claimed.
-/
import Johnson.Desc.Sound.MembersAtB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Place Strs FileDescription Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Numbers)
open Johnson.Pack

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × First.S → Tok)

/-- **At a place of the kind the table's extractor lays pads alone.** -/
theorem extQ_k2 (N : Numbers) (links : List ModelPart) (p : Place) (hk : p.kind = .K2)
    (a : P × First.S) (y : Strs) (behind : Option (P × First.S)) (w : Wit Cells Tok MsgT) :
    extQ cs G arr smp ms decT c₀ tokOf N links p a y behind w =
      extAt cs G arr smp decT c₀ [] (minePadAt ms N links p) false none a y w := by
  unfold extQ
  rw [mineAt_K2 ms N links p hk, laysTok_K2 links p hk]
  rfl

/-- **The same at sub-protocol number k.** -/
theorem extQAt_k2 {A : Type} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (p : Place) (hp : ps[k]? = some p) (hk : p.kind = .K2)
    (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w =
      extAt cs G arr smp decT c₀ [] (minePadAt ms N links p) false none (get a.1)
        (strsOf Fr a.2) w := by
  unfold extQAt
  rw [hp]
  exact extQ_k2 cs G arr smp ms decT c₀ tokOf N links p hk _ _ _ w

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.extQ_k2
#print axioms VerifiableInference.Desc.First.K2Caller.extQAt_k2
