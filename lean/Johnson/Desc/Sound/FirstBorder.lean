-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FirstBorder.lean: THE TABLE'S PROMISE AT THE FIRST CHAIN'S FIRST BORDER, AT A
STATEMENT OF THE CHAIN. One lemma. No protocol's soundness is said.

What is said. Johnson/Desc/First/BordersStart.lean shows the promise `onAt` at the front block's
place, at what is open at the start, of a first record (`IsStart`), from four things: the stored
table decodes; a lawful first record is in order; the two public items that are open at the start
hold of it (the request passes the start's test; no reply has been heard). `onQ_zero_of_start`
carries that to the condition at border 0 as the rule of composition takes it (`onQ`,
BordersQ.lean): where the list of places begins with the front block's.

Limits: those of BordersStart.lean. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.BordersStart
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First

/-- **The condition at border 0, at a statement whose record is a first record.** -/
theorem onQ_zero_of_start {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S)
    (hps : ps[0]? = some frontPlace) (a : A × Fr.E.Str) {codes : OnBytes.Codes}
    {req : Array UInt32} (ha : IsStart codes req (get a.1).2)
    (hd : Mg.decodes (get a.1) (strsOf Fr a.2))
    (hin : (get a.1).2.failed = none → Mg.inOrder (get a.1) = true)
    (hpub : (get a.1).2.failed = none → ∀ q ∈ pubStartM Mg.more, Mg.pub q (get a.1) = true)
    (hpp : (get a.1).2.failed = none → ∀ q ∈ pubStartM Mg.more, Mg.pubP q (get a.1))
    (hbk : N.treesAt (some frontPlace) = 0) (hms : N.msgsAt (some frontPlace) = 0) :
    onQ (Fr := Fr) N Mg links ps get 0 a := by
  unfold onQ
  rw [hps, openSets_head, pubSets_head]
  exact onAt_start N Mg links _ _ ha hd hin hpub hpp hbk hms

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.onQ_zero_of_start
