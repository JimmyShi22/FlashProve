-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/FullOfHear.lean: CONDITIONAL.

Not shown here. THAT A HEARING RETURNS. That the public data P at which it runs have the layout and
the scales of any public parameters X, and that X has four layers in a group: eY, eS and eL are
hypotheses (Honest/K4/Law/W/FullHead.lean has them at the library's own values). Of the hypotheses
together no example is known. THE FULL SIZE ALONE: `FullAt` names the library's reference sizes.
Nothing on soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import: no module under
Johnson/Goal/, Johnson/D/ or ThirdParty/, and none whose name holds RecCompile. It imports nothing
of the honest side (Johnson/Desc/ProofFile/Honest/).

The hypothesis `FullAt` (W/IdnOfField.lean) at what a hearing of the feed-forward layers' own rounds
(sub-protocol K4) returns. One statement with its proof: the library's `hear_public`
(OnBytes/Desc/First/K4/HearPublic.lean) says which environment the hearing lays: the layout, the
scales and the group are those at which it runs.

  `fullAt_of_hear`   `FullAt X g (layerShape X.P) DF o`, from a return of the hearing at group g.
-/
import OnBytes.Desc.First.K4.HearPublic
import Johnson.Road.K4.W.IdnOfField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2 Own)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.K4 (hear engFl hear_public)
open Inst.Model.All (DF)

/-- **`FullAt` at what a hearing returns.** CONDITIONAL: on hh, eY, eS and eL. -/
theorem fullAt_of_hear {P : Layer.Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hh : hear engFl P hp g fo F t = some (o, G, u)) {X : Verify.Public}
    (eY : P.y = X.y) (eS : P.sc = X.layers.sc) (eL : X.y.Lam = 4) :
    FullAt X g (Verify.layerShape X.P) DF o := by
  obtain ⟨_, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, _, _, ev, _⟩ := hear_public hh
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [ev]
    exact eY
  · rw [ev]
    exact eS
  · rw [ev]
  · rw [ev]
    show P.y.Lam = 4
    rw [eY]
    exact eL

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.fullAt_of_hear
