-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/Step1.lean: rounds 1 and 2 of the shared chain: the sending of the folded row
G_u.

Definitions only; no theorem is stated. The words are explained in State.lean, and what has been run
and what is not checked is told in Fold.lean.

In these two rounds G_u is sent, together with the messages that linWithU names: where the shape
sends masks ahead, the first of them is the mask message of the first fold of the test on G_u's
group. G_u's sample is answered, G_u joins its group, and the rows of the table's record are added
to that group as open rows.

Main names:
  eqGammaOf: the weights of the table's rows at the high coordinates of the shared point.
  step1: follows the first lines of foldeqVerify (OnBytes/Iop/Foldeq.lean) as linSharedVerify calls
    it (OnBytes/Iop/Lin.lean). It refuses unless the key's sizes fit the table's shape, no seed of
    the key has the factor 0, and the high part of the shared point has as many coordinates as the
    shape says. It writes the messages' numbers, the elements drawn, the answers, where the folded
    row is, and the mask message's number. At this place the program also asks foldeqOk. That is a
    clause of linOk, which step0 has asked, so it is not asked again.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.
What this comment says of the code rests on reading and is not machine-checked.


-/
import Johnson.Desc.Shared.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Shared
open OnBytes OnBytes.Params

/-- The weights of the table's rows at the high coordinates of the shared point. -/
def eqGammaOf (p : Par) (l : Loc) : Array E := foldeqWeights (l.psi.drop p.S.kLo)

/-- Rounds 1 and 2: the sending of the folded row. -/
def step1 (G : Ground Loc) (p : Par) (d : DState Loc) : List Fmt.RoundView → Option (DState Loc)
  | [r₁, r₂] => do
    let S := p.S.fold
    let w ← linWithU p.S
    if p.key.fits S.index && p.key.seeds.all (fun x => !isZeroE x.beta) &&
        (d.loc.psi.drop p.S.kLo).length == S.index.v then
      let (ids, sd, an, d₁) ← sendP G p d (#[(⟨S.u, S.leafClass⟩ : OracleNotice)] ++ w) r₁ r₂
      let u : FoldedRow := ⟨ids.getD 0 noId, vectorLay d₁.st.codes S.u S.rowsHigh⟩
      let mask ← if p.S.masksAhead then ((ids.extract 1 ids.size)[0]?).map some else some none
      let l : Loc := { d.loc with idsU := ids, sdU := sd, anU := an, u := u, mask := mask }
      let d₂ ← G.join p d₁ l.gU u.oracle false
      let rows ← p.key.seeds.zipIdx.mapM fun x =>
        foldeqRecordRow S x.1 p.key.record x.2 (eqGammaOf p l) u
      let d₃ ← G.addRows p d₂ l.gU rows
      some { d₃ with loc := l }
    else none
  | _ => none

end Desc.Shared
