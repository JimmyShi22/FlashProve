-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/LeftP.lean: kind K5: the claim that each of the segment's masked sumchecks
leaves, as one linear form a sumcheck. Pure: nothing is written.

It takes the place's numbers (Att/Geo.lean), each lookup call's key point, what the kind has heard
(Att/K5Heard.lean) and the ledger behind the hearing, which is read for what was shown under the end
values' numbers.
For a sumcheck it gives - (c - eps S0) + <u(r), the hiding polynomial's coefficients> + eps P (T - C),
the form that must be 0. S0 is the summand at the challenges on the shown end values: the one place
where values of the proof are multiplied with each other.

Main names:
  `formOf`: a copy of the part's form of a row (MaskedSum4.lean: row), without its write (the hearing
    has made that write).
  `left`: the row of a sumcheck of products under given weights. `scoreW`: a softmax-table unit's
    weights. `leftKey`: the row of the sumcheck for the key at the index.
  `Left`, `leftP`: all the segment's rows, in the order of hearing.
The tests are on lengths alone. A number under which nothing was shown is refused.
Four coordinates number a bit of an index, so an index has at most 16 bits; that is asked by
Att/ClaimsOk.lean, not here.
Not asked here: that a sent word is below the prime (the general fold's).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5AttentionKind
import Johnson.Desc.First.Att.Geo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc.Part

/-- The claim that a masked sumcheck leaves, as a form. The part's text, without its write. -/
def formOf (h : MaskedSum.Heard) (S0 : E) (kept : Aff) : Aff :=
  let (u, P) := MaskedSum.hidingAt (h.vars.zip h.r)
  let f := Aff.ofConst (subE zeroE (subE h.claim (mulE h.eps S0)))
  let f := MaskedSum.onSlots f h.first u
  let f := Aff.addMul f (Aff.ofConst h.target - h.start) (mulE h.eps P)
  Aff.addMul f kept h.eps

/-- The challenges of the variables' rounds: beta, the last, is left out. -/
def chal (h : MaskedSum.Heard) : Array E := h.r.dropLast.toArray

/-- LEFT of a sumcheck of products, under the weights W. -/
def left (F : Fork) (h : MaskedSum.Heard) (W : Array E) : Option Aff := do
  let s0 ← (List.range W.size).foldlM (fun a b => do
    pure (addE a (mulE (mulE (W.getD b zeroE) (← F.shown (h.sEnd + 2 * b))) (← F.shown (h.sEnd + (2 * b + 1)))))) zeroE
  pure (formOf h s0 {})

/-- The weights of a softmax-table unit's sumcheck. zk: its call's key point. r: the challenges. -/
def scoreW (g : Geo) (u : UnitG) (zk r : Array E) : Option (Array E) := do
  let z := inner u zk
  let a := g.lgk + (g.lnT - 1)
  let b := if u.below then a + g.lnT else g.lgk + g.lnT
  guard (z.size == b + 2 * g.lB)
  let head := eqPts (z.extract 0 g.lgk) (r.extract 0 g.lgk)
  let f :=
    if u.below then
      let (zs, rs) := (z.extract a b, r.extract a (a + g.lnT))
      mulE (mulE head (eqPts (z.extract g.lgk a) (r.extract g.lgk a))) (subE (eqPts zs rs) (mulE (ones zs) (ones rs)))
    else mulE head (eqPts (z.extract g.lgk b) (r.extract g.lgk (g.lgk + g.lnT)))
  pure ((weights u zk).map (mulE · f))

/-- LEFT of the sumcheck for the key at the index. rho: the challenges of the score at the index. -/
def leftKey (g : Geo) (F : Fork) (h : MaskedSum.Heard) (rho om' : Array E) : Option Aff := do
  let (lgk, lt) := (g.lgk, g.lt)
  let r := chal h
  let pj := r.extract 0 lt
  let sum ← (List.range g.NP).foldlM (fun a b => do
    let kc ← F.shown (h.sEnd + b / g.HA)
    let t ← (List.range lt).foldlM (fun t k => do
      let y := pj.getD (lt - 1 - k) zeroE
      let v ← F.shown (h.sEnd + (g.Lam + b * lt + k))
      pure (mulE t (addE (mulE v (subE (addE y y) oneE)) (subE oneE y)))) (mulE (om'.getD b zeroE) kc)
    pure (addE a t)) zeroE
  let f := mulE (eqPts (rho.extract 0 lt) (r.extract (lt + lgk) (2 * lt + lgk))) (eqPts (rho.extract lt (lt + lgk)) (r.extract lt (lt + lgk)))
  pure (formOf h (mulE f sum) {})

/-- The forms, in the order of hearing. -/
structure Left where
  scores : Array Aff
  division : Aff
  below : Aff
  on : Aff
  atIndex : Aff
  key : Aff
  cells : Aff

/-- **LEFT, for all the segment's sumchecks.** zk: each call's key point. F: the ledger behind the hearing. -/
def leftP (g : Geo) (zk : Array (Array E)) (h : Heard) (F : Fork) : Option Left := do
  let (lgk, lt) := (g.lgk, g.lt)
  let units := g.scores
  guard (units.length == h.scores.size)
  let scores ← (units.toArray.zip h.scores).mapM fun (u, _, s) => do
    left F s (← scoreW g u (zk.getD u.call #[]) (chal s))
  let wl ← g.single .wl
  let key := zk.getD wl.call #[]
  let (pw, zW) := (weights wl key, inner wl key)
  guard (pw.size == g.NP && zW.size == 1 + lgk + lt + g.ldh)
  let wHead := zW.extract 1 (1 + lgk)
  let wToken := zW.extract (1 + lgk) (1 + lgk + lt)
  let wTile := wToken.extract 0 g.lnT
  let r := chal h.division
  let division ← left F h.division (pw.map (mulE · (mulE (eqPts wHead (r.extract 0 lgk)) (eqPts wToken (r.extract lgk (lgk + lt))))))
  let r := chal h.below
  let atS := lgk + (g.lnT - 1)
  let w := tileSums g (eqTab (r.extract lgk atS)) (eqTab (r.extract atS (atS + g.lnT)))
  let below ← left F h.below (pw.map (mulE · (mulE (overTileRows g w.1 (eqTab wTile)) (eqPts wHead (r.extract 0 lgk)))))
  let r := chal h.on
  let on ← left F h.on (pw.map (mulE · (mulE (eqPts wHead (r.extract 0 lgk)) (eqPts wTile (r.extract lgk (lgk + g.lnT))))))
  let T := h.point
  let tg := T.extract 0 lgk
  let ti := T.extract lgk (lgk + lt)
  let tk := T.extract (lgk + lt) (lgk + lt + 4)
  let tbg := T.extract (lgk + lt + 4) (2 * lgk + lt + 4)
  let tbi := T.extract (2 * lgk + lt + 4) (2 * lgk + 2 * lt + 4)
  let rho := chal h.atIndex
  let atIndex ← left F h.atIndex (h.om.map (mulE · (mulE (eqPts tg (rho.extract lt (lt + lgk))) (eqPts ti (rho.extract 0 lt)))))
  let keyRow ← leftKey g F h.key rho h.om'
  let r := chal h.cells
  let cells ← left F h.cells (h.om''.map (mulE · (mulE (mulE (eqPts tbi (r.extract 0 lt)) (eqPts tbg (r.extract lt (lt + lgk)))) (eqPts tk (r.extract (lt + lgk) (lt + lgk + 4))))))
  pure { scores, division, below, on, atIndex, key := keyRow, cells }

end VerifiableInference.Desc.First.Att.P
