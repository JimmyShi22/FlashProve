-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Left.lean: from what was heard (Att/Hear.lean) to the claim that each sumcheck
leaves, and to the four records of OnBytes/Model's verifier. Pure. A seat's tool; no part of the kind.

`left`, `leftKey`: the row of a sumcheck, by OnBytes/Model's own form of a row.
`toOwn`: the four records as that verifier's routines fill them; the cuts of the key points and the
weights follow its lines.
Its tests (seven comparisons in three guards) are on lengths alone.
Beside them `left` and `leftKey` refuse where nothing was shown
under a number that they read.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Hear
import Johnson.Desc.First.Att.Records

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.Short
open OnBytes OnBytes.Attention OnBytes.K.Kc
open OnBytes.Model (Fork Aff)

/-- The row of a sumcheck of products, under the weights W. -/
def left (F : Fork) (s : Sum) (W : Array E) : Option Sc3 := do
  let nb := W.size
  let s0 ← (List.range nb).foldlM (fun a b => do
    pure (addE a (mulE (mulE (W.getD b zeroE) (← F.shown (s.ends + 2 * b))) (← F.shown (s.ends + (2 * b + 1)))))) zeroE
  pure { r := s.r, sEnd := s.ends, nb := nb, p := s.p, rowU := s.p.rowForm s0 {} }

/-- The row of the sumcheck for the key at the index. ρ: the challenges of the score at the index. -/
def leftKey (S : Shape) (F : Fork) (s : Sum) (ρ om' : Array E) : Option Scd := do
  let (lgk, lt) := (S.cf.lgk, S.cf.lt)
  let pj := s.r.extract 0 lt
  let sum ← (List.range S.NP).foldlM (fun a b => do
    let kc ← F.shown (s.ends + b / S.HA)
    let t ← (List.range lt).foldlM (fun t k => do
      let y := pj.getD (lt - 1 - k) zeroE
      let v ← F.shown (s.ends + (S.Lam + b * lt + k))
      pure (mulE t (addE (mulE v (subE (addE y y) oneE)) (subE oneE y)))) (mulE (om'.getD b zeroE) kc)
    pure (addE a t)) zeroE
  let f := mulE (eqPts (ρ.extract 0 lt) (s.r.extract (lt + lgk) (2 * lt + lgk))) (eqPts (ρ.extract lt (lt + lgk)) (s.r.extract lt (lt + lgk)))
  pure { r := s.r, sEnd := s.ends, p := s.p, rowU := s.p.rowForm (mulE f sum) {} }

/-- The four records of OnBytes/Model's verifier, rebuilt. zk: each call's key point. F: the ledger behind the hearing. -/
def toOwn (S : Shape) (zk : Array (Array E)) (h : Heard) (F : Fork) : Option Own := do
  let (lgk, lt, ldh, lB) := (S.cf.lgk, S.cf.lt, S.cf.ldh, S.cf.lB)
  -- the remainder units
  let kr := (unitsOf S .kr [.rm, .rd]).toArray
  let planes0 : Array PlaneClaim := (kr.zip h.remainders).map fun (u, s0) =>
    let key := zk.getD u.1 #[]
    { call := u.1, seg := u.2.2, z := inner S key u.2.2, isD := u.2.2 == Seg.rd, pw := pieces u.2.1 key u.2.2, s0 := s0, np := 3 }
  -- the score units
  let kfd := (unitsOf S .kfd [.fm, .fd]).toArray
  let (planes, scores) ← (kfd.zip h.scores).foldlM (fun (acc : Array PlaneClaim × Array Score) (u, s0, sc) => do
    let s := u.2.2
    let fm := s == Seg.fm
    let key := zk.getD u.1 #[]
    let pw := pieces u.2.1 key s
    let z := inner S key s
    let a := lgk + (S.lnT - 1)
    let b := if fm then a + S.lnT else lgk + S.lnT
    guard (z.size == b + 2 * lB)
    let zg := z.extract 0 lgk
    let zP := if fm then z.extract lgk a else #[]
    let zs := if fm then z.extract a b else #[]
    let zI := if fm then #[] else z.extract lgk b
    let wI := if fm then (tileSums S (Model.eqTab zP) (Model.eqTab zs)).1 else Model.eqTab zI
    let row ← left F sc (timesW pw (scoreFactor S s zg zP zs zI sc.r))
    pure (acc.1.push { call := u.1, seg := s, z := z, isD := s == Seg.fd, pw := pw, s0 := s0, np := 5 },
      acc.2.push { call := u.1, claim := acc.1.size, seg := s, pw := pw, zg := zg, zs := zs, zi := z.extract b (b + lB),
                   zj := z.extract (b + lB) (b + 2 * lB), wI := wI, s0 := s0, sc := row })) (planes0, #[])
  -- the division and the value product
  let (_, pwW, zW) ← unitOf S zk .wl
  let (_, pwX, zX) ← unitOf S zk .ix
  let (qWH, pwH, zH) ← unitOf S zk .wh
  guard (pwW.size == S.NP && pwX.size == S.NP && pwH.size == S.NP)
  guard (zW.size == 1 + lgk + lt + ldh && zX.size == lgk + lt && zH.size == lgk + lt + ldh)
  let zgW := zW.extract 1 (1 + lgk)
  let ziW := zW.extract (1 + lgk) (1 + lgk + lt)
  let zihi := ziW.extract 0 S.lnT
  let r := h.division.r
  let scE ← left F h.division (timesW pwW (mulE (eqPts zgW (r.extract 0 lgk)) (eqPts ziW (r.extract lgk (lgk + lt)))))
  let r := h.below.r
  let atS := lgk + (S.lnT - 1)
  let w := tileSums S (Model.eqTab (r.extract lgk atS)) (Model.eqTab (r.extract atS (atS + S.lnT)))
  let vpm ← left F h.below (timesW pwW (mulE (overTileRows S w.1 (Model.eqTab zihi)) (eqPts zgW (r.extract 0 lgk))))
  let r := h.on.r
  let vpd ← left F h.on (timesW pwW (mulE (eqPts zgW (r.extract 0 lgk)) (eqPts zihi (r.extract lgk (lgk + S.lnT)))))
  let d : Divide :=
    { pwW, pwX, pwH, qWH, zsl := zW.getD 0 zeroE, zgW, ziW, zcW := zW.extract (1 + lgk + lt) (1 + lgk + lt + ldh),
      zgX := zX.extract 0 lgk, ziX := zX.extract lgk (lgk + lt), zgH := zH.extract 0 lgk, ziH := zH.extract lgk (lgk + lt),
      zcH := zH.extract (lgk + lt) (lgk + lt + ldh), s5 := h.five, sIB := h.bits, s5h := h.two, scE,
      gam := h.gam.getD 1 zeroE, sCl := h.values, vpm, wJv := w.2, vpd }
  -- the maximum and the index
  let P := h.point
  let tg := P.extract 0 lgk
  let ti := P.extract lgk (lgk + lt)
  let tk := P.extract (lgk + lt) (lgk + lt + 4)
  let tbg := P.extract (lgk + lt + 4) (2 * lgk + lt + 4)
  let tbi := P.extract (2 * lgk + lt + 4) (2 * lgk + 2 * lt + 4)
  let r := h.atIndex.r
  let scF ← left F h.atIndex (scaled h.om (mulE (eqPts tg (r.extract lt (lt + lgk))) (eqPts ti (r.extract 0 lt))))
  let scd ← leftKey S F h.key r h.om'
  let r := h.cells.r
  let scH ← left F h.cells (scaled h.om'' (mulE (mulE (eqPts tbi (r.extract 0 lt)) (eqPts tbg (r.extract lt (lt + lgk)))) (eqPts tk (r.extract (lt + lgk) (lt + lgk + 4)))))
  pure { planes, scores, d, x := { tg, ti, sM6 := h.maxima, scF, scd, scH } }

end VerifiableInference.Desc.First.Att.Short
