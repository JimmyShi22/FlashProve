-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/TestAttKit14.lean: made-up records of an attention sub-proof at the verifier's
small configuration, for the tests of this folder. Definitions alone.

What is set up. The shape is what shapeHid returns for smallCfg
(OnBytes/Model/TestAttentionPlan.lean: 64 tokens in four tiles of 16, two heads of keys and values,
128 features a head, four layers, two query heads for each head of keys and values). The lookup's
point, the points of the four sumchecks and the element gam are made-up small numbers. The
verifier's records are cut from them as scoreUnit and divide cut them. The list of tables is what
the verifier's own function tables returns for these records. The matrices hold made-up integers.
The vector of tables is computed from the matrices: each entry is the sum of its block under its
table's weights.

Main names: Kf, toK, inBase; nums, Mz, zx, C0, gam0, pub; unit, division, heard; u3, valE, form,
cells, ptK, agree; score, product, below.

The program does not import this file.


-/
import Johnson.Road.Rows.AttEnds14
import OnBytes.Model.TestAttentionTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows.TestEnds14

open OnBytes.Attention
open OnBytes.Model (Aff SubM HTailF2 eqTab blockRows ofNat ofInt tenCell)
open Inst.Model.AttSeg (Calls Pub Step Aext Bext)

/-- The integers modulo the prime. -/
abbrev Kf : Type := Cb.Gl.F

/-- An element of the base field, read in Kf. -/
def toK (x : E) : Kf := ((x.c0.toNat : ℕ) : Kf)

/-- The element lies in the base field. -/
def inBase (x : E) : Bool := x.c1 == 0 && x.c2 == 0

/-- n made-up numbers. -/
def nums (n seed : Nat) : Array E := (Array.range n).map fun i => ofNat (seed + 5 * i + 2)

/-- The made-up matrices: number in the list, row, column. -/
def Mz (a r c : Nat) : Int := (((a * 31 + r * 7 + c * 13) % 257 : Nat) : Int) - 128

/-- The lookup's point: every call of the small configuration has one tree of 2^20 keys. -/
def zx : Array E := nums 20 3

/-- The library's numbers of the lookup at the small configuration. -/
def C0 : Calls := ⟨![20, 20, 20, 20], 20, 2⟩

/-- The element gam. -/
def gam0 : E := ofNat 77

/-- The library's challenges: the lookup's point and gam; the others are not read here. -/
def pub (z : Array E) : Pub Kf :=
  { z := fun j => toK (z.getD j zeroE), th := toK gam0, tg := fun _ => 0, ti := fun _ => 0,
    tbi := fun _ => 0, tbg := fun _ => 0, tk := fun _ => 0, o := fun _ => 0, o' := fun _ => 0,
    o'' := fun _ => 0, fi := fun _ => 0, fg := fun _ => 0, fn := fun _ => 0 }

/-- A unit of the scores, cut from the lookup's point as scoreUnit cuts it. r: the sumcheck's
point. -/
def unit (S : Shape) (u : Nat × ACall × Seg) (r : Array E) : Score :=
  let s := u.2.2
  let fm := s == Seg.fm
  let pw := pieces u.2.1 zx s
  let z := Attention.inner S zx s
  let lgk := S.cf.lgk
  let lB := S.cf.lB
  let a := lgk + (S.lnT - 1)
  let b := if fm then a + S.lnT else lgk + S.lnT
  let zP := if fm then z.extract lgk a else #[]
  let zs := if fm then z.extract a b else #[]
  let zI := if fm then #[] else z.extract lgk b
  { call := u.1, claim := 0, seg := s, pw := pw, zg := z.extract 0 lgk, zs := zs,
    zi := z.extract b (b + lB), zj := z.extract (b + lB) (b + 2 * lB),
    wI := if fm then (tileSums S (eqTab zP) (eqTab zs)).1 else eqTab zI, s0 := 0,
    sc := { r := r, sEnd := 100, nb := pw.size } }

/-- The division and the value product, cut as divide cuts them. -/
def division (S : Shape) : Option Divide := do
  let lgk := S.cf.lgk
  let lt := S.cf.lt
  let ldh := S.cf.ldh
  let zk := Array.replicate S.calls.size zx
  let (_, pwW, zW) ← unitOf S zk .wl
  let (_, pwX, zX) ← unitOf S zk .ix
  let (qWH, pwH, zH) ← unitOf S zk .wh
  let rM := nums S.nvVM 11
  let atS := lgk + (S.lnT - 1)
  pure {
    pwW := pwW, pwX := pwX, pwH := pwH, qWH := qWH, zsl := zW.getD 0 zeroE,
    zgW := zW.extract 1 (1 + lgk), ziW := zW.extract (1 + lgk) (1 + lgk + lt),
    zcW := zW.extract (1 + lgk + lt) (1 + lgk + lt + ldh),
    zgX := zX.extract 0 lgk, ziX := zX.extract lgk (lgk + lt),
    zgH := zH.extract 0 lgk, ziH := zH.extract lgk (lgk + lt),
    zcH := zH.extract (lgk + lt) (lgk + lt + ldh),
    s5 := 0, sIB := 0, s5h := 0, scE := { r := nums S.nvE 7, sEnd := 200, nb := S.NP },
    gam := gam0, sCl := 0, vpm := { r := rM, sEnd := 300, nb := S.NP },
    wJv := (tileSums S (eqTab (rM.extract lgk atS)) (eqTab (rM.extract atS (atS + S.lnT)))).2,
    vpd := { r := nums S.nvVD 13, sEnd := 400, nb := S.NP } }

/-- What the claims read, with the verifier's own list of tables. -/
def heard : Option Heard := do
  let (S, _) ← (shapeHid 24 smallCfg).toOption
  let d ← division S
  let us := unitsOf S Table.kfd [Seg.fm, Seg.fd]
  let scores := (us.zipIdx.map fun x => unit S x.1 (nums (S.nvKF x.1.2.2) (17 + x.2))).toArray
  let planes : Array PlaneClaim := scores.map fun k =>
    { call := k.call, seg := k.seg, z := Attention.inner S zx k.seg, isD := k.seg == Seg.fd,
      pw := k.pw, s0 := 0, np := 5 }
  let g := { TestTables.exampleLook with zx := zx }
  let x := TestTables.exampleAttain
  let t ← (Blk.runFrom (tables S (matrices S {}) S.tableElems g planes scores d x)
    { entries := [], st := {} } false [] []).map (·.1)
  pure { S := S, g := g, planes := planes, scores := scores, d := d, x := x, t := t, iU3 := 0 }

/-- Entry x of the vector of tables, from the matrices. bad: an entry that is given 1 too much. -/
def u3 (h : Heard) (bad : Option Nat) (x : Nat) : E :=
  let mats := matrices h.S {}
  let v := h.t.funs.foldl (fun s Fn =>
    let Mx := mats.getD Fn.mat {}
    let nsg := Mx.m / Fn.len
    if Fn.start ≤ x && x < Fn.start + Mx.k * nsg then
      let c := (x - Fn.start) / nsg
      let sg := (x - Fn.start) % nsg
      (List.range Fn.len).foldl (fun s y =>
        addE s (mulE (Fn.phi.getD y zeroE) (ofInt (Mz Fn.mat (sg * Fn.len + y) c)))) s
    else s) zeroE
  if bad == some x then addE v oneE else v

/-- The value of a form that names no slot, on the vector of tables. -/
def valE (h : Heard) (bad : Option Nat) (f : Aff) : E :=
  f.ents.foldl (fun s e => addE s (mulE e.coef (u3 h bad (e.row * h.S.tableElems + e.idx)))) f.const

/-- Runs a reader in a state in which the vector of tables is one row. -/
def form (h : Heard) (m : SubM Aff) : Option Aff :=
  (Blk.runFrom (m.run' { trees := #[{ R := 1, K := h.S.tableElems }] })
    { entries := [], st := {} } false [] []).map (·.1)

/-- The cells, in Kf. -/
def cells (h : Heard) : Inst.Model.AttSeg.Raw → Kf :=
  cellsK h.S fun a r c => ((Mz a r c : Int) : Kf)

/-- A point, in Kf. -/
def ptK (z : Array E) : Nat → Kf := fun j => toK (z.getD j zeroE)

/-- The verifier's form against the library's value. -/
def agree (h : Heard) (bad : Option Nat) (m : SubM Aff) (lib : Kf) : Option Bool :=
  (form h m).map fun f => inBase (valE h bad f) && decide (toK (valE h bad f) = lib)

/-- The two end values of piece number b of unit number i of the scores, against step st at the
pair of piece number b' and the lookup's point z. -/
def score (i b b' : Nat) (st : Step) (z : Array E) (bad : Option Nat := none) :
    Option (Bool × Bool) := do
  let h ← heard
  let k ← h.scores[i]?
  let tb ← h.t.score[i]?
  let w ← k.pw[b]?
  let w' ← k.pw[b']?
  let rc := lastCoords k.sc.r h.S.cf.ldh
  let D := L5.dimOf h.S
  let x ← agree h bad (readHead h tb.tQ h.S.atQ k.sc.r rc w.lam w.a)
    (Aext D C0 (pub z) (cells h) st (w'.lam * h.S.HA + w'.a) (ptK k.sc.r))
  let y ← agree h bad (readGroup h tb.tK h.S.atK k.sc.r rc w.lam)
    (Bext D C0 (pub z) (cells h) st (w'.lam * h.S.HA + w'.a) (ptK k.sc.r))
  pure (x, y)

/-- The same for the denominator times the output. -/
def product (b b' : Nat) (z : Array E) : Option (Bool × Bool) := do
  let h ← heard
  let w ← h.d.pwW[b]?
  let w' ← h.d.pwW[b']?
  let D := L5.dimOf h.S
  let x ← agree h none (readDenominator h h.t.hE h.d.scE.r w.lam w.a)
    (Aext D C0 (pub z) (cells h) .s8 (w'.lam * h.S.HA + w'.a) (ptK h.d.scE.r))
  let y ← agree h none (readHead h h.t.qO h.S.atO h.d.scE.r h.d.zcW w.lam w.a)
    (Bext D C0 (pub z) (cells h) .s8 (w'.lam * h.S.HA + w'.a) (ptK h.d.scE.r))
  pure (x, y)

/-- The same for the value product below the diagonal. -/
def below (b b' : Nat) (z : Array E) : Option (Bool × Bool) := do
  let h ← heard
  let w ← h.d.pwW[b]?
  let w' ← h.d.pwW[b']?
  let D := L5.dimOf h.S
  let x ← agree h none (do
      let p3 ← plane h h.t.tVM 3 w.lam w.a h.t.ptM false
      let p4 ← plane h h.t.tVM 4 w.lam w.a h.t.ptM false
      pure (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256)))
    (Aext D C0 (pub z) (cells h) .s11 (w'.lam * h.S.HA + w'.a) (ptK h.d.vpm.r))
  let y ← agree h none (do
      let v ← readGroup h h.t.qVM h.S.atV h.d.vpm.r h.d.zcW w.lam
      pure (Aff.ofConst h.d.gam + v))
    (Bext D C0 (pub z) (cells h) .s11 (w'.lam * h.S.HA + w'.a) (ptK h.d.vpm.r))
  pure (x, y)

end OnBytes.Road.Rows.TestEnds14
