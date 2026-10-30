-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Row/K5DryTwin.lean: kind K5: **A TWIN OF THE CLAIMS' TESTS ON THE PLAN
(claimsOk, Johnson/Desc/First/Att/ClaimsOk.lean) WITHOUT THE TWO THINGS FOUND SO FAR AT WHICH LEAN's
KERNEL STOPS OR SWELLS, AND THE EQUATION "claimsOk = its twin" AT EVERY ARGUMENT.**
General laws. NOTHING IS EVALUATED; NO WRITTEN VALUE IS NAMED. The walk of the dry run stays as it
is. THAT THESE TWO ARE THE STONES IS EVIDENCE, NO LAW: the sort: Lean's List.mergeSort was seen to
stop the kernel at other call sites (the tests told in the head of Johnson/Unfolds/MergeSort.lean,
at lists of two and three; three probes that stuck in
Attention.shape's sorts); pointsOf WITH piecesOf's sort in it has been put to no kernel; without it
a probe compiled; the size: a probe ended by a cap on memory with it, compiled with a number in its
place; all at literals made up for the probes. THE TWIN AS A WHOLE HAS BEEN DECIDED BY
LEAN's KERNEL AT ONE VALUE: A CONSTRUCTION MADE UP FOR THE PROBE, TIED TO NO PUBLIC FILE
(a probe, made for no build of the library: "= true" built in 26 s with 3.65 GiB of its own;
"= false", in a module of its own, failed after the same walk). AT NO PLAN OF ANY PUBLIC FILE.
THE TWO CURES. (a) THE SORT: piecesOf (Johnson/Desc/First/Att/Points.lean) sorts a unit's pieces by
Lean's List.mergeSort, which the kernel does not unfold. piecesOfF is its text over the bounded form
Johnson.Unfolds.sortF; piecesOf = piecesOfF by the unconditional law Johnson.Unfolds.mergeSort_eq
(both in Johnson/Unfolds/MergeSort.lean). (b) THE SIZE: lng (Johnson/Desc/First/Att/TablesP.lean)
asks "tokens.size == g.T" of an array of field elements that it has just been handed: to answer, the
kernel builds the array whole. lngS n is its text with the number n in that size's place; at the two
forms in which placeAll calls it the size is known by law: 2 ^ z.size at eqTab z (K5Law.eqTab_size)
and g.T at tok g a b (K5Law.tok_size).
THE TEXTS pointsOfBy · placeAllS · dryOkT ARE THE KIND's OWN, LIFTED BY A PROGRAM: pointsOf with a
letter for piecesOf; placeAll with addLongS at its eight calls of addLong; dryOk with the twins.

Main names (namespace VerifiableInference.Desc.First.Att.P, beside the texts that they mirror):
  piecesOfF · piecesOf_eq · pointsOfBy · pointsOf_by · blankPtsT · blankPts_T.
  lngS · lng_of_size · addLongS · addLong_eqTab · addLong_tok · placeAllS · placeAll_S · tablesPS ·
    tablesP_S.
  dryOkT · dryOk_T · claimsOkT ·
    **claimsOk_T : claimsOk c K k3 planesOk nzx = claimsOkT c K k3 planesOk nzx** · claimsOkAtT ·
    **claimsOkAtO_T : claimsOkAtO A = claimsOkAtT A**.
IS IT EMPTY HERE? Equations at letters: nothing to meet.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatO
import Johnson.Desc.First.Att.Claims.ReadsReturn
import Johnson.Unfolds.MergeSort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff)

/-! ## (a) The sort -/

/-- piecesOf's text over the bounded form of the sort. -/
def piecesOfF (u : UnitG) (zk : Array E) : Array W1 :=
  ((Johnson.Unfolds.sortF (fun x y : W1 => x.lam < y.lam || (x.lam == y.lam && x.a ≤ y.a))
    ((u.pcs.map fun pc => ({ lam := pc.lam, a := pc.a, wp := eqAt (zk.extract 0 (u.n - pc.b)) (pc.off >>> pc.b) } : W1)).length + 1)
    (u.pcs.map fun pc => ({ lam := pc.lam, a := pc.a, wp := eqAt (zk.extract 0 (u.n - pc.b)) (pc.off >>> pc.b) } : W1))).getD []).toArray

theorem piecesOf_eq : piecesOf = piecesOfF := by
  funext u zk
  unfold piecesOf piecesOfF
  rw [Johnson.Unfolds.mergeSort_eq]

/-- pointsOf's text, at a letter for piecesOf. -/
def pointsOfBy (pc : UnitG → Array E → Array W1) (g : Geo) (zk : Array (Array E)) (h : Heard) (L : Left) : Option Pts := do
  let (lgk, lt, ldh, lB) := (g.lgk, g.lt, g.ldh, g.lB)
  let kr := (g.units .kr [.rm, .rd]).toArray
  guard (kr.size == h.remainders.size)
  let planes0 : Array RemP := (kr.zip h.remainders).map fun (u, s0) =>
    let key := zk.getD u.1 #[]
    let un := g.unitAt u.1 u.2.1 u.2.2
    { call := u.1, z := inner un key, isD := u.2.2 == .rd, pw := pc un key, s0 := s0, np := 3 }
  let kfd := g.scores.toArray
  guard (kfd.size == h.scores.size && kfd.size == L.scores.size)
  let (planes, scores) ← ((kfd.zip h.scores).zip L.scores).foldlM (fun (acc : Array RemP × Array ScoreP) ((u, s0, sc), row) => do
    let key := zk.getD u.call #[]
    let pw := pc u key
    let z := inner u key
    let a := lgk + (g.lnT - 1)
    let b := if u.below then a + g.lnT else lgk + g.lnT
    guard (z.size == b + 2 * lB)
    let zP := if u.below then z.extract lgk a else #[]
    let zs := if u.below then z.extract a b else #[]
    let zI := if u.below then #[] else z.extract lgk b
    let wI := if u.below then (tileSums g (eqTab zP) (eqTab zs)).1 else eqTab zI
    pure (acc.1.push { call := u.call, z := z, isD := !u.below, pw := pw, s0 := s0, np := 5 },
      acc.2.push { call := u.call, claim := acc.1.size, below := u.below, pw := pw, zg := z.extract 0 lgk, zs := zs, zi := z.extract b (b + lB),
                   zj := z.extract (b + lB) (b + 2 * lB), wI := wI, s0 := s0, sc := sumOfP sc row })) (planes0, #[])
  let uW ← g.single .wl
  let uX ← g.single .ix
  let uH ← g.single .wh
  let (kW, kX, kH) := (zk.getD uW.call #[], zk.getD uX.call #[], zk.getD uH.call #[])
  let (pwW, pwX, pwH) := (pc uW kW, pc uX kX, pc uH kH)
  let (zW, zX, zH) := (inner uW kW, inner uX kX, inner uH kH)
  guard (pwW.size == g.NP && pwX.size == g.NP && pwH.size == g.NP)
  guard (zW.size == 1 + lgk + lt + ldh && zX.size == lgk + lt && zH.size == lgk + lt + ldh)
  let r := chal h.below
  let atS := lgk + (g.lnT - 1)
  let w := tileSums g (eqTab (r.extract lgk atS)) (eqTab (r.extract atS (atS + g.lnT)))
  let d : DivP :=
    { pwW, pwX, pwH, qWH := uH.call, zsl := zW.getD 0 zeroE, zgW := zW.extract 1 (1 + lgk), ziW := zW.extract (1 + lgk) (1 + lgk + lt)
      zcW := zW.extract (1 + lgk + lt) (1 + lgk + lt + ldh), zgX := zX.extract 0 lgk, ziX := zX.extract lgk (lgk + lt), zgH := zH.extract 0 lgk
      ziH := zH.extract lgk (lgk + lt), zcH := zH.extract (lgk + lt) (lgk + lt + ldh), s5 := h.five, sIB := h.bits, s5h := h.two
      scE := sumOfP h.division L.division, gam := h.gam.getD 1 zeroE, sCl := h.values, vpm := sumOfP h.below L.below, wJv := w.2
      vpd := sumOfP h.on L.on }
  pure { planes, scores, d
         x := { tg := h.point.extract 0 lgk, ti := h.point.extract lgk (lgk + lt), sM6 := h.maxima, scF := sumOfP h.atIndex L.atIndex
                scd := sumOfP h.key L.key, scH := sumOfP h.cells L.cells } }

theorem pointsOf_by (g : Geo) (zk : Array (Array E)) (h : Heard) (L : Left) : pointsOf g zk h L = pointsOfBy piecesOf g zk h L := rfl

/-- blankPts' text with the twin. -/
def blankPtsT (g : Geo) : Option Pts :=
  let z := Aff.ofConst zeroE
  pointsOfBy piecesOfF g (blankZk g) (blankHeard g) { scores := Array.replicate g.scores.length z, division := z, below := z, on := z, atIndex := z, key := z, cells := z }

theorem blankPts_T (g : Geo) : blankPts g = blankPtsT g := by
  unfold blankPts blankPtsT
  rw [pointsOf_by, piecesOf_eq]

/-! ## (b) The size -/

/-- lng's text with the number n in the place of the size of the weights on the positions. -/
def lngS (n : Nat) (g : Geo) (zc : Array E) (ptk : Unit → Array E) : T (Array E) := do
  let tokens ← T.weights g.T ptk
  mustAs "plan-tensor-layout" (n == g.T && 2 ^ g.la == 2 ^ g.ls * g.T)
  let c ← T.getAs "plan-tensor-layout" (cutLast zc g.ls)
  T.weights (2 ^ g.la) fun _ => blockRows (eqTab c.2) tokens

theorem lng_of_size {n : Nat} (g : Geo) (zc : Array E) (ptk : Unit → Array E) (h : (ptk ()).size = n) : lng g zc ptk = lngS n g zc ptk := by
  subst h
  rfl

/-- addLong's text with lngS. -/
def addLongS (n : Nat) (g : Geo) (mats : Array (Nat × Nat)) (mat : Nat) (zc : Array E)
    (ptk : Unit → Array E) (elems : Nat) : T Nat := do
  let phi ← lngS n g zc ptk
  add mats mat (2 ^ g.la) phi elems

theorem addLong_eqTab (g : Geo) (mats : Array (Nat × Nat)) (mat : Nat) (zc z : Array E) (elems : Nat) :
    addLong g mats mat zc (fun _ => eqTab z) elems = addLongS (2 ^ z.size) g mats mat zc (fun _ => eqTab z) elems := by
  unfold addLong addLongS
  rw [lng_of_size g zc (fun _ => eqTab z) (K5Law.eqTab_size z)]

theorem addLong_tok (g : Geo) (mats : Array (Nat × Nat)) (mat : Nat) (zc a b : Array E) (elems : Nat) :
    addLong g mats mat zc (fun _ => tok g a b) elems = addLongS g.T g mats mat zc (fun _ => tok g a b) elems := by
  unfold addLong addLongS
  rw [lng_of_size g zc (fun _ => tok g a b) (K5Law.tok_size g a b)]

/-- placeAll's text with addLongS at its eight calls of addLong. -/
def placeAllS (g : Geo) (mats : Array (Nat × Nat)) (nW : Nat) (lk : LookIn) (p : Pts) :
    T TablesP := do
  let (planes, scores, d, x) := (p.planes, p.scores, p.d, p.x)
  let gSo := g.fillO * g.T / 2 ^ g.la
  let gSq := g.fillQ * g.T / 2 ^ g.la
  let mb := 2 ^ g.lmb
  let iAO := g.NAs + 1
  let iBA := g.NAs + 2
  let iQA := g.NAs + 3
  let ptM := pointM g d
  let ptD := pointD g d
  let riE := d.scE.r.extract g.lgk (g.lgk + g.lt)
  mustAs "internal-a-merged-point" (mergedPlanes g.lmS lk.zx planes)
  let tA ← addAs g mats fun _ => lastN lk.zx g.lmS
  let tVM ← addAs g mats fun _ => lastN ptM g.lmS
  let tVD ← addAs g mats fun _ => lastN ptD g.lmS
  let tM ← scores.mapM fun k => addRow g mats fun _ => tok g k.wI k.zi
  let hW ← addRow g mats fun _ => eqTab d.ziW
  let hX ← addRow g mats fun _ => eqTab d.ziX
  let hE ← addRow g mats fun _ => eqTab riE
  let hT ← addRow g mats fun _ => eqTab x.ti
  let hPi ← addRow g mats fun _ => eqTab (x.pi g)
  let hR2 ← addRow g mats fun _ => eqTab (x.ri2 g)
  mustAs "internal-a-merged-point" (mergedTokens g lk.zx d)
  let tO ← addLongS (2 ^ (d.ziW).size) g mats iAO d.zcW (fun _ => eqTab d.ziW) gSo
  let tQK ← scores.mapM fun k => do
    let rcK := lastCoords k.sc.r g.ldh
    let tQ ← addLongS g.T g mats iQA rcK (fun _ => tok g (scoreTiles g k).1 k.zi) gSq
    let tK ← addLongS g.T g mats iQA rcK (fun _ => tok g (scoreTiles g k).2 k.zj) gSq
    pure (tQ, tK)
  let qO ← addLongS (2 ^ (riE).size) g mats iQA d.zcW (fun _ => eqTab riE) gSq
  let qVM ← addLongS g.T g mats iQA d.zcW (fun _ => tok g d.wJv (lastCoords d.vpm.r g.lB)) gSq
  let qVD ← addLongS g.T g mats iQA d.zcW
    (fun _ => tok g (eqTab (d.vpd.r.extract g.lgk (g.lgk + g.lnT)))
      (lastCoords d.vpd.r g.lB)) gSq
  let qF ← addLongS (2 ^ ((x.ri g)).size) g mats iQA (x.rc g) (fun _ => eqTab (x.ri g)) gSq
  let qKx ← addLongS (2 ^ ((x.pj g)).size) g mats iQA (x.rc g) (fun _ => eqTab (x.pj g)) gSq
  mustAs "forest-planes" lk.planesOk
  let phiB0 ← T.weights mb fun _ => lk.phiB0
  let tBit0 ← add mats iBA mb phiB0 g.kbA
  let phiB1 ← T.weights mb fun _ => lk.phiB1
  let tBit1 ← add mats iBA mb phiB1 g.kbA
  let tPin ← add mats iBA mb (← T.weights mb fun _ => lk.phiP) g.kbA
  let t ← T.placed
  mustAs "internal-af-W-length" (t.next == nW)
  let score : Array ScoreT := (tM.zip tQK).map fun y => ⟨y.1, y.2.1, y.2.2⟩
  pure {
    ptM := ptM, ptD := ptD, tA := tA, tVM := tVM, tVD := tVD, score := score,
    hW := hW, hX := hX, hE := hE, hT := hT, hPi := hPi, hR2 := hR2, tO := tO,
    qO := qO, qVM := qVM, qVD := qVD, qF := qF, qKx := qKx,
    tBit0 := tBit0, tBit1 := tBit1, tPin := tPin,
    tabLen := t.tabLen, funs := t.funs }

theorem placeAll_S (g : Geo) (mats : Array (Nat × Nat)) (nW : Nat) (lk : LookIn) (p : Pts) : placeAll g mats nW lk p = placeAllS g mats nW lk p := by
  unfold placeAll placeAllS
  simp only [addLong_eqTab, addLong_tok]

def tablesPS (g : Geo) (mats : Array (Nat × Nat)) (nW : Nat) (lk : LookIn) (p : Pts) :
    Option TablesP := do
  pure (← placeAllS g mats nW lk p {}).1

theorem tablesP_S (g : Geo) (mats : Array (Nat × Nat)) (nW : Nat) (lk : LookIn) (p : Pts) : tablesP g mats nW lk p = tablesPS g mats nW lk p := by
  unfold tablesP tablesPS
  rw [placeAll_S]

/-! ## The dry run and the test -/

/-- dryOk's text with the twins. -/
def dryOkT (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) : Bool :=
  let g := c.geo
  (do
    let p ← blankPtsT g
    let t ← tablesPS g c.mats c.nW { zx := zeros nzx, planesOk := planesOk, phiB0 := zeros (2 ^ g.lmb), phiB1 := zeros (2 ^ g.lmb), phiP := zeros (2 ^ g.lmb) } p
    let i : Runs.In := { g := g, p := p, t := t, zk := blankZk g, iU3 := c.iU3 }
    let f ← Runs.firstRun i K
    let _ ← Runs.keysRun i k3 f.2
    let _ ← Runs.secondRun i K
    pure ()).isSome

theorem dryOk_T (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) : dryOk c K k3 planesOk nzx = dryOkT c K k3 planesOk nzx := by
  unfold dryOk dryOkT
  simp only [blankPts_T, tablesP_S]

/-- claimsOk's text with the twin. -/
def claimsOkT (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) : Bool :=
  padKeyOk c.geo && Decidable.decide (c.geo.lt ≤ 16) && dryOkT c K k3 planesOk nzx

/-- **THE TEST IS ITS TWIN, AT EVERY ARGUMENT.** -/
theorem claimsOk_T (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) :
    claimsOk c K k3 planesOk nzx = claimsOkT c K k3 planesOk nzx := by
  unfold claimsOk claimsOkT
  rw [dryOk_T]

/-- claimsOkAtO's text (Johnson/Desc/First/Att/SeatO.lean) with the twin. -/
def claimsOkAtT (A : Attention.Plan) : Bool :=
  claimsOkT (parCOf A) (((A.seam.Fp.trees[A.iU3]?).map (·.K)).getD 0) (padOfO A.fs)
    (Look.planesOk A.fs A.S.cf.lmb) (A.fs.dT)

/-- **THE TEST AT A PLAN IS ITS TWIN, AT EVERY PLAN.** -/
theorem claimsOkAtO_T (A : Attention.Plan) : claimsOkAtO A = claimsOkAtT A := by
  unfold claimsOkAtO claimsOkAtT
  rw [claimsOk_T]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.piecesOf_eq
#print axioms VerifiableInference.Desc.First.Att.P.pointsOf_by
#print axioms VerifiableInference.Desc.First.Att.P.blankPts_T
#print axioms VerifiableInference.Desc.First.Att.P.addLong_eqTab
#print axioms VerifiableInference.Desc.First.Att.P.addLong_tok
#print axioms VerifiableInference.Desc.First.Att.P.placeAll_S
#print axioms VerifiableInference.Desc.First.Att.P.tablesP_S
#print axioms VerifiableInference.Desc.First.Att.P.dryOk_T
#print axioms VerifiableInference.Desc.First.Att.P.claimsOk_T
#print axioms VerifiableInference.Desc.First.Att.P.claimsOkAtO_T
#print axioms VerifiableInference.Desc.First.Att.P.lng_of_size
