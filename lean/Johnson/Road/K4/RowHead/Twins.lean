-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowHead/Twins.lean: THE FIRST HALF OF THE LAYERS' LAYOUT WITHOUT THE LINES AT WHICH
LEAN's KERNEL STOPS, for closed facts by the kernel. Definitions alone. IT IS THE ROUTINE's OWN
TEXT, COPIED BY PROGRAM, LESS THE LINES NAMED:
  `baseNoStops`: layoutBase (OnBytes/Model/LayerLayout.lean) less its test "policy-norm" on the two
    numbers eps1, eps2 (which are free in scope) and its two calls of tensorsFill (a sort).
  (`Forest.shapeNoAsk`, the forest's twin, stands once for all
    files in Johnson/Unfolds/ForestTwins.lean, which this file imports.)
  `onOk`: a test at a returned value. `Pv` | `clOf` | `withPlans`: a test at the layers' public
    parameters and plans as publicOf makes them over the twins, with the free numbers, the counts of
    padding keys, the scales and the rotary table as letters (a term of
Trial/K4Q2FrontFree.lean (not in this library), to the letter). Limits. NO PROGRAM CALLS THESE: they
stand in statements alone; what ties them to the routines is
Johnson/Road/K4/RowHead/Inversions.lean. Nothing on soundness.
-/
import OnBytes.Model.VerifyPublic
import Johnson.Goal.Meaning.ScopeScan
import Johnson.Unfolds.ForestTwins

set_option autoImplicit false

namespace OnBytes.Model.Layer

/-- layoutBase's text less its test on eps1, eps2 and its two calls of tensorsFill. -/
def baseNoStops (h : Shape) (pc : List (List String)) : Except String Lay := do
  let d := h.d
  let f := h.f
  let fe := h.fe
  refuseIf (h.prof < 3 || h.prof > 4) "policy-profile"
  let p3 := h.p3
  refuseIf (h.lt < 4 || h.lt > 16 || h.ll < 1 || h.ll > 6 || d == 0 || f == 0 || d > 2 ^ 20 ||
    f > 2 ^ 20 || (p3 && (manyBits fe || f != 2 * fe || (h.ll == 1 && fe == 1)))) "shape-words"
  let T := 2 ^ h.lt
  let Lam := 2 ^ h.ll
  refuseIf (h.L == 0 || h.L % Lam != 0) "shape-L"
  let NGr := h.L / Lam
  -- A matrix has the label 256 s + its number, where s, its sub-proof's number, is at most
  -- 1 + 2 NGr. Under this bound all labels are below 2^24, where the weight matrices' labels begin.
  refuseIf (2 + 2 * NGr ≥ 2 ^ 16) "shape-groups"
  groupsBaseHeld NGr
  let lPd := ceilLog2 d
  let lPf := ceilLog2 f
  let lfe := if p3 then ceilLog2 fe else 0
  refuseIf (h.la ≤ h.lt || h.la > 16) "shape-la"
  let ls := h.la - h.lt
  let S2 := 2 ^ ls
  refuseIf (d % S2 != 0 || f % S2 != 0 || (p3 && fe % S2 != 0)) "shape-la"
  refuseIf (h.H == 0 || h.Gk == 0 || h.dh == 0 || manyBits h.dh || h.dh < 2 || h.H * h.dh != d ||
    h.H + h.Gk > 64) "shape-heads"
  let dq := h.H * h.dh
  let dkv := h.Gk * h.dh
  let nqk := dq + dkv
  refuseIf (dkv % S2 != 0 || nqk % S2 != 0) "shape-la"
  refuseIf (h.cs != 12) "policy-cs"
  -- The classes of rounding sites, in the order of their numbers: q, k, v, o, gate, up, down, then
  -- the router's, then those of the layers with experts, which share the dense classes' forms.
  refuseIf ([h.hq, h.hq, h.hv, h.ho, h.hgD, h.huD, h.hdD].any (· > 2)) "policy-forms"
  refuseIf (!p3 && h.hr != 0) "header-absent-class"
  refuseIf (p3 && h.hr > 2) "policy-forms"
  refuseIf (h.ut != 1) "policy-ut"
  refuseIf (h.D < 2 || h.D > 4096 || manyBits h.D) "shape-D"
  refuseIf (h.xl != 4 && h.xl != 5) "internal-layout-words"
  let NE := h.NE
  let LamM := Lam / 2
  refuseIf (p3 && (NE < 2 || NE > 4096 || manyBits NE)) "shape-NE"
  refuseIf (h.gcl && !p3) "policy-gcl"
  refuseIf (h.rcl && !p3) "policy-rcl"
  let laid := layTensors (tensorAsks h Lam LamM nqk dq dkv) #[0, 0, 0, 0]
  let lm := [h.lmaf, h.lmad, h.lmar, h.lmq]
  let na := [h.NAf, h.NAd, 1, 1]
  refuseIf (h.lmq < h.la) "shape-la"
  refuseIf ((lm.zip na).any fun x => x.1 < h.lt || x.1 > 24 || x.2 == 0 || x.2 > 64)
    "shape-request-matrix"
  let sizes := ((laid.2.toList.zip lm).zip na).map fun x => matrixSizes T x.1.1 x.1.2 x.2
  refuseIf (h.lmaf < h.la) "shape-la"
  refuseIf (h.lmx < h.la || h.lmx > 24) "shape-request-matrix"
  let mxb := 2 ^ h.lmx
  let unit := mxb / T
  let xbFilled := roundUp (h.xl * d) unit
  let xb : TenAt := ⟨0, h.xl, 1, d⟩
  let sd := segmentList h nqk dkv
  let cl := if pc.isEmpty then builtInCalls p3 else pc
  refuseIf (cl.length > 8) "policy-call-list"
  let taken ← takeCalls sd cl [] []
  refuseIf (sd.any fun s => !taken.2.contains s.1) "policy-call-list"
  refuseIf (h.lmb > 24) "shape-lmb"
  -- place makes 2^(nmin - ll - lt) columns before any test on a call's size, so a large nmin must
  -- be refused here.
  refuseIf (h.nmin > 28) "shape-words"
  let calls := taken.1.map fun c => place c.1 c.2.1 c.2.2 (h.nmin - h.ll - h.lt)
  let (silu, fs) := gateTables h.eg h.smax p3 h.gcl
  pure {
    h := h, T := T, Lam := Lam, NGr := NGr, Pd := 2 ^ lPd, Pf := 2 ^ lPf, S2 := S2,
    NI := 2 * Lam, dq := dq, dkv := dkv, nqk := nqk, lPf := lPf, lfe := lfe, lPd := lPd, ls := ls,
    ldh := ceilLog2 h.dh, ten := laid.1,
    feat := (sizes.map (·.1)).toArray, filled := (sizes.map (·.2.1)).toArray,
    kcol := (sizes.map (·.2.2.1)).toArray, mrow := (sizes.map (·.2.2.2.1)).toArray,
    parts := (sizes.map (·.2.2.2.2)).toArray,
    xbFilled := xbFilled, kxb := xbFilled / unit, mxb := mxb, xb := xb,
    kinds := kindList h Lam LamM dq dkv, calls := calls.toArray,
    tauFC := (Array.range 65536).map fun t => (rowFC t).toUInt64,
    silu := silu, fs := fs,
    tauFL := (Array.range 65536).map fun t => (t + silu.getD t 0 * 2 ^ 28).toUInt64,
    tauFS := if p3 then (Array.range 65536).map fun t => (rowFS h.gcl fs t).toUInt64 else #[],
    LamM := LamM }


end OnBytes.Model.Layer

namespace OnBytes.Road.K4

/-- A test at a returned value; false where nothing is returned. -/
def onOk {ε α : Type} (x : Except ε α) (f : α → Bool) : Bool :=
  match x with
  | .ok a => f a
  | .error _ => false

theorem onOk_ok {ε α : Type} {x : Except ε α} {f : α → Bool} {a : α} (h : onOk x f = true)
    (e : x = .ok a) : f a = true := by
  subst e
  exact h

/-- The strict scan's closed form at the eight free numbers v
(Johnson/Goal/Meaning/ScopeScan.lean). -/
def Pv (v : VerifierAndGoals.FreeLines) : Model.PolScan := VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef v

/-- layoutLook's own first line. -/
def clOf (y : Model.Layer.Lay) : Array Model.Call := y.calls.mapIdx fun q cd => y.callRecord q cd

open OnBytes.Model in
/-- **A test at the layers' public parameters and plans as publicOf makes them, every stop written
away**: the eight free numbers v, the counts of padding keys pub, the scales sc and the rotary table
rope ARE LETTERS. -/
def withPlans (v : VerifierAndGoals.FreeLines) (pub : Array Nat) (sc : Layer.Scales) (rope : Array Nat)
    (f : Layer.Pub → Array Layer.HPlan2 → Bool) : Bool :=
  onOk (Layer.baseNoStops (Verify.layerShape (Pv v)) VerifierAndGoals.Lines.callsRef) fun y0 =>
    onOk (Forest.shapeNoAsk (clOf y0) y0.h.lidb) fun fo =>
      onOk (Forest.planeCols fo y0.h.lmb) fun kbm =>
        onOk (wsLayOf (Verify.weightShape (Pv v)
            { y0 with cl := clOf y0, fo := { fo with pub := pub }, kbm := kbm })
            y0.h.p3 (Pv v).lkW) fun wsLay =>
          onOk (Layer.Pub.of { y0 with cl := clOf y0, fo := { fo with pub := pub }, kbm := kbm }
              sc rope wsLay (Pv v).h.V #[] (Pv v).settings) fun L =>
            onOk (Layer.plansG L) fun G => f L G

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.onOk_ok
