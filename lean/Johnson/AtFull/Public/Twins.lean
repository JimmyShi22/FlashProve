-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/Twins.lean: THE HEAD's EXAMPLE: publicOfO AT THE STORED FULL-SIZE FILES: THE
  TWINS, EACH ONCE.
A twin is a routine's own text, copied by program by its first writers, less the lines at which
  Lean's kernel stops. Here they stand once.
RE-CUT BY PROGRAM
  out of an earlier working file of this project,
which is not in this repository (sha256 9ec468ab…),
  its lines 164-173, 255-426 and 729-816:
  sortG with its law mergeSort_sortG · Attention.placePiecesS · layCallS · shapeS · shapeHidS ·
    planS · groupS · PlanWritten.Attention.configS · Layer.baseNoFill.
Each twin is tied to its routine by an equation that is proved; at five of the nine (shapeHidS ·
  planS · groupS · configS · baseNoFill) under premises that the equation names. sortG's: here;
  base_eq: Johnson/AtFull/Public/Values.lean; the other seven's: Johnson/AtFull/Public/AttLaws.lean.
NOT HERE, EACH IMPORTED FROM ITS ONE PLACE: mergeF · sortF and their five laws:
  Johnson/Unfolds/MergeSort.lean (the working file's copy was that
file's text but for «Type» where it has «Type u»; that file bears the credit to Lean's core library,
  from which the two routines are adapted) ·
Forest.shapeNoAsk · callAskNoTab: Johnson/Unfolds/ForestTwins.lean · their three laws:
  Johnson/Unfolds/ShapeEq.lean.
The recursion limit is raised in this file (maxRecDepth 1000000).
Nothing on soundness.
-/
import Johnson.Unfolds.MergeSort
import Johnson.Unfolds.ShapeEq
import Johnson.Road.Lane5AttExp
import Johnson.Road.Lane5AttPlan
import Johnson.Road.Lane5AttCalls
import Johnson.Desc.Ok.PlanWritten.PublicAt
import Johnson.Goal.Meaning.ScopeScan
import OnBytes.Model.VerifyPublic
import OnBytes.Tie.Pv.Plan.PlanKits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace OnBytes.Road.K4.Trial
open Johnson.Unfolds (sortF mergeSort_eq)

/-- The bounded text of `List.mergeSort` at a bound above the length. -/
def sortG {α : Type} (le : α → α → Bool) (xs : List α) : List α := (sortF le (xs.length + 1)
    xs).getD []

/-- wp's mergeSort_eq, with a name for its right side. -/
theorem mergeSort_sortG {α : Type} (le : α → α → Bool) (xs : List α) : xs.mergeSort le = sortG le xs
    :=
  mergeSort_eq le xs

end OnBytes.Road.K4.Trial

/-! The forest's two twins (shapeNoAsk · callAskNoTab) and their three laws (asks_ok · shape_eq ·
  ask_eq)
stand in Johnson/Unfolds/ForestTwins.lean and Johnson/Unfolds/ShapeEq.lean, which is imported: the
  model's head's files
(Johnson/AtFull/Head/) import it too, and two declarations of one name cannot lie under one root. -/

namespace OnBytes.Attention
open OnBytes.Model (scaleNat refuseIf roundUp TenAt clamp)
open OnBytes.Road.K4.Trial (sortG)

/-- placePieces' text (OnBytes/Model/AttentionShape.lean:467-474), COPIED BY PROGRAM, with sortG for
  the sort. -/
def placePiecesS (cf : Cfg) (HA : Nat) (kind : Table) (sh : Nat) (segs : List Seg) :
    Array Piece × Nat :=
  let listed : List Piece := segs.flatMap fun s =>
    (List.range (2 ^ cf.ll)).flatMap fun lam =>
      if kind.bySh && cf.sh.getD lam 0 != sh then []
      else (List.range HA).map fun a =>
        ({ seg := s, lam := lam, a := a, b := segBits cf s } : Piece)
  layOff (sortG (fun x y => decide (y.b ≤ x.b)) listed) 0

/-- layCall's text (:502-514), COPIED BY PROGRAM, with placePiecesS for placePieces. -/
def layCallS (cf : Cfg) (HA Smax : Nat) (Tt : Array Nat) (x : Listed) : Except String ACall := do
  let (name, kind, sh, segs) := x
  let (pcs, tot) := placePiecesS cf HA kind sh segs
  let n := max (ceilLog2 tot) cf.nmin
  refuseIf (n < 10 || n > 44) "af-shape-call"
  let call : Model.Call :=
    match kind with
    | .kr => { name := name, n := n, kappa := 5, k := 16, fn := 2, tau := tableOf 16 (rowKR sh) }
    | .wh => { name := name, n := n, kappa := 5, k := 16, fn := 2, tau := tableOf 16 rowWH }
    | .r16 => { name := name, n := n, kappa := 5, k := 16, fn := 0 }
    | .kfd => { name := name, n := n, kappa := 5, k := cf.kFD, fn := 1, t0 := Tt.size,
                tau := tableOf cf.kFD (rowKFD Tt (shdOf Tt.size Smax sh) sh) }
  pure { call := call, kind := kind, sh := sh, segs := segs, pcs := pcs, tot := tot }

/-- shape's text (:522-573), COPIED BY PROGRAM, with sortG for the sort, layCallS for layCall, and
  the table of
exponentials as the argument tt. -/
def shapeS (tt : Option (Array Nat)) (cf : Cfg) : Except String Shape := do
  let lt := cf.lt
  refuseIf (lt < 2 || lt > 16 || cf.lB + 2 > lt) "af-shape-tiles"
  let T := 2 ^ lt
  let lnT := lt - cf.lB
  let G := 2 ^ cf.lgk
  refuseIf (cf.H == 0 || cf.H % G != 0) "af-shape-heads"
  let HA := cf.H / G
  let dh := 2 ^ cf.ldh
  let dq := cf.H * dh
  let dkv := G * dh
  let Lam := 2 ^ cf.ll
  refuseIf (cf.sh.size != Lam) "af-shape-sh"
  refuseIf (cf.la < lt || cf.la - lt > cf.ldh || cf.la > 16) "af-shape-la"
  let ls := cf.la - lt
  -- A remainder of the division has three bytes: lt + S + 1 is at most 24.
  refuseIf (cf.S < 1 || cf.S > 14 || cf.rx < 1 || cf.rx > 12 || lt + cf.S + 1 > 24)
    "af-policy-softmax"
  let Tt ← orRefuse tt "af-policy-softmax"
  let Smax := dh * clamp * clamp
  refuseIf (cf.lmS > nDOf cf || cf.lmS < 1) "af-shape-lmS"
  let shs := (sortG (fun a b => decide (a ≤ b)) cf.sh.toList).eraseDups
  refuseIf (cf.kFD < 8 || cf.kFD > 16) "af-policy-kF"
  shs.forM (shTests cf Tt.size Smax)
  wrapTests cf T Smax
  refuseIf (!linesValid cf.lines) "af-policy-call-list"
  let listed := cf.lines.flatMap (expandLine shs)
  refuseIf (cf.nmin < 10) "af-policy-nmin"
  -- A block is no larger than a column of ao or of qa, and whole blocks fill a column.
  refuseIf (2 ^ cf.la > cf.wcO * T || 2 ^ cf.la > cf.wcQ * T || cf.wcO % 2 ^ ls != 0 ||
    cf.wcQ % 2 ^ ls != 0) "af-shape-la"
  refuseIf (listed.length > 12) "af-policy-call-list"
  let calls ← listed.mapM (layCallS cf HA Smax Tt)
  let cells := 5 * Lam * HA * (2 ^ nMOf cf + 2 ^ nDOf cf)
  let unit := cf.NAs * 2 ^ cf.lmS
  -- In ah a row's maximum and its denominator have four limbs each, for every layer and query head.
  let oIb := 8 * Lam * cf.H
  let featH := oIb + Lam * lt * cf.H
  let featO := 2 * Lam * dq
  let oK := 2 * Lam * dq
  let oV := oK + 2 * Lam * dkv
  let oO := oV + 2 * Lam * dkv
  let featQ := oO + 2 * Lam * dq
  pure {
    cf := cf, T := T, B := 2 ^ cf.lB, nT := 2 ^ lnT, hP := 2 ^ lnT / 2, G := G, HA := HA, dh := dh,
    dq := dq, dkv := dkv, Lam := Lam, u0 := Tt.size, lnT := lnT, nM := nMOf cf, nD := nDOf cf,
    ls := ls, Tt := Tt, calls := calls.toArray, kAs := (cells + unit - 1) / unit * cf.NAs,
    featH := featH, featO := featO, featQ := featQ, fillH := roundUp featH cf.wcH,
    fillO := roundUp featO cf.wcO, fillQ := roundUp featQ cf.wcQ, oMr := 0,
    oZr := 4 * Lam * cf.H, oIb := oIb, oRh := 0, oRhp := Lam * dq, oQ := 0, oK := oK, oV := oV,
    oO := oO, atQ := ⟨0, 2, Lam, dq⟩, atK := ⟨oK, 2, Lam, dkv⟩,
    atV := ⟨oV, 2, Lam, dkv⟩, atO := ⟨oO, 2, Lam, dq⟩, Smax := Smax }

/-- shapeHid's text (:595-611), COPIED BY PROGRAM, with shapeS for shape and the twin
  Forest.shapeNoAsk for
Forest.shape. -/
def shapeHidS (tt : Option (Array Nat)) (lid : Nat) (cf : Cfg) : Except String (Shape ×
    Model.Forest.Shape) := do
  let A ← shapeS tt cf
  let h ← Model.Forest.shapeNoAsk (A.calls.map (·.call)) lid
  -- Two tables of evaluations serve several calls: they are read at the last lmS, or lt + ldh,
  -- coordinates of the calls' key points (the points at which the lookup reads the key vectors).
  -- These coordinates are the same for all calls only if they are among the dT that place a key in
  -- its tree.
  refuseIf (h.dT < max cf.lmS (cf.lt + cf.ldh)) "forest-depth-A"
  let kbA ← Model.Forest.planeCols h cf.lmb
  let calls := A.calls.mapIdx fun q c => { c with call := { c.call with iota := h.iota.getD q 0 } }
  -- The padding keys of a call are one run of keys, from number tot to the last.
  let counted ← calls.foldlM (fun (st : Array Nat × Nat) c => do
    let pub ← Model.Forest.pubRun h st.1 st.2 c.tot (2 ^ c.call.n - c.tot)
    pure (pub, st.2 + 1)) (Model.Forest.noPub h, 0)
  Model.Forest.pubAsk h counted.1
  pure ({ A with kbA := kbA, calls := calls },
    { h with pub := counted.1, calls := calls.map (·.call) })

end OnBytes.Attention

namespace OnBytes.Attention
open OnBytes.Model (refuseIf)

/-- plan's text (OnBytes/Model/AttentionPlan.lean:278-300), COPIED BY PROGRAM, with shapeHidS for
  shapeHid. -/
def planS (tt : Option (Array Nat)) (settings : Model.Settings) (i : In) (cf : Cfg) : Except String
    Plan := do
  if i.hb == 0 then throw "hid-hb"
  if i.aO == 0 then throw "hid-a-owner-uses"
  if cf.Ty != 2 ^ (1 + Model.lbz) then throw "internal-a-Ty"
  let (S, fs) ← shapeHidS tt settings.lidb cf
  let c := S.cf
  if c.NAs + 4 > 256 then throw "hid-a-fold-list"
  let seam0 ← Seam.shape settings (matrices S i) settings.tau i.col0Q i.ktO i.aO
  let x := Counts.of S
  let msg := ownScalars S fs x + seam0.smallElems
  if seam0.tl.NM != c.NAs + 4 then throw "internal-a-claim-count"
  let reads := tableReads S x
  let nLin := ownClaims S fs x + seam0.tl.lins reads
  let own : Params.AttentionRounds :=
    { lt := c.lt, lgk := c.lgk, pairs := S.NP, Lam := S.Lam, planeMessages := x.nKRp,
      score := x.score.toList, e := S.nvE, valueM := S.nvVM, valueD := S.nvVD, attained := S.nvF,
      bits := S.nvH, rows := nLin + seam0.tl.equationsF reads }
  if msg ≥ 2 ^ 30 then throw "hid-a-slots"
  let nW := S.tableElems
  let seam ← seam0.plan nW i.hb settings.hb
  pure { S := S, fs := fs, settings := settings, inp := i, seam := seam, ns := msg, nMsg := msg,
         nLin := nLin, NC := S.calls.size, NP := S.NP, nKRp := x.nKRp, nKFp := x.nKFp, nW := nW,
         own := own }

/-- group's text (OnBytes/Model/AttentionConfig.lean:179-192), COPIED BY PROGRAM, with planS for
  plan. -/
def groupS (tt : Option (Array Nat)) (P : Model.PolScan) (y : Model.Layer.Lay) (s :
    Model.Layer.Scales) (midQ : Nat → Nat)
    (lines : List Line) (g : Nat) : Except String Plan := do
  let cf ← fill P y s lines g
  let X ← planS tt P.settings (inOf P.settings y (midQ g) g) cf
  refuseIf (P.h.iotaA0 != 32 + X.fs.dT) "policy-iotaA"
  let A := X.S
  refuseIf (A.fillQ != y.filled.getD 3 0 || A.featQ != y.feat.getD 3 0) "internal-qa-layout"
  Model.Layer.tensorsAgree ((y.ten.filter fun t => t.mat == 3).map fun t => (t.name, t.place))
    [("q", A.atQ), ("kx", A.atK), ("v", A.atV), ("o", A.atO)]
  refuseIf (A.Lam != y.Lam || A.dq != y.dq || A.dkv != y.dkv || A.ls != y.ls ||
    A.dh % y.S2 != 0) "plan-tensor-layout"
  refuseIf (A.atQ.J != A.cf.H * A.dh || A.atO.J != A.atQ.J || A.atK.J != A.G * A.dh ||
    A.atV.J != A.atK.J) "plan-tensor-layout"
  pure X

end OnBytes.Attention

namespace VerifiableInference.PlanWritten.Attention
open OnBytes OnBytes.Attention
open OnBytes.Model (refuseIf)

/-- configO's text (Johnson/Desc/Ok/PlanWritten/PublicAt.lean:100-112), COPIED BY PROGRAM, with
  groupS for group. -/
def configS (tt : Option (Array Nat)) (o : Nat → ByteArray → ByteArray) (P : Model.PolScan) (y :
    Model.Layer.Lay) (s : Model.Layer.Scales) (midQ : Nat → Nat) :
    Except String Config := do
  let h := P.h
  let lines ← readLines P.polCallsA
  refuseIf (h.Gk &&& (h.Gk - 1) != 0) "af-shape-heads"
  refuseIf (h.lmh < h.lt || h.lmh > 24 || h.lmo < h.lt || h.lmo > 24 || h.lmbA > 24 ||
    h.lmS > 24 || h.NAs == 0 || h.NAs > 64) "shape-request-matrix-A"
  let plans ← (List.range y.NGr).mapM (groupS tt P y s midQ lines)
  match plans with
  | X :: _ =>
    tableHeldO o P .exp X.S.Tt
    pure { plans := plans.toArray, hCallsA := callsDigestO o lines }
  | [] => throw "shape-L"

end VerifiableInference.PlanWritten.Attention

namespace OnBytes.Model.Layer

/-- layoutBase's text (OnBytes/Model/LayerLayout.lean:476-560) less its two calls of tensorsFill
  (:533-535),
COPIED BY PROGRAM; its law base_eq lies in Johnson/AtFull/Public/Values.lean. -/
def baseNoFill (h : Shape) (pc : List (List String)) : Except String Lay := do
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
  refuseIf ([h.eps1, h.eps2].any fun e => e < 1 || e ≥ 2 ^ 59) "policy-norm"
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

#print axioms OnBytes.Road.K4.Trial.mergeSort_sortG
