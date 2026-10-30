-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/LayerPanels.lean: the batched sumcheck of a layer sub-proof and its weight claims.

The keys of many lookup segments hold inner products: of a vector of cells with a column of a
weight matrix, or of two vectors over the tokens. One sumcheck proves all of them together. Its
summand is a product A B of two long vectors. A stretch of them, which is called a panel here, holds
the inner products of one segment on the group's layers, or on the experts of one layer. A panel has
rows (these layers or experts) and columns (the index that an inner product sums over).

Words. Calls and segments are those of OnBytes/Model/Calls.lean. A shown value is the scalar that
the prover has sent for a hidden value (Fork in OnBytes/Model/Hide.lean). The selector of a layer
with routed experts is tensor sel: for each token one entry for each of the NE experts, in an honest
proof 1 for the expert that the router chooses and 0 for the others.

Some vectors are never sent: the A side of the down product's panel and, with routed experts, the
column factor of each routed down product's panel. Such a vector holds, for each feature, the gated
product s u, summed over the tokens under the equality weights of a token point. The prover does not
commit to it. At the sumcheck's end the prover shows the vector's value at the end point. A product
layer that starts from this value (hearGated in OnBytes/Model/Layer.lean) reduces it to values of s
and u.

This file follows the parts of verifier/src/vf_layers_check.inc that
 - list the panels (panelsA, panelsT) and place them in the long vectors (placePanels),
 - compute, at the sumcheck's end point, what the shown values of the two sides must equal and what
   the summand is on the shown values (stackEnd),
 - list the claims on the committed matrix of weights that the panels leave, each as one factor for
   each index group of its unit (weightClaims).

A definition that has the name of a local type or function of the C++ routine runForkHidG2 in that
file follows it (SBlk, plain, tri, isAcc, kT, kTM, facRs, facEw).

No function here receives a message or draws a challenge. Where the C++ source refuses, the function
that follows it returns none, and the caller (form in OnBytes/Model/Layer.lean) fails without a name
of its own, where the C++ verifier gives a name (internal-stack, internal-claim-unit and
plan-tensor-layout among them). facRs, facEw and claimE also return none where an index would lie
past a table's end, a case for which the C++ source has no test. Everywhere else an index past an
array's end reads as 0 or as an empty record (getD). On a layout that has passed layout no such read
occurs: each array is made with the length over which it is read, from the same public numbers, and
the caller has compared the numbers of places and of weight claims with the plan. This is by
reading; no test or theorem here shows it. Three tests of the C++ lines, on the number of places and
on the number of weight claims, are made in the caller (OnBytes/Model/Layer.lean). None of these
refusals depends on a value of a proof.

Main definitions: SBlk, Panels, plain, tri, panelsA, panelsT, placePanels, StackEnd, stackEnd,
ropeC, facRs, facEw, claimE, weightClaims.

What is not claimed: nothing is proved here.
-/
import OnBytes.Model.LayerForms
import OnBytes.Model.Weights

namespace OnBytes.Model.Layer

/-! ## The panels -/

/-- One panel of the batched sumcheck. -/
structure SBlk where
  /-- the rows carry the selector: A(e, yv) = sl[e] xx[yv] -/
  tri : Bool := false
  /-- for a panel whose B side is a weight matrix: the number of its first weight claim -/
  v0 : Option Nat := none
  /-- 0 for a panel of the lookup's join, 1 for one of the second token sumcheck's terms -/
  claim : Nat := 0
  /-- the weight of the panel's call in the lookup -/
  ec : E := zeroE
  /-- the rows -/
  ni : Nat := 0
  /-- the columns -/
  ny : Nat := 0
  /-- the bits of a column's number -/
  wy : Nat := 0
  /-- the bits of a place in the panel -/
  w : Nat := 0
  /-- the panel's first place in the long vectors -/
  off : Nat := 0
  /-- the A side at (row, column), if it is given as a form -/
  A : Option (Nat → Nat → Option Aff) := none
  /-- the B side at (row, column), if it is given as a form -/
  B : Option (Nat → Nat → Option Aff) := none
  /-- the weight of each row; one weight for a panel with the selector -/
  wt : Array E := #[]
  /-- with the selector: its shown values -/
  sl : Array E := #[]
  /-- with the selector: the column factor, unless it is a vector that is never sent -/
  xx : Array Aff := #[]
  /-- the number of the never-sent vector that is the A side or the column factor -/
  virt : Option Nat := none

/-- The list of panels so far, and the number of the next weight claim. -/
structure Panels where
  /-- the panels, in the list's order -/
  bl : Array SBlk := #[]
  /-- the number of the next weight claim -/
  nextV : Nat := 0

/-- What the lists of panels read besides the tables. -/
structure PanelEnv where
  /-- the tables and the calls' points -/
  v : Env
  /-- for each call its weight in the lookup -/
  e : Array E
  /-- the values that the second token sumcheck has shown, from its first end value on: the
  reciprocal of every norm, then the score of every layer with routed experts, then the selector's
  entries of every such layer -/
  shownT : Array E
  /-- the last lt coordinates of the lookup's point -/
  zt : Array E
  /-- what takes the place of the attention output at profile 3: layer, token,
  feature -/
  stubO : Nat → Nat → Nat → Int

/-- Appends a panel with two factors, over all layers of the group, or over those with routed
experts if moeSet. A, B and wt take the layer's number in the group. Without B the B side is a
weight matrix, and each row leaves one weight claim. -/
def plain (y : Lay) (ec : E) (claim : Nat) (moeSet : Bool) (ny : Nat)
    (A B : Option (Nat → Nat → Option Aff)) (wt : Nat → E) (virt : Option Nat) (s : Panels) :
    Panels :=
  let ni := if moeSet then y.LamM else y.Lam
  let row (i : Nat) : Nat := if moeSet then 2 * i + 1 else i
  let wy := ceilLog2 ny
  let b : SBlk :=
    { claim := claim, ec := ec, ni := ni, ny := ny, wy := wy, w := ceilLog2 ni + wy,
      A := A.map fun f => fun i yv => f (row i) yv
      B := B.map fun f => fun i yv => f (row i) yv
      wt := (Array.range ni).map fun i => wt (row i)
      v0 := if B.isNone then some s.nextV else none
      virt := virt }
  { bl := s.bl.push b, nextV := if B.isNone then s.nextV + ni else s.nextV }

/-- Appends a panel whose rows carry the selector: NE rows, nk columns, one weight and one weight
claim. -/
def tri (y : Lay) (ec : E) (claim nk : Nat) (sl : Array E) (xx : Array Aff) (virt : Option Nat)
    (wt : E) (s : Panels) : Panels :=
  let wy := ceilLog2 nk
  let b : SBlk :=
    { tri := true, claim := claim, ec := ec, ni := y.h.NE, ny := nk, wy := wy,
      w := ceilLog2 (max y.h.NE 1) + wy, sl := sl, xx := xx, virt := virt, wt := #[wt],
      v0 := some s.nextV }
  { bl := s.bl.push b, nextV := s.nextV + 1 }

/-- True for a segment whose key holds an inner product with a weight matrix at the lookup's
point. -/
def isAcc (s : String) : Bool := ["G", "U", "V", "O", "D", "LR"].contains s

/-- The numbers of the calls that hold a segment for which isAcc is true, in the order of
y.calls. -/
def callsAC (y : Lay) : List Nat :=
  (y.calls.toList.zipIdx.filter fun c => c.1.segs.any fun s => isAcc s.name).map (·.2)

/-- The factor 2^max(0, 16 - k), where k is word i of the record of layer l. -/
def kT (sc : Scales) (l i : Nat) : E := pw (tOf (sc.kl l i))

/-- The same for word i of the record of a layer with routed experts. -/
def kTM (sc : Scales) (l i : Nat) : E := pw (tOf (sc.klM l i))

/-- What takes the place of the attention output at profile 3, at the token point zt: a public
number. et: the equality table of zt. -/
def stubAt (p : PanelEnv) (et : Array E) (lam k2 : Nat) : Aff :=
  Aff.ofConst ((List.range p.v.y.T).foldl
    (fun ao t => addE ao (mulE (et.getD t zeroE) (ofInt (p.stubO (p.v.lay lam) t k2)))) zeroE)

/-- The panels of one segment of a call of the lookup's join. el: the weights of the layers at the
call's point. -/
def panelA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels) : Panels :=
  let v := p.v
  let y := v.y
  let h := y.h
  let wtOf (i : Nat) : Nat → E := fun lam => mulE (el.getD lam zeroE) (kT v.sc (v.lay lam) i)
  if sn == "G" || sn == "U" then
    let m := v.tensorAt "m" "zt"
    plain y ec 0 false h.d (some fun lam k2 => v.shIn m lam k2) none
      (wtOf (if sn == "U" then Lku else Lkg)) none s
  else if sn == "V" then
    let a := v.tensorAt "a" "zt"
    plain y ec 0 false h.d (some fun lam k2 => v.shIn a lam k2) none (wtOf Lkv) none s
  else if sn == "O" then
    let et := eqTab p.zt
    let o := v.tensorAt "o" "zt"
    plain y ec 0 false y.dq
      (some fun lam k2 => if h.p4 then v.shIn o lam k2 else some (stubAt p et lam k2)) none
      (wtOf Lko) none s
  else if sn == "D" then plain y ec 0 false h.f none none (wtOf Lkd) (some 0) s
  else if sn == "LR" then
    let m := v.tensorAt "m" "zt"
    plain y ec 0 true h.d (some fun lam k2 => v.shIn m lam k2) none
      (fun lam => mulE (el.getD lam zeroE) (kTM v.sc (v.lay lam) 0)) none s
  else s

/-- The panels of the calls of the lookup's join, in the order of the calls and their segments. -/
def panelsA (p : PanelEnv) (s : Panels) : Panels :=
  (callsAC p.v.y).foldl
    (fun s q =>
      let el := eqTab (p.v.zl q)
      (p.v.y.calls.getD q default).segs.foldl
        (fun s g => panelA p (p.e.getD q zeroE) el g.name s) s)
    s

/-- The panels of one segment of a call that has terms in the second token sumcheck. -/
def panelT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels) : Option Panels := do
  let v := p.v
  let y := v.y
  let h := y.h
  let NE := h.NE
  let elAt (lam : Nat) : E := el.getD lam zeroE
  let sSc := y.NN * y.Lam
  let sSel := sSc + y.LamM
  let sh (i : Nat) : Aff := Aff.ofConst (p.shownT.getD i zeroE)
  if sn == "N1" || sn == "N2" then
    let n2 := if sn == "N2" then 1 else 0
    let wh ← v.ewh sn
    pure (plain y ec 1 false 1 (some fun lam _ => some (sh (2 * lam + n2)))
      (some fun lam _ => v.SxsA wh "Y" (2 * lam + n2)) elAt none s)
  else if sn == "QK" then
    let a := v.tensorAt "a" "rt"
    pure (plain y ec 1 false h.d (some fun lam k2 => v.shIn a lam k2) none
      (fun lam => mulE (elAt lam) (kT v.sc (v.lay lam) Lkq)) none s)
  else if !h.p3 then pure s
  else if sn == "XR" then
    let ew ← v.ewOf "XR"
    pure (plain y ec 1 true 1 (some fun lam _ => some (sh (sSc + lam / 2)))
      (some fun lam _ => v.shSum ew h.d "m" "rt" lam) elAt none s)
  else if sn == "DD" || sn == "MR" then
    let ew ← v.ewOf sn
    let wS := if sn == "DD" then sumE ew else ew.getD 0 zeroE
    pure (plain y ec 1 true NE (some fun lam e => some (sh (sSel + (lam / 2) * NE + e)))
      (some fun lam e => v.shA "lr" "rt" (lam / 2) e) (fun lam => mulE (elAt lam) wS) none s)
  else if sn == "G" || sn == "U" || sn == "D" then
    (List.range y.LamM).foldlM
      (fun s lm => do
        let lam := 2 * lm + 1
        let sl := (Array.range NE).map fun e => p.shownT.getD (sSel + lm * NE + e) zeroE
        if sn == "D" then
          pure (tri y ec 1 h.fe sl #[] (some (1 + lm))
            (mulE (elAt lam) (kT v.sc (v.lay lam) Lkd)) s)
        else
          let xr := v.tensorAt "xr" "rt"
          let xx ← (Array.range h.d).mapM fun k2 => v.shIn xr lm k2
          pure (tri y ec 1 h.d sl xx none
            (mulE (elAt lam) (kTM v.sc (v.lay lam) (if sn == "U" then 2 else 1))) s))
      s
  else pure s

/-- The panels of the calls that have terms in the second token sumcheck. TS: their numbers. -/
def panelsT (p : PanelEnv) (TS : List Nat) (s : Panels) : Option Panels :=
  TS.foldlM
    (fun s q =>
      let el := eqTab (p.v.zl q)
      (p.v.y.calls.getD q default).segs.foldlM
        (fun s g => panelT p (p.e.getD q zeroE) el g.name s) s)
    s

/-- Places the panels one after the other, the largest first, panels of one size in the list's
order. Returns the panels in the list's order, each with its first place, and the number of all
places. -/
def placePanels (bl : Array SBlk) : Array SBlk × Nat :=
  let ord := (List.range bl.size).mergeSort fun a b =>
    decide ((bl.getD b {}).w ≤ (bl.getD a {}).w)
  ord.foldl
    (fun (s : Array SBlk × Nat) i =>
      (s.1.modify i fun b => { b with off := s.2 }, s.2 + 2 ^ (bl.getD i {}).w))
    (bl, 0)

/-! ## The end of the batched sumcheck -/

/-- What the end of the batched sumcheck leaves. -/
structure StackEnd where
  /-- what the shown value of the A side must equal -/
  Alin : Aff := {}
  /-- what the shown value of the B side must equal -/
  Blin : Aff := {}
  /-- the value of the A side at the end point, computed from what was shown: shownA plus the
  panels' parts that hold a never-sent vector -/
  As : E := zeroE
  /-- the value of the B side at the end point, computed from what was shown: shownB plus the
  panels' parts that hold a weight claim -/
  Bs : E := zeroE
  /-- the bits of the panel of the down product -/
  wD : Nat := 0

/-- What one panel adds to the end of the batched sumcheck. rs: the challenges, rs[t] for bit t;
lam: their number; om: the weights of the two claims; H1: the shown values of the never-sent
vectors; V: the shown values of the weight claims. Returns none if the panel's place does not fit
the lam bits, if a panel with the selector and a never-sent vector has a number of column bits other
than lfe, if a second panel has a never-sent vector as its whole A side, or if a side that is needed
is absent. That a panel has at most lam bits is not tested here: the caller has tested that lam is
the logarithm, rounded up, of the number of all panels' places (internal-stack in
OnBytes/Model/Layer.lean). -/
def stackEndOf (y : Lay) (rs : Array E) (lam : Nat) (om H1 V : Array E) (s : StackEnd) (b : SBlk) :
    Option StackEnd := do
  if !eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) then none
  let sb := eqLowAt rs b.w lam (b.off / 2 ^ b.w)
  let EY := eqLow rs 0 b.wy
  let EI := eqLow rs b.wy b.w
  let omb := om.getD b.claim zeroE
  let co := mulE (mulE sb omb) b.ec
  let wt (i : Nat) : E := b.wt.getD i zeroE
  let ei (i : Nat) : E := EI.getD i zeroE
  if b.tri then
    let v0 ← b.v0
    let s1 := (List.range y.h.NE).foldl
      (fun a e => addE a (mulE (b.sl.getD e zeroE) (ei e))) zeroE
    let c1 := mulE (mulE co (wt 0)) s1
    let Bs := addE s.Bs (mulE sb (V.getD v0 zeroE))
    match b.virt with
    | some k =>
      if b.wy != y.lfe then none
      else pure { s with As := addE s.As (mulE c1 (H1.getD k zeroE)), Bs := Bs }
    | none =>
      let Alin := (List.range b.ny).foldl
        (fun a k2 => a.addMul (b.xx.getD k2 {}) (mulE c1 (EY.getD k2 zeroE))) s.Alin
      pure { s with Alin := Alin, Bs := Bs }
  else
    match b.virt with
    | some k =>
      -- Here ec and the rows' weights are on the B side. So the panel's A side is om times the
      -- never-sent vector itself, and hearGated can start from that vector's shown value.
      let v0 ← b.v0
      if s.wD != 0 then none
      else
        let Bs := (List.range b.ni).foldl
          (fun a i =>
            addE a (mulE (mulE (mulE (mulE sb (ei i)) b.ec) (wt i)) (V.getD (v0 + i) zeroE)))
          s.Bs
        pure { s with wD := b.w, As := addE s.As (mulE (mulE sb omb) (H1.getD k zeroE)), Bs := Bs }
    | none =>
      let A ← b.A
      (List.range b.ni).foldlM
        (fun s i => do
          let ca := mulE (mulE co (wt i)) (ei i)
          let cb := mulE sb (ei i)
          let s ← (List.range b.ny).foldlM
            (fun (s : StackEnd) yv => do
              let ey := EY.getD yv zeroE
              let Alin := s.Alin.addMul (← A i yv) (mulE ca ey)
              match b.v0, b.B with
              | none, some B =>
                pure { s with Alin := Alin, Blin := s.Blin.addMul (← B i yv) (mulE cb ey) }
              | none, none => none
              | some _, _ => pure { s with Alin := Alin })
            s
          match b.v0 with
          | some v0 =>
            pure { s with Bs := addE s.Bs (mulE (mulE sb (ei i)) (V.getD (v0 + i) zeroE)) }
          | none => pure s)
        s

/-- The end of the batched sumcheck over all panels. shownA, shownB: the two shown values that stand
for the parts of the two sides that are forms in the reads. Returns none unless the panel of the
down product has ll + lPf bits. -/
def stackEnd (y : Lay) (bl : Array SBlk) (rs : Array E) (lam : Nat) (om H1 V : Array E)
    (shownA shownB : E) : Option StackEnd := do
  let s ← bl.foldlM (stackEndOf y rs lam om H1 V) { As := shownA, Bs := shownB }
  if s.wD != y.h.ll + y.lPf then none else pure s

/-! ## The weight claims -/

/-- What the list of weight claims reads. -/
structure ClaimEnv where
  /-- the tables and the calls' points -/
  v : Env
  /-- the layout of the committed matrix of weights -/
  wsLay : WsLay
  /-- the rotary table, as ropeOf gives it -/
  rope : Array Nat
  /-- the challenges of the batched sumcheck, rs[t] for bit t -/
  rs : Array E
  /-- the end point of the second token sumcheck -/
  rt : Array E

/-- An entry of the rotary table for layer l of the model, token t and pair i of coordinates. A word
of the table holds its entry plus 4096, and the sines follow all cosines. A layer without rotary
embeddings has the cosine 2^cs and the sine 0. C++: ropeC in runStage,
verifier/src/cp_verify.cpp. -/
def ropeC (h : Shape) (sc : Scales) (rope : Array Nat) (l t i : Nat) (sine : Bool) : Int :=
  if sc.klRp l == 0 then (if sine then 0 else 2 ^ h.cs)
  else
    let half := h.dh / 2
    (rope.getD ((if sine then 2 ^ h.lt * half else 0) + t * half + i) 0 : Int) - 4096

namespace ClaimEnv

/-- The factor for a group whose index is given by the bits lo0 to lo0 + wtot - 1 of the batched
sumcheck's place. Returns none if these bits are too few for every index of the group, or if the
place has fewer bits. -/
def facRs (c : ClaimEnv) (G : WsGrp) (lo0 wtot : Nat) : Option WsFac := do
  if G.z > wtot || lo0 + wtot > c.rs.size then none
  let e := eqLow c.rs (lo0 + G.z) (lo0 + wtot)
  let HV ← (Array.range G.o).mapM fun hi => e[hi]?
  pure { pt := (Array.range G.z).map fun i => c.rs.getD (lo0 + G.z - 1 - i) zeroE, HV }

/-- The factor for a group whose index x runs over the entries x0 + x of segment sn: the segment's
weights at the point of its call. Returns none if no call holds the segment, if the group has more
low bits than the call's point has coordinates of the column, if an index lies past the segment's
entries, or if a column lies past the equality table. -/
def facEw (c : ClaimEnv) (G : WsGrp) (sn : String) (x0 : Nat) : Option WsFac := do
  let (q, cd, s) ← c.v.callOf sn
  if G.z > cd.lJ then none
  let zj := c.v.zj q cd.lJ
  let e := eqTab (zj.extract 0 (cd.lJ - G.z))
  let HV ← (Array.range G.o).mapM fun xh => do e[(← s.pos[x0 + xh * 2 ^ G.z]?) / 2 ^ G.z]?
  pure { pt := (Array.range G.z).map fun i => zj.getD (cd.lJ - G.z + i) zeroE, HV }

/-- The claim on the unit of kind X at layer lam of the group, with the factor fac G for each of the
unit's groups G. The kinds: 0 qk, 1 v, 2 o, 3 g, 4 u, 5 gs, 6 us, 7 gr, 8 ur, 9 dn, 10 dnr, 11 r
(kindList in OnBytes/Model/LayerLayout.lean), 12 the embedding. Returns none if the layout of the
weights has no such unit, or if fac returns none. -/
def claim (c : ClaimEnv) (X lam : Nat) (fac : WsGrp → Option WsFac) : Option WsClaim := do
  let ui ← c.wsLay.unitOf X (c.v.lay lam)
  let u ← c.wsLay.U[ui]?
  pure { ui := ui, f := ← u.g.mapM fac }

/-- The claims of one segment of a call of the lookup's join: one for each of the panel's rows. -/
def claimsA (c : ClaimEnv) (sn : String) : Option (List WsClaim) :=
  let y := c.v.y
  if !isAcc sn then some []
  else
    (List.range (if sn == "LR" then y.LamM else y.Lam)).mapM fun i =>
      let lam := if sn == "LR" then 2 * i + 1 else i
      let mo := c.v.isMoe lam
      let X := if sn == "G" then (if mo then 5 else 3)
        else if sn == "U" then (if mo then 6 else 4)
        else if sn == "V" then 1 else if sn == "O" then 2 else if sn == "D" then 9 else 11
      let wy := ceilLog2 (if sn == "O" then y.dq else if sn == "D" then y.h.f else y.h.d)
      c.claim X lam fun G => if G.name == "kk" then c.facRs G 0 wy else c.facEw G sn 0

/-- At the point of the call that holds segment QK: the weights of the heads, and the equality table
of the coordinates within a head. The segment holds the features of q, then those of k. The first
array has 64 entries, as in the C++ source: the H heads of q, the Gk heads of k, then zeros; the
layout has refused H + Gk above 64 (shape-heads). Returns none if no call holds QK, if the layout
lacks tensor q or kx, if the call's point has fewer than ldh coordinates of the column, or if a head
does not fit its tensor. -/
def headWeights (c : ClaimEnv) : Option (Array E × Array E) := do
  let y := c.v.y
  let h := y.h
  let (q, cd, s) ← c.v.callOf "QK"
  let (hi, lo) ← (cutLast (c.v.zj q cd.lJ) y.ldh).toOption
  let e := eqTab hi
  let tq := (← y.T_ "q").place
  let tk := (← y.T_ "kx").place
  let AH ← (List.range (h.H + h.Gk)).foldlM
    (fun (a : Array E) hd => do
      let x ← if hd < h.H then (headFeat tq hd h.dh).toOption
        else (headFeat tk (hd - h.H) h.dh).toOption.map (tq.J + ·)
      pure (a.setIfInBounds hd (e.getD (s.pos.getD x 0 / h.dh) zeroE)))
    (Array.replicate 64 zeroE)
  pure (AH, eqTab lo)

/-- The factor on the coordinates within a head for the query-key unit of layer lam: the rotation
by the rotary table, summed over the tokens under the weights et, applied to lfc. -/
def ropeFactor (c : ClaimEnv) (et lfc : Array E) (lam : Nat) : Array E :=
  let h := c.v.y.h
  let l := c.v.lay lam
  let sumOver (i : Nat) (sine : Bool) : E :=
    (List.range c.v.y.T).foldl
      (fun a t => addE a (mulE (et.getD t zeroE) (ofInt (ropeC h c.v.sc c.rope l t i sine)))) zeroE
  (Array.range (h.dh / 2)).flatMap fun i =>
    let Ct := sumOver i false
    let St := sumOver i true
    let a := lfc.getD (2 * i) zeroE
    let b := lfc.getD (2 * i + 1) zeroE
    #[addE (mulE Ct a) (mulE St b), subE (mulE Ct b) (mulE St a)]

/-- The claims of one segment of a call that has terms in the second token sumcheck. -/
def claimsT (c : ClaimEnv) (sn : String) : Option (List WsClaim) := do
  let y := c.v.y
  let h := y.h
  if sn == "QK" then
    let (AH, lfc) ← c.headWeights
    let et := eqTab c.rt
    (List.range y.Lam).mapM fun lam =>
      let kap := c.ropeFactor et lfc lam
      c.claim 0 lam fun G =>
        if G.name == "hd" then some { AV := AH }
        else if G.name == "cd" then some { AV := kap }
        else c.facRs G 0 (ceilLog2 h.d)
  else if h.p3 && (sn == "G" || sn == "U" || sn == "D") then
    let wk := ceilLog2 (if sn == "D" then h.fe else h.d)
    (List.range y.LamM).mapM fun lm =>
      c.claim (if sn == "G" then 7 else if sn == "U" then 8 else 10) (2 * lm + 1) fun G =>
        if G.name == "kk" then c.facRs G 0 wk
        else if G.name == "e" then c.facRs G wk (ceilLog2 (max h.NE 1))
        else c.facEw G sn (if sn == "D" then 0 else h.fe)
  else pure []

/-- The embedding's claim, which the first group proves. ZE: the point of ls + lt coordinates; tkh:
the lPd - ls further coordinates of the feature; V: the size of the vocabulary; tokv: the request's
tokens. The factor on the vocabulary gives each token's id the weight of its positions. Returns none
unless there are T tokens, each below V; also if the layout of the weights has no unit for the
embedding, if ZE has fewer than lt coordinates, if a group has more than lPd low bits, or if an
index lies past a table's end. The lengths of ZE and tkh are not tested here: the caller draws them
with these lengths. -/
def claimE (c : ClaimEnv) (ZE tkh : Array E) (V : Nat) (tokv : Array Nat) : Option WsClaim := do
  let y := c.v.y
  if tokv.size != y.T || tokv.any (· ≥ V) then none
  let ui ← c.wsLay.unitOf 12 y.h.L
  let u ← c.wsLay.U[ui]?
  let (low, tok) ← (cutLast ZE y.h.lt).toOption
  let pnt := tkh ++ low
  let et := eqTab tok
  let psi := (List.range y.T).foldl
    (fun (a : Array E) t => a.modify (tokv.getD t 0) fun x => addE x (et.getD t zeroE))
    (Array.replicate V zeroE)
  let f ← u.g.mapM fun (G : WsGrp) =>
    if G.name == "v" then some ({ AV := psi } : WsFac)
    else if G.z > y.lPd then none
    else do
      let e := eqTab (pnt.extract 0 (y.lPd - G.z))
      let HV ← (Array.range G.o).mapM fun hi => e[hi]?
      pure { pt := (Array.range G.z).map fun i => pnt.getD (y.lPd - G.z + i) zeroE, HV }
  pure { ui := ui, f := f }

/-- The weight claims of the panels, in the order in which panelsA and then panelsT list the panels:
a panel with two factors whose B side is a weight matrix gives one claim for each row, a panel with
the selector gives one. TS: the numbers of the calls that have terms in the second token
sumcheck. -/
def weightClaims (c : ClaimEnv) (TS : List Nat) : Option (List WsClaim) := do
  let y := c.v.y
  let segsOf (q : Nat) : List String := (y.calls.getD q default).segs.map (·.name)
  let a ← ((callsAC y).flatMap segsOf).mapM c.claimsA
  let t ← (TS.flatMap segsOf).mapM c.claimsT
  pure (a.flatten ++ t.flatten)

end ClaimEnv

end OnBytes.Model.Layer
