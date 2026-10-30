-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/HeadForms.lean: the forms from which the claims of the head's sub-proof are made.

A form is an affine expression in hidden values (OnBytes/Model/Hide.lean). This file holds the
public weights of the lookup's segments, the readers that turn entries of the tables of reads into
forms, and, for each segment, the form that stands for the segment's part of its call's key vector
at the call's key point. The C++ counterpart is the set of local functions in the last part of
runForkHidH2 in vf_output_head_check.inc. A definition that mirrors one of them keeps its name.
The names of matrices, tensors and segments are explained in OnBytes/Model/HeadLayout.lean.

A margin. At a real place (a vocabulary entry v and a covered position t) the margin is
  D = logit[win_t] + [t has a cost] (c_t + b_t 2^37) - logit[v] - [v < win_t].
It is written in three digits, D = K_2 + 2^sh K_1 + 2^(sh + 15) K_0. Each digit is looked up in a
range table. Together with the no-overflow conditions (`h9` in OnBytes/Model/HeadLayout.lean) this
is meant to show that D is not negative: the checked token has the largest logit, up to the
position's cost, and the first of equal logits counts as the largest.

Main definitions: `ewOf`, `ewh`, `wxOf`, `onSum`, `placeTermH`, `publicTermH`, `Sl`, `xbA`,
`sh2`, `RowAH`, `rowAt`, `row5At`, `gapAt`, `LINE`, `keyForm`.
What is not claimed: no theorem is stated here. Hidden is the name of a value's part in the protocol
(OnBytes/Model/Hide.lean). Nothing here says that a value stays hidden.
-/
import OnBytes.Model.HeadTables

namespace OnBytes.Model.Head

/-- The names of this file's refusals. Where cp_verify appends the name of a segment to a
name, the name here ends before it. `held` passes on the last of them from `cutLast`
(OnBytes/Model/Tensors.lean). -/
def Forms.names : List String :=
  ["internal-h-join-place", "internal-segment", "internal-line", "plan-tensor-layout"]

/-- The hidden value in a slot. -/
abbrev S_ (s : Nat) : Aff := Aff.slot s

/-- The power 2^k as an element of the field. -/
def pw (k : Nat) : E := ofNat (2 ^ k)

/-- The offset of a cell of one byte: a cell holds its digit minus 128. -/
def o1 : E := ofNat 128

/-- The offset of two cells read at radix 256. -/
def o2 : E := ofNat 32896

/-- A call and one of its segments, by the segment's name. -/
def segOf (R : Run) (sn : String) : SubM (Nat × CallD × Seg) := do
  let q ← getAs "internal-segment" (callNo R.L sn)
  let c := R.L.calls.getD q default
  let g ← getAs "internal-segment" (c.seg? sn)
  pure (q, c, g)

/-- The public weights of a segment's entries: entry x has the equality weight of its column at
the column coordinates of its call's key point. -/
def ewOf (R : Run) (sn : String) : SubM (Array E) := do
  let (q, _, g) ← segOf R sn
  let e := eqTab (zjOf R.L R.x.g1 q)
  pure (g.pos.map fun p => e.getD p zeroE)

/-- The public weights of a segment's blocks of S2 neighbouring entries. Let e be the equality table
at the column coordinates of the call's key point without their last ls. Block xh gets e[pos[S2 xh]
/ S2]. So the column of a block's first entry stands for the whole block. That is right if S2
divides the segment's length, because `place` then puts each block in S2 neighbouring columns that
begin at a multiple of S2. `admitted` tests this for d and `numbers` for JVa, and JV is a multiple
of S2 by its definition. -/
def ewh (R : Run) (sn : String) : SubM (Array E) := do
  let (q, _, g) ← segOf R sn
  let k ← held (cutLast (zjOf R.L R.x.g1 q) R.h.ls)
  let e := eqTab k.1
  let S2 := R.h.S2
  pure ((Array.range (g.n / S2)).map fun xh => e.getD (g.pos.getD (S2 * xh) 0 / S2) zeroE)

/-- The sum of a segment's weights over the entries of the vocabulary alone, for HD0, HD1 or HD2,
whose entry x is entry x of the vocabulary. -/
def wxOf (R : Run) (ew : Array E) : E := sumE (ew.extract 0 R.h.V)

/-- The sum of eq(P, t) over the covered positions t. -/
def onSum (R : Run) (P : Array E) : E :=
  let e := eqTab P
  (List.range R.h.T).foldl
    (fun s t => if R.cov.hOn.getD t false then addE s (e.getD t zeroE) else s) zeroE

/-- The public term of the margins that makes the first of equal logits the largest: the sum over
the covered positions t of et[t] times the sum of ew[v] over v < win_t. -/
def placeTermH (R : Run) (ew et : Array E) : E :=
  let pre := ((List.range (R.h.V - 1)).foldl
    (fun (a : Array E × E) v =>
      let s := addE a.2 (ew.getD v zeroE)
      (a.1.push s, s)) (#[zeroE], zeroE)).1
  (List.range R.h.T).foldl
    (fun s t =>
      if R.cov.hOn.getD t false then
        addE s (mulE (et.getD t zeroE) (pre.getD (R.x.win.getD t 0) zeroE))
      else s) zeroE

/-- A further public term of the margins. Always 0. It is kept so that the margin has the same terms
as in the C++ routine. -/
def publicTermH (_ew _et : Array E) : E := zeroE

/-- A tensor of hf under a segment's weights, read in the long table at Z: nl limbs of J features
from feature OFF on, at radix 256. -/
def Sl (R : Run) (sn : String) (OFF nl J : Nat) : SubM Aff := do
  let wh ← ewh R sn
  let t ← tabAt R "hf@Z"
  let mut s : Aff := {}
  for xh in [0:wh.size] do
    for l in [0:nl] do
      s := Aff.addMul s (← U3at R t ((OFF + l * J) / R.h.S2 + xh))
        (scaleNat (wh.getD xh zeroE) (256 ^ l))
  pure s

/-- Block kh of the residual stream in the table that begins at t: its limbs at radix 256. -/
def xbA (R : Run) (t kh : Nat) : SubM Aff := do
  let mut s : Aff := {}
  for l in [0:R.b.nl] do
    s := Aff.addMul s (← U3at R t (R.b.cell l 0 / R.h.S2 + kh)) (ofNat (256 ^ l))
  pure s

/-- Feature j of hd in the table that begins at t: its two limbs at radix 256. -/
def sh2 (R : Run) (t j : Nat) : SubM Aff := do
  pure ((← U3at R t j) + Aff.scale (← U3at R t (R.h.d + j)) (ofNat 256))

/-- The norm's row with four limbs: 74 digits, and the numbers that they represent. `rowAt` only
adds up digits. What a field's docstring says of it is what the ledger's lines (`claimLedger4` in
OnBytes/Model/Head.lean) claim. Which digits spell which number, low digit first:
  0 to 7 V; 8 to 43 the carries c_1 to c_6, six digits each, each plus 2^47;
  44 to 48 sigma = 2 D44 + D45 + 2^8 D46 + 2^16 D47 + 2^24 D48;
  49 to 52 l1; 53 to 56 h1; 57 to 59 Rlo; 60 to 62 Rhi; 63 to 65 p1; 66 to 69 rr; 70 to 73 rq. -/
structure RowAH where
  /-- the digits; a cell holds its digit minus 128 -/
  Dg : Array Aff
  /-- V, the sum of the squares -/
  V : Aff
  /-- the carries c_0 to c_7: c_0 is 0, c_7 is digit 7 of V, and c_1 to c_6 are here without their
  2^47 -/
  c : Array Aff
  /-- the lowest bit of sigma -/
  s0 : Aff
  /-- sigma, the integer square root -/
  sig : Aff
  /-- V + eps - sigma^2 -/
  l1 : Aff
  /-- 2 sigma - l1 -/
  h1 : Aff
  /-- the low 24 bits of the reciprocal R -/
  Rlo : Aff
  /-- the bits of R from bit 24 on -/
  Rhi : Aff
  /-- the reciprocal -/
  R : Aff
  /-- Rhi sigma -/
  p1 : Aff
  /-- the remainder of the division -/
  rr : Aff
  /-- sigma - 1 - rr -/
  rq : Aff

/-- The number that the n digits from digit a on represent, low digit first. -/
def digits (Dg : Array Aff) (a n : Nat) : Aff :=
  (List.range n).foldl (fun s j => Aff.addMul s (Dg.getD (a + j) {}) (ofNat (256 ^ j))) {}

/-- The norm's row with four limbs, read in the table of hr under the weights named P. -/
def rowAt (R : Run) (P : String) : SubM RowAH := do
  let t ← tabAt R ("hr@" ++ P)
  let mut Dg : Array Aff := #[]
  for j in [0:74] do
    Dg := Dg.push ((← U3at R t j) + Aff.ofConst (ofNat 128))
  let D := fun j => Dg.getD j {}
  let dig := digits Dg
  let Rlo := dig 57 3
  let Rhi := dig 60 3
  pure {
    Dg := Dg
    V := dig 0 8
    c := (Array.range 8).map fun s =>
      if s == 0 then {} else if s == 7 then D 7
      else dig (8 + 6 * (s - 1)) 6 - Aff.ofConst (ofNat (2 ^ 47))
    s0 := D 45
    sig := Aff.scale (D 44) (ofNat 2) + D 45 + Aff.scale (D 46) (ofNat 256) +
      Aff.scale (D 47) (ofNat 65536) + Aff.scale (D 48) (ofNat (2 ^ 24))
    l1 := dig 49 4
    h1 := dig 53 4
    Rlo := Rlo
    Rhi := Rhi
    R := Rlo + Aff.scale Rhi (ofNat (2 ^ 24))
    p1 := dig 63 3
    rr := dig 66 4
    rq := dig 70 4 }

/-- The norm's row with five limbs, read in the table of hr under the weights named P. -/
def row5At (R : Run) (P : String) : SubM (Row5 Aff) := do
  let t ← tabAt R ("hr@" ++ P)
  let mut cells : Array Aff := #[]
  for j in [0:99] do
    cells := cells.push (← U3at R t j)
  pure (row5 fun j => cells.getD j {})

/-- One of the six hidden numbers of the positions with a cost (i = 0 to 5: c, b, u, k, z, zs), read
in the table of hr under the weights named P, "phiC" or "rhoC": the sum over the positions of weight
times number. A cell holds its digit minus 128, so every digit gets 128 times wsum, the sum of the
weights. -/
def gapAt (R : Run) (P : String) (i : Nat) (wsum : E) : SubM Aff := do
  let t ← tabAt R ("hr@" ++ P)
  let g := ledG.getD i (0, 0)
  let o := ledNR R.h.XL + g.1
  let mut s : Aff := {}
  for l in [0:g.2] do
    s := Aff.addMul s ((← U3at R t (o + l)) + Aff.ofConst (scaleNat wsum 128)) (ofNat (256 ^ l))
  pure s

/-- The difference between a value of the table of exponentials and its cells read at radix 256:
128 for each digit, and 1. -/
def offE : Nat := 128 * ((2 ^ (8 * exc) - 1) / 255) + 1

/-- The sum of the weights phiC: see `costWeights`. -/
def ercOf (R : Run) : E := (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.1

/-- The position coordinates of the key point of the call that has the segment sn. -/
def ztSeg (R : Run) (sn : String) : SubM (Array E) := do
  pure (ztOf R.h R.L R.x.g1 (← getAs "internal-segment" (callNo R.L sn)))

/-- The middle digit of the margins under the weights of segment sn, with its offset at the real
places, whose weights add up to wR. -/
def middleDigit (R : Run) (sn : String) (wR : E) : SubM Aff := do
  pure (Aff.ofConst (mulE o2 wR) + (← Sl R sn R.L.oD1 2 R.L.JV))

/-- The low digit of the margins under the weights of segment sn, with its offset at the real
places, whose weights add up to wR. -/
def lowDigit (R : Run) (sn : String) (wR : E) : SubM Aff := do
  pure (Aff.ofConst (mulE o1 wR) + (← Sl R sn R.L.oD2 1 R.L.JV))

/-- The part of a call's key vector at the call's key point that belongs to segment sn, as a form.

NF, NFH: the two keys of the final norm's rounding. HD2, HD1: the low and the middle digit of a
margin, read in their cells. HD0: the top digit has no cell; its key is the margin less the two
lower digits, times the inverse of 2^(sh + 15). Of the margin's parts, the one in the logits is the
first slot of the last token sumcheck, which holds it times 2^-lPd; c and b are read in the ledger
under phiC. HE0, HE1: the key is the middle digit plus 2^16 times the table value ex. ROW: the
ledger's digits, each times its multiplier. CNF: the clamp's key, packed at radix 2^28.

The offsets of d1 and d2 and the margin's parts carry weight at the real places only; the cells
carry weight at every place. The cells of ex hold ex - 1 in digits minus 128 at every place, real or
not, so the offset of ex has the weight of all the segment's columns. At a place that is not real
the keys are meant to be in their tables only if d1 = d2 = 0 and ex = EX[0]. -/
def LINE (R : Run) (sn : String) : SubM Aff := do
  let h := R.h
  let L := R.L
  let ew ← ewOf R sn
  let w := sumE ew
  if sn == "NF" then
    pure (Aff.ofConst (mulE w (subE (pw (h.KF - 1)) (mulE (pw 16) o2))) -
      Aff.scale (← Sl R sn L.oAw 2 h.d) (pw h.KF) - Aff.scale (← Sl R sn L.oRa 2 h.d) (pw 16))
  else if sn == "NFH" then
    pure (Aff.scale (Aff.ofConst (mulE o2 w) + (← Sl R sn L.oRa 2 h.d)) (pw (32 - h.KF)))
  else if sn == "HD0" || sn == "HD1" || sn == "HD2" then
    let wx := wxOf R ew
    let wR := mulE wx (onSum R (← ztSeg R sn))
    if sn == "HD1" then middleDigit R sn wR
    else if sn == "HD2" then lowDigit R sn wR
    else
      let et := eqTab (ztOf h L R.x.g1 R.x.qH)
      let iw := invE (pw (h.digSh + 15))
      let ERC := ercOf R
      let cost := (← gapAt R "phiC" 0 ERC) + Aff.scale (← gapAt R "phiC" 1 ERC) (ofNat bigH)
      pure (Aff.scale
        (Aff.scale (S_ R.x.tH.sCl) (pw h.lPd) + Aff.scale cost wx -
          Aff.ofConst (addE (placeTermH R ew et) (publicTermH ew et)) -
          Aff.scale (← middleDigit R sn wR) (pw h.digSh) - (← lowDigit R sn wR)) iw)
  else if sn == "HE0" || sn == "HE1" then
    let v0 := firstEntry L sn
    let wx := sumE (ew.extract 0 (h.V - v0))
    pure (Aff.ofConst (mulE (mulE o2 wx) (onSum R (← ztSeg R sn))) +
      (← Sl R sn (L.oD1 + v0) 2 L.JV) +
      Aff.scale (Aff.ofConst (scaleNat w offE) + (← Sl R sn (L.oE + v0) exc L.JV)) (pw 16))
  else if sn == "ROW" then
    let t ← tabAt R "hr@zt_ROW"
    let mut a : Aff := {}
    for idx in [0:ledNRH h.XL] do
      let mu := if idx < ledNR h.XL then ledMu h.XL idx else 1
      a := Aff.addMul a ((← U3at R t idx) + Aff.ofConst (ofNat 128))
        (scaleNat (ew.getD idx zeroE) mu)
    pure a
  else if sn == "CNF" then
    let t ← tabAt R "hd@zt_FC"
    let mut b : Aff := {}
    for x in [0:h.d] do
      b := Aff.addMul b (← sh2 R t x) (ew.getD x zeroE)
    pure ((← Sl R sn L.oAw 2 h.d) + Aff.scale b (pw 28) +
      Aff.ofConst (mulE w (ofNat (2 ^ 15 + 2 ^ 39))))
  else refuse "internal-line"

/-- Marks the columns of one segment. A column gets 1 if it holds real places and 2 if its entry is
not an entry of the vocabulary. A column that two segments list is refused, and so is a column
beyond the call's last. -/
def markColumns (R : Run) (weighed : Array Nat) (g : Seg) : Option (Array Nat) :=
  let v0 := firstEntry R.L g.name
  (List.range g.n).foldlM
    (fun w x =>
      let p := g.pos.getD x 0
      if p < w.size && w.getD p 1 == 0 then
        some (w.set! p (if perEntry g.name && v0 + x ≥ R.h.V then 2 else 1))
      else none)
    weighed

/-- The form that stands for call number q's key vector at the call's key point: the padding key
times the weight of the columns that no segment lists, the first slot of the sumcheck of the
stream times the reciprocal if the call has the segment NF, and the segments' forms.

The padding is described twice: by its number in each tree (`pubOf`) and by its places, which are
taken here from the segments' lists of columns. Both descriptions come from these lists, so
comparing them shows no fault in a list or inside a form. laid[y] counts in tree y the keys of the
columns that no segment lists and of the columns whose entry is not an entry of the vocabulary. A
column whose entry is not in the vocabulary has a form, but its cells must give the call's padding
key: 0, or row 0 of the table of exponentials. Returns the form and the new counts. -/
def keyForm (R : Run) (q : Nat) (laid : Array Nat) : SubM (Aff × Array Nat) := do
  let c := R.L.calls.getD q default
  let e := eqTab (zjOf R.L R.x.g1 q)
  let mut lines : Aff := {}
  let mut weighed := Array.replicate c.J 0
  for g in c.segs do
    lines := lines + (← LINE R g.name)
    weighed ← getAs "internal-h-join-place" (markColumns R weighed g)
  let fs := R.x.g1.shape
  let mut padW := zeroE
  let mut laid := laid
  for j in [0:c.J] do
    if weighed.getD j 0 == 0 then padW := addE padW (e.getD j zeroE)
    if weighed.getD j 0 != 1 then
      let y := fs.first.getD q 0 + j / 2 ^ (fs.dT - R.h.lt)
      mustAs "internal-h-join-place" (y < laid.size)
      laid := laid.modify y (· + R.h.T)
  let k := R.L.cl.getD q default
  let v := Aff.ofConst (scaleE (k.tauAt k.t0) padW)
  let v := if q == R.x.qN then v + S_ R.x.tN.sCl else v
  pure (v + lines, laid)

end OnBytes.Model.Head
