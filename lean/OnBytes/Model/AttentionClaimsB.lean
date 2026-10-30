-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionClaimsB.lean: the claims of the attention sub-proof on the division, the
value product, the row maximum and the bits of its index.

Part 6 of the check of the attention sub-proof (OnBytes/Model/Attention.lean) lists linear claims. A
claim says that an affine form in hidden values is 0. This file lists four groups of claims,
numbered 5 to 8 as in AttentionSubProof::run of vf_attention_check.h. The page on the sub-proof is
docs/format/11-3-attention-segment.md (section 11.3 of the format).
OnBytes/Model/AttentionHeard.lean explains the terms.
  Claim 5: the division. The values sent for the denominator, for the high parts of the two
           remainders and for the bits of the index are what the tables hold. The value ZO is the
           product of denominator and output. Claim 5 also sets key forms (see the first section).
  Claim 6: the value product. The accumulator is the sum of the softmax weights times the values,
           and the denominator is the sum of the softmax weights. A drawn element gam puts the two
           in one sum.
  Claim 7: the score at the index is the row maximum.
  Claim 8: the cells of the index are bits.

The order of the claims matters: each claim gets its own power of the batching element.

Main definitions: claim5, claim6, claim7, claim8.

What this file does not claim. It holds no theorem. It receives no message and draws nothing: the
claims read only what the earlier parts of the check have stored (Heard). The row of a sumcheck was
made when the sumcheck's messages were received, and here it is only added to the claims. The file
makes no test of its own. The tests are those of the forms of OnBytes/Model/AttentionClaimsA.lean,
on public numbers. Whether the claims hold is not decided here. All claims of the sub-proof are
added into one equation, which is handed to the request's chain (OnBytes/Model/Trees.lean).
-/
import OnBytes.Model.AttentionClaimsA

namespace OnBytes.Attention

open OnBytes.Model

/-! ## Claim 5: the key forms

Claim 5 sets the key forms of the calls of kinds R16 and WH. A key form is a definition and not a
claim. The one claim on all key forms, the join, is added in OnBytes/Model/Attention.lean between
claim 5 and claim 6.
-/

/-- Where the high part of the first remainder is in the matrix ao. -/
def atRh (S : Shape) : TenAt := { off := S.oRh, nl := 1, cnt := S.Lam, J := S.dq }

/-- Where the high part of the second remainder is in the matrix ao. -/
def atRhp (S : Shape) : TenAt := { off := S.oRhp, nl := 1, cnt := S.Lam, J := S.dq }

/-- The form REM = 2 ACC + ZC - 2 ZO on the values sent. -/
def remForm (d : Divide) : Aff :=
  Aff.scale (Aff.slot d.sACC) (ofNat 2) + Aff.slot d.sZC - Aff.scale (Aff.slot d.sZO) (ofNat 2)

/-- The index as a form on the values IB_k sent for its lt bits: the sum of 2^k IB_k. -/
def indexForm (d : Divide) (lt : Nat) : Aff :=
  (List.range lt).foldl (fun s k => Aff.addMul s (Aff.slot (d.sIB + k)) (ofNat (2 ^ k)))
    (Aff.ofConst zeroE)

/-- The term of segment wl in a key form. With LW the sum of the pieces' weights it is
(1 - zsl) (REM - 2^16 (RH + 128 LW)) + zsl (2 ZC - LW - REM - 2^16 (RHP + 128 LW)). -/
def keyWL (d : Divide) : Aff :=
  let lw := sumW d.pwW
  let l128 := Aff.ofConst (scaleNat lw 128)
  let rem := remForm d
  let tw0 := rem - Aff.scale (Aff.slot d.sRH + l128) (ofNat 65536)
  let tw1 := Aff.scale (Aff.slot d.sZC) (ofNat 2) - Aff.ofConst lw - rem -
    Aff.scale (Aff.slot d.sRHP + l128) (ofNat 65536)
  Aff.scale tw0 (subE oneE d.zsl) + Aff.scale tw1 d.zsl

/-- The term of segment ix in a key form. With LW the sum of the pieces' weights and id the
extension of the map that sends a token to its number, it is
2^(16 - lt) (LW id(ziX) - the sum of 2^k IB_k). The shape has lt at most 16 (af-shape-tiles,
OnBytes/Model/AttentionShape.lean). -/
def keyIX (S : Shape) (d : Divide) : Aff :=
  Aff.scale (Aff.ofConst (mulE (sumW d.pwX) (idOf d.ziX)) - indexForm d S.cf.lt)
    (ofNat (2 ^ (16 - S.cf.lt)))

/-- The key form of the call of kind WH. With LW the sum of the pieces' weights it is
(RH2 + 128 LW) + 2^20 (RHP2 + 128 LW). -/
def keyWH (d : Divide) : Aff :=
  let l128 := Aff.ofConst (scaleNat (sumW d.pwH) 128)
  (Aff.slot d.s5h + l128) + Aff.scale (Aff.slot (d.s5h + 1) + l128) (ofNat (2 ^ 20))

/-- Sets the key form of every call of kind R16, in list order: the term of wl if the call holds
that segment, plus the term of ix if it holds that one. -/
def joinR16 (S : Shape) (d : Divide) (j : Joins) : Joins :=
  let tWL := keyWL d
  let tIX := keyIX S d
  S.calls.toList.zipIdx.foldl (fun j x =>
    if x.1.kind == .r16 then
      let v := Aff.ofConst zeroE
      let v := if x.1.holds .wl then v + tWL else v
      let v := if x.1.holds .ix then v + tIX else v
      j.set x.2 v
    else j) j

/-! ## Claim 5 -/

/-- Adds the two claims on the end values of pair number b of the sumcheck for denominator times
output. w is piece number b of segment wl. The first end value is the denominator. The second is the
output at the point zcW on the features of a head. Both are read at the sumcheck's point. -/
def endValuesE (h : Heard) (b : Nat) (w : PW) : SubM Unit := do
  let d := h.d
  let z ← readDenominator h h.t.hE d.scE.r w.lam w.a
  SubM.lin (sc3A d.scE b - z)
  let o ← readHead h h.t.qO h.S.atO d.scE.r d.zcW w.lam w.a
  SubM.lin (sc3B d.scE b - o)

/-- Claim 5. One claim for each of ZC, RH, RHP, IB_0 and so on, RH2 and RHP2, in the order of
sending: the value is the sum over its segment's pieces of the piece's weight times a reading of a
table. Then the row of the sumcheck for denominator times output, and the claims on its end values.
Returns j with the key forms of the calls of kinds R16 and WH set. pwW has an entry for every pair
b, so the default in getD is never used: divide refuses otherwise (internal-af-calls). -/
def claim5 (h : Heard) (j : Joins) : SubM Joins := do
  let S := h.S
  let d := h.d
  let t := h.t
  let zc ← lessPieces (Aff.slot d.sZC) d.pwW fun w => readDenominator h t.hW d.zgW w.lam w.a
  let rh ← lessPieces (Aff.slot d.sRH) d.pwW fun w =>
    readHead h t.tO (atRh S) d.zgW d.zcW w.lam w.a
  let rhp ← lessPieces (Aff.slot d.sRHP) d.pwW fun w =>
    readHead h t.tO (atRhp S) d.zgW d.zcW w.lam w.a
  let r2 ← lessPieces (Aff.slot d.s5h) d.pwH fun w =>
    readHead h t.tO (atRh S) d.zgH d.zcH w.lam w.a
  let r2p ← lessPieces (Aff.slot (d.s5h + 1)) d.pwH fun w =>
    readHead h t.tO (atRhp S) d.zgH d.zcH w.lam w.a
  SubM.lin zc
  SubM.lin rh
  SubM.lin rhp
  for k in List.range S.cf.lt do
    let f ← lessPieces (Aff.slot (d.sIB + k)) d.pwX fun w => readIndexBit h t.hX d.zgX w.lam w.a k
    SubM.lin f
  SubM.lin r2
  SubM.lin r2p
  SubM.lin d.scE.rowU
  for b in List.range S.NP do
    endValuesE h b (d.pwW.getD b default)
  pure ((joinR16 S d j).set d.qWH (keyWH d))

/-! ## Claim 6 -/

/-- The claims of one of the two sumchecks of the value product: its row, then two claims for each
pair. The first end value is the softmax weight, which the matrix `as` holds in planes 3 and 4. It
is plane 3 plus 128 plus 256 times plane 4, read in the table that begins at tS at the point pt. The
second end value is gam plus the value, read in the table that begins at tV. isD is true for the
sumcheck on the diagonal tiles. Pair number b is the pair of piece number b of segment wl, which
has one piece for each pair. -/
def valueProduct (h : Heard) (sc : Sc3) (tS : Nat) (pt : Array E) (isD : Bool) (tV : Nat) :
    SubM Unit := do
  SubM.lin sc.rowU
  for b in List.range h.S.NP do
    let w := h.d.pwW.getD b default
    let p3 ← plane h tS 3 w.lam w.a pt isD
    let p4 ← plane h tS 4 w.lam w.a pt isD
    SubM.lin (sc3A sc b - (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256)))
    let v ← readGroup h tV h.S.atV sc.r h.d.zcW w.lam
    SubM.lin (sc3B sc b - (Aff.ofConst h.d.gam + v))

/-- Claim 6. The two sums sent add up to ACC + gam ZC. Then the claims of the sumcheck below the
diagonal, which starts from the first sum, and those of the sumcheck on the diagonal, which starts
from the second. -/
def claim6 (h : Heard) : SubM Unit := do
  let d := h.d
  SubM.lin (Aff.slot d.sCl + Aff.slot (d.sCl + 1) - Aff.slot d.sACC -
    Aff.scale (Aff.slot d.sZC) d.gam)
  valueProduct h d.vpm h.t.tVM h.t.ptM false h.t.qVM
  valueProduct h d.vpd h.t.tVD h.t.ptD true h.t.qVD

/-! ## Claim 7 -/

/-- Claim 7. For each pair, the value sent for the row maximum is what the table holds. Then the row
of the sumcheck for the score at the index, and for each pair the claim that its first end value is
the query. Its second end values are the start of the sumcheck for the key at the index. Then come
that sumcheck's row, for each layer the claim that an end value is the key, and for each pair and
each k the claim that an end value is bit k of the index. -/
def claim7 (h : Heard) : SubM Unit := do
  let S := h.S
  let x := h.x
  let t := h.t
  for b in List.range S.NP do
    let m ← readMaximum h t.hT x.tg (b / S.HA) (b % S.HA)
    SubM.lin (Aff.slot (x.sM6 + b) - m)
  SubM.lin x.scF.rowU
  for b in List.range S.NP do
    let q ← readHead h t.qF S.atQ (x.rg S) (x.rc S) (b / S.HA) (b % S.HA)
    SubM.lin (sc3A x.scF b - q)
  SubM.lin x.scd.rowU
  for lam in List.range S.Lam do
    let kx ← readGroup h t.qKx S.atK (x.pg S) (x.rc S) lam
    SubM.lin (Aff.slot (x.sKC + lam) - kx)
  for b in List.range S.NP do
    for k in List.range S.cf.lt do
      let bit ← readIndexBit h t.hPi (x.pg S) (b / S.HA) (b % S.HA) k
      SubM.lin (Aff.slot (x.sIb S b k) - bit)

/-! ## Claim 8 -/

/-- Claim 8. The row of the sumcheck for the bits, which starts from 0. Then two claims for each
pair: the second end value is the first minus 1, and the first is the sum over k < lt of eq(rk, k)
times bit k of the index. The point rk has four coordinates, so eq(rk, .) has 16 entries. Those from
lt on are not used. -/
def claim8 (h : Heard) : SubM Unit := do
  let S := h.S
  let x := h.x
  SubM.lin x.scH.rowU
  let ek := eqTab (x.rk S)
  for b in List.range S.NP do
    SubM.lin (sc3B x.scH b - sc3A x.scH b + Aff.ofConst oneE)
    let f ← (List.range S.cf.lt).foldlM (fun s k => do
      let bit ← readIndexBit h h.t.hR2 (x.rg2 S) (b / S.HA) (b % S.HA) k
      pure (Aff.addMul s bit (mulE minusOne (ek.getD k zeroE)))) (sc3A x.scH b)
    SubM.lin f

end OnBytes.Attention
