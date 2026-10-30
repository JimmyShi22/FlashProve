-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionClaimsA.lean: how the claims of the attention sub-proof read its tables, and
the claims on the calls of kinds KR and KFD.

In part 6 the check of the attention sub-proof (OnBytes/Model/Attention.lean) lists linear claims.
A claim says that an affine form in hidden values is 0. The hidden values of this file are of two
kinds: a value that the prover sent under a mask, which is named by its slot, and an entry of a
table. All tables are stored one after the other in one committed array.
OnBytes/Model/AttentionHeard.lean explains the terms.

The file has two parts: the forms on the tables, and the claims on the calls of kinds KR and KFD.
Each begins with its own account.

The C++ source is verifier/src/vf_attention_check.h, in the list of claims of
AttentionSubProof::run, whose comments number these claims 3 and 4. The page on the attention
sub-proof is docs/format/11-3-attention-segment.md (section 11.3 of the format). The order of the
claims matters: the engine of the sub-proofs (OnBytes/Model/Hide.lean) multiplies a claim by a power
of the batching element, and the exponent is the claim's number in the list.

Main definitions: u3at, weighted, plane, shV, xl, overG, readDenominator, readMaximum, readIndexBit,
readHead, readGroup, linPlanes, claim3, claim4.

Names of refusals: see the section The names of the refusals of OnBytes/Model/Attention.lean. Of
this file's two names the C++ verifier puts the sub-proof's prefix before internal-a-table-index
only.

What this file does not claim. It holds no theorem. It receives no message and draws nothing. Its
tests are on public numbers only. It does not decide whether a claim holds: SubM.lin hands the
claim to the engine, which adds all claims of a sub-proof into one equation.
-/
import OnBytes.Model.AttentionHeard

namespace OnBytes.Attention

open OnBytes.Model

/-! ## Forms on the tables

The first part of this file defines the forms that stand for values of the committed matrices at the
points of the check. Each form is a sum of entries of one table with public coefficients. The other
claims of the sub-proof (OnBytes/Model/AttentionClaimsB.lean) use the same forms.
-/

/-- The element -1. -/
def minusOne : E := subE zeroE oneE

/-- Entry i of the table that begins at t. It refuses if no table begins at t or if the table has no
entry i. The forms of this file and of OnBytes/Model/AttentionClaimsB.lean, and the lookup's claims
on the planes in OnBytes/Model/Attention.lean, read the tables only through this function. So they
read no entry outside a table: they use only entries that the reads of the smallness test cover
(objectsF in OnBytes/Model/Tail.lean). -/
def u3at (h : Heard) (t i : Nat) : SubM Aff := do
  mustAs "internal-a-table-index" (decide (i < (h.t.tabLen.lookup t).getD 0))
  uEnt h.iU3 (t + i)

/-- The sum over i below n of w[i] times the form f i. The forms are made in the order of i. -/
def weighted (n : Nat) (w : Array E) (f : Nat → SubM Aff) : SubM Aff :=
  (List.range n).foldlM (fun s i => do
    let x ← f i
    pure (Aff.addMul s x (w.getD i zeroE))) (Aff.ofConst zeroE)

/-- The powers 256^0 to 256^(n - 1): the weights of the limbs of a number that is stored in n
limbs to the radix 256. The callers have n at most 4. -/
def limbWeights (n : Nat) : Array E := (Array.range n).map fun l => ofNat (256 ^ l)

/-- Plane x of the matrix `as` for the pair (lam, a), at the point z. An entry of the table that
begins at t is a sum over 2^lmS neighbouring places, weighted by the last lmS coordinates of the
point. So the form reads the coordinates before them. isD is true if the point is one on the places
of the diagonal tiles. Their cells come after those of the tiles below the diagonal. A plane of one
pair has 2^nD places on the diagonal tiles and 2^nM places below the diagonal. -/
def plane (h : Heard) (t x lam a : Nat) (z : Array E) (isD : Bool) : SubM Aff :=
  let S := h.S
  let nb := if isD then S.nD else S.nM
  let first := (if isD then (5 * S.Lam * S.HA) <<< S.nM else 0) +
    (((x * S.Lam + lam) * S.HA + a) <<< nb)
  let eh := eqTab (z.extract 0 (nb - S.cf.lmS))
  weighted eh.size eh fun hi => u3at h t ((first >>> S.cf.lmS) + hi)

/-- A number of a tensor that the matrix ah stores in nl limbs, for layer lam and feature j. The
tensor begins at feature off, and each limb of a layer has J features. The table that begins at t
has one entry for each feature. -/
def shV (h : Heard) (t off nl J lam j : Nat) : SubM Aff :=
  weighted nl (limbWeights nl) fun l => u3at h t (off + (l * h.S.Lam + lam) * J + j)

/-- The tensor X for layer lam and head hd, at the point zc on the features of one head. hd is a
query head, or a head of keys and values, as the tensor has them. An entry of the table that begins
at t is a sum over a block of 2^ls neighbouring features, weighted by the last ls coordinates of the
point. So the form reads the first ldh - ls coordinates of zc. It refuses if zc, cut to its first
ldh coordinates, has fewer than ls, if the number dh of a head's features is 0 or does not divide
the tensor's features, or if the tensor has no head hd. -/
def xl (h : Heard) (t : Nat) (X : TenAt) (lam hd : Nat) (zc : Array E) : SubM Aff := do
  let S := h.S
  let .ok cut := cutLast (zc.extract 0 S.cf.ldh) S.ls | refuse "plan-tensor-layout"
  let ec := eqTab cut.1
  let .ok j0 := headFeat X hd S.dh | refuse "plan-tensor-layout"
  weighted ec.size ec fun ch =>
    weighted X.nl (limbWeights X.nl) fun l => u3at h t (tenCell X l lam j0 / 2 ^ S.ls + ch)

/-- The sum over the heads g of keys and values of eq(zg, g) times the form f g. It reads the first
lgk coordinates of zg. -/
def overG (h : Heard) (zg : Array E) (f : Nat → SubM Aff) : SubM Aff :=
  weighted h.S.G (eqTab (zg.extract 0 h.S.cf.lgk)) f

/-- The denominator of pair (lam, a), read in the table that begins at t and summed over the heads g
of keys and values with the weights eq(zg, g). The matrix ah stores it in four limbs. -/
def readDenominator (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat) : SubM Aff :=
  overG h zg fun g => shV h t h.S.oZr 4 h.S.cf.H lam (g * h.S.HA + a)

/-- The row maximum of pair (lam, a), read in the table that begins at t and summed over the heads g
of keys and values with the weights eq(zg, g). The matrix ah stores it in four limbs. -/
def readMaximum (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat) : SubM Aff :=
  overG h zg fun g => shV h t h.S.oMr 4 h.S.cf.H lam (g * h.S.HA + a)

/-- Bit k of the index of pair (lam, a), read in the table that begins at t and summed over the
heads g of keys and values with the weights eq(zg, g). The matrix ah stores the lt bits of a layer
one after the other, each with one feature for each of the H query heads. -/
def readIndexBit (h : Heard) (t : Nat) (zg : Array E) (lam a k : Nat) : SubM Aff :=
  overG h zg fun g =>
    shV h t h.S.oIb 1 (h.S.cf.lt * h.S.cf.H) lam (k * h.S.cf.H + g * h.S.HA + a)

/-- A tensor X that has features for each query head, at pair (lam, a): read in the table that
begins at t, at the point zc on the features of one head, and summed over the heads g of keys and
values with the weights eq(zg, g). -/
def readHead (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam a : Nat) : SubM Aff :=
  overG h zg fun g => xl h t X lam (g * h.S.HA + a) zc

/-- A tensor X that has features for each head of keys and values, at layer lam: read in the table
that begins at t, at the point zc on the features of one head, and summed over these heads g with
the weights eq(zg, g). -/
def readGroup (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam : Nat) : SubM Aff :=
  overG h zg fun g => xl h t X lam g zc

/-- The form start minus the sum over the pieces w of w.wp times the form f w. The forms are made
in the order of the pieces. -/
def lessPieces (start : Aff) (pw : Array PW) (f : PW → SubM Aff) : SubM Aff :=
  pw.foldlM (fun s w => do
    let x ← f w
    pure (Aff.addMul s x (mulE minusOne w.wp))) start

/-- Adds one claim for each plane of a plane claim: the value sent for the plane equals the sum over
the unit's pieces of the piece's weight times the plane at the unit's inner point. -/
def linPlanes (h : Heard) (pc : PlaneClaim) : SubM Unit :=
  (List.range pc.np).forM fun x => do
    let f ← lessPieces (Aff.slot (pc.s0 + x)) pc.pw fun w =>
      plane h h.t.tA x w.lam w.a pc.z pc.isD
    SubM.lin f

/-! ## Claim 3: the calls of kind KR

The second part lists the claims on the calls of two kinds. A call of kind KR looks up the two bytes
of a gap's remainder together with a flag. A call of kind KFD is the lookup of the exponential. Its
key packs three numbers: the gap minus that remainder, the flag, and the softmax weight. For each
call the claims tie the values that were sent to the tables. The values sent then make up the call's
key form. This file sets the key forms. The join is added later, in OnBytes/Model/Attention.lean.
-/

/-- What one unit adds to the key form of a call of kind KR. The three values sent are R0 and R1,
for the two bytes of the gap's remainder, and FL, for the flag. With LW the sum of the pieces'
weights the unit adds (R0 + 128 LW) + 2^20 (R1 + 128 LW) + 2^40 FL. -/
def keyKR (pc : PlaneClaim) : Aff :=
  let l128 := Aff.ofConst (scaleNat (sumW pc.pw) 128)
  (Aff.slot pc.s0 + l128) + Aff.scale (Aff.slot (pc.s0 + 1) + l128) (ofNat (2 ^ 20)) +
    Aff.scale (Aff.slot (pc.s0 + 2)) (ofNat (2 ^ 40))

/-- Adds the claims of the units of call q, a call of kind KR, in the order in which their values
were sent. Returns the call's key form. The padding has no term in it: the padding key of a call of
kind KR must be 0, which paddingLaid in OnBytes/Model/Attention.lean tests. -/
def callKR (h : Heard) (q : Nat) : SubM Aff :=
  h.planes.foldlM (fun v pc =>
    if pc.call == q then do
      linPlanes h pc
      pure (v + keyKR pc)
    else pure v) (Aff.ofConst zeroE)

/-- Claim 3. For each call of kind KR, in list order, it adds the claims of the call's units and
sets the call's key form. -/
def claim3 (h : Heard) (j : Joins) : SubM Joins :=
  h.S.calls.toList.zipIdx.foldlM (fun j x =>
    if x.1.kind == .kr then do
      let v ← callKR h x.2
      pure (j.set x.2 v)
    else pure j) j

/-! ## Claim 4: the calls of kind KFD (its account stands with claim 3's) -/

/-- The sum of the weights of all pieces of call c at its key point zk. -/
def wall (c : ACall) (zk : Array E) : E :=
  c.pcs.foldl (fun s pc => addE s (eqAt (zk.extract 0 (c.call.n - pc.b)) (pc.off >>> pc.b))) zeroE

/-- The padding's term in the key form of call c. Its weight is 1 minus the sum of the pieces'
weights (wall). Its key is row t0 of the call's table, from which the lookup takes the padding key
too. -/
def padTerm (c : ACall) (zk : Array E) : Aff :=
  Aff.ofConst (scaleE (c.call.tauAt c.call.t0) (subE oneE (wall c zk)))

/-- What one unit adds to the key form of a call of kind KFD. The seven values sent are R0, R1 (the
two bytes of the gap's remainder), FL (the flag), E0, E1 (the two bytes of the softmax weight), MS
(the row maximum) and SS (the score). LW is the sum of the pieces' weights. The unit adds
DP - (R0 + 128 LW) - 256 (R1 + 128 LW) + 2^32 FL + 2^33 (E0 + 128 LW + 256 E1).
Below the diagonal DP is MS - SS + C LW ones(zs). On the diagonal it is
MS - SS + Om LW (1 - LE(zj, zi)). C and Om are the numbers d.C and d.Om of the call's shift. ones
and LE are the functions onesOf and leOf of OnBytes/Model/AttentionShape.lean. -/
def keyKFD (d : ShD) (k : Score) : Aff :=
  let s := k.s0
  let lw := sumW k.pw
  let l128 := Aff.ofConst (scaleNat lw 128)
  let dp := Aff.slot (s + 5) - Aff.slot (s + 6) +
    Aff.ofConst (if k.seg == Seg.fm then mulE (scaleNat lw d.C) (onesOf k.zs)
      else mulE (scaleNat lw d.Om) (subE oneE (leOf k.zj k.zi)))
  dp - (Aff.slot s + l128) - Aff.scale (Aff.slot (s + 1) + l128) (ofNat 256) +
    Aff.scale (Aff.slot (s + 2)) (ofNat (2 ^ 32)) +
    Aff.scale (Aff.slot (s + 3) + l128 + Aff.scale (Aff.slot (s + 4)) (ofNat 256)) (ofNat (2 ^ 33))

/-- Adds the two claims on the end values of piece number b of a unit's sumcheck. The first end
value is the query of the piece's pair. The second is the key of the pair's layer. Both are summed
over the heads of keys and values and read at the sumcheck's point: rc is its last ldh
coordinates. -/
def endValues (h : Heard) (k : Score) (tb : ScoreTables) (rc : Array E) (b : Nat) (w : PW) :
    SubM Unit := do
  let q ← readHead h tb.tQ h.S.atQ k.sc.r rc w.lam w.a
  SubM.lin (sc3A k.sc b - q)
  let kx ← readGroup h tb.tK h.S.atK k.sc.r rc w.lam
  SubM.lin (sc3B k.sc b - kx)

/-- Adds the claims of one unit of a call of kind KFD. i is the unit's number in the list of scores.
The claims are, in this order: the five planes; the row maximum; the row of the unit's sumcheck;
the two end values of each piece. It refuses if the unit's tables or its plane claim are missing
from h. -/
def unitKFD (h : Heard) (i : Nat) (k : Score) : SubM Unit := do
  let S := h.S
  let tb ← SubM.get h.t.score[i]?
  let pc ← SubM.get h.planes[k.claim]?
  linPlanes h pc
  let f ← lessPieces (Aff.slot (k.s0 + 5)) k.pw fun w => readMaximum h tb.tM k.zg w.lam w.a
  SubM.lin f
  SubM.lin k.sc.rowU
  let rc := k.sc.r.extract (k.sc.r.size - S.cf.ldh) k.sc.r.size
  k.pw.toList.zipIdx.forM fun x => endValues h k tb rc x.2 x.1

/-- Adds the claims of the units of call c, which has the number q, in the order in which their
values were sent. Returns the call's key form: the padding's term at the key point of call q, and
what each unit adds. -/
def callKFD (h : Heard) (q : Nat) (c : ACall) : SubM Aff :=
  let d := h.S.shd c.sh
  h.scores.toList.zipIdx.foldlM (fun v x =>
    if x.1.call == q then do
      unitKFD h x.2 x.1
      pure (v + keyKFD d x.1)
    else pure v) (padTerm c (h.g.zk.getD q #[]))

/-- Claim 4. For each call of kind KFD, in list order, it adds the claims of the call's units and
sets the call's key form. -/
def claim4 (h : Heard) (j : Joins) : SubM Joins :=
  h.S.calls.toList.zipIdx.foldlM (fun j x =>
    if x.1.kind == .kfd then do
      let v ← callKFD h x.2 x.1
      pure (j.set x.2 v)
    else pure j) j

/-- The names that this file passes to its tests. unitKFD takes its tables and its plane claim with
SubM.get, which has no name: if one is missing, it fails under the general name refused (unnamed in
OnBytes/Iop/Ground.lean). uEnt, which u3at calls, refuses under internal-L-row (lookNames). -/
def claimsANames : List String := ["internal-a-table-index", "plan-tensor-layout"]

end OnBytes.Attention
