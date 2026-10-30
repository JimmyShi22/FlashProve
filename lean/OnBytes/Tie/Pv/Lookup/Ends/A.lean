-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/A.lean: the key vector, the table and the planes of counts of the lookup
of an attention sub-proof's own calls, written as terms over a reading of named cells.

Definitions, and two statements by rfl. "A", in the names and the docstrings, is this lookup. "The
port" is the Lean verifier under OnBytes/; the records are its own (Attention.Shape with its calls
and pieces, OnBytes/Model/AttentionShape.lean; Forest.Shape, OnBytes/Model/Forest.lean). cell :
NameA → R is a reading of the names, an argument; R is any commutative ring.
Main names:
  `NameA`: a name: cell (row r, column c) of matrix number M of the smallness test's list: the NAs
    parts of "as", then ah, ao, bA, qa.
  `A.asC`, `featC`, `mx`, `den`, `ib`, `ten`, `rh`, `rhp`: the cells by their meaning: plane x of
    "as" at a place; a feature's cell at a token; the row maximum and the denominator (four limbs
    each); an index bit; a tensor of qa (its limbs); the high parts of the two remainders.
  `A.score`, `wt`, `acc`: three functions of the cells that are no cells themselves: the score
    q . k, the softmax weight, the accumulator.
  `A.segKey S cell sh s lam a κ`: key number κ of the piece of segment s for the pair (lam, a), in a
    call of shift sh.
  `A.kvSel S h cell sel pad q X`: call q's key number X: the piece that holds X gives segKey, if sel
    admits its segment, else 0; where no piece holds X, the call's padding row, if pad, else 0.
  `A.kvA`: kvSel with all segments and the padding.
  `A.placeBA`: where bit j of the count of row u of the joint table lies in bA; none for a call's
    number from NC on, for j ≥ 32 and for u ≥ 2^d.
  `A.keyA`, `tabA`, `bitsA`: the joint key vector, the joint table, the planes as one vector.
  `A.keyA_eq`, `A.tabA_eq`: keyA and tabA are jointKey (at kvA) and jointTab of
    OnBytes/Tie/Pv/Lookup/Ends/Joint.lean at the shape h, by rfl.
Limits: nothing is assumed. tauN is a table row's 64-bit number as a natural number; kvSel, jointKey
and jointTab cast it into R. The tables of kinds KR, KFD and WH are written tables: their rows are
numbers below the port's prime, and the cast says what the port means in a ring of the port's
characteristic alone. No definition is marked noncomputable; the lines "#print axioms" at the end
print what five of them and keyA_eq depend on, beside three of the port's own declarations.
Does not say: that an accepted proof's keys are these; that the port computes these terms; that the
calls of h are those of S (S and h are two arguments, and nothing ties them); anything on a claim, a
round or a message.

-/
import OnBytes.Model.AttentionShape
import OnBytes.Tie.Pv.Lookup.Ends.Joint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends

open OnBytes.Model

/-- A name at A: cell (r, c) of matrix number M of the smallness test's list. -/
structure NameA where
  /-- the matrix's number in the list -/
  M : ℕ
  /-- the row of cells -/
  r : ℕ
  /-- the column -/
  c : ℕ
  deriving DecidableEq, Repr

namespace A

open OnBytes.Attention (Seg)

/-- The port's shape of an attention sub-proof. -/
abbrev Sh : Type := OnBytes.Attention.Shape

variable {R : Type} [CommRing R]

/-! ## The cells by their meaning -/

/-- Plane x of "as" for the pair (lam, a) at place π; isD: a place of the diagonal tiles. -/
def asC (S : Sh) (cell : NameA → R) (x lam a : ℕ) (isD : Bool) (π : ℕ) : R :=
  let nb := if isD then S.nD else S.nM
  let n := (if isD then 5 * S.Lam * S.HA * 2 ^ S.nM else 0) +
    ((x * S.Lam + lam) * S.HA + a) * 2 ^ nb + π
  let col := n / 2 ^ S.cf.lmS
  let w := S.kAs / S.cf.NAs
  cell ⟨col / w, n % 2 ^ S.cf.lmS, col % w⟩

/-- The cell of feature F at token i in matrix M, whose columns hold wc features each. -/
def featC (S : Sh) (cell : NameA → R) (M wc F i : ℕ) : R := cell ⟨M, F % wc * S.T + i, F / wc⟩

/-- The sum of f 0, .., f (n - 1). Written out as a fold, so that no term here leans on a proof of
Mathlib's: with Finset.sum the lines "#print axioms" of segKey, kvA and keyA would name
Classical.choice. -/
def sumN (n : ℕ) (f : ℕ → R) : R := (List.range n).foldl (fun s i => s + f i) 0

/-- A number in nl limbs to the radix 256. -/
def limbs (nl : ℕ) (f : ℕ → R) : R := sumN nl fun l => ((256 ^ l : ℕ) : R) * f l

/-- The row maximum of layer lam, query head hd, token i. -/
def mx (S : Sh) (cell : NameA → R) (lam hd i : ℕ) : R :=
  limbs 4 fun l => featC S cell S.cf.NAs S.cf.wcH (S.oMr + (l * S.Lam + lam) * S.cf.H + hd) i

/-- The denominator of layer lam, query head hd, token i. -/
def den (S : Sh) (cell : NameA → R) (lam hd i : ℕ) : R :=
  limbs 4 fun l => featC S cell S.cf.NAs S.cf.wcH (S.oZr + (l * S.Lam + lam) * S.cf.H + hd) i

/-- Bit k of the index of layer lam, query head hd, token i. -/
def ib (S : Sh) (cell : NameA → R) (lam k hd i : ℕ) : R :=
  featC S cell S.cf.NAs S.cf.wcH (S.oIb + lam * (S.cf.lt * S.cf.H) + (k * S.cf.H + hd)) i

/-- The tensor X of qa at layer lam, the tensor's own feature f, token i. -/
def ten (S : Sh) (cell : NameA → R) (X : TenAt) (lam f i : ℕ) : R :=
  limbs X.nl fun l => featC S cell (S.cf.NAs + 3) S.cf.wcQ (tenCell X l lam f) i

/-- The high part of the division's first remainder, at layer lam, feature f of q's, token i. -/
def rh (S : Sh) (cell : NameA → R) (lam f i : ℕ) : R :=
  featC S cell (S.cf.NAs + 1) S.cf.wcO (S.oRh + lam * S.dq + f) i

/-- The high part of the second remainder. -/
def rhp (S : Sh) (cell : NameA → R) (lam f i : ℕ) : R :=
  featC S cell (S.cf.NAs + 1) S.cf.wcO (S.oRhp + lam * S.dq + f) i

/-! ## Functions of the cells that are no cells themselves -/

/-- The score of query head hd at token ti with the key of head g at token tj. -/
def score (S : Sh) (cell : NameA → R) (lam hd g ti tj : ℕ) : R :=
  sumN S.dh fun n =>
    ten S cell S.atQ lam (hd * S.dh + n) ti * ten S cell S.atK lam (g * S.dh + n) tj

/-- The softmax weight at a place. -/
def wt (S : Sh) (cell : NameA → R) (lam a : ℕ) (isD : Bool) (π : ℕ) : R :=
  asC S cell 3 lam a isD π + 128 + 256 * asC S cell 4 lam a isD π

/-- The place (g | P | sg | i | j) below the diagonal. -/
def codeM (S : Sh) (g P sg i j : ℕ) : ℕ := (((g * S.hP + P) * S.nT + sg) * S.B + i) * S.B + j

/-- The place (g | I | i | j) on the diagonal tiles. -/
def codeD (S : Sh) (g I i j : ℕ) : ℕ := ((g * S.nT + I) * S.B + i) * S.B + j

/-- The accumulator of the pair (lam, a) at head g, token i, feature n of a head: the sum over the
places of the token's row of softmax weight times value. The empty tile slot is left out; the
places above the diagonal are left in. -/
def acc (S : Sh) (cell : NameA → R) (lam a g i n : ℕ) : R :=
  (sumN S.hP fun P => sumN (S.nT - 1) fun sg =>
    if (S.cover P sg).1 = i / S.B then
      sumN S.B fun j => wt S cell lam a false (codeM S g P sg (i % S.B) j) *
        ten S cell S.atV lam (g * S.dh + n) ((S.cover P sg).2 * S.B + j)
    else 0) +
  sumN S.B fun j => wt S cell lam a true (codeD S g (i / S.B) (i % S.B) j) *
    ten S cell S.atV lam (g * S.dh + n) (i / S.B * S.B + j)

/-! ## The keys -/

/-- The score's part of the gap at place κ of segment fm or fd: 0 at the empty tile slot. -/
def ssAt (S : Sh) (cell : NameA → R) (isD : Bool) (lam a κ : ℕ) : R :=
  let j := κ % S.B
  let i := κ / S.B % S.B
  if isD then
    let I := κ / (S.B * S.B) % S.nT
    let g := κ / (S.B * S.B * S.nT)
    score S cell lam (g * S.HA + a) g (I * S.B + i) (I * S.B + j)
  else
    let sg := κ / (S.B * S.B) % S.nT
    let P := κ / (S.B * S.B * S.nT) % S.hP
    let g := κ / (S.B * S.B * S.nT * S.hP)
    if sg = S.nT - 1 then 0
    else score S cell lam (g * S.HA + a) g ((S.cover P sg).1 * S.B + i) ((S.cover P sg).2 * S.B + j)

/-- The gap at place κ without the score: the row maximum; the constant C at the empty tile slot;
Om more above the diagonal. -/
def gapAt (S : Sh) (cell : NameA → R) (sh : ℕ) (isD : Bool) (lam a κ : ℕ) : R :=
  let j := κ % S.B
  let i := κ / S.B % S.B
  if isD then
    let I := κ / (S.B * S.B) % S.nT
    let g := κ / (S.B * S.B * S.nT)
    mx S cell lam (g * S.HA + a) (I * S.B + i) + (if i < j then ((S.shd sh).Om : R) else 0)
  else
    let sg := κ / (S.B * S.B) % S.nT
    let P := κ / (S.B * S.B * S.nT) % S.hP
    let g := κ / (S.B * S.B * S.nT * S.hP)
    if sg = S.nT - 1 then ((S.shd sh).C : R)
    else mx S cell lam (g * S.HA + a) ((S.cover P sg).1 * S.B + i)

/-- **Key number κ of the piece of segment s for the pair (lam, a), in a call of shift sh.** -/
def segKey (S : Sh) (cell : NameA → R) (sh : ℕ) (s : Seg) (lam a κ : ℕ) : R :=
  let isD := s == Seg.rd || s == Seg.fd
  match s with
  | .rm | .rd =>
    (asC S cell 0 lam a isD κ + 128) + ((2 ^ 20 : ℕ) : R) * (asC S cell 1 lam a isD κ + 128) +
      ((2 ^ 40 : ℕ) : R) * asC S cell 2 lam a isD κ
  | .fm | .fd =>
    gapAt S cell sh isD lam a κ - ssAt S cell isD lam a κ - (asC S cell 0 lam a isD κ + 128) -
      256 * (asC S cell 1 lam a isD κ + 128) + ((2 ^ 32 : ℕ) : R) * asC S cell 2 lam a isD κ +
      ((2 ^ 33 : ℕ) : R) * wt S cell lam a isD κ
  | .wl =>
    let n := κ % S.dh
    let i := κ / S.dh % S.T
    let g := κ / (S.dh * S.T) % S.G
    let hd := g * S.HA + a
    let dn := den S cell lam hd i
    let re := 2 * acc S cell lam a g i n + dn - 2 * (dn * ten S cell S.atO lam (hd * S.dh + n) i)
    if κ / (S.dh * S.T * S.G) = 0 then re - 65536 * (rh S cell lam (hd * S.dh + n) i + 128)
    else 2 * dn - 1 - re - 65536 * (rhp S cell lam (hd * S.dh + n) i + 128)
  | .ix =>
    let i := κ % S.T
    let hd := κ / S.T * S.HA + a
    ((2 ^ (16 - S.cf.lt) : ℕ) : R) *
      ((i : R) - sumN S.cf.lt fun k => ((2 ^ k : ℕ) : R) * ib S cell lam k hd i)
  | .wh =>
    let n := κ % S.dh
    let i := κ / S.dh % S.T
    let hd := κ / (S.dh * S.T) * S.HA + a
    (rh S cell lam (hd * S.dh + n) i + 128) +
      ((2 ^ 20 : ℕ) : R) * (rhp S cell lam (hd * S.dh + n) i + 128)

/-- Call q's key number X, of the segments that sel admits; pad: with the padding. -/
def kvSel (S : Sh) (h : Forest.Shape) (cell : NameA → R) (sel : Seg → Bool) (pad : Bool)
    (q X : ℕ) : R :=
  match S.calls[q]? with
  | none => 0
  | some c =>
    match c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
    | some p => if sel p.seg then segKey S cell c.sh p.seg p.lam p.a (X - p.off) else 0
    | none => if pad then (tauN h q (t0N h q) : R) else 0

/-- **Call q's key number X at A.** -/
def kvA (S : Sh) (h : Forest.Shape) (cell : NameA → R) (q X : ℕ) : R :=
  kvSel S h cell (fun _ => true) true q X

/-- **Where bit j of the count of row u of the joint table lies at A**: in bA. -/
def placeBA (S : Sh) (h : Forest.Shape) (u j : ℕ) : Option NameA :=
  let c := u % 2 ^ h.cK
  let t := u / 2 ^ h.cK
  if c < h.NC ∧ j < 32 ∧ u < 2 ^ h.d then
    some ⟨S.cf.NAs + 2, t % 2 ^ (S.cf.lmb - 5) * 32 + j,
      c * 2 ^ (h.kT + 5 - S.cf.lmb) + t / 2 ^ (S.cf.lmb - 5)⟩
  else none

/-- The joint key vector at A. -/
def keyA (S : Sh) (h : Forest.Shape) (cell : NameA → R) (θ : R) (X : ℕ) : R :=
  jointKey h (kvA S h cell) θ X

/-- The joint table at A. -/
def tabA (h : Forest.Shape) (θ : R) (u : ℕ) : R := jointTab h θ u

theorem keyA_eq (S : Sh) (h : Forest.Shape) (cell : NameA → R) :
    keyA S h cell = jointKey h (kvA S h cell) := rfl

theorem tabA_eq (h : Forest.Shape) : (tabA h : R → ℕ → R) = jointTab h := rfl

/-- The planes at A as one vector: entry X = u * 32 + j. -/
def bitsA (S : Sh) (h : Forest.Shape) (cell : NameA → R) (X : ℕ) : R :=
  match placeBA S h (X / 32) (X % 32) with
  | some x => cell x
  | none => 0

end A

end OnBytes.Ends

#print axioms OnBytes.Ends.A.segKey
#print axioms OnBytes.Ends.A.kvA
#print axioms OnBytes.Ends.A.placeBA
#print axioms OnBytes.Ends.A.keyA
#print axioms OnBytes.Ends.A.bitsA
#print axioms OnBytes.Ends.A.keyA_eq
#print axioms OnBytes.Attention.Shape
#print axioms OnBytes.Attention.Shape.cover
#print axioms OnBytes.Attention.Shape.shd
