-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyData.lean: the data of a key file's three chains as a protocol made of steps.

OnBytes/Slice/KeyDefs.lean has the public numbers of the loops and the written rounds (`KeyN`). This
file adds what the steps of OnBytes/Slice/KeyChain1.lean and KeyChain2.lean need beside them
(`KeyD`): the sizes of the stored table and of the test for a linear claim on it; the formats of the
six sent messages, where their rows stand in a column, the first stages of the four proximity tests
and the seats; the four chains of stages; the program's public data on the matrix and the lookups;
and where things stand in the sent messages.

The public arithmetic of the lookups and of the passage to the linear claim is defined behind the
structure (`KeyD.fac` to `KeyD.tcOf`): forms over the field of the program's functions, at the
public inputs that the program makes of its public data.

Many fields stand for things of the program, and each says for what. Three stand for routines: the
ledgers when the lookups begin (`free₀`), and the rows of the first proximity test as vectors on its
tables (`vecG`, `sampleG`). The others are readings and places: the other two words of the first
test's first tree (`zG`, `gG`), how three drawn values are read (`gPt`, `gLoc`, `gZeta`), where Z's
mask entries stand (`entZ`), where the six messages' rows stand in a column, the seams, openings and
keys of the three views (`G₀`), and the program's public data (`X`). A statement on a `KeyD` is a
statement for every choice of these fields. A choice that reads more than the verifier is shown (a
decoding, the table at places that were not asked for) makes the blocks' statements easy and "the
program's yes gives the yes in the field" false.

Main definitions.
 `FRow`, `FRow.Holds`   a row in the field: a form in mask entries, a form in the tables of bits, a
                 target. `eqPairs`: the equality vector at a point, as a product of pairs.
 `chi`, `eqEvalL`, `battClaim`, `battSummand`, `battRow`   the batching of rows on the matrix
                 (OnBytes/Slice/KeyLeaves.lean: `Leaves.TRowF`) into one, after the program's text
                 (OnBytes/Iop/Batt.lean: chiOf, claimOf, summandOf, rowOf), over the field. Known
                 differences: the weights on the matrix's rows are one function of the row's number;
                 the claim has kCol variables, where the program's has as many as the first row's
                 column point has coordinates (the program tests that these are kCol).
 `LkN.eLkp`, `KeyN.eSigma`, `batCount`   the error counts of LKP, BAT-sigma and BAT, from the
                 numbers.
 `Sent`         what is sent and drawn in a SEND of two rounds.
 `TC`           what the verifier holds of the linear claim on the table.
 `KeyD.WfSrc`   the program's public data on the matrix and the lookups, as letters.
 `KeyD`         the data. `KeyD.Str`, `MU`: a stored table, a decoded table. `KeyD.clOf`: the linear
                 claim, once Z is fixed.
 `KeyD.pubOf`, `fac`, `sTie1`, `sTie`, `sLeaves`, `sBits`, `lastOrd`, `rowCnt`, `pendOf`, `ptOf`,
 `tcF`, `tcOf`   the public arithmetic.
 `KeyD.Wf`      the four chains' lists of rounds are those of `KeyN`.
Not claimed. No theorem is in this file. That the definitions which name a function of the program
agree with that function is not stated here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyDefs
import OnBytes.Slice.KeyProxGp
import OnBytes.Slice.KeyLinExit
import OnBytes.Slice.KeyPscN
import OnBytes.Slice.KeyDraws
import OnBytes.Slice.KeySound
import OnBytes.Slice.KeyLeaves
import OnBytes.Slice.KeySummands
import OnBytes.Slice.KeyPlanesDefs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open OnBytes.Params (WfPart WfLookup)

/-! ## Rows in the field -/

/-- The equality vector at a point, as a product of pairs: for each coordinate p the pair
(1 - p, p). -/
def eqPairs (p : List GE) : List (GE × GE) := p.map fun a => (1 - a, a)

/-- A row in the field, on the message with the multiplicities. masks: a form in mask entries. maps:
a form in the lookups' tables of bits: for each term the lookup's number, a coefficient, and a
vector on the table that is a product of pairs, one pair for each variable. -/
structure FRow where
  masks : PscF.MaskForm
  maps : List (ℕ × GE × List (GE × GE))
  target : GE

/-- The row holds. W: the values of the mask entries. B i v: the sum of lookup number i's table of
bits under the vector v. -/
def FRow.Holds (W : PscF.World) (B : ℕ → List (GE × GE) → GE) (r : FRow) : Prop :=
  W.form r.masks + (r.maps.map fun a => a.2.1 * B a.1 a.2.2).sum = r.target

/-! ## Many rows on the matrix become one -/

/-- 1, x, x^2 and so on: n powers (OnBytes/Iop/Batt.lean: chiOf). -/
def chi (x : GE) (n : ℕ) : List GE := (List.range n).map fun j => x ^ j

/-- The equality polynomial of two points. -/
def eqEvalL (p q : List GE) : GE := ((p.zip q).map fun a => a.1 * a.2 + (1 - a.1) * (1 - a.2)).prod

/-- The claim of the sumcheck once x is drawn (claimOf). -/
def battClaim (kCol : ℕ) (rows : List Leaves.TRowF) (x : GE) : PscF.Claim where
  vars := List.replicate kCol (PscF.Weight.plain 3)
  masks := ((chi x rows.length).zip rows).flatMap fun p => PscF.scaleForm p.1 p.2.masks
  target := (((chi x rows.length).zip rows).map fun p => p.1 * p.2.target).sum

/-- The summand once x is drawn (summandOf): no constant; kept map number j has the coefficient
x^j times the equality polynomial of row j's column point and the point. -/
def battSummand (rows : List Leaves.TRowF) (x : GE) : PscF.Summand where
  shown := 0
  kept := rows.length
  degree := 0
  coeffs := fun point _ =>
    0 :: ((chi x rows.length).zip rows).map fun p => p.1 * eqEvalL p.2.psi point

/-- The one row that is handed on (rowOf). -/
def battRow (rows : List Leaves.TRowF) (o : PscF.Out) : Leaves.TRowF where
  g := fun i => ((rows.zip o.rowMaps).map fun p => p.2 * p.1.g i).sum
  psi := o.point
  masks := o.rowMasks
  target := o.rowTarget

/-! ## Error counts from the numbers -/

/-- The number of bad values of alpha in a lookup: the number of leaves of all parts' trees, less
one. -/
def LkN.eLkp (L : LkN) : ℕ := (L.parts.map fun v => 2 ^ v).sum - 1

/-- The number of bad values of BAT-sigma's element: the number of rows that the round's entry
counts, less one. The step tests that so many rows on the matrix wait. -/
def KeyN.eSigma (N : KeyN) : ℕ := N.sigma.entry.rows - 1

/-- The error count of a round BAT: the number of rows that its entry counts, less one, times the
number in the law of the format's sampler (OnBytes/Slice/KeyExit.lean: batSemAt_of, for lists of one
word). -/
def batCount (d : PQ.RD) : ℕ := 1 * (d.entry.rows - 1) * (bsRound .two d.entry d.kind).w

/-! ## The data -/

/-- What is sent and drawn in a SEND of two rounds: the message with the root, the verifier's
message with the sample's seeds, the message with the answers. -/
structure Sent (dS dA : PQ.RD) where
  m : (wRound dS).Msg
  c : (wRound dS).Chal
  a : (wRound dA).Msg

/-- What the verifier holds of the linear claim on the table: weights on the rows of the matrix, a
point for its columns, coefficients on entries of Z, a target. -/
structure TC (lin : KLin) (cl : KClose lin) where
  g : Fin lin.nY → GE
  ψ : lin.D.Pt
  cZ : Fin cl.nF → GE
  τ : GE

/-- The program's public data on the matrix and the lookups, as letters. The first argument of
each member but the first is the lookup's number; `part` also takes the part's. The members are the
letters of OnBytes/Slice/KeyLeaves.lean's statement `Leaves.Top`, and the layout of the planes of
bits (OnBytes/Slice/BlkPlanes.lean). -/
structure KeyD.WfSrc where
  mx : Wf.Matrix
  lk : ℕ → WfLookup
  id : ℕ → ℕ
  part : ℕ → ℕ → WfPart
  LF : ℕ → Leaves.LkF
  (rowV natV : ℕ → ℕ → GE)
  θ : ℕ → GE
  /-- the numbers, and each lookup's blocks of planes, of the layout of M's main table -/
  (rb logEll : ℕ)
  bs : ℕ → List Wf.Block

/-- The data of a key file's three chains. -/
structure KeyD where
  /-- the numbers of the loops and the written rounds -/
  N : KeyN
  /-- the sizes of the stored table and of the test for a linear claim on it -/
  lin : KLin
  /-- the formats of Z (the index masks), W, U (the folded row), O (Omega), K (the holder of the
  element that splits the fold's row), the first stages of the three tests that close that test, the
  seats, and where the test's vectors stand in the messages -/
  cl : KClose lin
  /-- the format of M (the multiplicities), the first stage of the test on it, and M's seat -/
  bM : Mb
  sG : Sg
  σM : Site sG bM
  /-- where the rows of the six messages stand in a column -/
  (lZ lM lW lU lO lK : Lay)
  /-- the rounds after the batching of the four proximity tests -/
  cG : Chain sG
  cU : Chain cl.sU
  cO : Chain cl.sO
  cW : Chain cl.sW
  /-- the free mask entries of each oracle message, by its number, when the lookups begin. Stands
  for the ledgers that OnBytes/Iop/Send.lean opens where it takes an oracle message in. -/
  free₀ : ℕ → List ℕ
  /-- the program's public data on the matrix and the lookups -/
  X : KeyD.WfSrc
  /-- the entry of Z at which its mask entry with a number stands, if there is one: a number can
  name a place on a row of padding, which is no entry -/
  entZ : ℕ → Option cl.MZ.cd.J
  /-- a row in the field as a row on the tables of the first test's first stage, if it names nothing
  but entries of M. Stands for OnBytes/Iop/Ground.lean's `addToGroupRow`. -/
  vecG : FRow → Option (RowAt sG)
  /-- the sample rows of M, as rows on the tables of the first test's first stage. Stands for the
  rows that OnBytes/Iop/Send.lean lays at the oracle message where it takes it in. -/
  sampleG : Sent N.mSeed N.mAns → List (RowAt sG)
  /-- the other two words of the first test's first tree: the fresh mask rows, which ride in M's
  tree, and the masking word -/
  zG : Sent N.mSeed N.mAns → cG.Msg0 → sG.cFr.Word
  gG : Sent N.mSeed N.mAns → sG.cIn.Word
  /-- how the three drawn values of chain 2 are read -/
  gPt : Vals .two (Fmt.dsOf N.pt.entry N.pt.kind) → lin.D.Pt
  gLoc : Vals .two (Fmt.dsOf N.loc.entry N.loc.kind) → Fin lin.t → lin.S.Pos
  gZeta : Vals .two (Fmt.dsOf N.zeta.entry N.zeta.kind) → Fin lin.l → GE
  /-- the seams, the stored table's openings and the trees' keys in the three views; its lists of
  rounds, its number a and its choice of the verifier messages' types are not read -/
  G₀ : Stretches

namespace KeyD

variable (D : KeyD)

/-- A stored table, as the verifier's oracle. -/
abbrev Str : Type := D.lin.S.Pos → PQ.SgX

/-- A decoded table. -/
abbrev MU : Type := D.lin.S.ix.Row × D.lin.S.En → GE

/-- The messages Z and M, decoded. -/
abbrev MZ : Type := D.cl.MZ.cd.J → GE
/-- See MZ. -/
abbrev MM : Type := D.bM.cd.J → GE

/-- The linear claim, once Z is fixed. -/
def clOf (t : TC D.lin D.cl) (z : D.MZ) : D.lin.Cl :=
  ⟨t.g, t.ψ, ∑ a, t.cZ a * z (D.cl.φZ a), t.τ⟩

/-! ## The public arithmetic of the lookups and of the passage to the linear claim

Each definition is a form over the field of the function of the program that it names, at the
public inputs which OnBytes/Iop/Wf.lean's `lookupOf` makes of `D.X`: one table, the range table (its
list of rows is empty: row number t holds t); one padding key; no shift. That a definition agrees
with the program's function is not stated here; where it is proved, it is proved in the files that
read the program (for the public factor: OnBytes/Slice/BlkTableRead.lean: read_factorOf). -/

/-- The public inputs of lookup number i (OnBytes/Iop/Wf.lean: lookupOf). -/
def pubOf (i : ℕ) : Lkp.Public := Wf.lookupOf (D.X.id i) D.X.mx (D.X.lk i)

/-- The public factor of lookup number i at alpha: alpha less the padding key, to the power of the
number of places of padding (`Lkp.factorOf`, which multiplies over the places of padding;
`lookupOf` gives them all the row with the padding key's number, which in the range table holds that
number). -/
def fac (i : ℕ) (a : GE) : GE :=
  (a - ((D.X.lk i).paddingKey.toNat : GE)) ^ Lkp.paddingCount (D.pubOf i)

/-- The summand of the tie's first step, at alpha (OnBytes/Iop/Lkp.lean: summandTieFirst). -/
def sTie1 (i : ℕ) (a : GE) : PscF.Summand := PscF.summandTieFirst (D.fac i a)

/-- The summand of the tie's later steps (`Lkp.summandTie`). -/
def sTie (_ : KeyD) : PscF.Summand := PscF.summandTie

/-- The summand of the leaves of the table's tree, at alpha (`Lkp.summandLeaves`). -/
def sLeaves (i : ℕ) (a : GE) : PscF.Summand := PscF.summandLeaves (Planes.lfR (D.X.lk i).d a)

/-- The summand bit^2 - bit (`Lkp.summandBits`). -/
def sBits (_ : KeyD) : PscF.Summand := PscF.summandBits

/-- The order of the variables of the last level of a part's tree: the program's own function on
numbers. -/
def lastOrd (i l : ℕ) : List ℕ := Lkp.orderBeginning (D.pubOf i).lastKeyLevelOrder l

/-- The row that says that the counts add up to the number of keys that are not padding (the last
`leave` of `Lkp.run`). -/
def rowCnt (i : ℕ) : FRow :=
  ⟨[], [(i, 1, Planes.countPairs (D.X.lk i).mu (D.X.lk i).d)],
    ((∑ k ∈ Finset.range (D.X.lk i).parts.length, 2 ^ (D.X.mx.kCol + (D.X.part i k).logPlaces) -
      Lkp.paddingCount (D.pubOf i) : ℕ) : GE)⟩

/-- The row on the matrix that a claim on the leaves of a part's tree becomes: the lookup's number,
alpha, the part's number, the claim (OnBytes/Iop/Wf.lean's `pendingRow` after `Lkp.keysOf`). -/
def pendOf (i : ℕ) (a : GE) (j : ℕ) (c : PscF.PointClaim) : Leaves.TRowF :=
  Leaves.pendingRowF D.X.mx.kCol (D.X.LF i) (D.X.part i j).runs
    (Leaves.keysOfF (D.pubOf i) (D.X.rowV i) (D.X.natV i) (D.X.θ i) a j c)
    (Leaves.eqPlacesF D.X.mx.kCol c.point)

/-- A column point, from a list of coordinates. -/
def ptOf (psi : List GE) : D.lin.D.Pt :=
  (fun i => psi.getD (D.lin.klo + i.val) 0, fun i => psi.getD i.val 0)

/-- What the test on the table takes of a row on the matrix. entZ j: the entry of Z at which its
mask entry number j stands, if there is one. -/
def tcF (entZ : ℕ → Option D.cl.MZ.cd.J) (r : Leaves.TRowF) : TC D.lin D.cl where
  g := fun y => r.g y.val
  ψ := D.ptOf r.psi
  cZ := fun a => (r.masks.map fun t => if entZ t.1.index = some (D.cl.φZ a) then t.2 else 0).sum
  τ := r.target

/-- What the test on the table takes of the one row on the matrix (the `LinClaim` that
OnBytes/Iop/Lin.lean's `memberFirstVerify` makes). -/
def tcOf (r : Leaves.TRowF) : TC D.lin D.cl := D.tcF D.entZ r

/-- The four chains' lists of rounds are those of the plain lists. -/
structure Wf : Prop where
  g : D.cG.rds = D.N.tG.chain
  u : D.cU.rds = D.N.tU.chain
  o : D.cO.rds = D.N.tO.chain
  w : D.cW.rds = D.N.tW.chain

end KeyD

end OnBytes.Slice
