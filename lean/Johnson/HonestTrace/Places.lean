-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Places.lean

Where each named cell of the model's run, and each bit of a lookup's count, lies in the byte
format's matrices of cells: the definitions, at any sizes and any number of groups.

The byte format's pages on the three sorts of segment (docs/format/11-1-machinery.md to
11-4-output-head.md) give each segment a list of matrices of cells and say by rules in the parameter
file's numbers how many rows and columns a matrix has and where a cell lies. This file writes these
rules as functions over a structure of numbers, "Sz". The names of the layers' and attention's cells
are the library's own (Inst/Model/FF/Index.lean, Inst/Model/Att/Trace.lean); a cell of the head is
named by its feature and position, as in the library's trace (Inst/Model/All/Trace.lean); the bits
of the lookups' counts have new names. The way back, from a place to the name that stands there, is
a formula. No definition of this file picks by choice. The laws on these definitions are in
Johnson/HonestTrace/PlacesBack.lean. What ties them to the Lean verifier under OnBytes/Model/ is in
Johnson/HonestTrace/PlacesTies.lean and PlacesTiesHead.lean.

Main definitions:
* "Sz": the numbers. "Sz.OK", "Sz.Fit": what the laws ask of them.
* "Sz.rows", "Sz.k", "Sz.shape": the rows of cells and the columns of a matrix in a segment's list.
* "Sz.mu": the number of a matrix in a segment's list, "none" for whatever is not in the list.
  "mu_inj", "mu_lt", "mu_onto": on a segment of the proof these numbers are different for different
  names, and are exactly the numbers below the list's length "Sz.len".
* "Sz.owner": who committed a matrix that a segment borrows.
* "Name", "Name.Valid", "Name.place": names of cells and bits, which of them are own names of a
  segment, and the place of a name.
* "Sz.nameAt": the own name at a place. "lay": matrices from cells by names.
* "Sz.ref", "Sz.small": the numbers of the two example sets. "ref_ok", "small_ok": both meet "OK"
  and "Fit". "ref_cols", "small_cols": the sixteen numbers of columns at each.

Limits. The rules were typed by a reading of the format's pages. The names are those for which the
library has arrays: the parameter file's digit forms and switches are fixed at hq = 2, the other six
forms 1, gcl = rcl = 1, five limbs of the stream (xl 5) and routed experts in every second layer.
Both example sets have these. hr has 120 features in use, which is the format's number at xl 5
alone. An "Sz" need not be the numbers of a model or of a parameter file: nothing here ties P.T to
2^lt, P.layers to nGr 2^ll, or the numbers of calls to a list of calls. kT and NC are numbers for
each segment, since by the format's pages an attention segment's list of calls can depend on the
group's shifts; all other numbers of attention are the same in every group. "Sz.ref" and "Sz.small"
were typed by hand from the two parameter files, some of their numbers derived from the files' lines
as their docstrings say, and the thirty-two numbers of columns from the two layout files; no theorem
of this file reads a file. Of this file's theorems only "ref_cols" and "small_cols" hold a number or
a rule against the example sets' files (through numbers typed by hand), and only the columns;
"ref_ok" and "small_ok" fail on a wrong number only if it breaks "OK" or "Fit". Rows, places and
owners are held against nothing here. A count of 2^32 or more has digits that "lay" does not lay.

Not claimed: that any program lays its cells so; that a verifier reads them so (for that see the two
files of ties, and their limits); anything on the values of the cells.

-/
import Inst.Model.All.Trace
import Inst.Model.FF.IndexFacts
import Inst.Model.Att.AddrFacts
import Johnson.HonestTrace.Names

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open Inst.Model.AttSeg.AddrFacts (adr phi pos mat SM SD S1 S2 S3 Phi)

/-! ## Names: what this file adds -/

/-- Whether a segment is one of a proof with G groups is decided by comparing two numbers. -/
instance Seg.decBelow (G : ℕ) (σ : Seg) : Decidable (σ.Below G) := by
  cases σ <;> unfold Seg.Below <;> infer_instance

/-- The part's number in a name; 0 for a matrix that lies in one part. -/
def MatName.part : MatName → ℕ
  | .af p | .ad p | .as p | .hf p => p
  | _ => 0

/-- Part number p of the same matrix. The name of a matrix in one part stays as it is. -/
def MatName.setPart : MatName → ℕ → MatName
  | .af _, p => .af p
  | .ad _, p => .ad p
  | .as _, p => .as p
  | .hf _, p => .hf p
  | μ, _ => μ

/-- The name of the matrix that holds the planes of a segment's lookup: b, bA or bH. -/
def planeOf : Seg → MatName
  | .ff _ => .b
  | .att _ => .bA
  | .head => .bH

/-! ## The sizes -/

/-- **The numbers that a shape or a place reads.** P: the model's sizes, of which d, nq, nkv, ch, f,
nexp and V are read. 2^lt positions; 2^ll layers in a group; nGr groups. 2^lg heads of keys and
values, 2^lB positions in a tile, 2^ln channels of a head. u0: a number of the library's sizes of
attention that no place reads. la: V is rounded up to a multiple of 2^(la - lt). wc..: the features
in a column of af, ad, ar, qa, the three matrices of the stream, ah, ao, hf, hd, hr; in the
parameter file a matrix has a line for the logarithm lm of its rows, and wc = 2^(lm - lt). NAf, NAd,
NAs, NHf: the numbers of parts. lmS, lmb, lmbA, lmbH: the logarithms of the rows of as and of the
three matrices of planes. kT σ, NC σ: the lookup of segment σ has NC σ calls, and its largest table
2^(kT σ) rows. -/
structure Sz where
  P : Params
  lt : ℕ
  ll : ℕ
  nGr : ℕ
  lg : ℕ
  lB : ℕ
  ln : ℕ
  u0 : ℕ
  la : ℕ
  wcaf : ℕ
  NAf : ℕ
  wcad : ℕ
  NAd : ℕ
  wcar : ℕ
  lmb : ℕ
  wcq : ℕ
  wcx : ℕ
  lmS : ℕ
  NAs : ℕ
  wch : ℕ
  wco : ℕ
  lmbA : ℕ
  wchf : ℕ
  NHf : ℕ
  wchd : ℕ
  wchr : ℕ
  lmbH : ℕ
  kT : Seg → ℕ
  NC : Seg → ℕ

namespace Sz
variable (S : Sz)

/-- The library's sizes of a feed-forward segment. What is read of them below (the number of a
feature, the features of a matrix, which names are cells) reads P, lT and lL alone, by a reading of
Inst/Model/FF/Index.lean; the other fields but the parts are 0. -/
def DF : FFSeg.Dim := ⟨S.P, S.lt, S.ll, 0, 0, 0, S.NAf, 0, 0, 0⟩

/-- The library's sizes of an attention segment. Its positions are 2^lt if lB + 1 ≤ lt. -/
def DA : AttSeg.Dim := ⟨S.lg, S.lt - 1 - S.lB, S.lB, S.ln, S.P.nq / S.P.nkv, 2 ^ S.ll, S.u0⟩

/-- V rounded up to a multiple of 2^(la - lt). The subtraction is on natural numbers: at la < lt it
is V. -/
def JV : ℕ := (S.P.V + 2 ^ (S.la - S.lt) - 1) / 2 ^ (S.la - S.lt) * 2 ^ (S.la - S.lt)

/-- The features in a column of a matrix of features; 0 for as and the planes. -/
def wc : MatName → ℕ
  | .af _ => S.wcaf | .ad _ => S.wcad | .ar => S.wcar | .qa => S.wcq
  | .xbO => S.wcx | .xbI => S.wcx | .xbL => S.wcx
  | .ah => S.wch | .ao => S.wco
  | .hf _ => S.wchf | .hd => S.wchd | .hr => S.wchr
  | _ => 0

/-- The logarithm of the rows of a segment's matrix of planes. -/
def lmP : Seg → ℕ
  | .ff _ => S.lmb
  | .att _ => S.lmbA
  | .head => S.lmbH

/-- The rows of cells of a matrix (of each part): a column of a matrix of features holds wc features
of 2^lt cells each. -/
def rows : MatName → ℕ
  | .as _ => 2 ^ S.lmS
  | .b => 2 ^ S.lmb
  | .bA => 2 ^ S.lmbA
  | .bH => 2 ^ S.lmbH
  | μ => S.wc μ * 2 ^ S.lt

/-- The number of parts of a matrix. -/
def np : MatName → ℕ
  | .af _ => S.NAf | .ad _ => S.NAd | .as _ => S.NAs | .hf _ => S.NHf | _ => 1

/-- What a matrix holds in all its parts together: features in use in a matrix of features, cells in
use in as, and 0 for the planes. For hr it is the numeral 120, which is the format's NR + 21 at five
limbs of the stream (xl 5). -/
def n : MatName → ℕ
  | .af _ => FFSeg.nFeatMx S.DF .af
  | .ad _ => FFSeg.nFeatMx S.DF .ad
  | .ar => FFSeg.nFeatMx S.DF .ar
  | .qa => FFSeg.nFeatMx S.DF .qa
  | .xbO => FFSeg.nFeatMx S.DF .xout
  | .xbI => FFSeg.nFeatMx S.DF .xin
  | .xbL => FFSeg.nFeatMx S.DF .xout
  | .as _ => SM S.DA + SD S.DA
  | .ah => Phi S.DA .ah
  | .ao => Phi S.DA .ao
  | .hf _ => 4 * S.P.d + 6 * S.JV
  | .hd => 2 * S.P.d
  | .hr => Head.nB
  | _ => 0

/-- a / b, rounded up; 0 at b = 0. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- The columns of one part of a matrix that holds no planes: what the matrix holds, by what a
column of all parts together holds, rounded up. -/
def kF : MatName → ℕ
  | .as _ => ceilDiv (S.n (.as 0)) (S.NAs * 2 ^ S.lmS)
  | μ => ceilDiv (S.n μ) (S.np μ * S.wc μ)

/-- The columns of a segment's matrix of planes: NC 2^(kT + 5 - lm). -/
def kP (σ : Seg) : ℕ := S.NC σ * 2 ^ (S.kT σ + 5 - S.lmP σ)

/-- The columns of one part of a matrix in a segment's list. -/
def k (σ : Seg) : MatName → ℕ
  | .b | .bA | .bH => S.kP σ
  | μ => S.kF μ

/-- **The number of a matrix in the list of a segment**, which the format's pages call mu:
"MatName.no?" at a segment of the proof, and "none" at a group from nGr on. In a feed-forward
segment the order is af, ad, ar, b, qa, xbO, xbI. The numbers of arrays in a layout file are others:
there the arrays that no other segment reads come first, so in group 0 xbI stands before qa and xbO
(docs/format/11-2-feed-forward-segment.md, the table of moments). -/
def mu (σ : Seg) (μ : MatName) : Option ℕ :=
  if σ.Below S.nGr then MatName.no? S.NAf S.NAd S.NAs S.NHf σ μ else none

/-- The length of a segment's list of matrices. -/
def len : Seg → ℕ
  | .ff _ => S.NAf + S.NAd + 5
  | .att _ => S.NAs + 4
  | .head => S.NHf + 4

/-- **The shape of a matrix**: rows of cells and columns; (0, 0) for whatever has no number in the
segment's list. -/
def shape (σ : Seg) (μ : MatName) : ℕ × ℕ :=
  if (S.mu σ μ).isSome then (S.rows μ, S.k σ μ) else (0, 0)

/-- **Who committed a matrix.** qa in an attention segment is qa of the group's feed-forward
segment; xbI from group 1 on is xbO of the group before; xbL is xbO of the last group. Every other
matrix is its own. (nGr - 1 is 0 at nGr = 0; "OK" asks 0 < nGr.) -/
def owner : Seg → MatName → Seg × MatName
  | .att g, .qa => (.ff g, .qa)
  | .ff g, .xbI => if g = 0 then (.ff g, .xbI) else (.ff (g - 1), .xbO)
  | .head, .xbL => (.ff (S.nGr - 1), .xbO)
  | σ, μ => (σ, μ)

/-- What the laws on places ask of the numbers: there is a group; a column of each matrix of
features holds a feature; each of af, ad, as, hf has a part; 5 ≤ lm ≤ kT + 5 for the planes of each
segment of the proof (nothing is asked of kT at a group from nGr on); lB + 1 ≤ lt, so that
attention's positions are 2^lt. -/
structure OK : Prop where
  nGr : 0 < S.nGr
  wcaf : 0 < S.wcaf
  wcad : 0 < S.wcad
  wcar : 0 < S.wcar
  wcq : 0 < S.wcq
  wcx : 0 < S.wcx
  wch : 0 < S.wch
  wco : 0 < S.wco
  wchf : 0 < S.wchf
  wchd : 0 < S.wchd
  wchr : 0 < S.wchr
  NAf : 0 < S.NAf
  NAd : 0 < S.NAd
  NAs : 0 < S.NAs
  NHf : 0 < S.NHf
  planes : ∀ σ : Seg, σ.Below S.nGr → 5 ≤ S.lmP σ ∧ S.lmP σ ≤ S.kT σ + 5
  lB : S.lB + 1 ≤ S.lt

/-- What the laws on attention's borrowed names ask besides: the library's two sizes "DF" and "DA"
speak of one model. -/
structure Fit : Prop where
  nkv : S.P.nkv = 2 ^ S.lg
  ch : S.P.ch = 2 ^ S.ln
  nq : S.P.nkv ∣ S.P.nq

end Sz

/-! ## Names of cells, and their places -/

/-- **Names of cells and of bits.** A cell of a feed-forward segment or of an attention segment of
group g, by the library's names (attention's borrowed names among them); feature φ at position i of
hf, hd or hr; bit j of the count at row t of the table of call c of segment σ's lookup, the table
repeated up to 2^kT rows. Which of them are own names of a segment: "Name.Valid". -/
inductive Name
  | ff (g : ℕ) (c : FFSeg.Cell)
  | att (g : ℕ) (c : AttSeg.Raw)
  | hf (φ i : ℕ)
  | hd (φ i : ℕ)
  | hr (φ i : ℕ)
  | bit (σ : Seg) (t c j : ℕ)
  deriving DecidableEq

/-- Which names are own cells at the numbers S: a group below nGr and a name that the library's
sizes admit; x0, the stream that enters, in group 0 alone; of attention's names those of as, ah, ao;
a feature in use at a position below 2^lt; for a bit a segment of the proof, t < 2^kT, c < NC, j <
32. -/
def Name.Valid (S : Sz) : Name → Prop
  | .ff g c => g < S.nGr ∧ c.Valid S.DF ∧ (c.X = .x0 → g = 0)
  | .att g c => g < S.nGr ∧ c.Valid S.DA ∧ c.Own = true
  | .hf φ i => φ < S.n (.hf 0) ∧ i < 2 ^ S.lt
  | .hd φ i => φ < S.n .hd ∧ i < 2 ^ S.lt
  | .hr φ i => φ < S.n .hr ∧ i < 2 ^ S.lt
  | .bit σ t c j => σ.Below S.nGr ∧ t < 2 ^ S.kT σ ∧ c < S.NC σ ∧ j < 32

/-- A place: segment, matrix, row of cells, column. -/
abbrev Place : Type := Seg × MatName × ℕ × ℕ

/-- The library's names of a feed-forward segment's matrices, as names of this folder (part 0). -/
def famOf : FFSeg.Mx → MatName
  | .af => .af 0 | .ad => .ad 0 | .ar => .ar | .b => .b | .qa => .qa | .xin => .xbI
  | .xout => .xbO

namespace Sz
variable (S : Sz)

/-- **Where a feature's cell lies.** With wc features in a column and k columns in a part, feature φ
is in part φ / wc / k, in column φ / wc mod k of that part, and its cell for position i in row (φ
mod wc) 2^lt + i (docs/format/11-2-feed-forward-segment.md, "Features"). In the name of a matrix in
one part the part's number is not kept. -/
def atFeat (σ : Seg) (μ : MatName) (φ i : ℕ) : Place :=
  (σ, μ.setPart (φ / S.wc μ / S.kF μ), φ % S.wc μ * 2 ^ S.lt + i, φ / S.wc μ % S.kF μ)

/-- **Where a cell of as lies.** Cell number N is in row N mod 2^lmS of column N / 2^lmS, and column
C is column C mod k of part C / k (docs/format/11-3-attention-segment.md, "The arrays and what each
cell holds"). -/
def atCell (g N : ℕ) : Place :=
  (.att g, .as (N / 2 ^ S.lmS / S.kF (.as 0)), N % 2 ^ S.lmS, N / 2 ^ S.lmS % S.kF (.as 0))

/-- **Where a bit of a count lies.** With N = (c 2^kT + t) 32 + j, in row N mod 2^lm and column N /
2^lm (docs/format/11-1-machinery.md, "Where the multiplicities are"). -/
def atBit (σ : Seg) (t c j : ℕ) : Place :=
  (σ, planeOf σ, ((c * 2 ^ S.kT σ + t) * 32 + j) % 2 ^ S.lmP σ,
    ((c * 2 ^ S.kT σ + t) * 32 + j) / 2 ^ S.lmP σ)

end Sz

/-- **The place of a name.** The number of a feature and the number of a cell of as are the
library's ("FFSeg.feat"; "adr", "phi", "pos", "mat" of Inst/Model/Att/AddrFacts.lean). A borrowed
name of attention (qry, key, val, out), which is no valid own name, is laid at its owner: in qa of
the group's feed-forward segment. -/
def Name.place (S : Sz) : Name → Place
  | .ff g c => S.atFeat (.ff g) (famOf c.X.mx) (FFSeg.feat S.DF c.X c.k c.inst c.j) c.i
  | .att g (.c ρ jj b x) => S.atCell g (adr S.DA ρ jj b x)
  | .att g c =>
    match mat c with
    | .ah => S.atFeat (.att g) .ah (phi S.DA c) (pos c)
    | .ao => S.atFeat (.att g) .ao (phi S.DA c) (pos c)
    | _ => S.atFeat (.ff g) .qa (phi S.DA c) (pos c)
  | .hf φ i => S.atFeat .head (.hf 0) φ i
  | .hd φ i => S.atFeat .head .hd φ i
  | .hr φ i => S.atFeat .head .hr φ i
  | .bit σ t c j => S.atBit σ t c j

/-! ## The way back, by formula -/

/-- The cell of a feed-forward segment that is feature φ of the matrix μ at position i: the first
array of the matrix whose range of features holds φ, and in it the limb, the instance and the
channel by division. "none" if no array holds φ. -/
def ffName (D : FFSeg.Dim) (μ : FFSeg.Mx) (φ i : ℕ) : Option FFSeg.Cell :=
  ((FFSeg.arrs μ).find? fun X =>
      decide (FFSeg.OFF D X ≤ φ ∧ φ < FFSeg.OFF D X + X.nFeat D)).map fun X =>
    ⟨X, (φ - FFSeg.OFF D X) / X.width D / X.cnt D, (φ - FFSeg.OFF D X) / X.width D % X.cnt D,
      (φ - FFSeg.OFF D X) % X.width D, i⟩

/-- The pair b of layer lam and query head h. -/
def bOf (D : AttSeg.Dim) (lam h : ℕ) : ℕ := D.na * lam + h % D.na
/-- The head of keys and values that query head h reads. -/
def gOf (D : AttSeg.Dim) (h : ℕ) : ℕ := h / D.na

/-- The name of cell number A of as; "none" from the number of cells in use on. -/
def asName (D : AttSeg.Dim) (A : ℕ) : Option AttSeg.Raw :=
  if A < SM D then some (.c .M (A / 2 ^ D.lM / D.nb) (A / 2 ^ D.lM % D.nb) (A % 2 ^ D.lM))
  else if A < SM D + SD D then
    some (.c .D ((A - SM D) / 2 ^ D.lD / D.nb) ((A - SM D) / 2 ^ D.lD % D.nb)
      ((A - SM D) % 2 ^ D.lD))
  else none

/-- The name of feature φ of ah at position i; "none" from the number of features in use on. -/
def ahName (D : AttSeg.Dim) (φ i : ℕ) : Option AttSeg.Raw :=
  if φ < 4 * S1 D then
    some (.mx (φ / D.nH / D.nl) (bOf D (φ / D.nH % D.nl) (φ % D.nH)) (gOf D (φ % D.nH)) i)
  else if φ < 8 * S1 D then
    some (.den ((φ - 4 * S1 D) / D.nH / D.nl)
      (bOf D ((φ - 4 * S1 D) / D.nH % D.nl) ((φ - 4 * S1 D) % D.nH))
      (gOf D ((φ - 4 * S1 D) % D.nH)) i)
  else if φ < 8 * S1 D + S2 D then
    some (.ib ((φ - 8 * S1 D) / D.nH % D.lT)
      (bOf D ((φ - 8 * S1 D) / D.nH / D.lT) ((φ - 8 * S1 D) % D.nH))
      (gOf D ((φ - 8 * S1 D) % D.nH)) i)
  else none

/-- The name of feature φ of ao at position i; "none" from the number of features in use on. -/
def aoName (D : AttSeg.Dim) (φ i : ℕ) : Option AttSeg.Raw :=
  if φ < S3 D then
    some (.qh (bOf D (φ / D.ch / D.nH) (φ / D.ch % D.nH)) (gOf D (φ / D.ch % D.nH)) i
      (φ % D.ch))
  else if φ < 2 * S3 D then
    some (.qh' (bOf D ((φ - S3 D) / D.ch / D.nH) ((φ - S3 D) / D.ch % D.nH))
      (gOf D ((φ - S3 D) / D.ch % D.nH)) i ((φ - S3 D) % D.ch))
  else none

namespace Sz
variable (S : Sz)

/-- The feature and the position at a row and a column of a matrix of features. -/
def featOf (μ : MatName) (r c : ℕ) : ℕ × ℕ :=
  ((μ.part * S.kF μ + c) * S.wc μ + r / 2 ^ S.lt, r % 2 ^ S.lt)

/-- The number of the cell at a row and a column of a part of as. -/
def cellOf (μ : MatName) (r c : ℕ) : ℕ := (μ.part * S.kF μ + c) * 2 ^ S.lmS + r

/-- The bit at a row and a column of a segment's matrix of planes. -/
def bitName (σ : Seg) (r c : ℕ) : Name :=
  .bit σ ((c * 2 ^ S.lmP σ + r) / 32 % 2 ^ S.kT σ) ((c * 2 ^ S.lmP σ + r) / 32 / 2 ^ S.kT σ)
    ((c * 2 ^ S.lmP σ + r) % 32)

/-- The own name of feature φ at position i of a matrix of features; "none" for a feature that is
not in use, in a borrowed matrix, and for whatever is no matrix of features of the segment. -/
def nameOfFeat (σ : Seg) (μ : MatName) (φ i : ℕ) : Option Name :=
  match σ, μ with
  | .ff g, .af _ => (ffName S.DF .af φ i).map (.ff g)
  | .ff g, .ad _ => (ffName S.DF .ad φ i).map (.ff g)
  | .ff g, .ar => (ffName S.DF .ar φ i).map (.ff g)
  | .ff g, .qa => (ffName S.DF .qa φ i).map (.ff g)
  | .ff g, .xbO => (ffName S.DF .xout φ i).map (.ff g)
  | .ff g, .xbI => if g = 0 then (ffName S.DF .xin φ i).map (.ff g) else none
  | .att g, .ah => (ahName S.DA φ i).map (.att g)
  | .att g, .ao => (aoName S.DA φ i).map (.att g)
  | .head, .hf _ => if φ < S.n μ then some (.hf φ i) else none
  | .head, .hd => if φ < S.n μ then some (.hd φ i) else none
  | .head, .hr => if φ < S.n μ then some (.hr φ i) else none
  | _, _ => none

/-- **The way back, by formula**: the own name that stands at a row and a column of a matrix; "none"
outside the shape, at padding and in a borrowed matrix. -/
def nameAt (σ : Seg) (μ : MatName) (r c : ℕ) : Option Name :=
  if r < (S.shape σ μ).1 ∧ c < (S.shape σ μ).2 then
    match σ, μ with
    | .att g, .as _ => (asName S.DA (S.cellOf μ r c)).map (.att g)
    | .ff _, .b => some (S.bitName σ r c)
    | .att _, .bA => some (S.bitName σ r c)
    | .head, .bH => some (S.bitName σ r c)
    | _, _ => S.nameOfFeat σ μ (S.featOf μ r c).1 (S.featOf μ r c).2
  else none

end Sz

/-! ## The laying -/

/-- Cells by names: the library's trace, a type without sizes (Inst/Model/All/Trace.lean), and for
each segment the counts m σ t c of its lookup. -/
structure Src where
  T : All.Trace
  m : Seg → ℕ → ℕ → ℕ

/-- The cell at a name. At a bit: 1 if that binary digit of the count is set, else 0. -/
def Src.get (X : Src) : Name → ℤ
  | .ff g c => X.T.ff g c
  | .att g c => X.T.att g c
  | .hf φ i => X.T.hf φ i
  | .hd φ i => X.T.hd φ i
  | .hr φ i => X.T.hr φ i
  | .bit σ t c j => if (X.m σ t c).testBit j then 1 else 0

/-- **The laying: from cells by names to matrices.** Inside the shape of the matrix as the reading
segment has it: the cell at the own name that stands at that row and column of the owner's matrix,
and 0 at padding. Outside the shape: 0. -/
def lay (S : Sz) (X : Src) : Seg → MatName → ℕ → ℕ → ℤ := fun σ μ r c =>
  if r < (S.shape σ μ).1 ∧ c < (S.shape σ μ).2 then
    match S.nameAt (S.owner σ μ).1 (S.owner σ μ).2 r c with
    | some n => X.get n
    | none => 0
  else 0

/-! ## Arithmetic -/

/-- (a w + b) / w = a for b < w. -/
theorem mulAdd_div {a b w : ℕ} (h : b < w) : (a * w + b) / w = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) h),
    Nat.div_eq_of_lt h, Nat.zero_add]

/-- (a w + b) mod w = b for b < w. -/
theorem mulAdd_mod {a b w : ℕ} (h : b < w) : (a * w + b) % w = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

/-- For 0 < b: a is at most a / b rounded up, times b. -/
theorem le_ceilDiv_mul (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ Sz.ceilDiv a b * b := by
  unfold Sz.ceilDiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  rw [Nat.mul_comm] at h1
  omega

/-- With np > 0 parts, w > 0 features in a column and k = n / (np w) rounded up: a feature φ < n
lies in a part below np and a column below k. -/
theorem part_col_lt {n np w φ : ℕ} (hnp : 0 < np) (hw : 0 < w) (hφ : φ < n) :
    φ / w / Sz.ceilDiv n (np * w) < np ∧
      φ / w % Sz.ceilDiv n (np * w) < Sz.ceilDiv n (np * w) := by
  have h1 := le_ceilDiv_mul n (Nat.mul_pos hnp hw)
  generalize Sz.ceilDiv n (np * w) = k at h1 ⊢
  have h2 : φ < k * (np * w) := Nat.lt_of_lt_of_le hφ h1
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.zero_mul] at h2
      exact absurd h2 (Nat.not_lt_zero _)
    · exact h
  refine ⟨?_, Nat.mod_lt _ hk0⟩
  rw [Nat.div_lt_iff_lt_mul hk0, Nat.div_lt_iff_lt_mul hw]
  calc φ < k * (np * w) := h2
    _ = np * k * w := by ring

/-- For 0 < w and i < T the row (φ mod w) T + i is below w T. -/
theorem row_lt {w T φ i : ℕ} (hw : 0 < w) (hi : i < T) : φ % w * T + i < w * T := by
  have h := Nat.mod_lt φ hw
  calc φ % w * T + i < φ % w * T + T := by omega
    _ = (φ % w + 1) * T := by ring
    _ ≤ w * T := Nat.mul_le_mul_right _ h

/-! ## The numbers in a segment's list -/

/-- In one segment two names with one number are one name. -/
theorem mu_inj (S : Sz) {σ : Seg} {μ ν : MatName} {a : ℕ} (hμ : S.mu σ μ = some a)
    (hν : S.mu σ ν = some a) : μ = ν := by
  unfold Sz.mu at hμ hν
  by_cases hb : σ.Below S.nGr
  · rw [if_pos hb] at hμ hν
    exact MatName.no?_inj hμ hν
  · rw [if_neg hb] at hμ
    exact absurd hμ (by simp)

/-- A number in a segment's list is below the list's length. -/
theorem mu_lt (S : Sz) {σ : Seg} {μ : MatName} {a : ℕ} (h : S.mu σ μ = some a) :
    a < S.len σ := by
  unfold Sz.mu at h
  by_cases hb : σ.Below S.nGr
  · rw [if_pos hb] at h
    cases σ <;> cases μ <;> simp [MatName.no?, Sz.len] at h ⊢ <;> omega
  · rw [if_neg hb] at h
    exact absurd h (by simp)

/-- In a segment of the proof every number below the list's length is the number of a name: the
numbers have no gaps. -/
theorem mu_onto (S : Sz) {σ : Seg} (hσ : σ.Below S.nGr) {a : ℕ} (h : a < S.len σ) :
    ∃ μ, S.mu σ μ = some a := by
  unfold Sz.mu
  simp only [if_pos hσ]
  cases σ with
  | ff g =>
    have h' : a < S.NAf + S.NAd + 5 := h
    by_cases h1 : a < S.NAf
    · exact ⟨.af a, by simp [MatName.no?, h1]⟩
    by_cases h2 : a < S.NAf + S.NAd
    · exact ⟨.ad (a - S.NAf), by simp [MatName.no?]; omega⟩
    obtain h3 | h3 | h3 | h3 | h3 : a = S.NAf + S.NAd ∨ a = S.NAf + S.NAd + 1 ∨
        a = S.NAf + S.NAd + 2 ∨ a = S.NAf + S.NAd + 3 ∨ a = S.NAf + S.NAd + 4 := by omega
    · exact ⟨.ar, by simp [MatName.no?, h3]⟩
    · exact ⟨.b, by simp [MatName.no?, h3]⟩
    · exact ⟨.qa, by simp [MatName.no?, h3]⟩
    · exact ⟨.xbO, by simp [MatName.no?, h3]⟩
    · exact ⟨.xbI, by simp [MatName.no?, h3]⟩
  | att g =>
    have h' : a < S.NAs + 4 := h
    by_cases h1 : a < S.NAs
    · exact ⟨.as a, by simp [MatName.no?, h1]⟩
    obtain h3 | h3 | h3 | h3 : a = S.NAs ∨ a = S.NAs + 1 ∨ a = S.NAs + 2 ∨ a = S.NAs + 3 := by
      omega
    · exact ⟨.ah, by simp [MatName.no?, h3]⟩
    · exact ⟨.ao, by simp [MatName.no?, h3]⟩
    · exact ⟨.bA, by simp [MatName.no?, h3]⟩
    · exact ⟨.qa, by simp [MatName.no?, h3]⟩
  | head =>
    have h' : a < S.NHf + 4 := h
    by_cases h1 : a < S.NHf
    · exact ⟨.hf a, by simp [MatName.no?, h1]⟩
    obtain h3 | h3 | h3 | h3 : a = S.NHf ∨ a = S.NHf + 1 ∨ a = S.NHf + 2 ∨ a = S.NHf + 3 := by
      omega
    · exact ⟨.hd, by simp [MatName.no?, h3]⟩
    · exact ⟨.hr, by simp [MatName.no?, h3]⟩
    · exact ⟨.bH, by simp [MatName.no?, h3]⟩
    · exact ⟨.xbL, by simp [MatName.no?, h3]⟩

/-! ## Two sizes -/

/-- The numbers of calls in both example sets: the numbers of lines call, callA, callH of their
parameter files, 8, 4 and 6. By the format's page on attention the number of lines callA is the
number of calls if a group's layers have one shift; the columns of bA in both layout files are those
of 4 calls ("ref_cols", "small_cols"). -/
def ncBoth : Seg → ℕ
  | .ff _ => 8
  | .att _ => 4
  | .head => 6

/-- The numbers of the full-size example (examples/full-size/config/policy.txt), typed by hand. A
line lm of the file is seen in the exponent: wcaf = 2^(lmaf - lt) = 2^(16 - 10). nGr, lg and ln are
derived from the lines L, ll, G, dh. u0 is the length of the table of exponentials at the lines S
and rx. kT is the logarithm of the largest table's rows. The scales in P are the reference's. -/
def Sz.ref : Sz :=
  { P := ppref, lt := 10, ll := 2, nGr := 12, lg := 3, lB := 6, ln := 7, u0 := 2307, la := 16,
    wcaf := 2 ^ (16 - 10), NAf := 3, wcad := 2 ^ (15 - 10), NAd := 1, wcar := 2 ^ (13 - 10),
    lmb := 16, wcq := 2 ^ (16 - 10), wcx := 2 ^ (16 - 10), lmS := 16, NAs := 1,
    wch := 2 ^ (13 - 10), wco := 2 ^ (16 - 10), lmbA := 14, wchf := 2 ^ (16 - 10), NHf := 4,
    wchd := 2 ^ (14 - 10), wchr := 2 ^ (13 - 10), lmbH := 15, kT := fun _ => 16, NC := ncBoth }

/-- The numbers of the small example (examples/accepted-proof/config/policy.txt), typed by hand and
derived as in "Sz.ref". The scales in P are the reference's; no shape and no place reads them. -/
def Sz.small : Sz :=
  { P := { ppref with T := 64, V := 512, layers := 8, d := 512, nq := 4, nkv := 2, ch := 128,
                      f := 1024, fe := 512, nexp := 4 },
    lt := 6, ll := 2, nGr := 2, lg := 1, lB := 4, ln := 7, u0 := 2307, la := 8,
    wcaf := 2 ^ (13 - 6), NAf := 3, wcad := 2 ^ (12 - 6), NAd := 1, wcar := 2 ^ (12 - 6),
    lmb := 13, wcq := 2 ^ (13 - 6), wcx := 2 ^ (13 - 6), lmS := 11, NAs := 1,
    wch := 2 ^ (12 - 6), wco := 2 ^ (13 - 6), lmbA := 13, wchf := 2 ^ (14 - 6), NHf := 1,
    wchd := 2 ^ (12 - 6), wchr := 2 ^ (12 - 6), lmbH := 13, kT := fun _ => 16, NC := ncBoth }

/-- The full-size example's numbers meet "OK" and "Fit". -/
theorem ref_ok : Sz.ref.OK ∧ Sz.ref.Fit := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    first | decide | (intro σ _; cases σ <;> simp [Sz.ref, Sz.lmP])

/-- The small example's numbers meet "OK" and "Fit". -/
theorem small_ok : Sz.small.OK ∧ Sz.small.Fit := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    first | decide | (intro σ _; cases σ <;> simp [Sz.small, Sz.lmP])

/-- At the full-size example's numbers the columns of af, ad, ar, b, qa, xbO, xbI, as, ah, ao, bA,
hf, hd, hr, bH, xbL, the first eleven in group 0, are these sixteen numbers. They were counted off
that example's config/layout.txt by a program outside Lean, and typed here by hand. The layout file
has no array for xbL: the sixteenth number is that of the last group's xbO. -/
theorem ref_cols :
    ([(Seg.ff 0, MatName.af 0), (.ff 0, .ad 0), (.ff 0, .ar), (.ff 0, .b), (.ff 0, .qa),
      (.ff 0, .xbO), (.ff 0, .xbI), (.att 0, .as 0), (.att 0, .ah), (.att 0, .ao), (.att 0, .bA),
      (.head, .hf 0), (.head, .hd), (.head, .hr), (.head, .bH), (.head, .xbL)].map
        fun p => Sz.ref.k p.1 p.2) =
      [5990, 3200, 324, 256, 1536, 400, 400, 7200, 360, 640, 512, 4816, 640, 15, 384, 400] := by
  decide +kernel

/-- The same at the small example's numbers, against its config/layout.txt. -/
theorem small_cols :
    ([(Seg.ff 0, MatName.af 0), (.ff 0, .ad 0), (.ff 0, .ar), (.ff 0, .b), (.ff 0, .qa),
      (.ff 0, .xbO), (.ff 0, .xbI), (.att 0, .as 0), (.att 0, .ah), (.att 0, .ao), (.att 0, .bA),
      (.head, .hf 0), (.head, .hd), (.head, .hr), (.head, .bH), (.head, .xbL)].map
        fun p => Sz.small.k p.1 p.2) =
      [247, 160, 14, 2048, 96, 20, 20, 120, 4, 32, 1024, 20, 16, 2, 1536, 20] := by
  decide +kernel

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.Sz.nameAt
#print axioms OnBytes.HonestTrace.lay
#print axioms OnBytes.HonestTrace.mulAdd_div
#print axioms OnBytes.HonestTrace.mulAdd_mod
#print axioms OnBytes.HonestTrace.le_ceilDiv_mul
#print axioms OnBytes.HonestTrace.part_col_lt
#print axioms OnBytes.HonestTrace.row_lt
#print axioms OnBytes.HonestTrace.mu_inj
#print axioms OnBytes.HonestTrace.mu_lt
#print axioms OnBytes.HonestTrace.mu_onto
#print axioms OnBytes.HonestTrace.ref_ok
#print axioms OnBytes.HonestTrace.small_ok
#print axioms OnBytes.HonestTrace.ref_cols
#print axioms OnBytes.HonestTrace.small_cols
