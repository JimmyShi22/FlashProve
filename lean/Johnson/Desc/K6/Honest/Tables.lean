-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Tables.lean: THE OUTPUT HEAD'S OWN ROUNDS, THE HONEST PROVER'S SIDE: THE
HIDDEN VALUES AND THE FOUR SUMS, as functions of the committed cells and of the challenges heard.
WHAT IT IS NOT. No prover: it plays no round, lays no mask and knows no transcript. Nothing is
claimed of it: not that the verifier accepts what is made of it, nothing on soundness, nothing on
what a proof hides. Section 3 holds equations between definitions, no more: three by unfolding, and
that the logits' second map in the form for use is the plain form, which calls UH. The tests of
section 4 are runs at one small synthetic example: they try the definitions and prove nothing.
WHAT IT IS. Definitions with code. The sub-protocol (Johnson/Desc/Kinds/Head.lean) has two rounds in
which hidden scalars are sent by themselves, and four masked sumchecks. For the first:
  wScalars   the nine sums of limb products of the stream's squares   the format's W_s
  pScalars   the seven products of the row's fields                   the format's P_i
For the second, each as a sum of weighted products of pairs of maps (Pairs.lean: PairSum), which
says at once the claimed sum, each round's polynomial and the end values:
  sqSum   the sums of squares           maps XG, XG            end values vL_4, vR_4
  prSum   the row's products            maps a, b, Rlo, Rhi    end values EV_0 .. EV_3
  nmSum   the reciprocal times the stream   maps R, SX         end values EN_0, EN_1
  lgSum   the logits                    maps act, UH           end values EH_0, EH_1
and the three claimed sums that the prover sends: prLead, nmLead, lgLead: the format's Cl_V, Cl_N,
Cl_H. The names on the right are those of the table "The scalars of the head's own steps" in
docs/format/11-4-output-head.md.
WHAT IS CALLED, WHAT IS WRITTEN A SECOND TIME, WHAT IS NEW. The cells are the structures Cells
(Johnson/Desc/Kinds/HeadLaw.lean) and NCells (Johnson/Desc/Kinds/HeadNormLaw.lean): integer cells of
the committed matrices and of the stream, and the head's weights. CALLED from these two files:
limbZ, str, wsqZ, rowZ, fieldE, prodE, act, UH, and, as two of the three claimed sums, trueNormed
and trueSum. WRITTEN A SECOND TIME: the sums over the positions in wScalars and pScalars: they are
normHeardAt's text, and heard_scalars says that the two texts are one term;
UH's text in uhMapOf, which has UH's two sums handed in (they are meant to be made once for a sum;
nothing here tries what a call costs): uhMapOf_eq says that it is uhMap, which calls UH.
NEW: the five limbs under the powers of gam (sqMap); the stream under the lookup's weights
(streamMap); the seven products under the powers of om (prLead, and the weights in prSum); how an
index of a sum is cut into feature and position; that a padded feature holds 0.
AN INDEX. A sum over n variables runs over the indices below 2^n, the first variable being the
highest bit. The sums of squares: feature k, position t: k T + t. The logits: t 2^lPd + k. The two
others: t. That is the order of the coordinates in the point that the verifier hands to each
sumcheck (Norm.lean: hearRest; HeadNorm.lean: hear; Head.lean: hear).
THE SAME MAPS ELSEWHERE IN THE LIBRARY. Tables after the same formulas, in the same order of the
bits, over the field K of that folder (Law/NoWrap.lean) in place of the program's words, are defined
in Johnson/Desc/Kinds/Law/: NormSquares.lean (AtS, at the point zS), NormProducts.lean (AtR),
Normed.lean (AtN, BtN), Lemma2b.lean (AtP, UtP, at the point zP). HeadSends.lean, K06Honest.lean and
K06HonestWhole.lean there speak of rounds whose hidden values are those tables' sums and their
values at the challenges. This file calls none of these seven files and states no tie to them;
TablesLaw.lean states ties to the tables of the first four.
LIMITS.
THE POINTS' LENGTHS ARE TESTED BY NOTHING HERE. A sum has as many variables as pV or zt has
coordinates, while the maps are cut, and the scalars and the claimed sums summed, by T = 2^lt. The
definitions are meant at pV.size = lt and zt.size = lt alone. At another length nothing refuses: a
sum may differ from its claimed sum and read cells at positions from T on, or agree with it on a
part of the positions only (the last tests of section 4 show each). Who fills pV and zt owes the
lengths.
Tokens and the next token are meant below V: UH reads the weights' column of the token that a
position is about (win: the next position's token; at the last position the next token), whatever it
is, while the claim on the weights that the verifier hands on sums over the vocabulary
entries below V.
Five limbs a feature of the stream, and one norm, are written in.
streamMap reads the weight of an entry (ew), as trueNormed does; the verifier's form on that end
value reads the weight of a block and the point inside a block (ewh, zl). The two agree where
ew k x = ewh k (x / S2) * eq zl (x % S2). The head's own class says this equation of its fields
(HeadCells.lean: In); the normalization's class (HeadNorm.lean: In), whose ew is read here, names
the fields and not the equation. The tests lay it (HeadNormLaw.lean: NPt.normIn); nothing here
enforces it. The verifier's forms count d / S2 blocks: the tests are at sizes where S2 divides d.
A map has a value at every index; a sum reads it below 2^n alone.
WHAT THE TESTS DO NOT TRY. No value is held against a written number here, no mask of the hiding
polynomial is laid, and the form that a masked sumcheck leaves is not made. By its own head comment
Johnson/Desc/ProofFile/Honest/K6/Toy.lean plays all rounds against the sub-protocol's own text and
holds the 69 sent scalars and 29 hidden values against numbers that were reckoned apart from Lean.

-/
import Johnson.Desc.K6.Honest.Pairs
import Johnson.Desc.Kinds.HeadNormLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Honest

open OnBytes (E)
open OnBytes.Desc.First (P6.rowProducts P6.summand)
open Norm (lt ls d lPd T S2)
open Law (ofInt limbZ str wsqZ rowZ fieldE prodE UH trueSum trueNormed)

section Definitions
variable [Sizes]

/-! ## 1. Hidden scalars that are sent by themselves -/

/-- The nine sums of limb products of the stream's squares, each summed over the positions under the
equality weights of the drawn point pV. -/
def wScalars (c : Law.NCells) (pV : Point) : List E :=
  (List.range 9).map fun s => ∑ t < T, eq pV t * ofInt (wsqZ c t s)

/-- The seven products of the row's fields a, b, Rlo, Rhi, summed likewise. -/
def pScalars (c : Law.NCells) (pV : Point) : List E :=
  (List.range 7).map fun n => ∑ t < T, eq pV t * prodE c t n

/-! ## 2. The four sums -/

/-- The map of the sums of squares, at the index k T + t: the five limbs of feature k of the stream
at position t under the powers of gam. A padded feature holds 0. -/
def sqMap (c : Law.NCells) (gam : E) (i : Nat) : E :=
  if i / T < d then ∑ l < 5, gam ^ l * ofInt (limbZ c (i % T) l (i / T)) else 0

/-- **The sums of squares.** The map times itself. The features are summed plainly, which lPd
coordinates 1/2 do up to the factor 2^-lPd; the positions under pV. In front stands the empty point
on the norms' numbers, as in the verifier's own text: here one norm is batched. -/
def sqSum (c : Law.NCells) (pV : Point) (gam : E) : PairSum :=
  { z := ((#[] : Point) ++ halves lPd ++ pV).toList
    maps := [sqMap c gam, sqMap c gam]
    pairs := [(1, 0, 1)] }

/-- **The row's products.** The maps are the four fields at a position; product number n of the
row's list stands under om^n. -/
def prSum (c : Law.NCells) (pV : Point) (om : E) : PairSum :=
  { z := pV.toList
    maps := (List.range 4).map fun j t => fieldE c t j
    pairs := P6.rowProducts.zipIdx.map fun x => (om ^ x.2, x.1.1, x.1.2) }

/-- The claimed sum of the row's products: the seven hidden products under the powers of om. -/
def prLead (c : Law.NCells) (pV : Point) (om : E) : E :=
  let P := pScalars c pV
  ∑ n < 7, om ^ n * P.getD n 0

section Lookup
variable [FinalNorm.In]

/-- The reciprocal at position t. -/
def recMap (c : Law.NCells) (t : Nat) : E := (rowZ c t).R.const

/-- The stream at position t, its features summed under the lookup's weights of the key remLow. -/
def streamMap (c : Law.NCells) (t : Nat) : E :=
  ∑ x < d, FinalNorm.ew .remLow x * ofInt (str c t x)

/-- **The reciprocal times the stream**, at the lookup's point on the positions. -/
def nmSum (c : Law.NCells) : PairSum :=
  { z := FinalNorm.zt.toList
    maps := [recMap c, streamMap c]
    pairs := [(1, 0, 1)] }

/-- Its claimed sum. -/
def nmLead (c : Law.NCells) : E := trueNormed c

variable [Policy] [Request] [Token] [In]

/-- The activation at the index t 2^lPd + k. A padded feature holds 0. -/
def actMap (c : Law.Cells) (i : Nat) : E :=
  if i % 2 ^ lPd < d then ofInt (Law.act c (i / 2 ^ lPd) (i % 2 ^ lPd)) else 0

/-- The second map of the head's own sumcheck at the same index: at a checked position, under the
top digit's weights, the weights' column of the token that the position is about (win: the next
position's token; at the last position the next token) less that of each vocabulary entry. A padded
feature holds 0. -/
def uhMap (c : Law.Cells) (i : Nat) : E :=
  if i % 2 ^ lPd < d then UH c (i % 2 ^ lPd) (i / 2 ^ lPd) else 0

/-- The share of that map which hangs on the feature alone: entry k, for k < d, is the weights of
feature k summed over the vocabulary entries under the top digit's weights. -/
def uhCol (c : Law.Cells) : Array E :=
  ((List.range d).map fun k => ∑ v < V, ew .marginTop v * ofInt (c.Wh k v)).toArray

/-- uhMap for use: the sum of the top digit's weights (w) and the array of the sums over the
vocabulary (col) are handed in: they are meant to be made once for a sum, not at every index. At
w = wx .marginTop and col = uhCol c it is uhMap: uhMapOf_eq in section 3. -/
def uhMapOf (c : Law.Cells) (w : E) (col : Array E) (i : Nat) : E :=
  if i % 2 ^ lPd < d then
    if checked (i / 2 ^ lPd) then
      w * ofInt (c.Wh (i % 2 ^ lPd) (win (i / 2 ^ lPd))) - col.getD (i % 2 ^ lPd) 0
    else 0
  else 0

/-- **The logits.** The positions under the lookup's point, the features plainly. The maps are
actMap and uhMap (lgSum_eq in section 3); the second stands in the form whose two sums are meant to
be made once. -/
def lgSum (c : Law.Cells) : PairSum :=
  let w := wx .marginTop
  let col := uhCol c
  { z := (FinalNorm.zt ++ halves lPd).toList
    maps := [actMap c, uhMapOf c w col]
    pairs := [(1, 0, 1)] }

/-- Its claimed sum: 2^-lPd times the sum over positions and true features. -/
def lgLead (c : Law.Cells) : E := OnBytes.invE (2 ^ lPd) * trueSum c

end Lookup

/-! ## 3. The same terms as in HeadNormLaw.lean and HeadLaw.lean

Three definitions fill the verifier's classes from the cells: normHeardAt and finalHeardAt
(HeadNormLaw.lean), heardAt (HeadLaw.lean). The sixteen scalars and two of the three claimed sums of
this file are the terms that stand there: three equations by unfolding. The third claimed sum and
the ten end values have no such equation: those definitions leave them empty. Nothing is sent in
this file, and what a prover sends of these values bears a mask. -/

/-- A value as a hidden scalar whose variable is the constant form. -/
def known (x : E) : Hid := { var := ((x : E) : Form) }

/-- The fields W and P of normHeardAt (HeadNormLaw.lean) are wScalars and pScalars, entry by entry,
each as a constant form.
WHAT IT IS NOT: it holds by unfolding definitions and says only that two texts name the same terms.
Nothing on the verifier's decision, on the masks under which the scalars are sent, or on whether the
cells meet any equation. -/
theorem heard_scalars (c : Law.NCells) (pV : Point) :
    (Law.normHeardAt c pV).W = ((wScalars c pV).map known).toArray ∧
      (Law.normHeardAt c pV).P = ((pScalars c pV).map known).toArray := by
  unfold wScalars pScalars
  rw [List.map_map, List.map_map]
  exact ⟨rfl, rfl⟩

/-- The claimed sum in finalHeardAt (HeadNormLaw.lean) is nmLead, as a constant form.
WHAT IT IS NOT: it holds by unfolding definitions. That nmLead is the total of nmSum is not stated:
a test of section 4 tries it at one example. -/
theorem heard_normed [FinalNorm.In] (c : Law.NCells) :
    (Law.finalHeardAt c).normed.claimed = known (nmLead c) := rfl

/-- The claimed sum in heardAt (HeadLaw.lean) is lgLead, as a constant form.
WHAT IT IS NOT: it holds by unfolding definitions. That lgLead is the total of lgSum is not stated:
a test of section 4 tries it at one example. -/
theorem heard_logits [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Law.Cells) :
    (Law.heardAt c).logits.claimed = known (lgLead c) := rfl

/-! ### The logits' second map: the form for use is the plain form -/

/-- Entry k of uhCol, for a true feature k, is the sum that UH has in its place. -/
theorem uhCol_getD [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Law.Cells) (k : Nat)
    (h : k < d) : (uhCol c).getD k 0 = ∑ v < V, ew .marginTop v * ofInt (c.Wh k v) := by
  unfold uhCol
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range h]
  rfl

/-- At every index the form for use, at the two sums as lgSum binds them, is uhMap, which calls UH.
WHAT IT IS NOT: an equation between two definitions of this file, by unfolding and by reading an
array at an index; no law of the field is used. Nothing on the verifier, and nothing on cost. -/
theorem uhMapOf_eq [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Law.Cells) (i : Nat) :
    uhMapOf c (wx .marginTop) (uhCol c) i = uhMap c i := by
  unfold uhMapOf uhMap
  by_cases h : i % 2 ^ lPd < d
  · rw [if_pos h, if_pos h, uhCol_getD c _ h]
    rfl
  · rw [if_neg h, if_neg h]

/-- The logits' sum is the sum of the maps actMap and uhMap.
WHAT IT IS NOT: as uhMapOf_eq. -/
theorem lgSum_eq [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Law.Cells) :
    lgSum c = { z := (FinalNorm.zt ++ halves lPd).toList
                maps := [actMap c, uhMap c]
                pairs := [(1, 0, 1)] } := by
  have h : uhMapOf c (wx .marginTop) (uhCol c) = uhMap c := funext (uhMapOf_eq c)
  show ({ z := (FinalNorm.zt ++ halves lPd).toList
          maps := [actMap c, uhMapOf c (wx .marginTop) (uhCol c)]
          pairs := [(1, 0, 1)] } : PairSum) = _
  rw [h]

end Definitions

/-! ## 4. Tests at a small synthetic example

Four positions, six features (two more are padding) in blocks of two, five vocabulary entries.
Synthetic cells and weights, made-up points and challenges; the cells meet none of the
normalization's equations, which these tests do not read. WHAT IS THE VERIFIER'S OWN TEXT IN A TEST:
the start form of the sums of squares, the rule by which a round's polynomial is summed (the masked
sumcheck's complete), ten forms on claimed sums and end values, and the claim on the weights. For
the forms the verifier's classes are filled with the sum's values as hidden scalars and with the
reads in truth (the sums of the cells: normReadsAtCells, readsAt), and these forms must then be 0.
WHAT IS NOT: the end term, that is the summand on the end values as shown. The verifier's text has
it only as the argument of the form that a masked sumcheck leaves, which needs the rounds and is not
made here. So the end term is written by hand in three tests (a product of two values); the
products' test calls the part's own summand. Each test takes the cells twice, once for the filling
and once for the verifier's side: with one cell, weight or token turned on one side it must say
no. -/

namespace TablesTest

open Part.MaskedSum (valueAt complete)

@[reducible] def sizes : Sizes :=
  { lt := 2, ls := 1, d := 6, MF := 40, KF := 20, epsF := 1, V := 5, sh := 7, F := 24 }
@[reducible] def policy : Policy := { C := 300, theta := 200, cap := 1 }
/-- The last position is checked, the first is not. -/
@[reducible] def request : Request := { tok := fun t => (2 * t + 1) % 5, r := 1, e := 4 }

attribute [local instance] sizes policy

/-- A matrix's number. -/
def num : Matrix → Nat
  | .wide => 1 | .act => 2 | .row => 3

def cells : Law.NCells :=
  { cell := fun m f t => ((29 * num m + 7 * f + 13 * t + f * t) % 23 : Nat) - 11
    Wh := fun k v => ((3 * k + 7 * v + k * v) % 17 : Nat) - 8
    stream := fun f t => ((5 * f + 3 * t + 2 * f * t) % 19 : Nat) - 9 }

/-- The cells with 1 added to one cell of a matrix, to one cell of the stream, to one weight. -/
def turnCell (m : Matrix) (f t : Nat) : Law.NCells :=
  { cells with cell := fun m' f' t' =>
      cells.cell m' f' t' + if num m' == num m && f' == f && t' == t then 1 else 0 }
@[inherit_doc turnCell] def turnStream (f t : Nat) : Law.NCells :=
  { cells with stream := fun f' t' => cells.stream f' t' + if f' == f && t' == t then 1 else 0 }
@[inherit_doc turnCell] def turnWeight (k v : Nat) : Law.NCells :=
  { cells with Wh := fun k' v' => cells.Wh k' v' + if k' == k && v' == v then 1 else 0 }

/-- Every element has all three coordinates. -/
def el (a b c : Nat) : E := ⟨a.toUInt64, b.toUInt64, c.toUInt64⟩

def pV : Point := #[el 3 1 4, el 1 5 9]
def gam : E := el 2 6 5
def om : E := el 3 5 8
def beta : E := el 9 7 9
/-- From the lookup: its points, and made-up weights of the blocks. -/
def nPt : Law.NPt :=
  { zt := #[el 2 7 1, el 8 2 8], zl := #[el 1 8 2], ewh := fun k i => el (k.idx + 2) (i + 1) 7 }
def hPt : Law.Pt := { zt := nPt.zt, zl := nPt.zl, ewh := fun k i => el (k.idx + 11) (i + 3) 5 }
/-- Challenges and masks, as many as are asked for. -/
def chal (seed n : Nat) : List E :=
  (List.range n).map fun i => el (seed + i) (2 * i + 1) (seed * i + 3)

/-- All forms are the constant 0. -/
def allZero (l : List Form) : Bool :=
  l.all fun f => f.const == 0 && f.slots.isEmpty && f.ents.isEmpty

/-- A sum's polynomial in the further variable, at beta, is the given end term on the end values as
they are shown: each plus beta times its mask. -/
def endTerm (s : PairSum) (rs : List E) (term : (Nat → E) → E) : Bool :=
  let m := chal 40 s.maps.length
  valueAt (s.inY rs m) beta == term fun j => (s.ends rs).getD j 0 + beta * m.getD j 0

/-- The polynomials of a sum's rounds at the challenges rs; the last is the one in the further
variable. -/
def polys (s : PairSum) (rs : List E) : List (List E) :=
  ((List.range s.z.length).map fun i => s.round (rs.take i)) ++ [s.inY rs (chal 40 s.maps.length)]

/-- Polynomials of three coefficients that continue one another as the verifier sums them: from a
polynomial's two higher coefficients and the running claim the masked sumcheck's own function
(complete, at a variable that is summed at the point z) makes the polynomial again. That is:
(1 - z) g(0) + z g(1) is the running claim. The running claim is the given sum at the first, and at
each later one the polynomial before at its challenge. The further variable, which has no point in
z, is summed at 0. -/
def chain (z rs : List E) (sum : E) (g : List (List E)) : Bool :=
  g.zipIdx.all fun x =>
    x.1.length == 3 && complete (.point (z.getD x.2 0) 3) (x.1.drop 1)
      (if x.2 == 0 then sum else valueAt (g.getD (x.2 - 1) []) (rs.getD (x.2 - 1) 0)) == x.1

/-- Coefficient j of polynomial number i, plus 1. -/
def turnPoly (g : List (List E)) (i j : Nat) : List (List E) :=
  g.zipIdx.map fun x =>
    if x.2 == i then x.1.zipIdx.map fun y => if y.2 == j then y.1 + 1 else y.1 else x.1

/-- The sums of squares: the sum is the verifier's start form on the nine scalars, and the rounds go
on from it; its second and third form on the end values; the end term, by hand. -/
def squaresFit (c c' : Law.NCells) : Bool :=
  let s := sqSum c pV gam
  let rs := chal 50 (lPd + lt)
  let _ := nPt.normIn
  let _ : Norm.Heard := { Law.normHeardAt c' pV with
    gam := gam, squares := { r := rs.toArray, ends := ((s.ends rs).map known).toArray } }
  let _ := Law.finalHeardAt c'
  let _ := Law.normReadsAtCells c'
  s.z.length == lPd + lt && (s.ends rs).length == 2
    && s.total == (Norm.squaresStart ((wScalars c' pV).map known).toArray gam #[]).const
    && chain s.z rs (Norm.squaresStart ((wScalars c' pV).map known).toArray gam #[]).const
        (polys s rs)
    && allZero (Norm.squareForms.drop 1)
    && endTerm s rs fun v => v 0 * v 1

/-- The row's products: the verifier's first form on the claimed sum and the seven scalars; the
rounds go on from the claimed sum; its last four forms on the end values; the end term, by the
part's own summand. -/
def productsFit (c c' : Law.NCells) : Bool :=
  let s := prSum c pV om
  let rs := chal 60 lt
  let _ := nPt.normIn
  let _ : Norm.Heard := { Law.normHeardAt c' pV with
    om := om, products := { r := rs.toArray, claimed := known (prLead c pV om),
                            ends := ((s.ends rs).map known).toArray } }
  let _ := Law.finalHeardAt c'
  let _ := Law.normReadsAtCells c'
  s.z.length == lt && (s.ends rs).length == 4 && s.total == prLead c pV om
    && chain s.z rs (prLead c' pV om) (polys s rs)
    && allZero (Norm.productForms.eraseIdx 1)
    && endTerm s rs fun v => P6.summand (fun n => om ^ n) v

/-- The sum of the reciprocal times the stream at the made-up point. -/
def nmAt (c : Law.NCells) : PairSum :=
  let _ := nPt.normIn
  nmSum c

/-- The reciprocal times the stream: the claimed sum, and the rounds go on from it; the verifier's
second and third form on the end values; the end term, by hand. -/
def normedFit (c c' : Law.NCells) : Bool :=
  let _ := nPt.normIn
  let s := nmAt c
  let rs := chal 70 lt
  let _ := Law.normHeardAt c' pV
  let _ : FinalNorm.Heard :=
    { normed := { r := rs.toArray, ends := ((s.ends rs).map known).toArray } }
  let _ := Law.normReadsAtCells c'
  s.z.length == lt && (s.ends rs).length == 2 && s.total == nmLead c'
    && chain s.z rs (nmLead c') (polys s rs)
    && allZero (FinalNorm.normedForms.drop 1)
    && endTerm s rs fun v => v 0 * v 1

/-- The logits' sum at a request and a next token. -/
def lgAt (c : Law.NCells) (q : Request) (y : Nat) : PairSum :=
  let _ := q
  let _ : Token := ⟨y⟩
  let _ := nPt.normIn
  let _ := hPt.headIn
  lgSum c.toCells

/-- The logits: the claimed sum, and the rounds go on from it; the verifier's second form on the
first end value; the claim on the weights, which says what the second is; the end term, by hand. -/
def logitsFit (c c' : Law.NCells) (q q' : Request) (y y' : Nat) : Bool :=
  let s := lgAt c q y
  let rs := chal 80 (lt + lPd)
  let _ := q'
  let _ : Token := ⟨y'⟩
  let _ := nPt.normIn
  let _ := hPt.headIn
  let _ := Law.normHeardAt c' pV
  let _ := Law.finalHeardAt c'
  let _ : Heard := { logits := { r := rs.toArray, ends := ((s.ends rs).map known).toArray } }
  let _ := Law.normReadsAtCells c'
  let _ := Law.readsAt c'.toCells
  s.z.length == lt + lPd && (s.ends rs).length == 2 && s.total == lgLead c'.toCells
    && chain s.z rs (lgLead c'.toCells) (polys s rs)
    && allZero (logitForms.drop 1)
    && forTheMerge.value.var.const == (∑ v < V, ∑ k < d,
        forTheMerge.onVocabulary v * eq forTheMerge.onFeatures k * ofInt (c'.Wh k v))
    && endTerm s rs fun v => v 0 * v 1

-- The sizes are what the tests are meant for: two padded features, and a block does not straddle.
#guard lPd == 3 && T == 4 && S2 == 2
#guard (wScalars cells pV).length == 9 && (pScalars cells pV).length == 7

-- Each filling fits the verifier's text at the same cells.
#guard squaresFit cells cells
#guard productsFit cells cells
#guard normedFit cells cells
#guard logitsFit cells cells request request 2 2

-- No sum is 0, and no end value: a test above is not met by empty hands.
#guard [(sqSum cells pV gam).total, prLead cells pV om, (nmAt cells).total,
  (lgAt cells request 2).total].all (· != 0)
#guard ((sqSum cells pV gam).ends (chal 50 5) ++ (prSum cells pV om).ends (chal 60 2)
  ++ (nmAt cells).ends (chal 70 2) ++ (lgAt cells request 2).ends (chal 80 5)).all (· != 0)

-- NEGATIVE TESTS. One cell of the stream: a low limb, the highest limb of the last feature.
#guard !squaresFit cells (turnStream 0 0) && !squaresFit (turnStream 29 3) cells
#guard !normedFit cells (turnStream 0 0) && !normedFit (turnStream 29 3) cells
-- One digit of the row: of a, b, Rlo, Rhi for the products; of the reciprocal for normed.
#guard !productsFit cells (turnCell .row 58 0) && !productsFit (turnCell .row 61 1) cells
  && !productsFit cells (turnCell .row 63 2) && !productsFit (turnCell .row 80 3) cells
  && !productsFit cells (turnCell .row 85 0)
#guard !normedFit cells (turnCell .row 80 1) && !normedFit (turnCell .row 85 2) cells
-- A digit that is in none of the four fields is read by neither.
#guard productsFit cells (turnCell .row 64 0) && normedFit cells (turnCell .row 79 0)
-- One cell of the activations, either limb; one weight; the next token; a token; the stretch.
#guard !logitsFit cells (turnCell .act 0 1) request request 2 2
  && !logitsFit (turnCell .act 11 3) cells request request 2 2
#guard !logitsFit cells (turnWeight 5 4) request request 2 2
  && !logitsFit (turnWeight 0 0) cells request request 2 2
#guard !logitsFit cells cells request request 2 3
#guard !logitsFit cells cells request
  { request with tok := fun t => if t == 2 then 1 else request.tok t } 2 2
#guard !logitsFit cells cells request { request with r := 0 } 2 2
-- The first position is not checked: the column of the token that it is about (token 1) is not
-- read; token 0 is read by no position.
#guard logitsFit cells cells request
  { request with tok := fun t => if t ≤ 1 then 4 else request.tok t } 2 2
-- A token, or a next token, that is no vocabulary entry, on both sides: the claim on the weights,
-- which sums over the vocabulary entries, is not met.
#guard !logitsFit cells cells { request with tok := fun t => if t == 2 then 5 else request.tok t }
  { request with tok := fun t => if t == 2 then 5 else request.tok t } 2 2
#guard !logitsFit cells cells request request 5 5

-- THE TWO TESTS ON POLYNOMIALS CAN FAIL BY THEMSELVES. The chain: the sum plus 1; each coefficient
-- of each round's polynomial plus 1, and the constant of the last. (The two higher coefficients of
-- the last are read at beta alone: by the end term.)
/-- The four sums with their challenges. -/
def four : List (PairSum × List E) :=
  [(sqSum cells pV gam, chal 50 5), (prSum cells pV om, chal 60 2), (nmAt cells, chal 70 2),
   (lgAt cells request 2, chal 80 5)]
#guard four.all fun x => chain x.1.z x.2 x.1.total (polys x.1 x.2)
  && !chain x.1.z x.2 (x.1.total + 1) (polys x.1 x.2)
  && !chain x.1.z x.2 x.1.total (turnPoly (polys x.1 x.2) x.1.z.length 0)
  && (List.range x.1.z.length).all fun i => (List.range 3).all fun j =>
      !chain x.1.z x.2 x.1.total (turnPoly (polys x.1 x.2) i j)
-- The end term: another term.
#guard !endTerm (sqSum cells pV gam) (chal 50 5) fun v => v 0 * v 1 + 1
#guard !endTerm (prSum cells pV om) (chal 60 2) fun v => P6.summand (fun n => om ^ (n + 1)) v
#guard !endTerm (nmAt cells) (chal 70 2) fun v => v 0 * v 0
#guard !endTerm (lgAt cells request 2) (chal 80 5) fun v => v 1 * v 1

/-! ### A point of another length: nothing refuses -/

/-- A point without its last coordinate; with one more. -/
def short (p : Point) : Point := p.extract 0 (p.size - 1)
@[inherit_doc short] def long (p : Point) : Point := p.push (el 6 2 6)

/-- Each sum beside what it is meant to equal, at a given point on the positions. -/
def sqBoth (p : Point) : E × E :=
  ((sqSum cells p gam).total,
   (Norm.squaresStart ((wScalars cells p).map known).toArray gam #[]).const)
@[inherit_doc sqBoth] def prBoth (p : Point) : E × E :=
  ((prSum cells p om).total, prLead cells p om)
@[inherit_doc sqBoth] def nmBoth (c : Law.NCells) (p : Point) : E × E :=
  let _ := ({ nPt with zt := p } : Law.NPt).normIn
  ((nmSum c).total, nmLead c)
@[inherit_doc sqBoth] def lgBoth (p : Point) : E × E :=
  let _ := request
  let _ : Token := ⟨2⟩
  let _ := ({ nPt with zt := p } : Law.NPt).normIn
  let _ := hPt.headIn
  ((lgSum cells.toCells).total, lgLead cells.toCells)
/-- The two are one. -/
def same (x : E × E) : Bool := x.1 == x.2

-- At lt coordinates the two are one.
#guard same (sqBoth pV) && same (prBoth pV) && same (nmBoth cells nPt.zt) && same (lgBoth nPt.zt)
-- The sums of squares part at either other length: the index is cut by T.
#guard !same (sqBoth (short pV)) && !same (sqBoth (long pV))
-- One coordinate more: two sums read positions from T on, which their claimed sums do not.
#guard !same (prBoth (long pV)) && !same (nmBoth cells (long nPt.zt))
#guard (nmBoth (turnCell .row 80 4) (long nPt.zt)).1 != (nmBoth cells (long nPt.zt)).1
  && (nmBoth (turnCell .row 80 4) (long nPt.zt)).2 == (nmBoth cells (long nPt.zt)).2
-- The logits do not part there: no position from T on is checked.
#guard same (lgBoth (long nPt.zt))
-- One coordinate less: sum and claimed sum agree, AND BOTH LEAVE OUT THE UPPER HALF OF THE
-- POSITIONS: no comparison of the two shows it.
#guard same (prBoth (short pV)) && same (nmBoth cells (short nPt.zt))
  && same (lgBoth (short nPt.zt))
#guard nmBoth (turnCell .row 80 3) (short nPt.zt) == nmBoth cells (short nPt.zt)
  && nmBoth (turnCell .row 80 3) nPt.zt != nmBoth cells nPt.zt

end TablesTest

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.heard_scalars
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.heard_normed
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.heard_logits
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.uhCol_getD
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.uhMapOf_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.lgSum_eq
