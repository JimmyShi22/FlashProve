-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Cs.lean: the code switch (CS), a step of the proximity test of the first toy (a product test):
how the verifier moves its claim from what a fold hands on to one row on the next stage's oracle
message.

In a code switch the prover sends a new oracle message under new codes; the verifier reads the old
one at drawn positions and replaces its linear claim on the old message by one linear claim on the
new.
Definitions that compute, with tests (#guard). No theorem. No Mathlib. Generic in all sizes; total.

The text: the description of that toy that belongs to the programs (the C++ implementation that
comes with this Lean code), its Part 4 (sections 0 to 5), with Part 3's section 2.5 (what a fold
hands on). One writer there, one reader here.

The words. The head of Fmt/M1Types.lean says what the first toy's prover claims and how the
verifier's decision is divided among this folder's files. A stage (`Stage`, Fmt/M1Types.lean) is the
sizes at one oracle message of the proximity test: a main code C, a mask code Z, 2^k main rows, 2^h
mask rows, t positions to draw. A row on an oracle message (`GRow`) is a linear equation on its
entries: coefficients c on the main table, d on the mask table, and a target t. A tail is the r
entries that a code (`Code`, Fmt/M1Codes.lean) encodes beside a message. A draw is one position that
the verifier draws; a column (`Col`) is what the old tree opens there.

What CS is. A fold leaves three virtual rows (the folded main row M*, the folded old mask row W*,
the folded fresh mask row P*, with their folded tails) and one claim
<c, M*> + <d0, W*> + <d1, P*> = t. (An `SRow` is that claim.) The prover sends a new oracle message
g under the next stage's codes, which is to hold: in its main table M* (entry j at index j); in its
mask table, from index 0 on, W* | P* | the main tail | the old mask's tail | the fresh mask's tail;
then free room; at the last index the pad of g's sample. The verifier draws positions of the old
code and one element theta, reads the old tree's columns there, and makes rows on g (Part 4, 3 (c)):
    number 0: the carried claim, now on g's entries;
    number 1: g's sample row (made by `sampleRow`, Fmt/M1Send.lean: an argument here);
    number 2 + 3 (i - 1) + 0, 1, 2: for the i-th draw, in the order drawn, repeats counted:
      "what g holds, encoded again under the old main code (old mask code, twice), has at the drawn
      position the symbol that the old tree shows after folding".
It batches them under 1, theta, theta^2, .. (3 (e)). No equation is tested here: all is put off into
the new row.

Main names:
  `csFits old new`: of Part 4, 2's public conditions on the sizes those that are tested at a switch:
    two tie the two stages (2^k' l' = l; 2 l_zk + r + 2 r_zk + 1 ≤ 2^h' l'_zk), two bound h by k in
    each of them (h' ≤ k'; h ≤ k). (Primed: the new stage. l and r: the main code's message length
    and tail; l_zk and r_zk: the mask code's.) The others (all message lengths are powers of two;
    every stage but the last has k ≥ 1; the last has k = 0) are tested in `stagesOK`
    (Fmt/M1Dec.lean).
  `yOf f h s col`: 3 (b): the three folded symbols of a column: the main symbols at all of the
    fold's challenges, both masks' at the first h.
  `csRows`: 3 (c): all rows.
  `csStepLit`: 3 (e): their sum under the powers of theta: c on g's main table (2^k' l' entries), d
    on g's mask table (2^h' l'_zk entries).
  `addPre`, `addDraw`, `csStep`: `csStep` is the form that the decision runs (`blocks`,
    Fmt/M1All.lean).
  `foldRows`, `csOwnG`: the honest side (Part 4, 2 (1)).

Why `csStep` has its form: the carried claim and the sample row are made as in `csStepLit`; then,
draw by draw, the three rows are not written out: their entries lie in the base field, so that a
power of theta is multiplied by them coordinate by coordinate (`scaleE` for `mulE`: `mulE_ofF'`,
Fmt/FieldEFast.lean); on the mask table the three rows stand on stretches that do not meet, so that
one short list is added; entries at which a row is 0 are left alone. Lists and structural recursion:
no index.

This library's own, not the text's.
  (1) The output lies on g's own tables. In the programs the last stage's group has formally one row
    variable, with a second main row that nobody sent, c' at the indices 2 j, and that variable is
    then fixed at 0 (Part 4, 5.6): at k' = 0 that step is the identity on what stands here.
  (2) Totality: an entry beyond an array's end is 0; a vector longer than its room is cut.
  (3) The number of draws is not held against the stage's t.

What the tests show, and what not. They run a prover of this library's own at tiny sizes, in the
toy's two
shapes (k = 2, h = 0 into k' = h' = 1; k = h = 1 into k' = h' = 0), and in the second shape with a
mask code shorter than the main code (`CsOwn.o3`): rows and tails made up, folded, laid into g by
`csOwnG`; the old columns are encodings by `symE` (Fmt/M1Codes.lean), which is other code than the
generator's rows used here. Then: every row holds of g; the batched row holds; there are 2 + 3 t
rows; a repeated position counts twice; with one opened symbol changed, the batched row fails.
`csStep` gives `csStepLit`'s values, every coefficient and the target, in every one of these runs
(at the toy's real sizes too, tried once outside this file: 73 draws on 4,096 + 512 entries: equal;
about 2 s for about 7.6 s by the evaluator). Here these are tests. The theorem is in Fmt/M1CsEq.lean
(`csStep_eq`): `csStep` = `csStepLit` for all arguments, no hypothesis (every entry of the sum so
far is the result of an addition, so adding 0 changes nothing there).
And the new target is the text's own closed formula (3 (e)), computed apart: that alone holds the
order of batching (rows that hold give a batched row that holds in any order).
Reading a mask row at x in the place of x modulo the mask code's length is not tested, because it
makes no difference. The codes' points read the low bits of x alone.
But prover, rows and step are all written from one reading of one text: these tests show that the
reading is consistent, not that it is the programs'.
A second reading: Fmt/M1Ref.lean compares both switches of a tiny run, every coefficient and both
targets, with a reference program that another writer wrote from the same text: they agree, the
order of batching too.
The answers to questions about the programs (in words; one writer there): yes to:
  the order of batching as above;
  the i-th main (old mask, fresh mask) symbol of an opened column is row i, rows that nobody sent
    are 0;
  on g's own tables their step 5.6 is the identity, and nothing of the formal second row enters g's
    sample row;
  at every stage of the toy the mask code has the main code's length, so that a mask row is read at
    the drawn position itself. The free room of an honest g holds uniform elements.
The programs print, for both switches, the target, the three folded symbols at the first draw and
three coefficients of the new row, of an honest proof. The programs' own proof files are here. These
seven values a switch are fourteen of the nineteen of Fmt/M1Targets.lean. Lean computes the nineteen
from the bytes of their honest proofs, and they agree (Fmt/M1FullProgPTv.lean,
Fmt/M1FullProgPRv.lean, Fmt/M1FullProgPFv.lean); the verdicts on their honest, altered and false
files are in Fmt/M1FullProg*.lean, Run/M1Engine*.lean. These are tests when these files compile, no
theorem.

Limits: this file does not say what the sample row, the fold or the string of blocks (Part 4, 5) is:
other files (Fmt/M1Send.lean; Fmt/M1Fold.lean; `decWith`, Fmt/M1Dec.lean).
It does not say that the opened columns belong to the old root. That is the strict reader's
(`readOpens`, Fmt/Rules8.lean). The lenient reader compares no root and leaves it to the compiled
verifier (Run/ParseLax.lean).
The tests of form that the programs make inside CS (their answers' annex D, which completes Part 4,
4): none is made here. `csStep` takes values: a word that is not below p would be taken modulo p
(Fmt/FieldE.lean) and not refused.
Where these five tests of form stand, by reading the reader of a chain's file (this file has no
theorem on it):
  (i) the answer in canonical form: an item "answer" is read as three elements, each refused if not
    below p (Fmt/Rules8.lean: `readItem`; Fmt/Rules1.lean: `rdElt`);
  (ii) every opened symbol likewise (Fmt/Rules7.lean: `rdOpening`);
  (iii) as many columns and salts as the list has positions, as many digests as the walk takes, no
    count from the file; nothing behind the last item (`rdOpening`; `wholeChain`);
  (iv) the work test (Fmt/Rules5.lean: `Chain.queryW`) stands in the strict reader alone. The
    lenient reader (Run/ParseLax.lean) leaves it to the typed verifier, whose protocol with tests
    accepts only if all tests are passed (Iop/Grind.lean: `InteractiveOracleProof.grind`);
  (v) positions and theta are drawn from the chain's blocks, never read (Fmt/Rules8.lean: `step`),
    but for this: where the plan has a list of positions in the file, that list is read and compared
    with the list derived from the draw, and the file is refused if they differ (`readList`).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Types

namespace Fmt.M1

/-- The public conditions on a switch from the old stage into the new one that are tested here (the
head lists them). -/
def csFits (old new : Stage) : Bool :=
  2 ^ new.k * new.C.l == old.C.l &&
    decide (2 * old.Z.l + old.C.r + 2 * old.Z.r + 1 ≤ 2 ^ new.h * new.Z.l) &&
    decide (new.h ≤ new.k) && decide (old.h ≤ old.k)

/-- the three folded symbols of a column -/
def yOf (f : Fld) (h : Nat) (s : SRow) (c : Col) : E × E × E :=
  (foldV f s.g c.main, foldV f (s.g.take h) c.mask, foldV f (s.g.take h) c.fresh)

/-- A vector of n entries with w from the index o on, and 0 elsewhere; what of w has no room is
cut. -/
def layAt (n o : Nat) (w : List E) : Array E :=
  Array.ofFn (n := n) fun i => if o ≤ i.val then w.getD (i.val - o) Fld.zeroE else Fld.zeroE

/-- the number of rows at t draws -/
def nRows (t : Nat) : Nat := 2 + 3 * t

/-- one draw's three rows -/
def drawRows (f : Fld) (old : Stage) (nM nD : Nat) (s : SRow) (x : Nat) (cl : Col) : List GRow :=
  let y := yOf f old.h s cl
  let x' := cp old.Z x
  let lz := old.Z.l
  let gm := (genM old.Z x').map Fld.ofF
  let gt := (genT old.Z x').map Fld.ofF
  [⟨layAt nM 0 ((genM old.C x).map Fld.ofF), layAt nD (2 * lz) ((genT old.C x).map Fld.ofF), y.1⟩,
   ⟨#[], addV f (layAt nD 0 gm) (layAt nD (2 * lz + old.C.r) gt), y.2.1⟩,
   ⟨#[], addV f (layAt nD lz gm) (layAt nD (2 * lz + old.C.r + old.Z.r) gt), y.2.2⟩]

/-- All rows on the new oracle message, in the order of batching; `none` if a drawn position has no
column. -/
def csRows (f : Fld) (old new : Stage) (s : SRow) (sample : GRow)
    (xs : List Nat) (col : Nat → Option Col) : Option (List GRow) :=
  let nM := 2 ^ new.k * new.C.l
  let nD := 2 ^ new.h * new.Z.l
  let carried : GRow :=
    ⟨layAt nM 0 (fitL Fld.zeroE old.C.l s.c.toList),
      addV f (layAt nD 0 (fitL Fld.zeroE old.Z.l s.d0.toList))
        (layAt nD old.Z.l (fitL Fld.zeroE old.Z.l s.d1.toList)),
      s.t⟩
  let smp : GRow := ⟨layAt nM 0 sample.c.toList, layAt nD 0 sample.d.toList, sample.t⟩
  (xs.foldr (fun x (acc : Option (List GRow)) =>
    match acc, col x with
    | some rs, some cl => some (drawRows f old nM nD s x cl ++ rs)
    | _, _ => none) (some [])).map fun rs => carried :: smp :: rs

/-- The code switch, literally: the rows, then their sum under the powers of theta. The meaning of
`csStep`. -/
def csStepLit (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List Nat)
    (theta : E) (col : Nat → Option Col) : Option GRow :=
  (csRows f old new s sample xs col).map (sumRows f theta)

/-- b added onto the front of a; a's length is kept -/
def addPre (f : Fld) : List E → List E → List E
  | a :: as, b :: bs => f.addE a b :: addPre f as bs
  | as, [] => as
  | [], _ => []

/-- One draw's three rows added onto (main table, mask table, target), under the powers w, w theta,
w theta^2; then the next power. On the mask table the three rows stand on five stretches that do not
meet, from the index 0 on: one list. -/
def addDraw (f : Fld) (old : Stage) (theta : E) (s : SRow) (x : Nat) (cl : Col) :
    List E × List E × E × E → List E × List E × E × E
  | (c, d, t, w0) =>
    let w1 := f.mulE w0 theta
    let w2 := f.mulE w1 theta
    let y := yOf f old.h s cl
    let gm := genM old.Z (cp old.Z x)
    let gt := genT old.Z (cp old.Z x)
    (addPre f c ((genM old.C x).map fun p => f.scaleE p w0),
      addPre f d
        (gm.map (fun p => f.scaleE p w1) ++ gm.map (fun p => f.scaleE p w2) ++
          (genT old.C x).map (fun p => f.scaleE p w0) ++
          gt.map (fun p => f.scaleE p w1) ++ gt.map (fun p => f.scaleE p w2)),
      f.addE (f.addE (f.addE t (f.mulE w0 y.1)) (f.mulE w1 y.2.1)) (f.mulE w2 y.2.2),
      f.mulE w2 theta)

/-- The code switch: the new row. The values of `csStepLit`, made faster (that they are equal:
`csStep_eq`, Fmt/M1CsEq.lean). -/
def csStep (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List Nat)
    (theta : E) (col : Nat → Option Col) : Option GRow :=
  (csRows f old new s sample [] col).bind fun two =>
    let g0 := sumRows f theta two
    (xs.foldl (fun (acc : Option (List E × List E × E × E)) x =>
      match acc, col x with
      | some st, some cl => some (addDraw f old theta s x cl st)
      | _, _ => none) (some (g0.c.toList, g0.d.toList, g0.t, f.mulE theta theta))).map fun st => ⟨st.1.toArray, st.2.1.toArray, st.2.2.1⟩

/-! ## The honest side: what the new oracle message holds (Part 4, 2 (1)) -/

/-- rows (lists of n entries) folded entry by entry at g -/
def foldRows (f : Fld) (g : List E) (rows : List (List E)) (n : Nat) : List E :=
  (List.range n).map fun j => foldV f g (rows.map fun r => r.getD j Fld.zeroE).toArray

/-- What an honest g holds: (its main table, its mask table). The arguments:
  g (the argument, not the message): the fold's challenges;
  M, Rh: the messages and tails of the old group's 2^k main rows (zero rows too);
  W, Sg: those of the 2^h old mask rows;
  P, Pi: those of the 2^h fresh mask rows;
  free: what stands in the free room (cut or filled with 0);
  pad: the last entry. -/
def csOwnG (f : Fld) (old new : Stage) (g : List E) (M Rh W Sg P Pi : List (List E))
    (free : List E) (pad : E) : Array E × Array E :=
  let g' := g.take old.h
  let rest := foldRows f g' W old.Z.l ++ foldRows f g' P old.Z.l ++ foldRows f g Rh old.C.r ++
    foldRows f g' Sg old.Z.r ++ foldRows f g' Pi old.Z.r
  ((foldRows f g M old.C.l).toArray,
    (rest ++ fitL Fld.zeroE (2 ^ new.h * new.Z.l - rest.length - 1) free ++ [pad]).toArray)

/-! ## Tests: a prover of this library's own, at tiny sizes (field 2: the codes' points lie there)
-/

namespace CsOwn

/-- made-up elements -/
def rnd (n : Nat) : E :=
  (Fld.two.red (n * 2654435761 + 12345),
    Fld.two.red (n * n * 40503 + 7),
    Fld.two.red (n * 97 + n * n * n))
def rv (s n : Nat) : List E := (List.range n).map fun i => rnd (1000 * s + i)

/-- One run of that prover and of the switch at the draws xs; with `spoil` the first main symbol of
the column at the first drawn position is made one larger. The three answers:
(the batched row holds of g; every row holds of g; the number of rows is 2 + 3 t, the output has the
tables' sizes, `csStep` gives `csStepLit`'s values, and the new target is the text's own formula
(Part 4, 3 (e)): t + theta alpha + the sum over the draws i of
theta^(2 + 3 (i - 1)) (y_main + theta y_0 + theta^2 y_1): this holds the order of batching, which
the first two do not see). -/
def run (o nw : Stage) (xs : List Nat) (spoil : Bool) : Bool × Bool × Bool :=
  let f : Fld := .two
  let gam := rv 1 o.k
  let gam' := gam.take o.h
  let M := (List.range (2 ^ o.k)).map fun b => rv (10 + b) o.C.l
  let Rh := (List.range (2 ^ o.k)).map fun b => rv (20 + b) o.C.r
  let W := (List.range (2 ^ o.h)).map fun b => rv (30 + b) o.Z.l
  let Sg := (List.range (2 ^ o.h)).map fun b => rv (40 + b) o.Z.r
  let P := (List.range (2 ^ o.h)).map fun b => rv (50 + b) o.Z.l
  let Pi := (List.range (2 ^ o.h)).map fun b => rv (60 + b) o.Z.r
  let nD := 2 ^ nw.h * nw.Z.l
  let Ws := foldRows f gam' W o.Z.l
  let Ps := foldRows f gam' P o.Z.l
  let gg := csOwnG f o nw gam M Rh W Sg P Pi (rv 70 nD) (rnd 71)
  let gMain : Array E := gg.1
  let gMask : Array E := gg.2
  let c := (rv 2 o.C.l).toArray
  let d0 := (rv 3 o.Z.l).toArray
  let d1 := (rv 4 o.Z.l).toArray
  let s : SRow :=
    ⟨c, d0, d1, f.addE (dot f c gMain) (f.addE (dot f d0 Ws.toArray) (dot f d1 Ps.toArray)), gam⟩
  let sc := (rv 5 gMain.size).toArray
  let sd := (rv 6 nD).toArray
  let smp : GRow := ⟨sc, sd, f.addE (dot f sc gMain) (dot f sd gMask)⟩
  let col : Nat → Option Col := fun x =>
    let mn := ((List.range (2 ^ o.k)).map fun b => symE o.C x (M.getD b []) (Rh.getD b [])).toArray
    some ⟨if spoil && x == xs.headD 0 then mn.setIfInBounds 0 (f.addE (ent mn 0) Fld.oneE) else mn,
      ((List.range (2 ^ o.h)).map fun b =>
        symE o.Z (cp o.Z x) (W.getD b []) (Sg.getD b [])).toArray,
      ((List.range (2 ^ o.h)).map fun b =>
        symE o.Z (cp o.Z x) (P.getD b []) (Pi.getD b [])).toArray⟩
  let holds : GRow → Bool := fun r => f.addE (dot f r.c gMain) (dot f r.d gMask) == r.t
  let th := rnd 999
  let pw : Nat → E := fun q => (List.range q).foldl (fun a _ => f.mulE a th) Fld.oneE
  let tauBy : E := (List.range xs.length).foldl (fun acc i =>
      match col (xs.getD i 0) with
      | some cl => let y := yOf f o.h s cl
                   f.addE acc
                     (f.mulE (pw (2 + 3 * i))
                       (f.addE y.1 (f.addE (f.mulE th y.2.1) (f.mulE (f.mulE th th) y.2.2))))
      | none => acc) (f.addE s.t (f.mulE th smp.t))
  match csStep f o nw s smp xs th col, csRows f o nw s smp xs col with
  | some g, some rows =>
    (holds g, rows.all holds,
      rows.length == nRows xs.length && g.c.size == gMain.size && g.d.size == nD && g.t == tauBy &&
        (csStepLit f o nw s smp xs th col).map (fun l => (l.c, l.d, l.t)) == some (g.c, g.d, g.t))
  | _, _ => (false, false, false)

/-- the shape of the toy's first switch: k = 2, h = 0 into k' = 1, h' = 1 -/
def o1 : Stage := ⟨⟨3, 4, 2⟩, ⟨3, 2, 1⟩, 2, 0, 3⟩
def n1 : Stage := ⟨⟨2, 2, 1⟩, ⟨2, 8, 1⟩, 1, 1, 3⟩
/-- the shape of its second: k = 1, h = 1 into k' = 0, h' = 0 -/
def o2 : Stage := ⟨⟨3, 4, 2⟩, ⟨3, 2, 1⟩, 1, 1, 3⟩
def n2 : Stage := ⟨⟨2, 4, 1⟩, ⟨2, 16, 1⟩, 0, 0, 3⟩
/-- a mask code shorter than the main code: the mask rows are read at the position modulo its
length -/
def o3 : Stage := ⟨⟨3, 4, 2⟩, ⟨2, 2, 1⟩, 1, 1, 3⟩

end CsOwn

#guard csFits CsOwn.o1 CsOwn.n1 && csFits CsOwn.o2 CsOwn.n2 && csFits CsOwn.o3 CsOwn.n2
-- the room in the mask table: 2 · 2 + 2 + 2 · 1 + 1 = 9
#guard csFits CsOwn.o1 { CsOwn.n1 with Z := ⟨2, 4, 1⟩ } == false
#guard csFits CsOwn.o1 { CsOwn.n1 with C := ⟨2, 4, 1⟩ } == false
#guard CsOwn.run CsOwn.o1 CsOwn.n1 [5, 2, 7] false == (true, true, true)
#guard CsOwn.run CsOwn.o2 CsOwn.n2 [5, 2, 7] false == (true, true, true)
#guard CsOwn.run CsOwn.o3 CsOwn.n2 [5, 2, 7] false == (true, true, true)
-- a repeated position counts twice
#guard CsOwn.run CsOwn.o1 CsOwn.n1 [5, 2, 5, 0] false == (true, true, true)
-- no draw: the carried claim and the sample row
#guard CsOwn.run CsOwn.o2 CsOwn.n2 [] false == (true, true, true)
-- one opened symbol changed
#guard CsOwn.run CsOwn.o1 CsOwn.n1 [5, 2, 7] true == (false, false, true)
#guard CsOwn.run CsOwn.o2 CsOwn.n2 [5, 2, 5] true == (false, false, true)
-- a drawn position without a column
#guard (csStep .two CsOwn.o1 CsOwn.n1 default default [1] Fld.oneE fun _ => none).isNone
#guard layAt 5 2 [(1, 0, 0), (2, 0, 0)] == #[(0, 0, 0), (0, 0, 0), (1, 0, 0), (2, 0, 0), (0, 0, 0)]
#guard layAt 3 2 [(1, 0, 0), (2, 0, 0)] == #[(0, 0, 0), (0, 0, 0), (1, 0, 0)]
#guard nRows 73 == 221 && nRows 74 == 224
-- the honest g: the tables' sizes; the pad at the last index
#guard (csOwnG .two CsOwn.o1 CsOwn.n1 (CsOwn.rv 1 2) [] [] [] [] [] [] [] (9, 0, 0)).1.size == 4 && (csOwnG .two CsOwn.o1 CsOwn.n1 (CsOwn.rv 1 2) [] [] [] [] [] [] [] (9, 0, 0)).2.size == 16 && ent (csOwnG .two CsOwn.o1 CsOwn.n1 (CsOwn.rv 1 2) [] [] [] [] [] [] [] (9, 0, 0)).2 15 == (9, 0, 0)

end Fmt.M1
