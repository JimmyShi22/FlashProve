-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Fold.lean: the verifier's side of a sum-check that folds a linear claim (block FOLD) and of
the two final checks (block BASE) of the first toy (a product test), as total functions that
compute.

The programs (the C++ implementation that comes with this Lean code) come with a description of the
first toy. This file renders the verifier's side of two of its blocks. It is generic in all sizes.
No Mathlib.

The words. The first toy is a small test protocol of the programs: the prover claims a_i b_i = c_i
for every i, for three rows a, b, c of one oracle message. A row on a group (`GRow`,
Fmt/M1Types.lean) is a linear equation on the entries of a main table and a mask table: coefficient
vectors c and d and a target t. FOLD is a sum-check of k rounds that starts from such a row and ends
in one linear equation on three rows (`SRow`, Fmt/M1Types.lean): the main table folded at the k
drawn elements, and the old and the fresh mask table, each folded at the first h of them. These rows
are called virtual: a symbol of one is computed from an opened column (`rowsAt`). BASE is the last
block: the prover sends four vectors (messages M0, M1 and encoding randomness R0, R1 for the codes
C, Z), and the verifier makes the checks B1 and B2 of part 1 below.

Sources. Written from part 3 of the programs' description of the toy; the numbers 2.1 to 2.5 and
"section 3" below are that part's. This file's sources include no file of the programs for this toy.
The layout of the fresh mask and the vector u(g), for every 0 ≤ h ≤ k, come from the answers to
questions that were added to the programs' description (its
annex on FOLD and BASE). By the same answers, the list of positions over which BASE's checks go is
the sorted set of the drawn positions.
In this file `baseOK` goes over whatever list `xs` its caller gives and sorts nothing; the decision
gives it the positions as drawn, repeats kept (the head of Fmt/M1Dec.lean: the same verdict as at
their sorted set). Below, "the text" is the programs' description of the toy.

1. What the file contains.
   `midCoeff`, `nextClaim`, `claimOf` (2.3): A round sends the constant and the quadratic
      coefficient of its polynomial. The linear one is recovered from q(0) + q(1) = the running
      claim. The new claim is q at the element drawn after the round. The first claim is sigma + eps
      times the row's target.
   `tailProd`, `hideVec` (2.5): The public vector u(g) whose product with the folded fresh mask row
      is the hiding polynomial at g, where a mask row has room for all entries of u(g) (`hideFits`,
      Fmt/M1Dec.lean).
   `foldStep f k h G sigma eps qs g` (2.5): What FOLD hands on: coefficients on the three virtual
      rows (c: the folded main row; d0: the folded old mask row; d1 := u(g), as long as d0: the
      folded fresh mask row), the target, and all k drawn elements. FOLD tests nothing on the spot.
      sigma: the element sent before the rounds; eps: the element drawn after it. Of qs and g the
      first k members count; a missing one counts as 0.
   `rowsAt` (2.5).
   baseB1, baseB2At, baseOK f C Z c d tau tauS lam M0 M1 R0 R1 xs col (Section 3, with one mask
      row.) B1: <c, M0> + <d, M1> = tauS + lam tau. B2, at every x of xs: the encoding of
      (M0, R0) under C at x is the masking word's main symbol plus lam times the last message's, and
      likewise under Z, at Z's position for x, for the mask symbols. The result is false if a column
      is missing. This library's own addition: it is false too if one of the four shown vectors
      has not its code's length.
   namespace `FoldOwn`: An honest prover of this library's own (`hidePoly`, `freshRows`, rounds by
   summing over
      the cube), written from the definitions of 2.1 to 2.3. `freshRows` has the general layout.

2. What is checked when the file compiles. Tests (#guard) at tiny sizes. The tests are this
library's own but for
   one group of known answers.
   The one group of known answers: the annex named under Sources gives the answer of a test of the
   programs at k = 3, h = 1 and an example at h = k = 2 (by the annex's word written out directly,
   not computed by a program); both are tests here.
   All the others, but for six named below, are against this library's own honest prover:
     With that prover, the linear coefficient that the verifier recovers is the true one in every
       round, and the claim that FOLD hands on holds of the three folded rows. The honest run is
       tested at (k, h) = (2, 0), (1, 1) (the toy's), (1, 0), (3, 0), (4, 0), (2, 1), (3, 1),
       (3, 2), (2, 2), (3, 3).
     The claim that FOLD hands on fails, at (k, h) = (2, 0), (1, 1) and (3, 1), if 1 is added to the
       first round's constant coefficient.
     BASE accepts one honest run of this library's own at tiny codes of field 2 and refuses seven
     altered
       copies of it; B1 and, at one position, B2 are also run apart on it.
   Six tests are of another kind: two compare `hideVec` and two compare `freshRow` with vectors and
   layouts written out after the description named under Sources; one tests the lengths of what is
   handed on, one `rowsAt`.
   The tests on the programs' own proof files are in other files (Fmt/M1FullProg.lean and the files
   that it gathers).

3. Theorems. None in this file: nothing is proved here.

4. What is not here.
   The hash chain, the proof of work and the openings: they belong to the file reader and to the
   compiled verifier.
   How a group's row is made from open rows, and how what FOLD hands on becomes a row on the next
   oracle message: other files.
   Coefficient vectors are written out. The programs hold c in a structured form: the same values at
   another cost.
   Kept rows do not occur.
   The encodings of Fmt/M1Codes.lean are field 2's. So `baseOK` means something at f := field 2
   alone; `foldStep` is generic in the field.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Types

namespace Fmt.M1

/-- The linear coefficient of a round's polynomial, recovered from the running claim; q: the
constant and the quadratic coefficient. -/
def midCoeff (f : Fld) (claim : E) (q : E × E) : E := f.subE (f.subE claim (f.addE q.1 q.1)) q.2

/-- The running claim after a round in which g is drawn. -/
def nextClaim (f : Fld) (claim : E) (q : E × E) (g : E) : E :=
  f.addE q.1 (f.addE (f.mulE (midCoeff f claim q) g) (f.mulE q.2 (f.mulE g g)))

/-- The running claim after k rounds. -/
def claimOf (f : Fld) (k : Nat) (first : E) (qs : List (E × E)) (g : List E) : E :=
  (List.range k).foldl
    (fun cl j => nextClaim f cl (qs.getD j (Fld.zeroE, Fld.zeroE)) (g.getD j Fld.zeroE)) first

/-- the product of g_j over j > l (variables counted from 1) -/
def tailProd (f : Fld) (g : List E) (l : Nat) : E :=
  (g.drop l).foldl (fun s a => f.mulE s a) Fld.oneE

/-- The public vector u(g), of length n; g: the k drawn elements. Its entries are cut, or filled up
with 0, to n. -/
def hideVec (f : Fld) (k h n : Nat) (g : List E) : Array E :=
  let ga (l : Nat) : E := g.getD (l - 1) Fld.zeroE
  let head : List E :=
    tailProd f g h :: (List.range h).map fun i => f.mulE (ga (i + 1)) (tailProd f g h)
  let mid : List E := (List.range (k - h)).flatMap fun i =>
    let l := h + 1 + i
    let sq := f.mulE (f.mulE (ga l) (ga l)) (tailProd f g l)
    if i = 0 then [sq] else [f.mulE (ga l) (tailProd f g l), sq]
  let all := head ++ mid ++ (if h < k then [Fld.oneE] else [])
  Array.ofFn (n := n) fun i => all.getD i.val Fld.zeroE

/-- FOLD, the verifier's side. -/
def foldStep (f : Fld) (k h : Nat) (G : GRow) (sigma eps : E) (qs : List (E × E)) (g : List E) :
    SRow :=
  let gk := (List.range k).map fun j => g.getD j Fld.zeroE
  let d0 := scaleV f (f.mulE eps (tailProd f gk h)) (foldLow f (gk.take h) G.d)
  { c := scaleV f eps (foldLow f gk G.c), d0 := d0, d1 := hideVec f k h d0.size gk,
    t := claimOf f k (f.addE sigma (f.mulE eps G.t)) qs g, g := gk }

/-- The three rows' symbols at a position, from the opened column: h of the drawn elements fold the
mask symbols -/
def rowsAt (f : Fld) (h : Nat) (S : SRow) (col : Col) : E × E × E :=
  (foldV f S.g col.main, foldV f (S.g.take h) col.mask, foldV f (S.g.take h) col.fresh)

/-- B1, the linear check (part 1 of the head). -/
def baseB1 (f : Fld) (c d : Array E) (tau tauS lam : E) (M0 M1 : List E) : Bool :=
  decide (f.addE (dot f c M0.toArray) (dot f d M1.toArray) = f.addE tauS (f.mulE lam tau))

/-- B2 at one position; o: the last message's main symbol, the masking word's main symbol, the last
message's mask symbol, the masking word's mask symbol -/
def baseB2At (f : Fld) (C Z : Code) (lam : E) (M0 M1 R0 R1 : List E) (x : Nat) (o : E × E × E × E) :
    Bool :=
  decide (symE C x M0 R0 = f.addE o.2.1 (f.mulE lam o.1)) &&
    decide (symE Z (cp Z x) M1 R1 = f.addE o.2.2.2 (f.mulE lam o.2.2.1))

/-- BASE's two checks. -/
def baseOK (f : Fld) (C Z : Code) (c d : Array E) (tau tauS lam : E) (M0 M1 R0 R1 : List E)
    (xs : List Nat) (col : Nat → Option (E × E × E × E)) : Bool :=
  decide (M0.length = C.l ∧ M1.length = Z.l ∧ R0.length = C.r ∧ R1.length = Z.r) &&
    baseB1 f c d tau tauS lam M0 M1 &&
  xs.all fun x =>
    match col x with
    | some o => baseB2At f C Z lam M0 M1 R0 R1 x o
    | none => false

/-! ### An honest prover of this library's own, and the tests -/

namespace FoldOwn

/-- the coefficients of the hiding polynomial: w l t for l = 1 .. k, t = 1, 2; and the constant -/
structure Hide where
  w  : Nat → Nat → E
  w0 : E

/-- the hiding polynomial at a point -/
def hidePoly (f : Fld) (k : Nat) (U : Hide) (xs : List E) : E :=
  (List.range k).foldl (fun s i =>
    let x := xs.getD i Fld.zeroE
    f.addE s (f.mulE (f.addE (f.mulE (U.w (i + 1) 1) x) (f.mulE (U.w (i + 1) 2) (f.mulE x x))) (tailProd f (xs.take k) (i + 1)))) U.w0

/-- row b "reaches" l (1 ≤ l ≤ h): its bits l - 1, .., h - 1 are all 1 -/
def reaches (h b l : Nat) : Bool := (List.range (h + 1 - l)).all fun j => b.testBit (l - 1 + j)

/-- one row of the fresh mask, for every 0 ≤ h ≤ k -/
def freshRow (f : Fld) (k h : Nat) (U : Hide) (b : Nat) : List E :=
  ((List.range h).foldl (fun s i => if reaches h b (i + 1) then f.addE s (U.w (i + 1) 1) else s)
      (if h < k then U.w (h + 1) 1 else U.w0)) ::
    ((List.range h).map fun i => if reaches h b (i + 1) then U.w (i + 1) 2 else Fld.zeroE) ++
    (if h < k then
        U.w (h + 1) 2 ::
          ((List.range (k - h - 1)).flatMap fun i => [U.w (h + 2 + i) 1, U.w (h + 2 + i) 2]) ++
          [U.w0]
      else [])

/-- the fresh mask's 2^h rows with these coefficients in them, as one table -/
def freshRows (f : Fld) (k h lzk : Nat) (U : Hide) : Array E :=
  Array.ofFn (n := 2 ^ h * lzk) fun i =>
    (freshRow f k h U (i.val % 2 ^ h)).getD (i.val / 2 ^ h) Fld.zeroE

/-- the points of the cube {0, 1}^n -/
def cube : Nat → List (List E)
  | 0 => [[]]
  | n + 1 => (cube n).flatMap fun p => [Fld.zeroE :: p, Fld.oneE :: p]

/-- made-up elements, told apart by a number -/
def mk (f : Fld) (n : Nat) : E :=
  (f.red (1000003 * n + 17), f.red (n * n + 5 * n + 3), f.red (7919 * n + 1))
def mkV (f : Fld) (n s : Nat) : Array E := Array.ofFn (n := n) fun i => mk f (s + 31 * i.val)

/-- the data of an honest run of FOLD -/
structure Trial where
  k   : Nat
  h   : Nat
  G   : GRow
  m   : Array E
  mu  : Array E
  U   : Hide
  eps : E
  g   : List E
  lzk : Nat

/-- all data made up; the target is the true value of the claim -/
def trial (f : Fld) (k h l lzk s : Nat) : Trial :=
  let c := mkV f (2 ^ k * l) s
  let d := mkV f (2 ^ h * lzk) (s + 1)
  let m := mkV f (2 ^ k * l) (s + 2)
  let mu := mkV f (2 ^ h * lzk) (s + 3)
  { k := k, h := h, G := ⟨c, d, f.addE (dot f c m) (dot f d mu)⟩, m := m, mu := mu,
    U := ⟨fun a t => mk f (s + 100 + 2 * a + t), mk f (s + 99)⟩, eps := mk f (s + 4)
    g := (List.range k).map fun j => mk f (s + 200 + j), lzk := lzk }

/-- the polynomial that is summed, at a point -/
def sumPoly (f : Fld) (T : Trial) (xs : List E) : E :=
  f.addE (hidePoly f T.k T.U xs)
    (f.mulE T.eps
      (f.addE (dot f (foldLow f (xs.take T.k) T.G.c) (foldLow f (xs.take T.k) T.m))
        (f.mulE (dot f (foldLow f (xs.take T.h) T.G.d) (foldLow f (xs.take T.h) T.mu))
          (tailProd f (xs.take T.k) T.h))))

/-- a round's polynomial at X: the earlier variables at the drawn elements, the later ones summed
over 0 and 1 -/
def roundAt (f : Fld) (T : Trial) (before : List E) (X : E) : E :=
  (cube (T.k - before.length - 1)).foldl
    (fun s p => f.addE s (sumPoly f T (before ++ X :: p))) Fld.zeroE

/-- the three coefficients of a polynomial of degree 2 from its values at 0, 1 and -1 -/
def coeffs (f : Fld) (v0 v1 vm : E) : E × E × E :=
  let q2 := f.subE (f.mulE (f.invE (f.addE Fld.oneE Fld.oneE)) (f.addE v1 vm)) v0
  (v0, f.subE (f.subE v1 v0) q2, q2)

/-- the honest rounds: what is sent, and with it the true linear coefficient -/
def honest (f : Fld) (T : Trial) : List E → List E → List ((E × E) × E)
  | _, [] => []
  | before, g :: gs =>
    let q := coeffs f (roundAt f T before Fld.zeroE)
      (roundAt f T before Fld.oneE) (roundAt f T before (f.negE Fld.oneE))
    ((q.1, q.2.2), q.2.1) :: honest f T (before ++ [g]) gs

def Trial.sigma (f : Fld) (T : Trial) : E :=
  (cube T.k).foldl (fun s p => f.addE s (hidePoly f T.k T.U p)) Fld.zeroE
def Trial.rounds (f : Fld) (T : Trial) : List ((E × E) × E) := honest f T [] T.g

/-- Whether in every round the coefficient that the verifier recovers is the true one. -/
def Trial.midOK (f : Fld) (T : Trial) : Bool :=
  (((T.rounds f).zip T.g).foldl
    (fun (s : E × Bool) r =>
      (nextClaim f s.1 r.1.1 r.2, s.2 && decide (midCoeff f s.1 r.1.1 = r.1.2)))
    (f.addE (T.sigma f) (f.mulE T.eps T.G.t), true)).2

/-- Whether the claim that FOLD hands on, at given rounds, holds of the three folded rows. -/
def Trial.outOK (f : Fld) (T : Trial) (qs : List (E × E)) : Bool :=
  let S := foldStep f T.k T.h T.G (T.sigma f) T.eps qs T.g
  decide (f.addE (dot f S.c (foldLow f S.g T.m))
      (f.addE (dot f S.d0 (foldLow f (S.g.take T.h) T.mu))
        (dot f S.d1 (foldLow f (S.g.take T.h) (freshRows f T.k T.h T.lzk T.U)))) = S.t)

def Trial.good (f : Fld) (T : Trial) : Bool := T.midOK f && T.outOK f ((T.rounds f).map (·.1))

/-- a number as an element -/
def nE (n : Nat) : E := (UInt64.ofNat n, 0, 0)
/-- the coefficients of the annex's example at k = 3: w_(1,1), w_(1,2), w_(2,1), w_(2,2),
w_(3,1), w_(3,2) = 1, 2, 3, 4, 6, 7; the constant 5 -/
def k31 : Hide := ⟨fun l t => nE (if l = 3 then 5 + t else 2 * (l - 1) + t), nE 5⟩
/-- coefficients for its example at k = 2: w_(1,1), w_(1,2), w_(2,1), w_(2,2) = 1, 2, 3, 4; the
constant 5 -/
def k22 : Hide := ⟨fun l t => nE (2 * (l - 1) + t), nE 5⟩

/-- the first round's constant coefficient changed -/
def spoil (f : Fld) : List (E × E) → List (E × E)
  | [] => []
  | q :: qs => (f.addE q.1 Fld.oneE, q.2) :: qs

-- the text's two written-out vectors u(g): k = 2, h = 0; k = h = 1
#guard hideVec .two 2 0 7 [(2, 0, 0), (3, 0, 0)] = #[(6, 0, 0), (12, 0, 0), (3, 0, 0), (9, 0, 0), (1, 0, 0), (0, 0, 0), (0, 0, 0)]
#guard hideVec .two 1 1 4 [(5, 0, 0)] = #[(1, 0, 0), (5, 0, 0), (0, 0, 0), (0, 0, 0)]
-- the toy's two shapes, both fields: FOLD 1 (k = 2, h = 0), FOLD 2 (k = h = 1)
#guard (trial .two 2 0 3 6 1).good .two && (trial .one 2 0 3 6 1).good .one
#guard (trial .two 1 1 3 4 2).good .two && (trial .one 1 1 3 4 2).good .one
-- other numbers of variables at h = 0
#guard (trial .two 1 0 2 4 3).good .two && (trial .two 3 0 2 8 4).good .two && (trial .two 4 0 1 9 5).good .two
-- the annex's own known answer (k = 3, h = 1; by its word the answer of a test of the programs that
-- runs in every build): the coefficients (w_(1,1), w_(1,2), w_(2,1), w_(2,2), w_(3,0), w_(3,1),
-- w_(3,2)) = (1, .., 7): the two rows; u at g = (2, 3, 5)
#guard (freshRow .two 3 1 k31 0, freshRow .two 3 1 k31 1) = ([3, 0, 4, 6, 7, 5].map nE, [4, 2, 4, 6, 7, 5].map nE)
#guard hideVec .two 3 1 7 [nE 2, nE 3, nE 5] = ([15, 30, 45, 5, 25, 1, 0].map nE).toArray
-- the annex's example h = k = 2 (by its word derived by hand): the four rows, at w_(1,1), w_(1,2),
-- w_(2,0), w_(2,1), w_(2,2) = 1, 2, 5, 3, 4; u = (1, g_1, g_2, 0)
#guard (List.range 4).map (freshRow .two 2 2 k22) = [[5, 0, 0].map nE, [5, 0, 0].map nE, [8, 0, 4].map nE, [9, 2, 4].map nE]
#guard hideVec .two 2 2 4 [nE 7, nE 9] = ([1, 7, 9, 0].map nE).toArray
-- the two layouts of the first text are cases of the general one
#guard freshRow .two 2 0 k31 0 = [1, 2, 3, 4, 5].map nE
#guard (freshRow .two 1 1 k31 0, freshRow .two 1 1 k31 1) = ([5, 0].map nE, [6, 2].map nE)
-- the shapes with 0 < h < k and h = k > 1, which no shape of the toy exercises: the honest run;
-- last, at (3, 1), a run with a changed coefficient (the next comment)
#guard (trial .two 2 1 2 5 6).good .two && (trial .two 3 1 2 7 7).good .two && (trial .two 3 2 1 6 8).good .two
#guard (trial .two 2 2 2 4 9).good .two && (trial .two 3 3 1 5 10).good .two && (trial .one 3 1 2 7 11).good .one
#guard (trial .two 3 1 2 7 7).outOK .two (spoil .two (((trial .two 3 1 2 7 7).rounds .two).map (·.1))) = false
-- a changed coefficient: the claim handed on fails
#guard (trial .two 2 0 3 6 1).outOK .two (spoil .two (((trial .two 2 0 3 6 1).rounds .two).map (·.1))) = false
#guard (trial .two 1 1 3 4 2).outOK .two (spoil .two (((trial .two 1 1 3 4 2).rounds .two).map (·.1))) = false
-- the lengths of what is handed on: l, lzk, lzk; all k drawn elements
#guard (let S := foldStep .two 2 0 (trial .two 2 0 3 6 1).G Fld.zeroE Fld.oneE [] (trial .two 2 0 3 6 1).g; (S.c.size, S.d0.size, S.d1.size, S.g.length)) = (3, 6, 6, 2)
-- a position of the three rows: folding an opened column is reading the folded row, for an encoding
-- that acts row by row (here: the entry itself, at place 1)
#guard (let T := trial .two 2 0 3 6 1; (rowsAt .two 0 (foldStep .two 2 0 T.G Fld.zeroE Fld.oneE [] T.g) ⟨T.m.extract 4 8, T.mu.extract 1 2, #[mk .two 9]⟩) = (ent (foldLow .two T.g T.m) 1, ent T.mu 1, mk .two 9))

/-- the arguments of a run of BASE (`baseOK`) but for the field and the positions. `btrial` below
fills them for an honest run at tiny codes of field 2, from the rows with their randomness, the
masking word with its, and lambda -/
structure BTrial where
  C    : Code
  Z    : Code
  c    : Array E
  d    : Array E
  tau  : E
  tauS : E
  lam  : E
  M0   : List E
  M1   : List E
  R0   : List E
  R1   : List E
  col  : Nat → Option (E × E × E × E)

def btrial (s : Nat) : BTrial :=
  let f := Fld.two
  let C : Code := ⟨4, 4, 2⟩
  let Z : Code := ⟨3, 3, 2⟩
  let c := mkV f 4 s
  let d := mkV f 3 (s + 1)
  let m0 := mkV f 4 (s + 2)
  let m1 := mkV f 3 (s + 3)
  let r0 := mkV f 2 (s + 4)
  let r1 := mkV f 2 (s + 5)
  let a0 := mkV f 4 (s + 6)
  let a1 := mkV f 3 (s + 7)
  let b0 := mkV f 2 (s + 8)
  let b1 := mkV f 2 (s + 9)
  let lam := mk f (s + 10)
  { C := C, Z := Z, c := c, d := d, tau := f.addE (dot f c m0) (dot f d m1),
    tauS := f.addE (dot f c a0) (dot f d a1), lam := lam
    M0 := (axpy f a0 lam m0).toList,
      M1 := (axpy f a1 lam m1).toList,
      R0 := (axpy f b0 lam r0).toList,
      R1 := (axpy f b1 lam r1).toList
    col := fun x =>
      some (symE C x m0.toList r0.toList,
          symE C x a0.toList b0.toList,
          symE Z (cp Z x) m1.toList r1.toList,
          symE Z (cp Z x) a1.toList b1.toList) }

def BTrial.run (T : BTrial) (xs : List Nat) : Bool :=
  baseOK .two T.C T.Z T.c T.d T.tau T.tauS T.lam T.M0 T.M1 T.R0 T.R1 xs T.col

#guard (btrial 1).run [0, 3, 6, 11, 15]
-- refused: another target; another tau*; an entry of a shown message; of the shown randomness; an
-- opened symbol; a column that lacks; a shown vector of another length
#guard ({ btrial 1 with tau := Fld.two.addE (btrial 1).tau Fld.oneE } : BTrial).run [0, 3, 6] = false
#guard ({ btrial 1 with tauS := Fld.two.addE (btrial 1).tauS Fld.oneE } : BTrial).run [0, 3, 6] = false
#guard ({ btrial 1 with M0 := Fld.oneE :: (btrial 1).M0.tail } : BTrial).run [0, 3, 6] = false
#guard ({ btrial 1 with R1 := Fld.oneE :: (btrial 1).R1.tail } : BTrial).run [0, 3, 6] = false
#guard ({ btrial 1 with col := fun x => ((btrial 1).col x).map fun o => (Fld.two.addE o.1 Fld.oneE, o.2) } : BTrial).run [0, 3, 6] = false
#guard ({ btrial 1 with col := fun x => if x = 3 then none else (btrial 1).col x } : BTrial).run [0, 3, 6] = false
#guard ({ btrial 1 with R0 := (btrial 1).R0 ++ [Fld.zeroE] } : BTrial).run [0, 3, 6] = false
-- the randomness is seen by B2 alone, the target by B1 alone
#guard (let T := btrial 1; baseB1 .two T.c T.d T.tau T.tauS T.lam T.M0 T.M1) = true
#guard (let T := btrial 1; ((T.col 6).map fun o => baseB2At .two T.C T.Z T.lam T.M0 T.M1 T.R0 T.R1 6 o)) = some true

end FoldOwn

end Fmt.M1
