-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/PendShapeLight.lean: THE PENDING ROW ON SHAPES (`pendB`, `pendS`,
Johnson/Desc/First/Pend/Shape/PendShape.lean) ONCE MORE, ON NUMBERS ALONE: `pendBL`, `pendSL`; AND
THE TWO TEXTS ARE EQUAL AT ALL ARGUMENTS: `pendB_eq`, `pendS_eq`. Eight definitions, nine general
theorems, three small evaluated examples. No statement here has a hypothesis.

Purpose. pendB and pendS read sizes, but build what they measure. (1) To compare the number of a
claim's coefficients with its unit's number of rows, claimFitsB builds the whole vector of
coefficients (`wsGamma`, OnBytes/Model/Weights.lean) at a claim made of zeros: outer products in the
field, one element for each row of the unit. (2) To cut a stretch of n rows into aligned blocks,
blocksSh runs `stretchBlocks` (OnBytes/Iop/Lin.lean) at an array of n zeros; pendB calls it once and
pendS twice. Whoever evaluates these texts at the full size pays for that. The light texts compute
the same Bool and the same value by arithmetic on the layout's units and on the claims' sizes.

How. The library has the number of coefficients as a product of sizes (`size_wsGamma_eq`,
`gamLenOf`, `facLen`, Johnson/Road/K4/PendLight.lean); at the claim made of zeros these sizes are
the numbers in the claim's shape (`gamLen_blank`). A block's two numbers depend on the block's
number of bits alone (the library's `block_len`; `block_vars` here), and that number on the rows'
numbers alone (`blockBits`, OnBytes/Iop/Lin.lean): `blocks_eq`, by recursion, after the library's
`lens_eq`.

Main names.
* `facLenS`, `gamLenS`, `gamLen_blank`; `unitS`; `claimFitsL`, **`claimFits_eq`**: claimFitsB lay n
  (recBlank c) = claimFitsL lay n c.
* `spanL`, `span_eq`: spanSh lay w = spanL lay w.
* `blocksL k first size fuel start`; `choice_len`, `block_vars`, `blocks_eq`; **`blocksSh_eq`**:
  blocksSh k first n = blocksL k first n (2 * k + 2) first.
* `pendBL`, **`pendB_eq`**: pendB lay S w claims = pendBL lay S w claims. `pendSL`, **`pendS_eq`**:
  pendS lay S im w claims a = pendSL lay S im w claims a.
* Examples, evaluated: `blocksL_toy`; `blocksSh_toy` (the library's own text at the same small
  stretch, by Lean's kernel); `blocksL_toy_no` (a control: one number changed: refused).

Limits. EQUALITIES OF TWO TEXTS. Nothing says that either test accepts anywhere, or that either
function returns. That the light texts are cheap to evaluate is not shown here: nothing at the full
size is evaluated. SECOND TEXTS: pendBL and pendSL repeat pendB's and pendS's texts clause for
clause; a change of the library's texts that breaks an equation stops the build. NO LAW TIES THESE
LIGHT TEXTS TO THE LIBRARY's OTHER LIGHT ONES: blocksL's first number d is, as 2 ^ d, the library's
blockLens (Johnson/Road/K4/PendLightDefs.lean: the same recursion), and no theorem says so; two more
tests named pendB stand in the library, on lists of units (there, and in
Johnson/Top/H0/MergeLaw/RowReturns.lean): pendBL is tied to Pend.Shape.pendB alone: a fact on one
light test cannot be carried to another. unitS lay c is unitOf lay (recBlank c) under a second name.
Every law is general, although the file stands under AtFull. blocksL_toy_no follows from
blocksL_toy: as a control it shows that the decision can say no at this type, no more. The examples
are one small stretch. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Pend.Shape.PendShape
import Johnson.Road.K4.PendLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Road.K4.Pend (facLen gamLenOf size_wsGamma_eq block_len)
open VerifiableInference.Desc.First.Pend (unitOf spanOf)
open VerifiableInference.Desc.First.Pend.Shape
open VerifiableInference.Desc.First.Shape (RecSh MergeSh)
open VerifiableInference.Desc.Ground.Sh (CoreSh modAt)

/-! ## 1 How many coefficients a claim has on its unit's rows: from three sizes a factor -/

/-- The length of a row factor's table, from the factor's three sizes. -/
def facLenS (x : Nat × Nat × Nat) (G : WsGrp) : Nat :=
  if G.cls == 'E' then x.1 * 2 ^ x.2.1 else if G.aTaken then 1 else x.2.2

/-- The number of a claim's coefficients on the rows of its unit, from the claim's shape. -/
def gamLenS (u : WsUnit) (c : RecSh) : Nat :=
  (c.f.zip u.g).reverse.foldl (fun n y => n * facLenS y.1 y.2) u.nlw

/-- It is the library's count at the claim made of zeros. -/
theorem gamLen_blank (u : WsUnit) (c : RecSh) : gamLenOf u (recBlank c) = gamLenS u c := by
  unfold gamLenOf gamLenS recBlank
  simp only [List.zip_map_left, ← List.map_reverse, List.foldl_map]
  congr 1
  funext n y
  simp [facLen, facLenS]

/-- The claim's unit; the default where the layout has none. -/
def unitS (lay : WsLay) (c : RecSh) : WsUnit := (lay.U[c.ui]?).getD default

/-- The four tests on one claim, on its shape: no vector is built. -/
def claimFitsL (lay : WsLay) (n : Nat) (c : RecSh) : Bool :=
  (lay.U[c.ui]?).isSome && gamLenS (unitS lay c) c == (unitS lay c).rows &&
    c.f.length == (unitS lay c).g.length && decide ((unitS lay c).off + (unitS lay c).rows ≤ n)

/-- **It is the library's test at the claim made of zeros.** -/
theorem claimFits_eq (lay : WsLay) (n : Nat) (c : RecSh) :
    claimFitsB lay n (recBlank c) = claimFitsL lay n c := by
  unfold claimFitsB claimFitsL
  rw [size_wsGamma_eq, gamLen_blank]
  have e : (recBlank c).f.length = c.f.length := List.length_map _
  rw [e]
  rfl

/-! ## 2 The span -/

/-- The first row of the claims' units, and the row behind their last, on shapes. Where the layout
has no unit for a claim it reads the default unit, as the library's spanOf does. -/
def spanL (lay : WsLay) (w : MergeSh) : Nat × Nat :=
  w.recs.foldl (fun r c =>
    (min r.1 (unitS lay c).off, max r.2 ((unitS lay c).off + (unitS lay c).rows))) (2 ^ 64 - 1, 0)

/-- It is the library's span at the claims made of zeros. -/
theorem span_eq (lay : WsLay) (w : MergeSh) : spanSh lay w = spanL lay w := by
  unfold spanSh spanL blanks spanOf
  rw [List.foldl_map]
  rfl

/-! ## 3 The blocks of a stretch: no array -/

/-- Of each block of the stretch of size rows from row first on: the number of its dense variables;
the number of its variables, written d + (k - d) as block_vars finds it: it is k wherever d ≤ k. At
most fuel blocks, from row start on. -/
def blocksL (k first size : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, start =>
    if first + size ≤ start then []
    else
      (blockBits k start (first + size) k 0,
          blockBits k start (first + size) k 0 + (k - blockBits k start (first + size) k 0)) ::
        blocksL k first size fuel (start + 2 ^ blockBits k start (first + size) k 0)

/-- choicePairs n v has n pairs. (The library has this law under other names too.) -/
theorem choice_len : ∀ n v : Nat, (choicePairs n v).length = n
  | 0, _ => rfl
  | n + 1, v => by
    show (choicePairs n (v / 2)).length + 1 = n + 1
    rw [choice_len n]

/-- A block's number of variables. -/
theorem block_vars (k start first d : Nat) (v : Array E) :
    (if d == 0 then
        ({ scalar := v.getD (start - first) zeroE } : Tensor).insertChoice 0 k start
      else
        ((({} : Tensor).pushDense d).insertChoice d (k - d) (start / 2 ^ d)).setValues v
          (start - first)).vars = d + (k - d) := by
  split
  · rename_i h
    have e : d = 0 := by simpa using h
    subst e
    simp [Tensor.vars, Tensor.insertChoice, choice_len]
  · simp [Tensor.vars, Tensor.setValues, Tensor.insertChoice, Tensor.pushDense, choice_len]

/-- **The library's blocks, seen through these two numbers, depend on how many values there are, and
on nothing else of them.** -/
theorem blocks_eq (k first : Nat) (v : Array E) : ∀ fuel start,
    (stretchBlocks k first v fuel start).map (fun t => (t.denseVars.length, t.vars)) =
      blocksL k first v.size fuel start
  | 0, _ => rfl
  | fuel + 1, start => by
    unfold stretchBlocks blocksL
    simp only []
    split
    · rfl
    · simp only [List.map_cons, block_len, block_vars, blocks_eq k first v fuel]

/-- **The library's blocks on shapes, which are made at an array of n zeros, are the light ones.**
-/
theorem blocksSh_eq (k first n : Nat) :
    blocksSh k first n = blocksL k first n (2 * k + 2) first := by
  unfold blocksSh
  rw [blocks_eq, Array.size_replicate]

/-- A small example, evaluated: the five rows 1 to 5 in a cube of eight: one row, then two blocks of
two. -/
theorem blocksL_toy : blocksL 3 1 5 8 1 = [(0, 3), (1, 3), (1, 3)] := by decide

/-- The library's own text at the same example, evaluated by itself: the same list. -/
theorem blocksSh_toy : blocksSh 3 1 5 = [(0, 3), (1, 3), (1, 3)] := by decide +kernel

/-- A control: the light blocks are not that list with one number changed. -/
theorem blocksL_toy_no : decide (blocksL 3 1 5 8 1 = [(0, 3), (1, 3), (2, 3)]) = false := by decide

/-! ## 4 The test and the function -/

/-- **THE TEST ON SHAPES, LIGHT**: pendB's text on numbers alone. -/
def pendBL (lay : WsLay) (S : LinShape) (w : MergeSh) (claims : Nat) : Bool :=
  let first := (spanL lay w).1
  let last := (spanL lay w).2
  lay.m0 == S.matrixRows && !w.recs.isEmpty && w.recs.length == claims && w.rm == lay.lk &&
    w.recs.all (fun c => (lay.U[c.ui]?).isSome) && decide (first < last) &&
    decide (last ≤ lay.m0) && decide (S.kRow ≤ 62) && decide (lay.m0 ≤ 2 ^ S.kRow) &&
    w.recs.all (claimFitsL lay last) &&
    decide (first + (last - first) ≤ S.matrixRows) && decide (S.kRow < 63) &&
    decide (first + (last - first) ≤ 2 ^ S.kRow) &&
    ((blocksL S.kRow first (last - first) (2 * S.kRow + 2) first).map fun x => 2 ^ x.1).sum ==
      last - first

/-- **THE TWO TESTS ARE ONE**, at all arguments. -/
theorem pendB_eq (lay : WsLay) (S : LinShape) (w : MergeSh) (claims : Nat) :
    pendB lay S w claims = pendBL lay S w claims := by
  unfold pendB pendBL
  simp only [span_eq, blocksSh_eq, blanks, List.all_map, Function.comp_def, claimFits_eq]
  rfl

/-- **THE PENDING ROW ON SHAPES, LIGHT**: pendS's text over the light test and the light blocks. -/
def pendSL (lay : WsLay) (S : LinShape) (im : Nat) (w : MergeSh) (claims : Nat) (a : CoreSh) :
    Option (VerifiableInference.Desc.K13.Honest.RowSh × CoreSh) :=
  if pendBL lay S w claims then
    match (a.st.oracles[im]?).bind (·.ledger) with
    | some l =>
      if !l.closed && decide (0 < l.left) then
        some (⟨(blocksL S.kRow (spanL lay w).1 ((spanL lay w).2 - (spanL lay w).1)
              (2 * S.kRow + 2) (spanL lay w).1).isEmpty,
            VerifiableInference.Desc.K13.Honest.varsMark
              ((blocksL S.kRow (spanL lay w).1 ((spanL lay w).2 - (spanL lay w).1)
                (2 * S.kRow + 2) (spanL lay w).1).map (·.2)),
            w.rm, [⟨im, VerifiableInference.Desc.First.Pend.nextEntry l.rows l.logRows
              (2 ^ l.logRows) l.next⟩]⟩,
          { a with st := { a.st with
              oracles := modAt a.st.oracles im fun x => { x with ledger := some (taken l) } } })
      else none
    | none => none
  else none

/-- **THE TWO FUNCTIONS ARE ONE**, at all arguments. -/
theorem pendS_eq (lay : WsLay) (S : LinShape) (im : Nat) (w : MergeSh) (claims : Nat)
    (a : CoreSh) : pendS lay S im w claims a = pendSL lay S im w claims a := by
  unfold pendS pendSL
  simp only [pendB_eq, span_eq, blocksSh_eq]
  rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.gamLen_blank
#print axioms Johnson.AtFull.Shape.claimFits_eq
#print axioms Johnson.AtFull.Shape.span_eq
#print axioms Johnson.AtFull.Shape.choice_len
#print axioms Johnson.AtFull.Shape.block_vars
#print axioms Johnson.AtFull.Shape.blocks_eq
#print axioms Johnson.AtFull.Shape.blocksSh_eq
#print axioms Johnson.AtFull.Shape.blocksL_toy
#print axioms Johnson.AtFull.Shape.blocksSh_toy
#print axioms Johnson.AtFull.Shape.blocksL_toy_no
#print axioms Johnson.AtFull.Shape.pendB_eq
#print axioms Johnson.AtFull.Shape.pendS_eq
#print axioms Johnson.AtFull.Shape.facLenS
#print axioms Johnson.AtFull.Shape.gamLenS
#print axioms Johnson.AtFull.Shape.unitS
#print axioms Johnson.AtFull.Shape.claimFitsL
#print axioms Johnson.AtFull.Shape.spanL
#print axioms Johnson.AtFull.Shape.blocksL
#print axioms Johnson.AtFull.Shape.pendBL
#print axioms Johnson.AtFull.Shape.pendSL
