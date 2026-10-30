-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean: the lemmas for `runBy_eq` (that `runBy`,
RunBy.lean, gives what the reference definition `testAll`, Test.lean, gives) that can be stated
without importing Test.lean, each as a named `Prop`. Each is proved in the file named beside it. The
main statement: RunBySpecTop.lean. The assembled proof: RunByEq.lean.

  `RunOut.toB`    the result of `runBy` as a `BOut` (Johnson/Prover/Link/BodyAll.lean); the warnings
                 are left out
  `groupOf_eq`, `rowAt_eq`, `keep_fst`   proved here: `groupOf` and `rowAt` equal `groupAt` and
                 `rowOf`; the state of `keep` is the state that `testAll` keeps
  `Tab`          a stage's state over the field (`PS`, Johnson/Prover/Link/BodyState.lean) and a
                 stage's lists of words (`PSt`, Fmt/M1Own.lean) hold the same values: each list is
                 the function's values in range, encoded
  `CoinTie`, `HideTie`, `CoinTies`   the random values grouped by use (`Sorted`, Run.lean) and those
                 of `testAll` (`BCoins`, BodyAll.lean) are the same: at a switch; at a fold; along
                 the stages
  `Spec.dense_reads`   RunByDense.lean
  `Spec.fold_eq`   RunByFold.lean
  `Spec.next_tab`   RunByNext.lean
  `Spec.col_eq`   RunByCols.lean
  `Spec.ans_eq`   RunByAns.lean
  `Spec.last_eq`   RunByLast.lean
  `Spec.stagesBy_eq`   RunByEq.lean, from the six above by `stagesBy_of` (RunByAll.lean)

Terms, for all files of this folder that point here. A proximity test runs through a list of stages.
A stage has 2 ^ k main rows and 2 ^ h mask rows. C and Z are its main and mask code. A code (a, l,
r) has codewords of length 2 ^ a, messages of l entries and a tail of r random entries. `Stage`
(Fmt/M1Types.lean) holds k and h; `Sg` (OnBytes/Slice/Stage.lean) holds h and g = k - h; `sgOf`
turns the first into the second. An element of the extension field is three 64-bit words; `toE`
decodes it into the field, `ofE` encodes with each word below the prime, `wr n f` encodes f 0 to f
(n - 1). "On words": on such triples, by the functions of Fmt/. "Over the field": on elements of the
field type `GE`, which are encoded afterwards. A fold brings a stage's rows down to one; its hiding
polynomial masks the sums that it sends. A code switch sends the folded row under the next stage's
codes. The fresh table is the table of the next fold's hiding polynomial's coefficients
(`freshRows`, Fmt/M1Fold.lean); it is sent with a stage's rows. At the last stage a masking word is
sent in its place. These two are what "rides" with a stage's rows (`riders`, Fmt/M1Own.lean). Coins:
the prover's random values. A row's symbol at position x is entry x of its codeword (`symE`). A tree
holds rows; its column at x is these rows' symbols at x, as words (`Tree`, Run.lean). An opening: a
round samples positions, and the prover shows each opened tree's columns there, one list for each
tree (`groupOf`). A group is the set of oracle messages that one test tests together. Each is a
member; its rows take a block of the first stage's rows; its sender is the part of the prover that
sent it, in a sending. A kept member's main rows are not folded with the group's. A claim is a
linear equation on a stage's two tables that the verifier's state holds: a row of coefficients for
each table and a target (`GroupRow`, OnBytes/Iop/Ground.lean; `GRow`, Fmt/). The main coefficients
are a form: a sum of tensors and single entries. A tensor has a pair for each variable; a
written-out factor gives some variables' share as a slice of an array instead. A job is what a
caller supplies for one test (`TestJob`, `RunJob`, `ManyJob`). The block is the verifier's side of
the test (`proximityTestKind guardedProximityTestParts p`): its declared rounds and its `decide`. A description is the list of
blocks of a whole protocol; a chain is a run of blocks that share a state, and the shared chain is
the one that all requests of a batch share. A seat puts a test's block into a chain: `enter` makes
the test's state from the chain's, `leave` writes it back (Johnson/Desc/K12/Seat.lean). A part is a
run of the prover's rounds (`Part`, Johnson/Desc/ProofFile/Honest/Frame.lean); a move computes one
round's message and what is handed on to the next move. The prover's side of a test is two parts:
the round "BAT" with the first fold, and all the rest (`firstLen`, Parts.lean). The pair with its
address is a `Placed`; the names with `Half` mean such a pair. A play runs parts on a list of
challenges (`play`, Frame.lean). The reference definition `testAll` (Test.lean) is this folder's
definition, over the field, of what the prover shows in a test.

Limits. But for three small equations, statements only. Nothing on completeness, soundness or
hiding.
-/
import Johnson.Desc.K12.Honest.Stages
import Johnson.Desc.ProofFile.Honest.K12.RunBy
import Johnson.Prover.Link.FoldWordsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE toE vecIn vecG)
open Johnson.Prover.Link (PS BCoins BOut wr μOf coefU groupAt rowOf)
open Fmt.M1 (Stage GRow)
open Fmt.M1.Own (PSt tabOf colOf lhs syms words)
open VerifiableInference.Desc.K12 (P12 T12 Laid)
open H2K.Pub (sgOf)

/-! ## 1 The relations -/

/-- The result of `runBy` as a `BOut`; the warnings are left out. -/
def RunOut.toB (o : RunOut) : BOut := ⟨o.rs, o.tr, o.gs⟩

theorem groupOf_eq (x : Tree) (poss : List ℕ) : groupOf x poss = groupAt x.1 poss x.2 := rfl

theorem rowAt_eq (t : T12) : rowAt t = rowOf t := by
  rcases t with ⟨st, book, roots, g, pass, mask⟩
  cases pass <;> rfl

theorem keep_fst (t : T12) (x : Except String T12) : (keep t x).1 = x.toOption.getD t := by
  cases x <;> rfl

/-- **A state by index and a state of lists hold the same values**: each of the six lists of p is
the matching function of P, encoded. last: at the last stage the lists `P` and `Pi` hold the masking
word's two rows and their tails, otherwise the fresh table's rows and tails. -/
structure Tab (s : Stage) (last : Bool) (P : PS) (p : PSt) : Prop where
  main : p.M = (List.range (2 ^ s.k)).map fun b => wr s.C.l fun c => P.tabM (b + 2 ^ s.k * c)
  mainT : p.Rh = (List.range (2 ^ s.k)).map fun b => wr s.C.r (P.tM b)
  mask : p.W = (List.range (2 ^ s.h)).map fun b => wr s.Z.l fun c => P.tabZ (b + 2 ^ s.h * c)
  maskT : p.Sg = (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.tZ b)
  ride : p.P = if last then [wr s.C.l P.sM, wr s.Z.l (P.fM 0)]
    else (List.range (2 ^ s.h)).map fun b => wr s.Z.l (P.fM b)
  rideT : p.Pi = if last then [wr s.C.r P.sT, wr s.Z.r (P.fT 0)]
    else (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.fT b)

/-- The hiding polynomial's coefficients of stage j decode to those of `testAll`, and their words
are below the prime (`freshRows` copies some of them into the fresh table unchanged). -/
def HideTie (K : Sorted) (B : BCoins) (j : ℕ) (s : Stage) : Prop :=
  coefU ((sgOf s).h + (sgOf s).g) (hideBy K (j + 1)) = B.W (sgOf s) j ∧
    ∀ n, Fmt.Fld.two.okE (K.hide (j + 1) n) = true

/-- **The random values of switch j**, from stage cur to stage next, are those of `testAll`,
encoded. The clause `free` holds for every n. `nextBy` lists N := 2 ^ next.h * next.Z.l values of
`K.free (j + 2)`, and `csOwnG` keeps n < N - 1 - off, where
off := 2 * cur.Z.l + cur.C.r + 2 * cur.Z.r. So off + 1 addresses are listed and dropped. With `pad`
the first of them, `K.free (j + 2) (N - 1 - off)`, equals `K.pad (j + 2)`: two addresses of
`Sorted`, one value. So a theorem on random values must speak of the addresses that are kept. -/
structure CoinTie (K : Sorted) (B : BCoins) (j : ℕ) (cur next : Stage) (last : Bool) : Prop where
  main : ∀ b q, K.main (j + 2) b q = ofE ((B.new j).tM b q)
  mask : ∀ b q, K.mask (j + 2) b q = ofE ((B.new j).tZ b q)
  free : ∀ n, K.free (j + 2) n = ofE (B.fr j (2 * cur.Z.l + cur.C.r + 2 * cur.Z.r + n))
  pad : K.pad (j + 2) = ofE (B.fr j (2 ^ next.h * next.Z.l - 1))
  fresh : last = false → ∀ b q, K.fresh (j + 2) b q = ofE ((B.new j).fT b q)
  hide : last = false → HideTie K B (j + 1) next
  word : last = true → ∀ n, K.word (j + 2) 0 n = ofE ((B.new j).sM n) ∧
    K.word (j + 2) 1 n = ofE ((B.new j).fM 0 n) ∧ K.word (j + 2) 2 n = ofE ((B.new j).sT n) ∧
    K.word (j + 2) 3 n = ofE ((B.new j).fT 0 n)

/-- `CoinTie` at every switch from stage j on. -/
def CoinTies (K : Sorted) (B : BCoins) : ℕ → Stage → List Stage → Prop
  | _, _, [] => True
  | j, cur, next :: rest => CoinTie K B j cur next rest.isEmpty ∧ CoinTies K B (j + 1) next rest

/-! ## 2 The lemmas -/

/-- If h ≤ k and C.l is a power of two, `denseAt row s` and `row` convert to the same vector over
the field (`vecIn`, `vecG`), and the two arrays of `denseAt` have the sizes of the stage's two
tables. -/
def Spec.dense_reads : Prop :=
  ∀ (row : OnBytes.GroupRow) (s : Stage), s.h ≤ s.k → pow2B s.C.l = true →
    vecIn (sgOf s) (denseAt row s) = vecG (sgOf s) row ∧
      (denseAt row s).c.size = 2 ^ s.k * s.C.l ∧ (denseAt row s).d.size = 2 ^ s.h * s.Z.l

/-- If h ≤ k, the claim's arrays have the tables' sizes and `Tab` holds, the rounds of a fold
computed on words (`Trial.sigma`, `FoldOwn.honest`) are the rounds defined over the field
(`foldShown`) at what the arrays and tables decode to. -/
def Spec.fold_eq : Prop :=
  ∀ (s : Stage) (G : GRow) (last : Bool) (P : PS) (p : PSt) (U : Fmt.M1.FoldOwn.Hide)
    (D : ℕ → Fmt.Drawn), s.h ≤ s.k → G.c.size = 2 ^ s.k * s.C.l → G.d.size = 2 ^ s.h * s.Z.l →
    Tab s last P p →
    (⟨[.e (Fmt.M1.FoldOwn.Trial.sigma .two
          { k := s.k, h := s.h, G := G, m := tabOf p.M s.C.l, mu := tabOf p.W s.Z.l, U := U
            eps := headE (D 0), g := (List.range s.k).map fun n => headE (D (1 + n))
            lzk := s.Z.l })], D 0⟩ ::
      ((Fmt.M1.FoldOwn.honest .two
          { k := s.k, h := s.h, G := G, m := tabOf p.M s.C.l, mu := tabOf p.W s.Z.l, U := U
            eps := headE (D 0), g := (List.range s.k).map fun n => headE (D (1 + n))
            lzk := s.Z.l } []
          ((List.range s.k).map fun n => headE (D (1 + n)))).map (·.1)).zipIdx.map
        fun q => ⟨[.e q.1.1, .e q.1.2], D (1 + q.2)⟩ : List Fmt.RoundView) =
      foldShown (sgOf s) (vecIn (sgOf s) G) (μOf (sgOf s) P)
        (coefU ((sgOf s).h + (sgOf s).g) U) D

/-- If `Tab` holds before a switch, it holds after it, between `nextBy` and `aNext`. Further
hypotheses: h ≤ k at both stages, `switchFitB`, `CoinTie`, and, unless the next stage is the last, 2
k + 1 ≤ h + Z.l there. -/
def Spec.next_tab : Prop :=
  ∀ (K : Sorted) (B : BCoins) (j : ℕ) (cur next : Stage) (last : Bool) (o : ℕ) (P : PS) (p : PSt)
    (D : ℕ → Fmt.Drawn), cur.h ≤ cur.k → next.h ≤ next.k → switchFitB cur next = true →
    (last = false → 2 * next.k + 1 ≤ next.h + next.Z.l) →
    Tab cur false P p → CoinTie K B j cur next last →
    Tab next last (aNext B last j cur next o P D)
      (nextBy Seams.lib .two K (j + 2) cur next last
        ((List.range cur.k).map fun n => headE (D (o + 1 + n))) p)

/-- If h ≤ k, `Tab` holds, and k = 0 at a last stage, the column computed on words (`colOf`) is the
column defined over the field (`aCol`), at all positions. -/
def Spec.col_eq : Prop :=
  ∀ (s : Stage) (last : Bool) (P : PS) (p : PSt), s.h ≤ s.k → (last = true → s.k = 0) →
    Tab s last P p → colOf s false last p = aCol last s P

/-- If h ≤ k at both stages, the next stage's two message lengths are powers of two and `Tab` holds,
the answer computed on words (`lhs` of `sampleRow` at the new tables) is `aAns`, the answer sent in
the round "CS", encoded. -/
def Spec.ans_eq : Prop :=
  ∀ (p : P12) (j : ℕ) (cur next : Stage) (last : Bool) (o : ℕ) (D : ℕ → Fmt.Drawn) (t₁ : T12)
    (Q : PS) (q : PSt), cur.h ≤ cur.k → next.h ≤ next.k → pow2B next.C.l = true →
    pow2B next.Z.l = true → Tab next last Q q →
    lhs .two
        (Fmt.M1.sampleRow .two next.Am next.Az
          ((List.range next.na).map fun i =>
            ((D (o + 1 + cur.k)).elems.take (OnBytes.Send.cube t₁.st.codes
              (OnBytes.switchTargetStage
                ((VerifiableInference.Desc.K12.stageAt p (j + 1) next).getD default).code
                ((VerifiableInference.Desc.K12.stageAt p (j + 1) next).getD default).maskCode
                next.k next.h 1).shape).bits).getD i Fmt.Fld.zeroE)
          (orOneW ((D (o + 1 + cur.k)).elems.getD (OnBytes.Send.cube t₁.st.codes
              (OnBytes.switchTargetStage
                ((VerifiableInference.Desc.K12.stageAt p (j + 1) next).getD default).code
                ((VerifiableInference.Desc.K12.stageAt p (j + 1) next).getD default).maskCode
                next.k next.h 1).shape).bits Fmt.Fld.zeroE))
          Fmt.Fld.zeroE)
        (tabOf q.M next.C.l) (tabOf q.W next.Z.l) =
      ofE (aAns p j cur next o D t₁ Q)

/-- At a last stage (k = 0, h = 0) where `Tab` holds, `stagesBy` gives the rounds, trees and opened
columns of `lastAll`. -/
def Spec.last_eq : Prop :=
  ∀ (S : Seams) (p : P12) (K : Sorted) (j : ℕ) (s : Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
    (q : PSt) (trees : List Tree) (D : ℕ → Fmt.Drawn), s.k = 0 → s.h = 0 → Tab s true P q →
    (stagesBy S p K [] j s l o t q trees D).toB = lastAll p j s o t P trees D

/-- If the stages pass `okFrom`, the random values agree (`CoinTies`, `HideTie`) and `Tab` holds,
`stagesBy` at `Seams.lib` gives the rounds, trees and opened columns of `stagesAll`. -/
def Spec.stagesBy_eq : Prop :=
  ∀ (p : P12) (K : Sorted) (B : BCoins) (rest : List Stage) (j : ℕ) (s : Stage) (l : Laid) (o : ℕ)
    (t : T12) (P : PS) (q : PSt) (trees : List Tree) (D : ℕ → Fmt.Drawn),
    okFrom s rest = true → CoinTies K B j s rest →
    (rest ≠ [] → HideTie K B j s) → Tab s rest.isEmpty P q →
    (stagesBy Seams.lib p K rest j s l o t q trees D).toB =
      stagesAll p B rest j s l o t P trees D

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.groupOf_eq
#print axioms ProofFile.Honest.K12.Light.rowAt_eq
#print axioms ProofFile.Honest.K12.Light.keep_fst
#print axioms ProofFile.Honest.K12.Light.RunOut.toB
#print axioms ProofFile.Honest.K12.Light.Tab
#print axioms ProofFile.Honest.K12.Light.HideTie
#print axioms ProofFile.Honest.K12.Light.CoinTie
#print axioms ProofFile.Honest.K12.Light.CoinTies
#print axioms ProofFile.Honest.K12.Light.Spec.dense_reads
#print axioms ProofFile.Honest.K12.Light.Spec.fold_eq
#print axioms ProofFile.Honest.K12.Light.Spec.next_tab
#print axioms ProofFile.Honest.K12.Light.Spec.col_eq
#print axioms ProofFile.Honest.K12.Light.Spec.ans_eq
#print axioms ProofFile.Honest.K12.Light.Spec.last_eq
#print axioms ProofFile.Honest.K12.Light.Spec.stagesBy_eq
