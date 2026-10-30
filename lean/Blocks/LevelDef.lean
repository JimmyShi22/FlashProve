-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LevelDef.lean: the levels, a recursive column test for one linear claim (definitions).

An array is a matrix of `rows` × `code.msg` entries over E, sent encoded row by row under a code,
without encoding randomness. A level proves one linear claim ⟨c, A⟩ = v on it. After a sumcheck
without pads the verifier sends coefficients θ. The prover commits the next array, which holds A'
(the rows of A folded at the sumcheck's point) and A'' (the θ-combination of the rows, for the
proximity test). The verifier reads q columns of A. The end of the sumcheck, an equation on A'
((T-end) below), and the comparison of these columns with A' and A'' become one linear claim on the
next array. The last array is sent in the clear and checked.

Levels over an array with gaps: Blocks/Level2Def.lean. (Words of this library: lean/GLOSSARY.md.)

Notation: `F`, `E`: fields with `[Algebra F E]`: the code is over F, the arrays are over E;
`a : LevSpec F`: the format of one array; `a.mu`: ℕ; the hypercube has mu variables
(`LevSpec.mle`); `a.mrow`: ℕ; the row part of the point ζ is its first mrow coordinates
(`LevSpec.foldW`: `eqN a.mrow 0 ζ`); `a.q`: ℕ; q columns are read. Of the code
`a.code : Code.Enc F` (Code/Iface.lean): the generator matrix has `n` rows (positions) and `k`
columns; the encoder applies it to a vector that holds the message at the first `msg` places; `fm`:
the full input of the generator; `GE E`: the generator over an extension field. `Shape.IsPoint`:
every round's oracle part is a string (Iop/Shape.lean).

Limits: nothing is proved here. The lemmas on the levels (Blocks/LevelAcc.lean, LevelLocal.lean,
LevelSound.lean) conclude neither the soundness, nor the completeness, nor the locality of the
levels as a whole.
-/
import Blocks.Basic
import Code.Iface
import Iop.ShapeKit

namespace Blocks
open Iop

/-- The format of one array (fixed by the public parameters); q columns are read. -/
structure LevSpec (F : Type) where
  code : Code.Enc F
  rows : ℕ
  mrow : ℕ
  mu : ℕ
  q : ℕ
  [nePos : Nonempty (Fin code.n)]

attribute [instance] LevSpec.nePos

namespace LevSpec
variable {F : Type} [Field F] (a : LevSpec F) (E : Type) [Field E] [Fintype E]
  [DecidableEq E] [Algebra F E]

/-- the array; the received word in the place of its encoding (at each position a column); a linear
claim on it -/
abbrev Arr : Type := Fin a.rows → Fin a.code.msg → E
abbrev Word : Type := Fin a.code.n → Fin a.rows → E
structure Claim where
  coef : Fin a.rows → Fin a.code.msg → E
  v : E

variable {E}

/-- an array from its entries as one sequence: entry t is in row t / msg at the index t % msg -/
def ofFlat (f : ℕ → E) : a.Arr E := fun i j => f (i.val * a.code.msg + j.val)
/-- the encoding of a row: no randomness -/
def encRow (m : Fin a.code.msg → E) : Fin a.code.n → E :=
  (a.code.GE E).mulVec (a.code.fm m (fun _ => 0))
/-- the honest encoding of an array -/
def word (A : a.Arr E) : a.Word E := fun p i => a.encRow (A i) p

def arrN (A : a.Arr E) : ℕ → ℕ → E := fun i j => nat (fun i' => nat (A i') j) i

/-- the multilinear extension of an array, placed at i ‖ j in the hypercube of mu variables -/
def mle (f : ℕ → ℕ → E) (pt : ℕ → E) : E :=
  ∑ i ∈ Finset.range a.rows,
    ∑ j ∈ Finset.range a.code.msg, eqN a.mu 0 pt (i * 2 ^ (a.mu - a.mrow) + j) * f i j

def ptAt (ζ : ℕ → E) (j : ℕ) (y : E) (z : ℕ) : ℕ → E :=
  fun t => if t < j then ζ t else if t = j then y else if z.testBit (a.mu - 1 - t) then 1 else 0

/-- the two coefficients of a round polynomial that are sent -/
def rp0 (c A : ℕ → ℕ → E) (ζ : ℕ → E) (j : ℕ) : E :=
  ∑ z ∈ Finset.range (2 ^ (a.mu - j - 1)), a.mle c (a.ptAt ζ j 0 z) * a.mle A (a.ptAt ζ j 0 z)
def rp2 (c A : ℕ → ℕ → E) (ζ : ℕ → E) (j : ℕ) : E :=
  ∑ z ∈ Finset.range (2 ^ (a.mu - j - 1)), (a.mle c (a.ptAt ζ j 1 z) - a.mle c (a.ptAt ζ j 0 z)) *
    (a.mle A (a.ptAt ζ j 1 z) - a.mle A (a.ptAt ζ j 0 z))

/-- the running claim after all rounds: cl_j = ζ_j cl_(j-1) + (1 - 2 ζ_j) s0_j + (ζ_j² - ζ_j) s2_j,
unrolled -/
def clEnd (v : E) (ζ s0 s2 : ℕ → E) : E :=
  (∏ i ∈ Finset.range a.mu, ζ i) * v +
    ∑ j ∈ Finset.range a.mu, ((1 - 2 * ζ j) * (∏ i ∈ Finset.Ico (j + 1) a.mu, ζ i) * s0 j +
      (ζ j ^ 2 - ζ j) * (∏ i ∈ Finset.Ico (j + 1) a.mu, ζ i) * s2 j)

/-- the fold of the rows of a received word, or of an array, at the row part of the point; and their
θ-combination -/
def foldW (w : a.Word E) (ζ : ℕ → E) (p : Fin a.code.n) : E := ∑ i, eqN a.mrow 0 ζ i.val * w p i
def combW (w : a.Word E) (θ : Fin a.rows → E) (p : Fin a.code.n) : E := ∑ i, θ i * w p i
def foldA (A : a.Arr E) (ζ : ℕ → E) : Fin a.code.msg → E := fun j =>
  ∑ i, eqN a.mrow 0 ζ i.val * A i j
def combA (A : a.Arr E) (θ : Fin a.rows → E) : Fin a.code.msg → E := fun j => ∑ i, θ i * A i j

/-- (T-end): the end of the sumcheck, read on a candidate for A' -/
def endVal (c : a.Claim E) (ζ : ℕ → E) (av : ℕ → E) : E :=
  a.mle (a.arrN c.coef) ζ * ∑ j ∈ Finset.range a.code.msg, eqN (a.mu - a.mrow) a.mrow ζ j * av j

variable (E) in
/-- three rounds: θ; the last array in the clear, then the positions; the next array encoded, then
the positions with χ0, χ1, χ' (the coefficients with which the checks at the positions enter the
next claim) -/
abbrev rTheta : Round := plainRound Unit (Fin a.rows → E) ()
variable (E) in
abbrev rLast : Round :=
  plainRound ((Fin a.code.msg → E) × (Fin a.code.msg → E))
    (Fin a.q → Fin a.code.n) (fun _ => 0, fun _ => 0)
variable (E) in
abbrev rNext (b : LevSpec F) : Round :=
  wordsRound Unit (fun _ => b.code.n) (fun _ => Fin b.rows → E) Unit
    ((Fin a.q → Fin a.code.n) × E × E × (Fin a.q → E)) (fun _ _ => 0) ()

/-- The claim of the next level on an array that holds (A' ‖ A'') as one sequence. -/
def nextClaim (b : LevSpec F) (c : a.Claim E) (w : a.Word E) (ζ s0 s2 : ℕ → E) (θ : Fin a.rows → E)
    (ch : (Fin a.q → Fin a.code.n) × E × E × (Fin a.q → E)) : b.Claim E where
  coef := b.ofFlat fun t =>
    if t < a.code.msg then
      a.mle (a.arrN c.coef) ζ * eqN (a.mu - a.mrow) a.mrow ζ t +
        ∑ i, ch.2.2.2 i * (ch.2.1 * nat (fun s => a.code.GE E (ch.1 i) s) t)
    else if t < 2 * a.code.msg then
      ∑ i, ch.2.2.2 i * (ch.2.2.1 * nat (fun s => a.code.GE E (ch.1 i) s) (t - a.code.msg))
    else 0
  v := a.clEnd c.v ζ s0 s2 +
    ∑ i, ch.2.2.2 i * (ch.2.1 * a.foldW w ζ (ch.1 i) + ch.2.2.1 * a.combW w θ (ch.1 i))

/-- the next array of the honest prover -/
def nextArr (b : LevSpec F) (A : a.Arr E) (ζ : ℕ → E) (θ : Fin a.rows → E) : b.Arr E :=
  b.ofFlat fun t =>
    if t < a.code.msg then nat (a.foldA A ζ) t else nat (a.combA A θ) (t - a.code.msg)

end LevSpec

variable {F : Type} [Field F] (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- The shape of the levels: the present array has the format a, the later ones those of the list;
the array after the last is sent in the clear. -/
def levelsShape : LevSpec F → List (LevSpec F) → Shape
  | a, [] => List.replicate a.mu (LinSh.rSC E) ++ [a.rTheta E, a.rLast E]
  | a, b :: rest =>
    List.replicate a.mu (LinSh.rSC E) ++ (a.rTheta E :: a.rNext E b :: levelsShape b rest)

variable {E}

/-- The verifier of the levels. -/
def levelsOk :
    (a : LevSpec F) → (rest : List (LevSpec F)) →
    a.Claim E → a.Word E → Tr (levelsShape E a rest) → Bool
  | a, [], c, w, τ =>
    let sc := trList (LinSh.rSC E) a.mu (Tr.fst τ)
    let tl : Tr [a.rTheta E, a.rLast E] := Tr.snd (s := List.replicate a.mu (LinSh.rSC E)) τ
    let ζ := ofList (sc.map fun x => x.2)
    let s0 := ofList (sc.map fun x => x.1.2.1)
    let s2 := ofList (sc.map fun x => x.1.2.2)
    let θ : Fin a.rows → E := tl.2.1
    let av : Fin a.code.msg → E := tl.2.2.1.2.1
    let bv : Fin a.code.msg → E := tl.2.2.1.2.2
    let pos : Fin a.q → Fin a.code.n := tl.2.2.2.1
    decide (
      a.endVal c ζ (nat av) = a.clEnd c.v ζ s0 s2 ∧
      ∀ i, a.encRow av (pos i) = a.foldW w ζ (pos i) ∧ a.encRow bv (pos i) = a.combW w θ (pos i))
  | a, b :: rest, c, w, τ =>
    let sc := trList (LinSh.rSC E) a.mu (Tr.fst τ)
    let tl : Tr (a.rTheta E :: a.rNext E b :: levelsShape E b rest) :=
      Tr.snd (s := List.replicate a.mu (LinSh.rSC E)) τ
    let ζ := ofList (sc.map fun x => x.2)
    let s0 := ofList (sc.map fun x => x.1.2.1)
    let s2 := ofList (sc.map fun x => x.1.2.2)
    levelsOk b rest (a.nextClaim b c w ζ s0 s2 tl.2.1 tl.2.2.2.1) (tl.2.2.1.1 ()) tl.2.2.2.2

/-- the positions at which the present array is read -/
def levelsPos :
    (a : LevSpec F) → (rest : List (LevSpec F)) →
    Rho (levelsShape E a rest) → Fin a.q → Fin a.code.n
  | a, [], ρ =>
    (Rho.snd (s := List.replicate a.mu (LinSh.rSC E)) (t := [a.rTheta E, a.rLast E]) ρ).2.1
  | a, b :: rest, ρ =>
      (Rho.snd (s := List.replicate a.mu (LinSh.rSC E))
        (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) ρ).2.1.1

variable (E) in
/-- all oracles of the levels are strings -/
def levelsPoint : (a : LevSpec F) → (rest : List (LevSpec F)) → (levelsShape E a rest).IsPoint
  | a, [] =>
    pointRep (LinSh.rSC E) (plainPoint _ _ _) a.mu (t := [a.rTheta E, a.rLast E])
      (plainPoint _ _ _, (plainPoint _ _ _, ()))
  | a, b :: rest =>
    pointRep (LinSh.rSC E) (plainPoint _ _ _) a.mu
      (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest)
      (plainPoint _ _ _, (wordsPoint Unit _ _ Unit _ (fun _ _ => 0) (), levelsPoint b rest))

/-- Equality of positions of the levels' oracles is decided part by part. -/
instance levelsDecEqOPos (a : LevSpec F) (rest : List (LevSpec F)) :
    DecidableEq (OPos (levelsShape E a rest)) :=
  (levelsPoint E a rest).decEqOPos

/-- the positions that are read in the later arrays, which the levels send themselves -/
def levelsReadsOwn :
    (a : LevSpec F) → (rest : List (LevSpec F)) →
    Rho (levelsShape E a rest) → Finset (OPos (levelsShape E a rest))
  | _, [], _ => ∅
  | a, b :: rest, ρ =>
      let ρ' : Rho (levelsShape E b rest) :=
        (Rho.snd (s := List.replicate a.mu (LinSh.rSC E))
          (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) ρ).2.2
      let up : OPos (a.rTheta E :: a.rNext E b :: levelsShape E b rest) →
          OPos (levelsShape E a (b :: rest)) :=
        posR (s := List.replicate a.mu (LinSh.rSC E))
      (Finset.univ.image fun i => up (.inr (.inl ⟨(), levelsPos b rest ρ' i⟩))) ∪
      ((levelsReadsOwn b rest ρ').image fun p => up (.inr (.inr p)))

end Blocks
