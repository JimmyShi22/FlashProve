-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/Plain3.lean: one protocol made of three stretches of written rounds, over one stored
table, with any decision on three views.

Run/PlanQX.lean turns one list of written rounds and a decision on one view into a protocol on two
stored tables (`skeletonOverBothExternalStrings`). This file is its counterpart for a file that holds three chains of rounds
and opens one stored table. The three chains are laid one behind the other as one protocol. Four
further rounds, the seams, stand before the first stretch, between the first and the second (two of
them) and between the second and the third. A seam is any round without an oracle and with one
verifier message; which rounds they are is a parameter, and the verifier does not look at them.

The verifier accepts if each stretch passes three tests and the decision says yes to three views,
one for each stretch. The three tests are those of `skeletonOverBothExternalStrings`: every round's test of work passes
(`PQ.passSL`); every opening of the stored table has as many draws as it says (`PQ.everyOpeningHasItsDraws`); every
symbol read from the stored table carries the position at which it was read (`carries1`, the
counterpart of `PQ.symbolsCarryTheirPositions` for one table; OnBytes/Slice/Plain3Asks.lean says when the two agree).

A view holds its own stretch's rounds and, round by round, the columns opened behind that round's
drawn positions: first the stored table's, then the prover's trees', in the order of
Run/PlanQX.lean's `wantedXL`. A written round names a tree that it opens by the tree's number in
the order of sending over all three stretches, so a stretch can open a tree that another stretch
sent. In view i the columns of tree n stand under the key `keyᵢ n`, where `keyᵢ` is a parameter.
Whether an entry is the stored table's or a tree's is settled before keys are given (`Ask`), so
nothing depends on keys being different.

Main definitions: `Seam`, `Seam.plain`, `Seam.written`, `Stretches` (the public data),
`Stretches.sh` (the shape), `Stretches.tr₁`, `tr₂`, `tr₃` (a transcript's three stretches),
`Ask`, `asksL`, `carries1`, `okOn`, `viewOn`, `Stretches.col`, `Stretches.pos`,
`Stretches.view₁`, `view₂`, `view₃`, `Stretches.accOn`, `Plain3`.

Not claimed. Definitions only: no statement on soundness, and none that any transcript is accepted.
Of a seam's three conditions the definitions use one, that it has no position, and only to decide
equality of positions; the other two say what a seam is meant to be.
The types let every stretch open every tree, also one that is sent later. Nothing asks that the
parts of a round's draws that go to the stored table are disjoint or use up the draws, nor that a
tree is opened at most once. The field `which` of an opening of the stored table chooses the key
under which the columns stand (the first or the second of Run/PlanQX.lean's two keys); there is one
table. A transcript is cut into its stretches with the library's `Tr.fst` and `Tr.snd`, which
take shapes as arguments; Run/PlanQS.lean explains why Lean's evaluator may be slow on such
functions. `accOn`, on the three stretches, has no such argument, and
OnBytes/Slice/Plain3Eval.lean cuts a transcript without one.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.Unfold
import Iop.ShapeKit

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Run

/-! ## Seams -/

/-- A seam: a round without an oracle and with one verifier message. -/
structure Seam where
  /-- the round -/
  r : Round
  /-- its oracle part has one value. (Why it is asked: the library wires only rounds whose oracle
  part is given by its symbols, Iop/Shape.lean: `Round.IsPoint`; without a position that leaves one
  value. This reason is not a theorem here.) -/
  noOrc : Subsingleton r.Orc
  /-- its oracle part has no position -/
  noPos : IsEmpty r.Pos
  /-- it has one verifier message -/
  one : Subsingleton r.Chal

/-- The seam that sends a plain part in T and nothing else. t is the fixed message of the right
format that every round has to name. -/
@[reducible] def Seam.plain (T : Type) (t : T) : Seam where
  r := { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim, Plain := T,
         Chal := Unit, dOrc := (), dPlain := t }
  noOrc := (inferInstance : Subsingleton Unit)
  noPos := (inferInstance : IsEmpty Empty)
  one := (inferInstance : Subsingleton Unit)

/-- A written round that sends no tree and has one verifier message is a seam. -/
@[reducible] def Seam.written (C : PQ.CK) (d : PQ.RD) (ht : d.tree = none)
    (h1 : Subsingleton (PQ.roundS C d).up.Chal) : Seam where
  r := (PQ.roundS C d).up
  noOrc := by
    show Subsingleton (Fin (PQ.posN d.tree) → Fin (PQ.colW d.tree) → UInt64)
    rw [ht]
    exact inferInstanceAs (Subsingleton (Fin 0 → Fin 0 → UInt64))
  noPos := by
    show IsEmpty (Fin (PQ.posN d.tree))
    rw [ht]
    exact inferInstanceAs (IsEmpty (Fin 0))
  one := h1

/-! ## What the drawn positions ask for -/

/-- What a round's drawn positions ask for: a position of the stored table, with the key under which
the column is to stand in a view, or a position of a tree of the prover, the tree named by its
number over all three stretches. -/
inductive Ask where
  | stored (key x : ℕ)
  | own (n x : ℕ)

/-- What the drawn positions of a list of rounds ask for, round by round: first the stored table, in
the order of xs, each opening at the sorted list without repeats of its own part of the draws,
modulo 2 ^ a; then the trees that the round opens, each at the sorted list without repeats of all
draws modulo the tree's number of leaves. `all` is the list of rounds in which trees are counted; i
is the number that xs has for the first round of the list. -/
def asksL (a : ℕ) (all : List PQ.RD) (xs : List PQ.XO) :
    ℕ → List PQ.RD → List Fmt.Drawn → List Ask
  | i, d :: ds, D :: Ds =>
    ((PQ.xsAt xs i).flatMap fun o =>
      (o.list a D).map fun x => Ask.stored (PQ.storedKey o.which) x) ++
    (d.opens.flatMap fun n =>
      match PQ.treeSh all n with
      | none => []
      | some s => (Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => Ask.own n x) ++
    asksL a all xs (i + 1) ds Ds
  | _, _, _ => []

/-- The position of the stored table that is asked for, if it is one and lies in the string. -/
def Ask.ext (a : ℕ) : Ask → Option (Fin (2 ^ a))
  | .stored _ x => if h : x < 2 ^ a then some ⟨x, h⟩ else none
  | .own _ _ => none

/-- The symbol at a position of the stored table that is asked for carries that position. False
where the position lies outside the string. -/
def Ask.carried (a : ℕ) (y : Fin (2 ^ a) → PQ.SgX) : Ask → Bool
  | .stored _ x => if h : x < 2 ^ a then (y ⟨x, h⟩).1 == x else false
  | .own _ _ => true

/-- The entry of a view's list of opened columns for what is asked: key, position, column. `key`
gives a tree's key, `col` its columns. -/
def Ask.shown (a : ℕ) (key : ℕ → ℕ) (y : Fin (2 ^ a) → PQ.SgX)
    (col : ℕ → ℕ → Option (List UInt64)) : Ask → Option (ℕ × ℕ × List UInt64)
  | .stored k x => if h : x < 2 ^ a then some (k, x, (y ⟨x, h⟩).2) else none
  | .own n x => (col n x).map fun c => (key n, x, c)

/-! ## One stretch -/

/-- Every symbol of the stored table that a stretch's draws ask for carries the position at which it
is read. -/
def carries1 (a : ℕ) (all ds : List PQ.RD) (xs : List PQ.XO) (Ds : List Fmt.Drawn)
    (y : Fin (2 ^ a) → PQ.SgX) : Bool :=
  (asksL a all xs 0 ds Ds).all (Ask.carried a y)

section
variable (C : PQ.CK) (a : ℕ) (all ds : List PQ.RD) (xs : List PQ.XO)

/-- What was drawn in a stretch. -/
def drOn (τ : Tr (PQ.uL C ds)) : List Fmt.Drawn := PQ.drawnSL C ds (PQ.rhoSL C ds τ)

/-- The three tests on a stretch: all tests of work pass; every opening of the stored table has
as many draws as it says; every symbol read from the stored table carries its position. In xs a
round is named by its number in the stretch. -/
def okOn (y : Fin (2 ^ a) → PQ.SgX) (τ : Tr (PQ.uL C ds)) : Bool :=
  PQ.passSL C ds (PQ.rhoSL C ds τ) && PQ.everyOpeningHasItsDraws xs (drOn C ds τ) &&
    carries1 a all ds xs (drOn C ds τ) y

/-- The view of a stretch: its rounds, and the columns that its draws ask for, in order. -/
def viewOn (key : ℕ → ℕ) (y : Fin (2 ^ a) → PQ.SgX) (col : ℕ → ℕ → Option (List UInt64))
    (τ : Tr (PQ.uL C ds)) : PQ.View where
  rounds := PQ.rvSL C ds τ
  opened := (asksL a all xs 0 ds (drOn C ds τ)).filterMap (Ask.shown a key y col)

end

/-! ## Three stretches -/

/-- The public data of a protocol in three stretches. -/
structure Stretches where
  /-- the choice of the types of verifier messages -/
  C : PQ.CK
  /-- the written rounds of the first stretch -/
  ds₁ : List PQ.RD
  /-- the written rounds of the second stretch -/
  ds₂ : List PQ.RD
  /-- the written rounds of the third stretch -/
  ds₃ : List PQ.RD
  /-- the seam before the first stretch -/
  s0 : Seam
  /-- the first seam between the first and the second stretch -/
  s1 : Seam
  /-- the second seam between the first and the second stretch -/
  s2 : Seam
  /-- the seam between the second and the third stretch -/
  s3 : Seam
  /-- the stored table's string has 2 ^ a symbols -/
  a : ℕ
  /-- the first stretch's openings of the stored table; a round is named by its number in the
  stretch -/
  xs₁ : List PQ.XO
  /-- the second stretch's openings of the stored table -/
  xs₂ : List PQ.XO
  /-- the third stretch's openings of the stored table -/
  xs₃ : List PQ.XO
  /-- the key in the first view of a tree, named by its number over all three stretches -/
  key₁ : ℕ → ℕ
  /-- the same for the second view -/
  key₂ : ℕ → ℕ
  /-- the same for the third view -/
  key₃ : ℕ → ℕ

/-- Equality of positions can be decided in a shape that begins with written rounds, if it can be
decided in what follows them. -/
def decApp (C : PQ.CK) (t : Shape) (h : DecidableEq (OPos t)) :
    (ds : List PQ.RD) → DecidableEq (OPos (PQ.uL C ds ++ t))
  | [] => h
  | d :: ds => by
      haveI := decApp C t h ds
      exact inferInstanceAs (DecidableEq (Fin (PQ.posN d.tree) ⊕ OPos (PQ.uL C ds ++ t)))

/-- A seam in front adds no position. -/
def decSeam (s : Seam) (t : Shape) (h : DecidableEq (OPos t)) : DecidableEq (OPos (s.r :: t)) := by
  haveI := h
  haveI : DecidableEq s.r.Pos := fun p _ => (s.noPos.false p).elim
  exact inferInstanceAs (DecidableEq (s.r.Pos ⊕ OPos t))

namespace Stretches
variable (G : Stretches)

/-- The fourth seam and the third stretch. -/
abbrev sh₃ : Shape := G.s3.r :: PQ.uL G.C G.ds₃

/-- The second and third seams, the second stretch, and what follows. -/
abbrev sh₂ : Shape := G.s1.r :: G.s2.r :: (PQ.uL G.C G.ds₂ ++ G.sh₃)

/-- The shape: seam, first stretch, two seams, second stretch, seam, third stretch. -/
abbrev sh : Shape := G.s0.r :: (PQ.uL G.C G.ds₁ ++ G.sh₂)

/-- Equality of two oracle positions of the protocol can be decided. -/
instance decO : DecidableEq (OPos G.sh) :=
  decSeam _ _ (decApp G.C _ (decSeam _ _ (decSeam _ _ (decApp G.C _
    (decSeam _ _ (PQ.decSL G.C G.ds₃)) G.ds₂))) G.ds₁)

/-- All written rounds: the list in which trees are counted. -/
def all : List PQ.RD := G.ds₁ ++ (G.ds₂ ++ G.ds₃)

/-! ### A transcript's parts -/

/-- The first stretch of a transcript. -/
def tr₁ (τ : Tr G.sh) : Tr (PQ.uL G.C G.ds₁) := Tr.fst τ.2.2

/-- What follows the third seam. -/
def trRest (τ : Tr G.sh) : Tr (PQ.uL G.C G.ds₂ ++ G.sh₃) :=
  (Tr.snd (s := PQ.uL G.C G.ds₁) τ.2.2).2.2.2.2

/-- The second stretch of a transcript. -/
def tr₂ (τ : Tr G.sh) : Tr (PQ.uL G.C G.ds₂) := Tr.fst (G.trRest τ)

/-- The third stretch of a transcript. -/
def tr₃ (τ : Tr G.sh) : Tr (PQ.uL G.C G.ds₃) := (Tr.snd (s := PQ.uL G.C G.ds₂) (G.trRest τ)).2.2

/-- The verifier messages of the first stretch. -/
def rho₁ (ρ : Rho G.sh) : Rho (PQ.uL G.C G.ds₁) := Rho.fst ρ.2

/-- The verifier messages behind the third seam. -/
def rhoRest (ρ : Rho G.sh) : Rho (PQ.uL G.C G.ds₂ ++ G.sh₃) :=
  (Rho.snd (s := PQ.uL G.C G.ds₁) ρ.2).2.2

/-- The verifier messages of the second stretch. -/
def rho₂ (ρ : Rho G.sh) : Rho (PQ.uL G.C G.ds₂) := Rho.fst (G.rhoRest ρ)

/-- The verifier messages of the third stretch. -/
def rho₃ (ρ : Rho G.sh) : Rho (PQ.uL G.C G.ds₃) := (Rho.snd (s := PQ.uL G.C G.ds₂) (G.rhoRest ρ)).2

/-- A position of the first stretch as a position of the whole. -/
def in₁ (p : OPos (PQ.uL G.C G.ds₁)) : OPos G.sh := .inr (OPos.left p)

/-- A position of the second stretch as a position of the whole. -/
def in₂ (p : OPos (PQ.uL G.C G.ds₂)) : OPos G.sh :=
  .inr (OPos.right (s := PQ.uL G.C G.ds₁) (t := G.sh₂) (.inr (.inr (OPos.left p))))

/-- A position of the third stretch as a position of the whole. -/
def in₃ (p : OPos (PQ.uL G.C G.ds₃)) : OPos G.sh :=
  .inr (OPos.right (s := PQ.uL G.C G.ds₁) (t := G.sh₂)
    (.inr (.inr (OPos.right (s := PQ.uL G.C G.ds₂) (t := G.sh₃) (.inr p)))))

/-! ### The trees, counted over all three stretches -/

/-- The column at position x of tree n. -/
def col (τ₁ : Tr (PQ.uL G.C G.ds₁)) (τ₂ : Tr (PQ.uL G.C G.ds₂)) (τ₃ : Tr (PQ.uL G.C G.ds₃))
    (n x : ℕ) : Option (List UInt64) :=
  if n < nTrees G.ds₁ then PQ.colAtS G.C G.ds₁ τ₁ n x
  else if n - nTrees G.ds₁ < nTrees G.ds₂ then PQ.colAtS G.C G.ds₂ τ₂ (n - nTrees G.ds₁) x
  else PQ.colAtS G.C G.ds₃ τ₃ (n - nTrees G.ds₁ - nTrees G.ds₂) x

/-- Position x of tree n as a position of the shape. -/
def pos (n x : ℕ) : Option (OPos G.sh) :=
  if n < nTrees G.ds₁ then (PQ.posAtS G.C G.ds₁ n x).map G.in₁
  else if n - nTrees G.ds₁ < nTrees G.ds₂ then
    (PQ.posAtS G.C G.ds₂ (n - nTrees G.ds₁) x).map G.in₂
  else (PQ.posAtS G.C G.ds₃ (n - nTrees G.ds₁ - nTrees G.ds₂) x).map G.in₃

/-- The position of the shape that is asked for, if it is one of a tree. -/
def own : Ask → Option (OPos G.sh)
  | .stored _ _ => none
  | .own n x => G.pos n x

/-! ### Views and decision -/

section
variable (y : Fin (2 ^ G.a) → PQ.SgX) (τ₁ : Tr (PQ.uL G.C G.ds₁)) (τ₂ : Tr (PQ.uL G.C G.ds₂))
  (τ₃ : Tr (PQ.uL G.C G.ds₃))

/-- The first view. It takes all three stretches' transcripts, since a stretch may open a tree
that another stretch sent. -/
def view₁ : PQ.View := viewOn G.C G.a G.all G.ds₁ G.xs₁ G.key₁ y (G.col τ₁ τ₂ τ₃) τ₁

/-- The second view. -/
def view₂ : PQ.View := viewOn G.C G.a G.all G.ds₂ G.xs₂ G.key₂ y (G.col τ₁ τ₂ τ₃) τ₂

/-- The third view. -/
def view₃ : PQ.View := viewOn G.C G.a G.all G.ds₃ G.xs₃ G.key₃ y (G.col τ₁ τ₂ τ₃) τ₃

/-- The verifier's decision, on the three stretches of a transcript: each stretch passes its
three tests, and the decision says yes to the three views. -/
def accOn (dec : PQ.View → PQ.View → PQ.View → Bool) : Bool :=
  okOn G.C G.a G.all G.ds₁ G.xs₁ y τ₁ && okOn G.C G.a G.all G.ds₂ G.xs₂ y τ₂ &&
    okOn G.C G.a G.all G.ds₃ G.xs₃ y τ₃ &&
    dec (G.view₁ y τ₁ τ₂ τ₃) (G.view₂ y τ₁ τ₂ τ₃) (G.view₃ y τ₁ τ₂ τ₃)

end

/-- What the verifier messages of a whole run ask for. -/
def asksAt (ρ : Rho G.sh) : List Ask :=
  asksL G.a G.all G.xs₁ 0 G.ds₁ (PQ.drawnSL G.C G.ds₁ (G.rho₁ ρ)) ++
    (asksL G.a G.all G.xs₂ 0 G.ds₂ (PQ.drawnSL G.C G.ds₂ (G.rho₂ ρ)) ++
      asksL G.a G.all G.xs₃ 0 G.ds₃ (PQ.drawnSL G.C G.ds₃ (G.rho₃ ρ)))

end Stretches

/-- The protocol in three stretches, with any decision on the three views. -/
@[reducible] def Plain3 (G : Stretches) (dec : PQ.View → PQ.View → PQ.View → Bool) :
    InteractiveOracleProof Unit (oneExternalString (2 ^ G.a) PQ.SgX) where
  shape := G.sh
  blinded := fun _ => true
  extReads := fun _ ρ => ((G.asksAt ρ).filterMap (Ask.ext G.a)).toFinset
  reads := fun _ ρ _ => ((G.asksAt ρ).filterMap G.own).toFinset
  accept := fun _ y τ => G.accOn y (G.tr₁ τ) (G.tr₂ τ) (G.tr₃ τ) dec

end OnBytes.Slice
