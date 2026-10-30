-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean.
HERE: AN ASSUMPTION OF THESE DATA, NO RULE OF THE FORMAT: ONE DRAW SERVES ALL THE TREES THAT A ROUND
OPENS (wantedL gives each tree of d.opens ALL the round's draws). A round whose draws are DIVIDED
among several trees (the format's R7.19) cannot be said in a Fmt.Spec, and ok cannot notice it;
shipped at one round alone, over stored tables, which ok refuses. A tree that no round of the chain
opens gets the stand-in bareShape: of its root these data know only that 32 bytes enter the hash
chain:
THAT IS THE SHIPPED CASE at the one shipped chain where ok holds (the second root of the proof's
first chain).

OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean: THE ROUNDS' DATA WITH A LIST OF TREES A ROUND. After the library's
Run/PlanQTypes.lean, declaration for declaration, as far as the skeleton's road (Run/PlanQS.lean)
needs it.
THE LIBRARY's FILE STANDS ON NO DECLARATION OF THE COMPILER's ROAD: IT DIFFERS BY MATTER: RD.tree :
Option Shape ("the shape of the tree whose root this round sends") against RD.trees : List Shape.
  DIFFER      RD (trees), rdsFrom, ok (roots ≤ maxRt), treeSh
  OWN         PosT, SymT, zeroT, colT, treeT, placeT, posAtT, finPosT, decPosT: the positions of a
              round with
              several trees, each tree with its own depth AND ITS OWN ALPHABET (a column of its own
              width); placeT_lt, posAtT_place, place_posAtT, posAtT_none: what a wire's laws ask of
              them
  THE SAME TEXT (they name RD)      rds, wantedL, wanted
  LEFT TO THE LIBRARY      ownNo, allOpens, shapeOfOwn, bareShape, nRoots, e0, CK, PlainOf and its
                           four, RV,
              View, E0
  NOT HERE    posN, colW (PosT | SymT stand for them)
  USED   ok, rds, rdsFrom: by the tie from a parsed file (Run/PageIs*.lean), Run/PlanQSpell.lean,
         Run/PlanQX*.lean; Run/PlanQJoin.lean: rds_ofLib: at one root a round they are the
              library's. ok SHUTS THE KEY OUT: it differs in one clause (roots ≤ maxRt) and
              keeps "no tree given from outside" (false at the key's second chain), "each own tree
              opened at most once" and "the randomness stands in the file" (false at its shared
              chain)
  NOT SAID (the road without skeletons)      roundOf, r0, shapeL, shapeOf, gL, gOf, drawnL, rvL,
                                             posAt, colAt,
              viewL, viewOf, decL, decO, Q0, QT; opensEachOnce(_le)

Terms: lean/GLOSSARY.md.

-/
import Run.PlanQTypes
import OnBytes.TypedOracleCompiler.Iop.BatchWire

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open _root_.Iop _root_.Run.PQ

/-! ## The rounds' data -/

structure RD where
  entry : _root_.Fmt.Entry
  kind  : _root_.Fmt.Kind
  items : List _root_.Fmt.Item
  /-- Here: the shapes of the trees whose roots this round sends, in the order of the roots -/
  trees : List _root_.Fmt.Shape
  opens : List Nat

def rdsFrom (S : _root_.Fmt.Spec) : Nat → List _root_.Fmt.Round → List RD
  | _, [] => []
  | sent, r :: rs =>
    ⟨r.entry, r.kind, r.items,
        (List.range r.entry.roots).map fun k =>
          (shapeOfOwn S (sent + k)).getD (bareShape S.firstTree (sent + k)),
        r.opens.filterMap ownNo⟩ ::
      rdsFrom S (sent + r.entry.roots) rs

def rds (S : _root_.Fmt.Spec) : List RD := rdsFrom S 0 S.rounds

/-- The limits. (Here: at most maxRt roots a round, where the library has at most one.) -/
def ok (S : _root_.Fmt.Spec) : Bool :=
  S.ok && S.rounds.all (·.entry.roots ≤ TypedOracleCompiler.Iop.maxRt) &&
  (allOpens S).all (fun o => (ownNo o).isSome) &&
  (List.range (nRoots S)).all
    (fun n => decide (((allOpens S).filter fun o => ownNo o == some n).length ≤ 1)) &&
  (match S.rand with
    | .inFile => true
    | _ => false)

/-! ## Here: the positions of a round with several trees -/

/-- the positions: those of the first tree, or those of the later ones -/
def PosT : List _root_.Fmt.Shape → Type
  | [] => Empty
  | s :: ts => Fin (2 ^ s.a) ⊕ PosT ts

/-- the alphabet at a position: a column of its own tree's width -/
def SymT : (ts : List _root_.Fmt.Shape) → PosT ts → Type
  | s :: _, .inl _ => Fin s.W → UInt64
  | _ :: ts, .inr p => SymT ts p

def zeroT : (ts : List _root_.Fmt.Shape) → (p : PosT ts) → SymT ts p
  | _ :: _, .inl _ => fun _ => (0 : UInt64)
  | _ :: ts, .inr p => zeroT ts p

/-- a column as a list of words -/
def colT : (ts : List _root_.Fmt.Shape) → (p : PosT ts) → SymT ts p → List UInt64
  | _ :: _, .inl _, c => List.ofFn c
  | _ :: ts, .inr p, c => colT ts p c

/-- the number of a position's tree among the round's trees -/
def treeT : (ts : List _root_.Fmt.Shape) → PosT ts → ℕ
  | _ :: _, .inl _ => 0
  | _ :: ts, .inr p => treeT ts p + 1

/-- the number of its leaf in that tree -/
def placeT : (ts : List _root_.Fmt.Shape) → PosT ts → ℕ
  | _ :: _, .inl x => x.val
  | _ :: ts, .inr p => placeT ts p

/-- the position at (tree, leaf) -/
def posAtT : (ts : List _root_.Fmt.Shape) → ℕ → ℕ → Option (PosT ts)
  | [], _, _ => none
  | s :: _, 0, j => if h : j < 2 ^ s.a then some (.inl ⟨j, h⟩) else none
  | _ :: ts, k + 1, j => (posAtT ts k j).map .inr

@[reducible] def finPosT : (ts : List _root_.Fmt.Shape) → Fintype (PosT ts)
  | [] => inferInstanceAs (Fintype Empty)
  | s :: ts => by
      haveI := finPosT ts
      exact inferInstanceAs (Fintype (Fin (2 ^ s.a) ⊕ PosT ts))

def decPosT : (ts : List _root_.Fmt.Shape) → DecidableEq (PosT ts)
  | [] => inferInstanceAs (DecidableEq Empty)
  | s :: ts => by
      haveI := decPosT ts
      exact inferInstanceAs (DecidableEq (Fin (2 ^ s.a) ⊕ PosT ts))

theorem placeT_lt :
    ∀ (ts : List _root_.Fmt.Shape) (p : PosT ts),
      ∃ d, (ts.map (·.a))[treeT ts p]? = some d ∧ placeT ts p < 2 ^ d
  | s :: _, .inl x => ⟨s.a, rfl, x.isLt⟩
  | _ :: ts, .inr p => by
      obtain ⟨d, h1, h2⟩ := placeT_lt ts p
      exact ⟨d, by simpa [treeT] using h1, h2⟩

theorem posAtT_place :
    ∀ (ts : List _root_.Fmt.Shape) (p : PosT ts), posAtT ts (treeT ts p) (placeT ts p) = some p
  | _ :: _, .inl x => dif_pos x.isLt
  | _ :: ts, .inr p => by
      show (posAtT ts (treeT ts p) (placeT ts p)).map Sum.inr = _
      rw [posAtT_place ts p]
      rfl

theorem place_posAtT :
    ∀ (ts : List _root_.Fmt.Shape) (k j : ℕ) (p : PosT ts),
      posAtT ts k j = some p → treeT ts p = k ∧ placeT ts p = j
  | [], _, _, _, h => by cases h
  | s :: _, 0, j, p, h => by
      have h0 : (if h : j < 2 ^ s.a then some (.inl ⟨j, h⟩) else none) = some p := h
      by_cases hj : j < 2 ^ s.a
      · rw [dif_pos hj] at h0
        cases Option.some.inj h0
        exact ⟨rfl, rfl⟩
      · rw [dif_neg hj] at h0
        cases h0
  | _ :: ts, k + 1, j, p, h => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1
          (show (posAtT ts k j).map Sum.inr = some p from h)
      obtain ⟨h1, h2⟩ := place_posAtT ts k j q hq
      exact ⟨congrArg (· + 1) h1, h2⟩

theorem posAtT_none :
    ∀ (ts : List _root_.Fmt.Shape) (k : ℕ), ts.length ≤ k → ∀ j, posAtT ts k j = none
  | [], _, _, _ => rfl
  | _ :: _, 0, h, _ => by cases h
  | _ :: ts, k + 1, h, j => by
      show (posAtT ts k j).map Sum.inr = none
      rw [posAtT_none ts k (Nat.le_of_succ_le_succ h) j]
      rfl

/-! ## The untyped view -/

/-- the shape of own tree n (here: the trees are numbered through the rounds, a round's in their
order) -/
def treeSh : List RD → Nat → Option _root_.Fmt.Shape
  | [], _ => none
  | d :: ds, n => if n < d.trees.length then d.trees[n]? else treeSh ds (n - d.trees.length)

/-- Which (tree, position) the drawn positions ask for. -/
def wantedL (all : List RD) : List RD → List _root_.Fmt.Drawn → List (Nat × Nat)
  | d :: ds, D :: Ds =>
    (d.opens.flatMap fun n =>
      match treeSh all n with
      | none => []
      | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x)) ++
          wantedL all ds Ds
  | _, _ => []

def wanted (ds : List RD) (Ds : List _root_.Fmt.Drawn) : List (Nat × Nat) := wantedL ds ds Ds

end TypedOracleCompiler.Run.PQ
