-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TreesOne.lean: at rounds with at most one tree, the typed rounds that
OnBytes/Maker/Trees.lean names are the library's (Run/PlanQTypes.lean, Run/PlanQS.lean), up to how a
position is written.

OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean and OnBytes/TypedOracleCompiler/Run/PlanQS.lean say the library's
Run/PlanQTypes.lean's and Run/PlanQS.lean's definitions again for rounds that may send several
roots; Trees.lean's names stand for theirs by definition. This file ties that second text to the
first where both speak: at a list `ds` of the library's rounds' data (`RD`), read as data with a
list of trees (`ofRD`: no tree, or the one).

A round's plain part and its verifier's message are the same types in both texts. Its positions are
not: the library has `Fin (posN t)`, the second text has `PosT t.toList` (Trees.lean's name for it),
which is `Empty` or `Fin (2 ^ s.a) ⊕ Empty`. So the tie is maps on positions, oracles, verifier's
messages and transcripts (there and back, and inverse, on one round's positions and oracles and on
transcripts; there alone on a chain's positions and verifier's messages), and equations that carry
each definition over.

What the file contains.
  `ofRD`: a round's data of the library, as data with a list of trees; no stored table.
  `posOne`, `posOneBack`, `orcOne`, `orcOneBack`: one round's positions and oracles, there and back.
  `rhoOne`, `trOne`, `trOneBack`, `oposOne`: for a chain: transcripts there and back; verifier's
    messages and positions there alone.
  `posOne_back`, `posOneBack_one`, `orcOne_back`, `orcOneBack_one`, `trOne_back`, `trOneBack_one`:
    the maps are inverse to each other.
  `drawnT_one`, `passT_one`, `rhoT_one`, `rvT_one`, `treeShT_one`, `posAtST_one`, `colAtST_one`:
    Trees.lean's names `drawnT`, `passT`, `rhoT`, `rvT`, `treeShT`, `posAtST`, `colAtST` for the
    second text's definitions, at `ds.map ofRD`, are the library's `drawnSL`, `passSL`, `rhoSL`,
    `rvSL`, `posAtS`, `colAtS` (Run/PlanQS.lean) and `treeSh` (Run/PlanQTypes.lean) at `ds`, along
    these maps.

What is not claimed. Nothing on a wiring, on a compiled verifier or on a run. Nothing at a round
with two trees, where the library has no text. OnBytes/TypedOracleCompiler/Run/PlanQJoin.lean (`ofLib`,
`treeSh_ofLib`), OnBytes/TypedOracleCompiler/Slice/CarryOne.lean (`posOne`, `rOne`, `sOne`) and
OnBytes/TypedOracleCompiler/Slice/EntryAccept.lean (`drawn_back`, `pass_back`, `rv_back`, `col_back`) hold the way
back and the same equations along it; the two are not joined.


-/
import OnBytes.Maker.Trees

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ

/-- A round's data of the library, as data with a list of trees. -/
def ofRD (d : RD) : RDT := ⟨⟨d.entry, d.kind, d.items, d.tree.toList, d.opens⟩, []⟩

/-! ## One round -/

def posOne : (t : Option Fmt.Shape) → Fin (posN t) → PosT t.toList
  | none, x => x.elim0
  | some _, x => .inl x

def posOneBack : (t : Option Fmt.Shape) → PosT t.toList → Fin (posN t)
  | none, p => nomatch p
  | some _, .inl x => x
  | some _, .inr p => nomatch p

theorem posOne_back : ∀ (t : Option Fmt.Shape) (p : PosT t.toList), posOne t (posOneBack t p) = p
  | none, p => nomatch p
  | some _, .inl _ => rfl
  | some _, .inr p => nomatch p

theorem posOneBack_one : ∀ (t : Option Fmt.Shape) (x : Fin (posN t)), posOneBack t (posOne t x) = x
  | none, x => x.elim0
  | some _, _ => rfl

def orcOne : (t : Option Fmt.Shape) → (Fin (posN t) → Fin (colW t) → UInt64) →
    (p : PosT t.toList) → SymT t.toList p
  | none, _, p => nomatch p
  | some _, o, .inl x => o x
  | some _, _, .inr p => nomatch p

def orcOneBack : (t : Option Fmt.Shape) → ((p : PosT t.toList) → SymT t.toList p) →
    Fin (posN t) → Fin (colW t) → UInt64
  | none, _, x => x.elim0
  | some _, o, x => o (.inl x)

theorem orcOne_back : ∀ (t : Option Fmt.Shape) (o : (p : PosT t.toList) → SymT t.toList p),
    orcOne t (orcOneBack t o) = o
  | none, _ => funext fun p => nomatch p
  | some _, _ => funext fun p => match p with
    | .inl _ => rfl
    | .inr q => nomatch q

theorem orcOneBack_one : ∀ (t : Option Fmt.Shape) (o : Fin (posN t) → Fin (colW t) → UInt64),
    orcOneBack t (orcOne t o) = o
  | none, _ => funext fun x => x.elim0
  | some _, _ => rfl

/-! ## A chain -/

section
variable (C : CK)

def rhoOne : (ds : List RD) → Rho (uL C ds) → Rho (uLT C (ds.map ofRD))
  | [], _ => ()
  | _ :: ds, (c, ρ) => (c, rhoOne ds ρ)

def trOne : (ds : List RD) → Iop.Tr (uL C ds) → Iop.Tr (uLT C (ds.map ofRD))
  | [], _ => ()
  | d :: ds, (m, c, τ) => ((orcOne d.tree m.1, m.2), c, trOne ds τ)

def trOneBack : (ds : List RD) → Iop.Tr (uLT C (ds.map ofRD)) → Iop.Tr (uL C ds)
  | [], _ => ()
  | d :: ds, (m, c, τ) => ((orcOneBack d.tree m.1, m.2), c, trOneBack ds τ)

def oposOne : (ds : List RD) → OPos (uL C ds) → OPos (uLT C (ds.map ofRD))
  | d :: _, .inl x => .inl (posOne d.tree x)
  | _ :: ds, .inr p => .inr (oposOne ds p)

theorem trOne_back : ∀ (ds : List RD) (τ : Iop.Tr (uLT C (ds.map ofRD))),
    trOne C ds (trOneBack C ds τ) = τ
  | [], _ => rfl
  | d :: ds, ((o, pl), c, τ) => by
      show ((orcOne d.tree (orcOneBack d.tree o), pl), c, trOne C ds (trOneBack C ds τ)) =
        ((o, pl), c, τ)
      rw [orcOne_back, trOne_back ds τ]
      rfl

theorem trOneBack_one : ∀ (ds : List RD) (τ : Iop.Tr (uL C ds)), trOneBack C ds (trOne C ds τ) = τ
  | [], _ => rfl
  | d :: ds, ((o, pl), c, τ) => by
      show ((orcOneBack d.tree (orcOne d.tree o), pl), c, trOneBack C ds (trOne C ds τ)) =
        ((o, pl), c, τ)
      rw [orcOneBack_one, trOneBack_one ds τ]

/-! ## Each definition, carried over -/

theorem drawnT_one : ∀ (ds : List RD) (ρ : Rho (uL C ds)),
    drawnT C (ds.map ofRD) (rhoOne C ds ρ) = drawnSL C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) =>
    congrArg (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: ·) (drawnT_one ds ρ)

theorem passT_one : ∀ (ds : List RD) (ρ : Rho (uL C ds)),
    passT C (ds.map ofRD) (rhoOne C ds ρ) = passSL C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => congrArg (GChal.pass (b := d.entry.work) c && ·) (passT_one ds ρ)

theorem rhoT_one : ∀ (ds : List RD) (τ : Iop.Tr (uL C ds)),
    rhoT C (ds.map ofRD) (trOne C ds τ) = rhoOne C ds (rhoSL C ds τ)
  | [], _ => rfl
  | _ :: ds, (_, c, τ) => congrArg (Prod.mk c) (rhoT_one ds τ)

theorem rvT_one : ∀ (ds : List RD) (τ : Iop.Tr (uL C ds)),
    rvT C (ds.map ofRD) (trOne C ds τ) = rvSL C ds τ
  | [], _ => rfl
  | d :: ds, (m, c, τ) =>
    congrArg ((⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
      C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ : RV) :: ·) (rvT_one ds τ)

end

theorem treeShT_one : ∀ (ds : List RD) (n : ℕ), treeShT (ds.map ofRD) n = treeSh ds n
  | [], _ => rfl
  | ⟨_, _, _, none, _⟩ :: ds, n => by
      show (if n < 0 then _ else treeShT (ds.map ofRD) (n - 0)) = treeSh ds n
      rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero, treeShT_one ds n]
  | ⟨_, _, _, some s, _⟩ :: ds, n => by
      show (if n < 1 then [s][n]? else treeShT (ds.map ofRD) (n - 1)) =
        if n = 0 then some s else treeSh ds (n - 1)
      by_cases h : n = 0
      · subst h
        rfl
      · rw [if_neg (by omega), if_neg h, treeShT_one ds (n - 1)]

theorem posAtST_one (C : CK) : ∀ (ds : List RD) (n x : ℕ),
    posAtST C (ds.map ofRD) n x = (posAtS C ds n x).map (oposOne C ds)
  | [], _, _ => rfl
  | ⟨e, k, it, none, op⟩ :: ds, n, x => by
      show (if n < 0 then _ else (posAtST C (ds.map ofRD) (n - 0) x).map Sum.inr) =
        ((posAtS C ds n x).map Sum.inr).map (oposOne C (⟨e, k, it, none, op⟩ :: ds))
      rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero, posAtST_one C ds n x]
      cases posAtS C ds n x <;> rfl
  | ⟨e, k, it, some s, op⟩ :: ds, n, x => by
      show (if n < 1 then (posAtT [s] n x).map Sum.inl
          else (posAtST C (ds.map ofRD) (n - 1) x).map Sum.inr) =
        (if n = 0 then (if h : x < 2 ^ s.a then some (Sum.inl ⟨x, h⟩) else none)
          else (posAtS C ds (n - 1) x).map Sum.inr).map (oposOne C (⟨e, k, it, some s, op⟩ :: ds))
      by_cases h : n = 0
      · subst h
        rw [if_pos Nat.one_pos, if_pos rfl]
        by_cases hx : x < 2 ^ s.a
        · have e : posAtT [s] 0 x = some (.inl ⟨x, hx⟩) := dif_pos hx
          rw [e, dif_pos hx]
          rfl
        · have e : posAtT [s] 0 x = none := dif_neg hx
          rw [e, dif_neg hx]
          rfl
      · rw [if_neg (by omega), if_neg h, posAtST_one C ds (n - 1) x]
        cases posAtS C ds (n - 1) x <;> rfl

theorem colAtST_one (C : CK) : ∀ (ds : List RD) (τ : Iop.Tr (uL C ds)) (n x : ℕ),
    colAtST C (ds.map ofRD) (trOne C ds τ) n x = colAtS C ds τ n x
  | [], _, _, _ => rfl
  | ⟨_, _, _, none, _⟩ :: ds, (_, _, τ), n, x => by
      show (if n < 0 then _ else colAtST C (ds.map ofRD) (trOne C ds τ) (n - 0) x) =
        colAtS C ds τ n x
      rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero, colAtST_one C ds τ n x]
  | ⟨_, _, _, some s, _⟩ :: ds, (m, _, τ), n, x => by
      show (if n < 1 then (posAtT [s] n x).map fun p => colT [s] p (orcOne (some s) m.1 p)
          else colAtST C (ds.map ofRD) (trOne C ds τ) (n - 1) x) =
        if n = 0 then (if h : x < 2 ^ s.a then some (List.ofFn (m.1 ⟨x, h⟩)) else none)
          else colAtS C ds τ (n - 1) x
      by_cases h : n = 0
      · subst h
        rw [if_pos Nat.one_pos, if_pos rfl]
        by_cases hx : x < 2 ^ s.a
        · have e : posAtT [s] 0 x = some (.inl ⟨x, hx⟩) := dif_pos hx
          rw [e, dif_pos hx]
          rfl
        · have e : posAtT [s] 0 x = none := dif_neg hx
          rw [e, dif_neg hx]
          rfl
      · rw [if_neg (by omega), if_neg h, colAtST_one C ds τ (n - 1) x]

end OnBytes.Maker
