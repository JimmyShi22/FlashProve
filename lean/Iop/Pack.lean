-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Pack.lean: protocols whose oracles are cut anew into positions: several old positions lie in one
new position, a column.

The file has definitions and three statements; the proofs are in Iop/PackProofs.lean. A round
(Iop/Shape.lean) has an oracle part `Orc` that is read at positions `Pos` with answers in `Sym`. The
protocols of Cb/ give each oracle message of a prover's message positions of its own. A Merkle leaf
of the programs holds a column: the symbols of several oracle messages at one place. The compiler
(Compile/) lays one position into one leaf and never takes a symbol apart. Between them is this one
construction: keep every round's `Orc`, `Plain` and `Chal`, and replace `Pos`, `Sym` and `rd` along
a
map of positions that may be many to one (`InteractiveOracleProof.pack`).

The datum for a round is a `Packing`: the columns, their alphabets, the column of an oracle (`col`),
in which column an old position lies (`colOf`), and its entry there (`prj`).
The verifier of the packed protocol reads the columns of the positions that the old one reads, and
decides as the old one does on the same messages.

Round-by-round soundness (`InteractiveOracleProof.Sound`) speaks of messages and challenges alone, so it is kept with
the same errors, for every datum (`Spec.pack_sound`). That the decision depends on the oracles only
where they are read (`InteractiveOracleProof.IsLocal`) is kept if an old symbol is the entry of its column
(`Packing.OK`; `Spec.pack_local`). That an oracle is a string given by its symbols (`Round.IsPoint`)
is kept if moreover a column is exactly the tuple of its entries (`Packing.Exact`;
`Round.IsPoint.pack`, Iop/PackProofs.lean).

Every other pass of this library on protocols (Iop/Pull.lean, Split, Join, Recut, Grind) maps
positions one to one. This one does not: so the positions read are an image, and the datum holds a
decision procedure for equality of columns.

Not claimed: nothing on the honest prover, on completeness, or on what a view discloses. `blinded`
at
a column is a field of the datum: by type any value. Nothing on protocols with slots
(Iop/Batch.lean).

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

-/
import Iop.InteractiveOracleProof

namespace Iop

/-- How the oracle of one round is cut anew into columns. -/
structure Packing (r : Round) where
  /-- the new positions: the columns -/
  Pos : Type
  /-- the alphabet at a column -/
  Sym : Pos → Type
  /-- the column of an oracle at a new position -/
  col : r.Orc → (q : Pos) → Sym q
  /-- in which column an old position lies -/
  colOf : r.Pos → Pos
  /-- the entry of an old position in its column -/
  prj : (p : r.Pos) → Sym (colOf p) → r.Sym p
  /-- is the oracle blinded at this column (by type any map; `InteractiveOracleProof.blinded`, Iop/InteractiveOracleProof.lean) -/
  blinded : Pos → Bool
  /-- the positions read are an image under `colOf` -/
  dec : DecidableEq Pos

/-- An old symbol is the entry of its column. -/
structure Packing.OK {r : Round} (k : Packing r) : Prop where
  prj_col : ∀ o p, k.prj p (k.col o (k.colOf p)) = r.rd o p

/-- A column is exactly the tuple of its entries: columns with the same entries are equal. Stated
for all columns at once, so that no column has to be carried along an equation of positions. (A
column in which no old position lies has then at most one symbol.) -/
structure Packing.Exact {r : Round} (k : Packing r) : Prop where
  ext : ∀ g g' : (q : k.Pos) → k.Sym q,
    (∀ p, k.prj p (g (k.colOf p)) = k.prj p (g' (k.colOf p))) → g = g'

/-- The same round, read column by column. -/
def Round.pack (r : Round) (k : Packing r) : Round :=
  { Orc := r.Orc, Pos := k.Pos, Sym := k.Sym, rd := k.col, Plain := r.Plain, Chal := r.Chal,
    dOrc := r.dOrc, dPlain := r.dPlain }

/-- One packing for each round. -/
def Packings : Shape → Type 1
  | [] => PUnit
  | r :: s => Packing r × Packings s

def Packings.OK : {s : Shape} → Packings s → Prop
  | [], _ => True
  | _ :: _, (k, ks) => k.OK ∧ Packings.OK ks

def Shape.pack : (s : Shape) → Packings s → Shape
  | [], _ => []
  | r :: s, (k, ks) => r.pack k :: Shape.pack s ks

/-- Verifier randomness does not change. -/
def Rho.unpack : {s : Shape} → (k : Packings s) → Rho (s.pack k) → Rho s
  | [], _, _ => ()
  | _ :: _, (_, ks), (c, ρ) => (c, Rho.unpack ks ρ)

/-- Messages and challenges do not change. -/
def Tr.unpack : {s : Shape} → (k : Packings s) → Tr (s.pack k) → Tr s
  | [], _, _ => ()
  | _ :: _, (_, ks), (m, c, τ) => (m, c, Tr.unpack ks τ)

def Plains.unpack : {s : Shape} → (k : Packings s) → Plains (s.pack k) → Plains s
  | [], _, _ => ()
  | _ :: _, (_, ks), (a, pl) => (a, Plains.unpack ks pl)

/-- The same errors. -/
def Err.pack : {s : Shape} → (k : Packings s) → Err s → Err (s.pack k)
  | [], _, _ => ()
  | _ :: _, (_, ks), (e, ε) => (e, Err.pack ks ε)

/-- in which column a position of the prover's oracles lies -/
def OPos.colOf : {s : Shape} → (k : Packings s) → OPos s → OPos (s.pack k)
  | _ :: _, (k, _), .inl p => .inl (k.colOf p)
  | _ :: _, (_, ks), .inr p => .inr (OPos.colOf ks p)

/-- its entry there -/
def OPos.prj : {s : Shape} → (k : Packings s) → (p : OPos s) →
    OSym (s.pack k) (OPos.colOf k p) → OSym s p
  | _ :: _, (k, _), .inl p => k.prj p
  | _ :: _, (_, ks), .inr p => OPos.prj ks p

def Packings.blinded : {s : Shape} → (k : Packings s) → OPos (s.pack k) → Bool
  | _ :: _, (k, _), .inl q => k.blinded q
  | _ :: _, (_, ks), .inr q => Packings.blinded ks q

def Packings.dec : {s : Shape} → (k : Packings s) → DecidableEq (OPos (s.pack k))
  | [], _ => fun a => nomatch a
  | _ :: _, (k, ks) =>
    haveI := k.dec
    haveI := Packings.dec ks
    inferInstanceAs (DecidableEq (k.Pos ⊕ OPos (Shape.pack _ ks)))

variable {X : Type} {E : ExtSpec}

/-- The protocol read column by column. -/
def InteractiveOracleProof.pack (Q : InteractiveOracleProof X E) (k : Packings Q.shape) : InteractiveOracleProof X E where
  shape    := Q.shape.pack k
  blinded  := k.blinded
  extReads := fun x ρ => Q.extReads x (Rho.unpack k ρ)
  reads    := fun x ρ pl =>
    haveI := k.dec
    (Q.reads x (Rho.unpack k ρ) (Plains.unpack k pl)).image (OPos.colOf k)
  accept   := fun x y τ => Q.accept x y (Tr.unpack k τ)

namespace Spec

/-- Statement: round-by-round soundness is kept, with the same errors, for every datum. -/
def pack_sound : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : InteractiveOracleProof X E) (k : Packings Q.shape) (L : X → E.Str → Prop)
      (ε : Err Q.shape),
    Q.Sound L ε → (Q.pack k).Sound L (Err.pack k ε)

/-- Statement: if an old symbol is the entry of its column, the decision of the packed protocol
depends on the oracles only at the columns read. -/
def pack_local : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : InteractiveOracleProof X E) (k : Packings Q.shape),
    k.OK → Q.IsLocal → (Q.pack k).IsLocal

/-- Statement: what the packed verifier reads of a transcript gives what the old one reads. -/
def pack_read : Prop :=
  ∀ (s : Shape) (k : Packings s), k.OK → ∀ (τ : Tr (s.pack k)) (p : OPos s),
    (Tr.unpack k τ).read p = OPos.prj k p (τ.read (OPos.colOf k p))

end Spec

end Iop
