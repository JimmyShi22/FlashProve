-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Split.lean: rounds are split: a prover message is sent in parts, each in a separate round.

Definitions and one statement. The proofs are in Iop/SplitProofs.lean. Many statements of this
library are written twice: a definition in the namespace `Spec` states a proposition, and a theorem
of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why. The compiler (Compile/) turns every round into one Fiat-Shamir query with one Merkle tree (for
`BatchProtocol`: one for each of the two components, Iop/BatchWire.lean) over all oracles of the prover
message. A program may instead hash every oracle and every plain message by a separate call, also
where the verifier says nothing between two of them, and give every oracle a separate tree.
The compiler is generic in the record of protocols (`BatchProtocol`; words of this
library: lean/GLOSSARY.md), and a round may have the empty challenge (Chal = Unit, Iop/Shape.lean).
So a record of protocols can be rewritten: a round whose prover message has several oracles and a
plain part becomes several rounds, each with one part of the message. After every part but the last
the verifier sends the empty challenge, and after the last part it sends the challenge of the old
round. The program's form is reached by this together with the optional roots of Iop/BatchWire.lean
(`has0`, `hasJ`). Without them every new round has a root, also a round without oracle.

Main names:
  `RCut r`: how the prover message of the round r is split in two: a first part (`c.fst`, with Chal
      = Unit) and the remainder (`c.snd`, with the challenge of r). The symbols of the parts are
      those of r by type: the alphabet at a position of a part is `r.Sym` at its image in `r.Pos`.
      So no term of this file needs a cast.
  `SPlan s`: a plan of splits for the list of rounds s: for each round, in order, either keep it, or
      split off a first part and go on with the remainder. It is an inductive family over lists of
      rounds, so that the maps below are structural recursions on the plan's three cases. `RPlan r`
      is the plan of a single round (a chain of splits).
  `P.shape`: the new list of rounds. `Tr.merge`, `Rho.merge`, `Plains.merge`, `OPos.mergeEquiv` go
      from the new list to the old one, `Strat.split`, `Err.split`, `InteractiveOracleProof.split`, `Honest.split` in
      the other direction.
Round-by-round soundness is preserved, and a new round has the error 0: `InteractiveOracleProof.Sound.split`
(Iop/SplitProofs.lean).

Related files:
  Iop/BatchSplit.lean, Iop/BatchSplitProofs.lean: the form for protocols with slots (`BatchProtocol`)
  Iop/SplitKit.lean: ready-made splits with their conditions
  Iop/SplitData.lean: the further data that the compiler asks of an instantiation: that oracles are
      strings, numberings, serializers

Notation: `Honest Q Wt` (a structure, Iop/InteractiveOracleProof.lean): the honest prover (among its fields:
`Bad : Set (Rho Q.shape)`, `Hid : Wt → X → Set (Rho Q.shape)`);
`H.withheld w x : Set (Rho Q.shape)` (there): the abort set, `H.Bad ∪ H.Hid w x`; `Rho s : Type`
(Iop/Shape.lean): the verifier's randomness of a whole execution.

Limits: nothing on which plan makes the protocols of an instantiation equal to what a given program
hashes: a plan is a datum of the instantiation. The number of rounds grows, so every number of the
compiler that counts rounds or queries changes.
-/
import Iop.InteractiveOracleProof

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. A split of one round -/

/-- A split of the prover message of the round r into a first part A and the remainder B. Oracle
part, plain part and positions are each split in two. -/
structure RCut (r : Round) where
  OrcA   : Type
  OrcB   : Type
  PosA   : Type
  PosB   : Type
  PlainA : Type
  PlainB : Type
  orc    : r.Orc ≃ OrcA × OrcB
  /-- every position of r is a position of exactly one part -/
  pos    : PosA ⊕ PosB ≃ r.Pos
  plain  : r.Plain ≃ PlainA × PlainB
  /-- the answers of the parts; the alphabet is that of r at the same position -/
  rdA    : OrcA → (p : PosA) → r.Sym (pos (.inl p))
  rdB    : OrcB → (p : PosB) → r.Sym (pos (.inr p))

variable {r : Round}

/-- The round of the first part: the challenge is empty. -/
@[reducible] def RCut.fst (c : RCut r) : Round where
  Orc := c.OrcA
  Pos := c.PosA
  Sym := fun p => r.Sym (c.pos (.inl p))
  rd := c.rdA
  Plain := c.PlainA
  Chal := Unit
  dOrc := (c.orc r.dOrc).1
  dPlain := (c.plain r.dPlain).1

/-- The round of the remainder: it ends with the challenge of r. -/
@[reducible] def RCut.snd (c : RCut r) : Round where
  Orc := c.OrcB
  Pos := c.PosB
  Sym := fun p => r.Sym (c.pos (.inr p))
  rd := c.rdB
  Plain := c.PlainB
  Chal := r.Chal
  dOrc := (c.orc r.dOrc).2
  dPlain := (c.plain r.dPlain).2

/-- The condition on a split: a position of a part is answered from that part only, as r answers it.
-/
structure RCut.OK (c : RCut r) : Prop where
  rdA : ∀ o p, r.rd o (c.pos (.inl p)) = c.rdA (c.orc o).1 p
  rdB : ∀ o p, r.rd o (c.pos (.inr p)) = c.rdB (c.orc o).2 p

/-- the prover message of r from its two parts -/
def RCut.join (c : RCut r) (a : c.fst.Msg) (b : c.snd.Msg) : r.Msg :=
  (c.orc.symm (a.1, b.1), c.plain.symm (a.2, b.2))
/-- the first part of a prover message of r -/
def RCut.left (c : RCut r) (m : r.Msg) : c.fst.Msg := ((c.orc m.1).1, (c.plain m.2).1)
/-- the remainder of a prover message of r -/
def RCut.right (c : RCut r) (m : r.Msg) : c.snd.Msg := ((c.orc m.1).2, (c.plain m.2).2)

/-- A transcript that begins with the remainder of the message, with the first part put back. -/
def RCut.glue (c : RCut r) {s : Shape} (a : c.fst.Msg) (z : Tr (c.snd :: s)) : Tr (r :: s) :=
  (c.join a z.1, z.2.1, z.2.2)

/-- Positions: those of the first part, then those of a list of rounds that begins with the
remainder. -/
def RCut.posAssoc (c : RCut r) (s : Shape) : c.PosA ⊕ OPos (c.snd :: s) ≃ OPos (r :: s) :=
  (Equiv.sumAssoc c.PosA c.PosB (OPos s)).symm.trans (Equiv.sumCongr c.pos (Equiv.refl (OPos s)))

/-- The alphabet at a position does not change when the first part is put back. -/
def RCut.symUp (c : RCut r) {s : Shape} :
    (z : OPos (c.snd :: s)) → OSym (c.snd :: s) z → OSym (r :: s) (c.posAssoc s (.inr z))
  | .inl _, a => a
  | .inr _, a => a

/-- The map back. -/
def RCut.symDown (c : RCut r) {s : Shape} :
    (z : OPos (c.snd :: s)) → OSym (r :: s) (c.posAssoc s (.inr z)) → OSym (c.snd :: s) z
  | .inl _, a => a
  | .inr _, a => a

/-! ## 2. Plans -/

/-- A plan of splits: go through the rounds; keep a round as it is, or split off a first part and go
on with the remainder of the round (which may be split again). -/
inductive SPlan : Shape → Type 1
  | nil : SPlan []
  | keep (r : Round) {s : Shape} (P : SPlan s) : SPlan (r :: s)
  | cut {r : Round} {s : Shape} (c : RCut r) (P : SPlan (c.snd :: s)) : SPlan (r :: s)

/-- The new rounds. -/
def SPlan.shape : {s : Shape} → SPlan s → Shape
  | _, .nil => []
  | _, .keep r P => r :: P.shape
  | _, .cut c P => c.fst :: P.shape

/-- All splits of the plan satisfy `RCut.OK`. -/
def SPlan.OK : {s : Shape} → SPlan s → Prop
  | _, .nil => True
  | _, .keep _ P => P.OK
  | _, .cut c P => c.OK ∧ P.OK

/-- The number of splits: the new list has this many rounds more. -/
def SPlan.cuts : {s : Shape} → SPlan s → ℕ
  | _, .nil => 0
  | _, .keep _ P => P.cuts
  | _, .cut _ P => P.cuts + 1

/-- Where an old round begins: the number (counted from 0) in the new list of the first part of the
old round number n. -/
def SPlan.idx : {s : Shape} → SPlan s → ℕ → ℕ
  | _, .nil, n => n
  | _, .keep _ _, 0 => 0
  | _, .keep _ P, n + 1 => P.idx n + 1
  | _, .cut _ _, 0 => 0
  | _, .cut _ P, n + 1 => P.idx (n + 1) + 1


/-- The plan of one round: a chain of splits. -/
inductive RPlan : Round → Type 1
  | keep (r : Round) : RPlan r
  | cut {r : Round} (c : RCut r) (rest : RPlan c.snd) : RPlan r


/-! ## 3. From the new list of rounds to the old one

In the definitions below an element of a type that depends on the new list is taken apart by
projections, after its type has been written out for the case at hand. -/

/-- The old transcript: the parts of each prover message are put together, the empty challenges are
dropped. -/
def Tr.merge : {s : Shape} → (P : SPlan s) → Tr P.shape → Tr s
  | _, .nil => fun _ => ()
  | _, .keep r P => fun (z : r.Msg × r.Chal × Tr P.shape) => (z.1, z.2.1, Tr.merge P z.2.2)
  | _, .cut c P => fun (z : c.fst.Msg × Unit × Tr P.shape) => c.glue z.1 (Tr.merge P z.2.2)

/-- The old verifier randomness: the empty challenges are dropped. -/
def Rho.merge : {s : Shape} → (P : SPlan s) → Rho P.shape → Rho s
  | _, .nil => fun _ => ()
  | _, .keep r P => fun (z : r.Chal × Rho P.shape) => (z.1, Rho.merge P z.2)
  | _, .cut c P => fun (z : Unit × Rho P.shape) => Rho.merge (s := c.snd :: _) P z.2

/-- In the other direction: empty challenges are put in. -/
def Rho.split : {s : Shape} → (P : SPlan s) → Rho s → Rho P.shape
  | _, .nil => fun _ => ()
  | _, .keep r P => fun (z : r.Chal × Rho _) => (z.1, Rho.split P z.2)
  | _, .cut _ P => fun ρ => ((), Rho.split P ρ)

/-- The old plain parts: the plain parts of the parts of each prover message are put together. -/
def Plains.merge : {s : Shape} → (P : SPlan s) → Plains P.shape → Plains s
  | _, .nil => fun _ => ()
  | _, .keep r P => fun (z : r.Plain × Plains P.shape) => (z.1, Plains.merge P z.2)
  | _, .cut c P =>
    fun (z : c.PlainA × Plains P.shape) =>
      (c.plain.symm (z.1, (Plains.merge P z.2).1), (Plains.merge P z.2).2)

/-- In the other direction: each plain part is split. -/
def Plains.split : {s : Shape} → (P : SPlan s) → Plains s → Plains P.shape
  | _, .nil => fun _ => ()
  | _, .keep r P => fun (z : r.Plain × Plains _) => (z.1, Plains.split P z.2)
  | _, .cut (r := r) c P =>
    fun (z : r.Plain × Plains _) => ((c.plain z.1).1, Plains.split P ((c.plain z.1).2, z.2))

/-- The positions of the new rounds are those of the old ones. -/
def OPos.mergeEquiv : {s : Shape} → (P : SPlan s) → OPos P.shape ≃ OPos s
  | _, .nil => Equiv.refl Empty
  | _, .keep r P => Equiv.sumCongr (Equiv.refl r.Pos) (OPos.mergeEquiv P)
  | _, .cut (s := s) c P =>
    (Equiv.sumCongr (Equiv.refl c.PosA) (OPos.mergeEquiv P)).trans (c.posAssoc s)

/-- The alphabet at a position does not change. -/
def OSym.merge :
    {s : Shape} → (P : SPlan s) → (p : OPos P.shape) → OSym P.shape p → OSym s (OPos.mergeEquiv P p)
  | _, .nil => fun p => Empty.elim p
  | _, .keep r P => fun (p : r.Pos ⊕ OPos P.shape) => match p with
      | .inl _ => fun a => a
      | .inr q => fun a => OSym.merge P q a
  | _, .cut c P => fun (p : c.PosA ⊕ OPos P.shape) => match p with
      | .inl _ => fun a => a
      | .inr q => fun a => c.symUp (OPos.mergeEquiv P q) (OSym.merge P q a)

/-- The map back. -/
def OSym.split :
    {s : Shape} → (P : SPlan s) → (p : OPos P.shape) → OSym s (OPos.mergeEquiv P p) → OSym P.shape p
  | _, .nil => fun p => Empty.elim p
  | _, .keep r P => fun (p : r.Pos ⊕ OPos P.shape) => match p with
      | .inl _ => fun a => a
      | .inr q => fun a => OSym.split P q a
  | _, .cut c P => fun (p : c.PosA ⊕ OPos P.shape) => match p with
      | .inl _ => fun a => a
      | .inr q => fun a => OSym.split P q (c.symDown (OPos.mergeEquiv P q) a)

/-! ## 4. From the old rounds to the new ones -/

/-- A strategy sends each of its messages part by part. -/
def Strat.split : {s : Shape} → {β : Type} → (P : SPlan s) → Strat s β → Strat P.shape β
  | _, _, .nil => fun b => b
  | _, β, .keep r P =>
    fun (z : r.Msg × (r.Chal → Strat _ β)) => (z.1, fun c => Strat.split P (z.2 c))
  | _, β, .cut (r := r) c P =>
    fun (z : r.Msg × (r.Chal → Strat _ β)) =>
      (c.left z.1, fun _ => Strat.split P (c.right z.1, z.2))

/-- Errors: a new round has the error 0; the last part of a round has the error of the round. -/
def Err.split : {s : Shape} → (P : SPlan s) → Err s → Err P.shape
  | _, .nil => fun _ => ()
  | _, .keep _ P => fun (z : ℕ × Err _) => (z.1, Err.split P z.2)
  | _, .cut _ P => fun ε => (0, Err.split P ε)

variable {X : Type} {E : ExtSpec}

/-- The protocol with its prover messages sent in parts. The verifier reads the same positions and
decides as before, on the old transcript (`Tr.merge`). -/
def InteractiveOracleProof.split (Q : InteractiveOracleProof X E) (P : SPlan Q.shape) : InteractiveOracleProof X E where
  shape    := P.shape
  blinded  := fun p => Q.blinded (OPos.mergeEquiv P p)
  extReads := fun x ρ => Q.extReads x (Rho.merge P ρ)
  reads    := fun x ρ pl =>
    (Q.reads x (Rho.merge P ρ) (Plains.merge P pl)).map (OPos.mergeEquiv P).symm.toEmbedding
  accept   := fun x y τ => Q.accept x y (Tr.merge P τ)

/-- The honest prover: the same coins and the same external string; the honest strategy sends its
messages in parts; a value of the verifier randomness is in the abort set (`Honest.withheld`,
Iop/InteractiveOracleProof.lean: `H.Bad ∪ H.Hid w x`) if the old one is, after the empty challenges are dropped
(`Rho.merge`): so in each of the two fields `Bad` and `Hid`. -/
def Honest.split {Q : InteractiveOracleProof X E} {Wt : Type} (H : Honest Q Wt) (P : SPlan Q.shape) :
    Honest (Q.split P) Wt where
  Coin  := H.Coin
  ext   := H.ext
  strat := fun w x c => Strat.split P (H.strat w x c)
  Bad   := {ρ | Rho.merge P ρ ∈ H.Bad}
  Hid   := fun w x => {ρ | Rho.merge P ρ ∈ H.Hid w x}

/-! ## 5. The statement -/

namespace Spec

/-- The new list has one round more for each split. -/
def splitLength : Prop := ∀ (s : Shape) (P : SPlan s), P.shape.length = s.length + P.cuts


end Spec

end Iop
