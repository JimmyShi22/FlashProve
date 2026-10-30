-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQTypes.lean: from a description of a proof's rounds in the programs' format to a protocol in
the form that the compiled verifier takes.

The programs are the C++ implementation that comes with this Lean code. Fmt/Rules8.lean describes a
proof (a chain of rounds) as a reader needs it (`Fmt.Spec`: label, plan, rounds with their items and
openings). Run/ToyQ.lean writes out directly, for one example, rounds, shape and protocol. All of
that except the decision is a function of the description and of the choice of challenge types (`C`,
below). This file is that function.
The protocol is a public-coin interactive oracle protocol of fixed shape, a value of `InteractiveOracleProof`
(Iop/InteractiveOracleProof.lean), which the compiled verifier takes as `BatchInteractiveOracleProof.ofProto` of it (Iop/Batch.lean).
The compiled verifier is `Compile.Batch.verifyOneProtocol` (Compile/Batch/Verifier.lean).

Sources. Fmt/Rules8.lean's Spec was written against the format page (docs/format/FORMAT.md, which
comes with the programs) in an edition that is not the one that ships. The design. All rounds are
uniform: there is one definition
`roundOf`, whose own term has no case split on a round's kind or on whether it sends a root: where
`d.tree` is `none` the oracle has 0 positions of width 0 (`posN`, `colW`, by cases on `d.tree`). The
decision is given on an untyped view: `Q0` accepts if `dec` accepts (for each round: the items read
and what was drawn; the opened columns); `QT` tests the proof of work besides. So a further protocol
needs a description and a decision on the format's own data, and no typed term.

1. What the file contains. Definitions that can be evaluated, and one theorem (part 3).
   `RD`: A round's data: the plan's entry; the kind; the message's items; the shape (`Fmt.Shape`) of
     the tree whose root this round sends (the description has a tree's shape where it is opened, so
     `rds` looks ahead; a tree that is opened nowhere gets `bareShape`); the own trees (by their
     number in the order of sending) that are opened at this round's drawn positions.
   `rds S`, `ok S`: The rounds' data. The limits, as a test: the description's own conditions; at
     most one root a round; no tree given from outside; each own tree opened at most once; the
     chain's random bytes stand in the file.
   `opensEachOnce S`: Each own tree is opened exactly once. No limit: a test for a description that
     is meant to open all its trees (Run/PlanQSOnce.lean tests it at the descriptions that its head
     names).
   `C : CK`: The choice of challenge types, a parameter: for each entry and kind a finite, nonempty
     type `C.Ch e k` of verifier messages, and `C.dr`, its map to the format's record of what was
     drawn. (Which type: at `ck` (Run/PlanDrawsQ.lean) the values of the round's draws themselves,
     so that the law of the wiring's sampler can be had; at `ckP` (Run/PlanPull.lean) a round's hash
     blocks; that is another file's matter.) (The block samplers' law with a bias:
     `Spec.planQ_samplers`, Run/PlanDrawsQ.lean; the exact law: `ChalUnif`, Run/PlanQWireLaws.lean,
     the head.)
   `PlainOf items`: The plain part of a prover's message: the items except the roots. `dflt`; `gots`
     (as the format's items read); `ofGots` (back, from a message's items read, roots passed over;
     refused if they do not fit); `bytes` (the message's bytes, the root at its place among the
     items).
   `roundOf C d`, `r0`, `shapeL`, `shapeOf`, `gL`, `gOf`: The rounds; the trivial round in front
     (its chain query is the call for the chain's first value); the shape; the proof-of-work bits.
   `RoundView`, `View`, `viewOf`: The untyped view. (The records are Fmt/View.lean's, so that a decision
     can be written in Fmt/.)
   `wanted`: A tree of depth a is opened at the set of the drawn positions modulo 2^a.
   `Q0 C ds dec`, `QT C ds dec`: The protocol without and with proof of work.

2. What is checked when the file compiles. Only the types and the proof.

3. Theorems. `opensEachOnce_le`: a description that opens each own tree exactly once meets the
limits' clause "at most once".

4. What is not claimed. Of a tree that a chain sends and never opens, the protocol made here knows
32 bytes that enter the hash chain, and nothing of what was committed under them: its oracle is one
word that nobody reads. That a later chain opens that root is outside this construction. No law.
That the protocol's reads cover what the decision reads holds by the form of `viewOf`, and is not
stated here. No statement on soundness. Wiring (Run/PlanQWire.lean), the spelling of queries
(Run/PlanQPage.lean) and the parser (Run/ParseChain.lean) are in other files.

Terms: lean/GLOSSARY.md.
-/
import Fmt.View
import Iop.Grind
import Iop.Batch

set_option autoImplicit false

namespace Run.PQ
open Iop

/-! ## The rounds' data -/

structure RD where
  entry : _root_.Fmt.Entry
  kind  : _root_.Fmt.Kind
  items : List _root_.Fmt.Item
  tree  : Option _root_.Fmt.Shape
  opens : List Nat

/-- the number of an own tree, if the opening is of one -/
def ownNo (o : _root_.Fmt.Shape × _root_.Fmt.Src) : Option Nat :=
  match o.2 with
  | .own n => some n
  | .given _ _ => none

/-- all openings of a chain -/
def allOpens (S : _root_.Fmt.Spec) : List (_root_.Fmt.Shape × _root_.Fmt.Src) :=
  S.rounds.flatMap (·.opens)

/-- the shape under which own tree n is opened -/
def shapeOfOwn (S : _root_.Fmt.Spec) (n : Nat) : Option _root_.Fmt.Shape :=
  ((allOpens S).find? fun o => ownNo o == some n).map (·.1)

/-- The shape that stands in for own tree n of a chain whose first own tree has the number `first`,
where no opening names it: a tree of depth 0 with one word a column, made in the run, under the
tree's own number. No position of it is ever read. -/
def bareShape (first n : Nat) : _root_.Fmt.Shape := ⟨0, 1, false, first + n⟩

def rdsFrom (S : _root_.Fmt.Spec) : Nat → List _root_.Fmt.Round → List RD
  | _, [] => []
  | sent, r :: rs =>
    ⟨r.entry, r.kind, r.items,
        if r.entry.roots = 0 then none
        else some ((shapeOfOwn S sent).getD (bareShape S.firstTree sent)),
        r.opens.filterMap ownNo⟩ ::
      rdsFrom S (sent + r.entry.roots) rs

def rds (S : _root_.Fmt.Spec) : List RD := rdsFrom S 0 S.rounds

/-- the number of roots that a chain sends -/
def nRoots (S : _root_.Fmt.Spec) : Nat := (S.rounds.map (·.entry.roots)).sum

/-- The limits on a description, as a test: the head lists them under `ok S`. -/
def ok (S : _root_.Fmt.Spec) : Bool :=
  S.ok && S.rounds.all (·.entry.roots ≤ 1) && (allOpens S).all (fun o => (ownNo o).isSome) &&
  (List.range (nRoots S)).all
    (fun n => decide (((allOpens S).filter fun o => ownNo o == some n).length ≤ 1)) &&
  (match S.rand with
    | .inFile => true
    | _ => false)

/-- Each own tree is opened exactly once. No limit of the construction, and no theorem in Run/ or
Fmt/ but `opensEachOnce_le` has it as a hypothesis: a test for a description that is meant to open
every tree that it sends. The limits allow a tree that is opened nowhere, so they do not notice an
opening that was left out of a description by mistake. This test does. -/
def opensEachOnce (S : _root_.Fmt.Spec) : Bool :=
  (List.range (nRoots S)).all
    (fun n => ((allOpens S).filter fun o => ownNo o == some n).length == 1)

/-- A description that opens each own tree exactly once meets the limits' clause "at most once". -/
theorem opensEachOnce_le (S : _root_.Fmt.Spec) (h : opensEachOnce S = true) :
    (List.range (nRoots S)).all
        (fun n => decide (((allOpens S).filter fun o => ownNo o == some n).length ≤ 1)) = true := by
  unfold opensEachOnce at h
  rw [List.all_eq_true] at h ⊢
  intro n hn
  exact decide_eq_true (Nat.le_of_eq (beq_iff_eq.1 (h n hn)))

/-! ## A verifier's message -/

/-- an entry without a draw, without work, without a message: the entry at which `CK.front` is
stated (Run/PlanQS.lean's round in front has it) -/
def e0 : _root_.Fmt.Entry := { name := "" }

/-- The kit of verifier's messages, that is, the choice of challenge types: for each entry and kind
a finite, nonempty type, and the map to the format's record of what was drawn; at the entry `e0` and
the kind `nothing` there is exactly one verifier message (`front`). -/
structure CK where
  Ch  : _root_.Fmt.Entry → _root_.Fmt.Kind → Type
  fin : ∀ e k, Fintype (Ch e k)
  ne  : ∀ e k, Nonempty (Ch e k)
  dr  : ∀ e k, Ch e k → _root_.Fmt.Drawn
  front : Unique (Ch e0 .nothing)

attribute [instance] CK.fin CK.ne CK.front

/-! ## The plain part of a prover's message -/

def PlainOf : List _root_.Fmt.Item → Type
  | [] => Unit
  | .root :: l => PlainOf l
  | .f :: l => UInt64 × PlainOf l
  | .word :: l => UInt64 × PlainOf l
  | .e :: l => _root_.Fmt.Ext × PlainOf l
  | .answer :: l => _root_.Fmt.Ext × PlainOf l

def PlainOf.dflt : (l : List _root_.Fmt.Item) → PlainOf l
  | [] => ()
  | .root :: l => PlainOf.dflt l
  | .f :: l => ((0 : UInt64), PlainOf.dflt l)
  | .word :: l => ((0 : UInt64), PlainOf.dflt l)
  | .e :: l => (((0, 0, 0) : _root_.Fmt.Ext), PlainOf.dflt l)
  | .answer :: l => (((0, 0, 0) : _root_.Fmt.Ext), PlainOf.dflt l)

/-- as the format's items read; the roots are not among them -/
def PlainOf.gots : (l : List _root_.Fmt.Item) → PlainOf l → List _root_.Fmt.ItemValue
  | [], _ => []
  | .root :: l, x => PlainOf.gots l x
  | .f :: l, (x : UInt64 × PlainOf l) => .f x.1 :: PlainOf.gots l x.2
  | .word :: l, (x : UInt64 × PlainOf l) => .word x.1 :: PlainOf.gots l x.2
  | .e :: l, (x : _root_.Fmt.Ext × PlainOf l) => .e x.1 :: PlainOf.gots l x.2
  | .answer :: l, (x : _root_.Fmt.Ext × PlainOf l) => .answer x.1 :: PlainOf.gots l x.2

/-- from a message's items read, the roots among them -/
def PlainOf.ofGots : (l : List _root_.Fmt.Item) → List _root_.Fmt.ItemValue → Option (PlainOf l)
  | [], [] => some ()
  | .root :: l, .root _ :: g => PlainOf.ofGots l g
  | .f :: l, .f x :: g => (PlainOf.ofGots l g).map fun y => ((x, y) : UInt64 × PlainOf l)
  | .word :: l, .word x :: g => (PlainOf.ofGots l g).map fun y => ((x, y) : UInt64 × PlainOf l)
  | .e :: l, .e x :: g => (PlainOf.ofGots l g).map fun y => ((x, y) : _root_.Fmt.Ext × PlainOf l)
  | .answer :: l, .answer x :: g => (PlainOf.ofGots l g).map fun y => ((x, y) : _root_.Fmt.Ext × PlainOf l)
  | _, _ => none

/-- the message's bytes: the items in their order, `rt` (the root's bytes; `PD` of
Run/PlanQPage.lean passes the empty string where a query has no root) at the place of each item
"root" -/
def PlainOf.bytes (rt : ByteArray) : (l : List _root_.Fmt.Item) → PlainOf l → ByteArray
  | [], _ => ByteArray.empty
  | .root :: l, x => rt ++ PlainOf.bytes rt l x
  | .f :: l, (x : UInt64 × PlainOf l) => _root_.Fmt.u64 x.1 ++ PlainOf.bytes rt l x.2
  | .word :: l, (x : UInt64 × PlainOf l) => _root_.Fmt.u64 x.1 ++ PlainOf.bytes rt l x.2
  | .e :: l, (x : _root_.Fmt.Ext × PlainOf l) => _root_.Fmt.ext x.1 ++ PlainOf.bytes rt l x.2
  | .answer :: l, (x : _root_.Fmt.Ext × PlainOf l) => _root_.Fmt.ext x.1 ++ PlainOf.bytes rt l x.2

/-! ## Rounds and shape -/

def posN : Option _root_.Fmt.Shape → Nat
  | none => 0
  | some s => 2 ^ s.a

def colW : Option _root_.Fmt.Shape → Nat
  | none => 0
  | some s => s.W

/-- A round. -/
@[reducible] def roundOf (C : CK) (d : RD) : Round where
  Orc := Fin (posN d.tree) → Fin (colW d.tree) → UInt64
  Pos := Fin (posN d.tree)
  Sym := fun _ => Fin (colW d.tree) → UInt64
  rd := fun o p => o p
  Plain := PlainOf d.items
  Chal := C.Ch d.entry d.kind
  dOrc := fun _ _ => 0
  dPlain := PlainOf.dflt d.items

/-- the trivial round in front -/
@[reducible] def r0 : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Unit
  Chal := Unit
  dOrc := ()
  dPlain := ()

def shapeL (C : CK) : List RD → Shape
  | [] => []
  | d :: ds => roundOf C d :: shapeL C ds

abbrev shapeOf (C : CK) (ds : List RD) : Shape := r0 :: shapeL C ds

def gL (C : CK) : (ds : List RD) → GBits (shapeL C ds)
  | [] => ()
  | d :: ds => (d.entry.work, gL C ds)

def gOf (C : CK) (ds : List RD) : GBits (shapeOf C ds) := (0, gL C ds)

/-! ## The untyped view -/

/-- one round, as a decision sees it: Fmt/View.lean's record -/
abbrev RV : Type := _root_.Fmt.RoundView

/-- the view: Fmt/View.lean's record -/
abbrev View : Type := _root_.Fmt.View

def drawnL (C : CK) : (ds : List RD) → Rho (shapeL C ds) → List _root_.Fmt.Drawn
  | [], _ => []
  | d :: ds, (c, ρ) => C.dr d.entry d.kind c :: drawnL C ds ρ

def rvL (C : CK) : (ds : List RD) → Tr (shapeL C ds) → List RV
  | [], _ => []
  | d :: ds, (m, c, τ) => ⟨PlainOf.gots d.items m.2, C.dr d.entry d.kind c⟩ :: rvL C ds τ

/-- the shape of own tree n -/
def treeSh : List RD → Nat → Option _root_.Fmt.Shape
  | [], _ => none
  | d :: ds, n =>
    match d.tree with
    | none => treeSh ds n
    | some s => if n = 0 then some s else treeSh ds (n - 1)

/-- Which (tree, position) the drawn positions ask for. -/
def wantedL (all : List RD) : List RD → List _root_.Fmt.Drawn → List (Nat × Nat)
  | d :: ds, D :: Ds =>
    (d.opens.flatMap fun n =>
      match treeSh all n with
      | none => []
      | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x)) ++ wantedL all ds Ds
  | _, _ => []

def wanted (ds : List RD) (Ds : List _root_.Fmt.Drawn) : List (Nat × Nat) := wantedL ds ds Ds

/-- a (tree, position) as a position of the shape -/
def posAt (C : CK) : (ds : List RD) → Nat → Nat → Option (OPos (shapeL C ds))
  | [], _, _ => none
  | d :: ds, n, x =>
    if d.tree.isSome then
      if n = 0 then (if h : x < posN d.tree then some (.inl ⟨x, h⟩) else none)
      else (posAt C ds (n - 1) x).map .inr
    else (posAt C ds n x).map .inr

/-- the column at a (tree, position) -/
def colAt (C : CK) : (ds : List RD) → Tr (shapeL C ds) → Nat → Nat → Option (List UInt64)
  | [], _, _, _ => none
  | d :: ds, (m, _, τ), n, x =>
    if d.tree.isSome then
      if n = 0 then (if h : x < posN d.tree then some (List.ofFn (m.1 ⟨x, h⟩)) else none)
      else colAt C ds τ (n - 1) x
    else colAt C ds τ n x

def viewL (C : CK) (ds : List RD) (τ : Tr (shapeL C ds)) : View where
  rounds := rvL C ds τ
  opened := (wanted ds (drawnL C ds τ.rho)).filterMap fun nx =>
    (colAt C ds τ nx.1 nx.2).map fun c => (nx.1, nx.2, c)

def viewOf (C : CK) (ds : List RD) (τ : Tr (shapeOf C ds)) : View := viewL C ds τ.2.2

/-! ## The protocol -/

/-- no external oracle: an encoded index of length 0 (the form in which an interface's Test has its
external oracle: `BatchProtocol.offline`, Iop/Batch.lean) -/
abbrev E0 : ExtSpec := oneExternalString 0 Unit

instance decL (C : CK) : (ds : List RD) → DecidableEq (OPos (shapeL C ds))
  | [] => inferInstanceAs (DecidableEq Empty)
  | d :: ds => by
      haveI := decL C ds
      exact inferInstanceAs (DecidableEq (Fin (posN d.tree) ⊕ OPos (shapeL C ds)))

instance decO (C : CK) (ds : List RD) : DecidableEq (OPos (shapeOf C ds)) :=
  inferInstanceAs (DecidableEq (Empty ⊕ OPos (shapeL C ds)))

/-- The protocol without proof of work. -/
@[reducible] def Q0 {Y : Type} (C : CK) (ds : List RD) (dec : Y → View → Bool) : InteractiveOracleProof Y E0 where
  shape := shapeOf C ds
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ =>
    (((wanted ds (drawnL C ds ρ.2)).filterMap fun nx =>
      (posAt C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (shapeOf C ds)))).toFinset
  accept := fun y _ τ => dec y (viewOf C ds τ)

/-- The protocol, with proof of work. -/
@[reducible] def QT {Y : Type} (C : CK) (ds : List RD) (dec : Y → View → Bool) : InteractiveOracleProof Y E0 :=
  (Q0 C ds dec).grind ℕ (gOf C ds)

end Run.PQ
