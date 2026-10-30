-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Sim.lean: THE PARTS OF A SIMULATED COMPILED RUN, for the simulator of the scheme
with the whole key published (argW, Johnson/WholeKey/Defs.lean), over the typed oracles. AT LETTERS.
The simulator itself is in Johnson/WholeKey/Wrap.lean.

General definitions, and one equation that holds by unfolding. This file states no goal of the
release, and it proves nothing on the simulator.

The idea. The simulator RUNS THE COMPILED PROVER's OWN CHAIN (chainO, OnBytes/Prover/Defs.lean; the
compiled prover of one slot is that chain followed by a step that asks nothing: proveX_eq_chainX),
at a strategy that it makes from the view which a simulator of the interactive protocol hands it,
under rules for answering the program's hash queries (Rom/Handle/Defs.lean) by which the answers are
drawn BEFORE the messages are made and are laid into the oracle's table LATE. So there is no second
text of the prover's chain.

A simulator of the interactive protocol (Honest.HVZK, Iop/InteractiveOracleProof.lean) wants all verifier messages
before it speaks. In a compiled run the verifier messages are read off the answers to the run's
Fiat-Shamir queries, and these queries hold the prover's messages. The way out of the circle is TWO
PASSES.
  PASS 1, dry (pass1, Johnson/WholeKey/Wrap.lean). The chain runs at the strategy of fixed messages.
     Each of its late queries (see below) gets a fresh uniform answer, on demand, and the answers
     are RECORDED in their order. No table is looked at or written. The outcome tells which tries of
     each search for a nonce pass, and so the verifier messages ρ; or that a search has run out.
     This serves because in the chain what is asked next hangs on the messages, but which try passes
     and what the verifier messages are hangs on the ANSWERS IN THEIR ORDER alone. (That is a
     reading of the program's text; it is not proved here.) So the nonces are made at the compiler;
     the number of tries that a search may make is a letter.
  BETWEEN. ρ goes to the interactive protocol's simulator, which gives a view or "none" (a stop).
     The strategy for pass 2 (stratFor) sends the view's plain parts and, as oracles, the view's
     symbols, with the wire's fixed symbol at every position of which the view holds nothing
     (stratOfView). At a stop, and where a search has run out: the strategy of fixed messages again.
  PASS 2 (pass2A, Johnson/WholeKey/Wrap.lean). ALWAYS: the chain runs at that strategy; its late
     queries get THE RECORDED answers in their order and are logged; its other queries go to the
     simulator's table. Its string is handed out, or "none" at a stop (handOut).

LAID LATE. Two kinds of queries. PLAIN: the inner nodes of trees, and the two queries of a table's
seed: they are asked of the simulator's table as everybody asks (lazy sampling). LATE: the leaves of
all trees, and a run's queries to the Fiat-Shamir oracle, to g and in the request tree: each gets
its answer WITHOUT A LOOK AT THE TABLE, and is not written into it.
When a string is handed out, these are written into the table, each only WHERE THE TABLE HAS NO
ENTRY (handOut): all logged queries of that run but its leaves, failed tries too; and the leaves, of
the run's own trees and of the tables, AT THE POSITIONS THAT THE RUN OPENS, with the digests that
the kept trees hold for them. WHICH LEAVES THESE ARE GOES BY PLACE (round, component, tree, leaf;
for a table: tree, leaf), never by a salt's or a query's value. All other leaves are never written.
At a stop nothing late is written.
So of the late kinds the table holds only queries of runs whose string was handed out, and of leaves
only opened ones (inner nodes are plain and stand in the table whatever is shown); no entry is ever
overwritten.

Main names (namespace OnBytes.WholeKey).
  lateRun, lateTab, mkRun, mkTab   which queries are late, in a compiled run and in the making of a
    table.
  stratOfView, stratFor   the strategy out of a view.
  notLeaf, laidTree, laidTrees, laidK, extLaid, handOut   what a string brings into the table; what
    is handed out.
  chainX, proveX_eq_chainX   the compiled prover's chain at the letters of the compiled prover.
  Sims           the three simulators of the interactive protocols (the session's: one for each
    number of a copy).
  Tb             the tables of lazy sampling over the scheme's oracles.

Limits. Definitions, and one equation that holds by unfolding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Defs
import Rom.Handle.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-! ## One simulated compiled run -/

section Generic
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The queries of a compiled run that are laid late: leaves, Fiat-Shamir queries, g, and the
request tree's. Plain: the inner nodes of trees. -/
def lateRun : ON₂ → Bool
  | .leaf => true
  | .rleaf => true
  | .rnode => true
  | .fb _ => true
  | .g _ => true
  | _ => false

/-- The queries of the making of a table that are laid late: its leaves. Plain: its inner nodes and
the two queries of its seed. -/
def lateTab : ON₂ → Bool
  | .leaf => true
  | _ => false

/-- lateRun as a test on (oracle, query) (Mark, Rom/Handle/Defs.lean). -/
def mkRun : Mark (typedOracleFamily lam K L) := fun o _ => lateRun o

/-- lateTab as a test on (oracle, query). -/
def mkTab : Mark (typedOracleFamily lam K L) := fun o _ => lateTab o

/-- The strategy that sends, whatever the verifier says, the given plain parts and, as oracles, the
given symbols, with the wire's fixed symbol at every position at which none is given. -/
def stratOfView : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Plains s →
    ((p : OPos s) → Option (OSym s p)) → Strat s Unit
  | [], _, _, _, _ => ()
  | _ :: s, (_, A), (w, W), (pl, pls), orc =>
      ((w.pt.ofSyms fun p => (orc (.inl p)).getD (w.pt.zero p), pl),
        fun _ => stratOfView s A W pls fun p => orc (.inr p))

variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L) (cap : ℕ → ℕ)

/-- Is an entry of a log no leaf? -/
def notLeaf (e : QA (typedOracleFamily lam K L)) : Bool :=
  match (e.1 : ON₂) with
  | .leaf => false
  | _ => true

/-- The leaves of one kept tree that stand at positions which are read, in the tree's order, each
with its digest: (the leaf's input, the entry of the lowest level). -/
def laidTree {r : Round} (posAt : ℕ → Option r.Pos) (rd : r.Pos → Bool) (T : TreeK lam L) :
    Trace (typedOracleFamily lam K L) :=
  ((List.range (T.lv.headD []).length).filter fun j =>
      match posAt j with
      | some p => rd p
      | none => false).map fun j =>
    ⟨TypedOracleCompiler.Compile.Batch.OracleName.leaf, T.inp j, (T.lv.headD []).getD j default⟩

/-- The same for the trees of one component of one round, from tree number k on. -/
def laidTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (rd : r.Pos → Bool) :
    ℕ → List (TreeK lam L) → Trace (typedOracleFamily lam K L)
  | _, [] => []
  | k, T :: Ts => laidTree (K := K) (posAt k) rd T ++ laidTrees posAt rd (k + 1) Ts

/-- **The leaves of a run's own trees that its string opens, BY PLACE** (round, component, tree,
leaf), out of what the prover's chain keeps, in the order in which the chain has hashed them: in
each round the slot's component, then the shared one. rd: is the position read? -/
def laidK : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Kept lam L s → (OPos s → Bool) →
    Trace (typedOracleFamily lam K L)
  | [], _, _, _, _ => []
  | _ :: s, (_, A), (w, W), (kp, ks), rd =>
      laidTrees w.posAtJ (fun p => rd (.inl p)) 0 kp.2.2 ++
        (laidTrees w.posAt0 (fun p => rd (.inl p)) 0 kp.2.1 ++
          laidK s A W ks fun p => rd (.inr p))

/-- The leaves of the tables that a run at the verifier messages ρ opens, BY PLACE (tree, leaf),
each with its digest, out of the trees as they are kept. -/
def extLaid (ρ : Rho Q.loc.shape) : Trace (typedOracleFamily lam K L) :=
  (wq.ext.all.filter fun p => haveI := wq.ext.dec; decide (p ∈ Q.loc.extReads x ρ)).map fun p =>
    ⟨TypedOracleCompiler.Compile.Batch.OracleName.leaf, (xt (wq.ext.which p)).inp (wq.ext.leaf p),
      ((xt (wq.ext.which p)).lv.headD []).getD (wq.ext.leaf p) default⟩

/-- The strategy of a simulated run: out of the view, if there is one; else that of fixed messages.
-/
def stratFor (v : Option (DView Q.loc)) : Strat Q.loc.shape Unit :=
  match v with
  | some v => stratOfView Q.loc.shape Q.ann wq.sh v.plains v.orc
  | none => Strat.dflt _ ()

/-- The compiled prover's chain at these letters: the compiled prover before its last step, which
asks nothing and makes the string out of what the chain has kept. -/
def chainX (σ : Strat Q.loc.shape Unit) (co : Coins lam L) :
    TypedOracleComputation lam K L (Res (OutP lam L Q.loc.shape)) :=
  chainO t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ

/-- The compiled prover of one slot is that chain, followed by the making of the string. -/
theorem proveX_eq_chainX (σ : Strat Q.loc.shape Unit) (co : Coins lam L) :
    proveX t Q wq embS embP xin cms x y xt σ co cap =
      (chainX t Q wq embS embP xin cms x cap σ co).bind fun r =>
        .pure (r.map fun z => (finish Q wq x y xt co z, trK Q.loc.shape z.2.1 z.1)) := rfl

/-- What a simulated run hands out, and the table that it leaves. go: there was a view. co: the
coins that the chain was handed. o: the chain's outcome, with the table after it and the run's own
log. If there was a view and the chain has come to its end: the string; and these are written into
the table, each only where there is no entry: all entries of the run's log that are no leaves; the
leaves of the run's own trees at the positions that are read; the tables' leaves at the positions
that are read. Else: none, and nothing late is written. -/
def handOut (go : Bool) (co : Coins lam L)
    (o : Res (OutP lam L Q.loc.shape) × RSt (typedOracleFamily lam K L) (Table (typedOracleFamily lam K L))) :
    Option (OneProtocolProof lam Q) × Table (typedOracleFamily lam K L) :=
  match go, o.1 with
  | true, .ok z =>
      (some (finish Q wq x y xt co z),
        ((o.2.base.lay (o.2.log.filter notLeaf)).lay
          (laidK Q.loc.shape Q.ann wq.sh z.2.1 fun p =>
            haveI := wq.decO
            decide (p ∈ Q.loc.reads x z.1 (trK Q.loc.shape z.2.1 z.1).plains))).lay
          (extLaid Q wq x xt z.1))
  | _, _ => (none, o.2.base)

end Generic

/-! ## At an object with out-of-domain samples -/

variable {I X : Type} {lam : ℕ}

/-- The simulators of the three interactive protocols, in the form of Honest.HVZK (Iop/InteractiveOracleProof.lean).
The session's: one for each number of a copy. -/
structure Sims (L : HolographicProtocol I X) where
  T : L.Rec → (ρ : Rho L.offline.shape) → ((oneExternalString L.wordLength L.Symbol).Pos → Option (oneExternalString L.wordLength L.Symbol).Sym) →
    PMF (Option (DView L.offline))
  Lk : L.Rec × L.Rec → (ρ : Rho L.link.shape) →
    ((twoExternalStrings L.wordLength L.Symbol).Pos → Option (twoExternalStrings L.wordLength L.Symbol).Sym) → PMF (Option (DView L.link))
  B : ℕ → X × L.Rec → (ρ : Rho L.onlineBatch.loc.shape) →
    ((oneExternalString L.wordLength L.Symbol).Pos → Option (oneExternalString L.wordLength L.Symbol).Sym) → PMF (Option (DView L.onlineBatch.loc))

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- The tables of lazy sampling over the scheme's oracles. -/
abbrev Tb (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) : Type :=
  Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))

end OnBytes.WholeKey
