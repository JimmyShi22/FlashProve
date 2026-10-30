-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ParseThin.lean.
TWO: CUT BY PROGRAM out of the library's Run/ParseThin.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), then turned by hand where it had to be. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
mkBPrfP, toBPrfP, Spec.parseThin_to, parseThin_to.

Run/ParseThin.lean: the parsers' typed side in a form that can be evaluated at rounds with very many
verifier messages: the protocol's skeleton in the place of the protocol.

Why. In the library a round carries the list of all its verifier messages as data. Observed
elsewhere in this folder (heads of Run/TwinDefs.lean, Run/ThinDefs.lean): compiled Lean can build
that list where a round, a shape, a protocol or an interface is handed over as a value, also as an
implicit argument; whether it does depends on the compiler, function by function. The rule of the
folder: no function on the path of an evaluation has a parameter of these types. The parsers of
Run/ParseChain.lean have {Q : BatchInteractiveOracleProof Y E}. Here the same functions take (P : Run.Twin.PS Y E),
the skeleton (Run/TwinDefs.lean), explicitly; the protocol P.up stands in types alone.

1. What the file contains.  Definitions that can be evaluated.
    TypingP P                 What a protocol supplies (as Typing): saltBytes; plains; place; sym.
                              T.up : Typing P.up.
    mkBPrfP P run roots plains opens : OneProtocolProof 256 P.up
    OpenB.table run paths     One opening's table: for each listed position (column, typed salt,
                              path): made once.
    atT sym tab x             The opening at x: a look-up in such a table.
    toBPrfP P T o, toBPrfFullP P T o
                              As toBPrf, toBPrfFull. The tables of all openings are built in front
                              of the function "opens": the verifier calls that function at each of
                              the 2^depth places of each tree, more than once; behind its λ stands a
                              look-up and the symbol's typing, nothing else.
    parseWP, parseLaxWP, parseFullWP h P S T file
                              The three parsers.

2. What is checked when the file compiles.  Only the types and proofs.

3. Theorems (Run.Spec.parseThin_*). toBPrfP P T o = toBPrf T.up o; toBPrfFullP P T o = toBPrfFull
T.up o; each parser = its namesake at T.up. (Tools: lookup_zip3, atT_table, lookup_map_snd.)

4. What is not claimed. That no list of verifier messages is built in an evaluation: that is a fact
about the compiler, no theorem. One trial was made (a skeleton of the small example of
Run/ParseChain.lean with a trace in every round's instance; the evaluations from another file): the
three parsers of this file gave the right argument string and built nothing. THE TRIAL HAS NO
POSITIVE CASE: IN IT THE PRESENT parseLaxW AT Q := P.up BUILT NOTHING EITHER (a control that asks
for the instance itself did fire the trace). SO THIS FORM RESTS ON THE RULE, NOT ON A DIFFERENCE
THAT WAS SEEN.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.ParseThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
import Run.ParseFull
import OnBytes.TypedOracleCompiler.Run.TwinDefs

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
export _root_.Run (TypingP Row3 atT atTT lookup_zip3 atT_table lookup_map_snd)
open _root_.Fmt (Spec ChainOut)

/-- the argument string -/
def mkBPrfP {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (run : ByteArray) (roots : List ByteArray)
    (plains : Plains (Twin.up P.S))
    (opens : (p : OPos (Twin.up P.S)) → Option (Opening 256 (OSym (Twin.up P.S) p))) :
    OneProtocolProof 256 P.up :=
  ⟨bytesToBits run, roots.map bytesToDig, plains, opens, fun _ => none, fun _ => false, 0, [], []⟩

/-- From what was read to the verifier's inputs. -/
def toBPrfP {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (T : TypingP P) (o : ChainOut) :
    Option (List (Dig 256) × OneProtocolProof 256 P.up) :=
  match o.run, T.plains o.rounds with
  | some run, some pl =>
      if (opensB o).all (fun x => x.2.2.ok T.saltBytes x.2.1) then
        let tabs : List (Nat × List (Nat × Row3)) :=
          (opensB o).map fun x => (x.1, x.2.2.table run x.2.2.paths)
        some ([bytesToDig o.pd],
          mkBPrfP P run (rootsB o) pl fun p => atTT (T.sym p) tabs (T.place p).1 (T.place p).2)
      else none
  | _, _ => none

section
variable {m : Type → Type}
  [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) {Y : Type} {E : ExtSpec}

end

/-! ## The ties -/

def Spec.parseThin_to : Prop :=
  ∀ {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (T : TypingP P) (o : ChainOut),
    toBPrfP P T o = toBPrf T.up o

theorem parseThin_to : Spec.parseThin_to := by
  intro Y E P T o
  unfold toBPrfP toBPrf
  cases hr : o.run with
  | none => rfl
  | some run =>
    cases hp : T.plains o.rounds with
    | none => simp [TypingP.up, hp]
    | some pl =>
      have hp' : T.up.plains o.rounds = some pl := hp
      simp only [hp']
      have e : (fun p =>
          atTT (T.sym p) ((opensB o).map fun x => (x.1, x.2.2.table run x.2.2.paths))
            (T.place p).1 (T.place p).2) =
          (fun p : OPos (Twin.up P.S) => match (opensB o).lookup (T.place p).1 with
            | none => none
            | some x => x.2.at (T.sym p) run (T.place p).2) := by
        funext p
        unfold atTT
        rw [lookup_map_snd (fun y : Nat × OpenB => y.2.table run y.2.paths)]
        cases (opensB o).lookup (T.place p).1 with
        | none => rfl
        | some x => exact atT_table _ _ _ _ _
      show (if _ then some (_, mkBPrfP P run (rootsB o) pl _) else none) = _
      rw [e]
      rfl

end TypedOracleCompiler.Run
