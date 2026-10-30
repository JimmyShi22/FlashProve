-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ParseLaws.lean.
TWO: CUT BY PROGRAM out of the library's Run/ParseLaws.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), then turned by hand where it had to be. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
Spec.parseLaws_some, parseLaws_some.

Run/ParseLaws.lean: what each field of the parser's argument string is: equations.

Run/ParseChain.lean makes, from what a reader of a proof file hands out (o : Fmt.ChainOut), the
inputs of the compiled verifier (Compile.Batch.verifyOneProtocol, the function that the compiler's verifier
runs on each proof string). Whoever connects a run of that function with the format page's own
verifier needs to know what stands in each field. Everything is generic in the protocol Q and its
typing T.

1. What the file contains.  Statements (Run.Spec.parseLaws_*) and proofs.
    opensAt T run o         The function "opens" of the argument string: at a position p: the
                            opening at column (T.place p).2 of the tree (T.place p).1, none if that
                            tree was not opened.
    opensAtF                The same for the parser that fills whole paths (Run/ParseFull.lean).

2. What is checked when the file compiles.  Only the types and proofs.

3. Theorems.
    parseLaws_some          toBPrf T o = some x if and only if there are run, pl with: o.run = some
                            run; T.plains o.rounds = some pl; every opening passes OpenB.ok; x =
                            (the list with the parameters' digest, mkBPrf Q run (rootsB o) pl
                            (opensAt T run o)).
    parseLaws_someF         The same for the parser that fills whole paths.
    parseLaws_fields        The fields of mkBPrf: salt: the run's value as bits; roots: the roots as
                            digests, in the order sent; plains; opens; no external opening; request
                            root: zeros; slot 0; empty path.
    parseLaws_opens         (opensB o).lookup (T.place p).1 = some (W, Ob) gives opensAt T run o p =
                            Ob.at (T.sym p) run (T.place p).2; = none gives none.
    parseLaws_at            Ob.at sym run x at a listed position: if (x, (col, salt, path)) is what
                            the look-up finds: some ⟨y, run's value ‖ salt, path⟩ where sym col =
                            some y; none where x is not listed.
    parseLaws_parse         At the identity monad: parseW, parseLaxW are the reader, then toBPrf.

4. What is not claimed.  What the readers hand out (o itself).  Nothing on lengths of bit strings.

Terms: lean/GLOSSARY.md.

-/
import Run.ParseLaws
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
import Run.ParseFull

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
export _root_.Run (opensAt opensAtF parseLaws_opens parseLaws_at)
open _root_.Fmt (ChainOut)

variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

def Spec.parseLaws_some : Prop :=
  ∀ {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (T : Typing Q)
      (o : ChainOut) (x : List (Dig 256) × OneProtocolProof 256 Q),
    toBPrf T o = some x ↔
    ∃ run pl,
      o.run = some run ∧
      T.plains o.rounds = some pl ∧
      (opensB o).all (fun y => y.2.2.ok T.saltBytes y.2.1) = true ∧
      x = ([bytesToDig o.pd], mkBPrf Q run (rootsB o) pl (opensAt T run o))

theorem parseLaws_some : Spec.parseLaws_some := by
  intro Y E Q T o x
  unfold toBPrf
  constructor
  · intro hx
    cases hr : o.run with
    | none => simp [hr] at hx
    | some run =>
      cases hp : T.plains o.rounds with
      | none => simp [hr, hp] at hx
      | some pl =>
        simp only [hr, hp] at hx
        by_cases hk : (opensB o).all (fun y => y.2.2.ok T.saltBytes y.2.1) = true
        · rw [if_pos hk] at hx
          exact ⟨run, pl, rfl, rfl, hk, (Option.some.inj hx).symm⟩
        · rw [if_neg hk] at hx
          exact absurd hx (by simp)
  · rintro ⟨run, pl, hr, hp, hk, rfl⟩
    simp only [hr, hp]
    rw [if_pos hk]
    rfl

end TypedOracleCompiler.Run
