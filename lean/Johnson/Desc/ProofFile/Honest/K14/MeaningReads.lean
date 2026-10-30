-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/MeaningReads.lean: the linear claim's shared rounds (kind K14):
THIS KIND's MAKER OF THE ITEMS' MEANING (mgWords, Honest/K14/Thread2.lean) READS A WITNESS AND NEVER
WRITES ONE. mgWords takes a WitLens: a reader `get` of a family of words off a witness, a writer
`set`, and two laws that tie them. Of these it uses `get` alone; the writer serves the maker of the
witness (witL) and nothing else.

Why. The last chain's thread needs the meaning of Omega's pin at a witness of another type than the
shared chain's. Whoever has a reader of words on that type and no writer with the two laws can lay
mgReads there.

  mgReads             the maker, from a reader of words
  mgWords_reads       mgWords at a lens is mgReads at the lens's reader: by unfolding
  pin_at_reads        at mgReads a shared message's pin reads no string

What is not claimed. That any item holds of any witness. No reader on the library's type of
witnesses is named here; mgReads wants one that reads no state, at the shared chain's own numbers.
That such a reader gives, at the last chain's witness, the words that the shared chain's thread
reads off its own is not shown here: at the threads of a proof file it is lastWords_at_lastWitness
(Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean), under that statement's own premise.
Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Thread2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (P14 St)
open Desc.K14.Honest (SmpOwn)
open Desc.K14.Law (NearAt RecAll OmU RowsU RowsO FoldAt uRK colsOf)

/-- **What this kind's and the sendings' shared items say, from a reader of words alone.** The
fields are mgWords' own, with `get` for the lens's reader; every other field stays Mg₀'s. -/
def mgReads {P₁ Wt : Type} (get : Wt → Words Cb.Gl.E) (Q : P14) (N : NumbersS)
    (Mg₀ : MeaningS St P₁ Wt) : MeaningS St P₁ Wt :=
  { Mg₀ with
    pin := fun j t s _ w => ∀ m, N.tenant m = (j, t) → SmpOwn (num m) s (get w)
    nearU := fun s y w => NearAt rdE Q.par (uRK Q.par s) (get w) (colsOf y.cell) 0
    recRow := fun s w => RecAll rdE Q.par (uRK Q.par s) (get w)
    omU := OmU Q.par (uRK Q.par) get
      (fun w y => get w 2 .main ((linLayOmega Q.codes Q.par.S).index y))
    row := fun c s w =>
      match c with
      | .sample m => SmpOwn (num m) s (get w)
      | .recG => RowsU rdE 0 Q.par.S.fold.index.answers s (get w)
      | .loc => RowsU rdE Q.par.S.fold.index.answers Q.par.S.fold.columns s (get w)
      | .fold => FoldAt rdE Q.par.S s (get w)
      | .foldU => RowsU rdE (Q.par.S.fold.index.answers + Q.par.S.fold.columns) 1 s (get w)
      | .foldOmega => RowsO rdE 0 1 s (get w) }

/-- mgWords at a lens is mgReads at the lens's reader. -/
theorem mgWords_reads {P₁ Wt : Type} (ℓ : WitLens Wt) (Q : P14) (N : NumbersS)
    (Mg₀ : MeaningS St P₁ Wt) : mgWords ℓ Q N Mg₀ = mgReads ℓ.get Q N Mg₀ := rfl

/-- At mgReads a shared message's pin reads no string. -/
theorem pin_at_reads {P₁ Wt : Type} (get : Wt → Words Cb.Gl.E) (Q : P14) (N : NumbersS)
    (Mg₀ : MeaningS St P₁ Wt) (a b : Nat) (e : St) (y y' : Strs) (v : Wt)
    (h : (mgReads get Q N Mg₀).pin a b e y v) : (mgReads get Q N Mg₀).pin a b e y' v := h

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.mgWords_reads
#print axioms ProofFile.Honest.K14.pin_at_reads
