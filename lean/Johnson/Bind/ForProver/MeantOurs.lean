-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/MeantOurs.lean: AT THE FULL SIZE: THE RELATION `Meant` HOLDS AT THIS FOLDER'S
TERMS, AND SO THE LIBRARY'S THEOREM ON THE LINK'S DECISION CAN BE CALLED AT THEM. Statements and
proofs: two calls.

Why. `Johnson.Prover.Link.link_yes` (Johnson/Prover/Link/LinkJoinF.lean) says of one sub-protocol,
the link between two committed tables, that the description's decision gives "true" at the view that
the library's prover of the link, written in the field, makes: for every instance, stored strings
and tables of coefficients that are `Meant` (Johnson/Prover/Link/LinkYesStm.lean). That file has
definitions alone: that `Meant` holds at any witness is not shown there. The library shows its seven
clauses, as a conjunction, at its own typed encoder (`FlashProve.meant_home`,
Johnson/Goal/Conditions/LinkMeant.lean). Here it is shown at stored strings that are made of the
stand-in committer's columns. Two inputs are spoken of below: the goals' (a matrix of cells, pads
and tails on finite ranges: what the library's typed encoder takes) and the frame's (functions of
two plain numbers: what the frame for an honest prover hands out).

Main names (namespace `Bind.ForProver`).
   **`meant_ours`**: `Meant` at the instance (`recAt`, `recAt`), the stored strings (`strAt`,
      `strAt`) and the tables of coefficients (`polysAt`, `polysAt`) of
      Johnson/Bind/ForProver/SevenAt.lean, at the full size's sizes and shape: at every table of
      plain entries, two values of the coins and two seeds. `seven_at_ours` at `agree_full`.
   **`link_yes_ours`**: `link_yes` called at `meant_ours`.
Limits. THE FULL SIZE ALONE. `link_yes_ours` IS A SENTENCE ON ONE SUB-PROTOCOL'S DECISION AT THE
COPY'S FILE: NOT ON verify(), NOT ON AN INTERACTIVE VERIFIER'S WHOLE ACCEPT, AND NOT COMPLETENESS.
(The library's accept law of the link, under its own premises, written at these terms:
`accL_at_ours`, Johnson/Bind/ForProver/HomeIsOurs.lean.) The prover whose view is decided
(`linkNext`, Johnson/Prover/Link/LinkAll.lean) is the library's prover of the copy's file's link,
over the field; the sentence stands at all letters C, which come from no finite type of coins, and
at ALL sampled values ϱ: no law of sampling is asked or given. It adds nothing to `link_yes` but a
witness of its premise. NOTHING THAT THE LIBRARY OWES IS PAID HERE: the seven clauses of `Meant` are
paid in the library, as a conjunction and without a premise, at the input of its typed compiler at
the full size (`FlashProve.meant_home`); this file carries a paid statement to this folder's terms.
THE PLAIN ENTRIES ARE A LETTER: any function of two numbers into the words; that they are the
packing of an index is not asked. TWO TABLES STAND SIDE BY SIDE, the same plain entries under both,
AND ALL FOUR OF ρ, σ, ρ', σ' ARE BARE LETTERS: (ρ, σ) stand where the link reads the committed table
(its item 0), (ρ', σ') where it reads a second table (its item 1). That ρ, σ are the coins and the
seed of the run that makes the commitment ID (its salts, tree, root and name; σ sampled at that
name), and that ρ', σ' are a copy's own, sampled apart, with a copy's tree, name and root: NEITHER
is said here. Nothing here says that each table's randomness has one seed, that the two tables'
randomness is sampled apart, or that the second table's is the one at which a session runs. THE
SEVEN TIE THESE TERMS TO EACH OTHER ALONE: three terms that read no plain entry (columns of 0,
coefficients 0, answers 0) would meet them all. That the terms read the plain entries is said by
`strAt_eq_honestTab` (Johnson/Bind/ForProver/SevenAt.lean) and `strAt_readers`
(Johnson/Bind/ForProver/SevenReaders.lean), not by `meant_ours`: it has the case of plain entries,
coins and answers that are all 0. Of `Meant`'s seven clauses the first two hold by `recAt`'s
definition, of every table of coefficients; what the two keys are that `link_yes` writes of `recAt`
is not said here. No map between the frame's input and the goals' is named. That an honest prover at
the protocol hands the link these strings, this instance and these coefficients is said by no file
beneath this one. No hash function, no query. This file writes no honest prover. Nothing on index
privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.SevenAt
import Johnson.Prover.Link.LinkJoinF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (frS frZ)
open ProofFile.Honest (TableRand)
open Bind.Column (shFull agree_full)

/-- **`Meant` at this folder's terms, at the full size**: at every table of plain entries, two
values of the coins and two seeds. Its first two clauses hold by `recAt`'s definition. -/
theorem meant_ours (entry : ℕ → ℕ → UInt64) (ρ ρ' : TableRand) (σ σ' : frZ.D) :
    Johnson.Prover.Link.Meant
      (recAt frS frZ shFull entry ρ σ, recAt frS frZ shFull entry ρ' σ')
      (strAt frS shFull entry ρ, strAt frS shFull entry ρ')
      (polysAt frS shFull entry ρ) (polysAt frS shFull entry ρ') := by
  obtain ⟨a, b, c, d, e, f, g⟩ := seven_at_ours frZ agree_full
    (le_of_eq (OnBytes.Slice.fr_cut _ _ _ _)) entry ρ ρ' σ σ'
  exact ⟨a, b, c, d, e, f, g⟩

section
open OnBytes OnBytes.Params OnBytes.Slice Cb Cb.Ood _root_.Run
open Iop hiding Shape
open VerifiableInference.Desc
open _root_.Desc.K15 (frP linkDescriptionAt linkDeclaredRounds linkRoundsMatchPlan)
open OnBytes.Flat (dsFull)
open TypedOracleCompiler.Run.PQ (drawnSL uL)
open Johnson.Prover.Link (LCoins linkNext keysOf viewOf)

/-- **The library's theorem on the link's decision, called at this folder's terms.** One
sub-protocol's decision, at the library's prover of the link in the field, at all letters C and all
sampled values ϱ; not the verifier's whole accept; not completeness. -/
theorem link_yes_ours (entry : ℕ → ℕ → UInt64) (ρ ρ' : TableRand) (σ σ' : frZ.D) (C : LCoins)
    (ϱ : Rho (uL (ckP .two) dsFull)) :
    (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run
      (keysOf (recAt frS frZ shFull entry ρ σ, recAt frS frZ shFull entry ρ' σ'))
      (viewOf dsFull frS.P.T.a frD.xs
        (linkNext frP frS 97
          (Johnson.Prover.Link.linOf
            (recAt frS frZ shFull entry ρ σ, recAt frS frZ shFull entry ρ' σ')
            (strAt frS shFull entry ρ, strAt frS shFull entry ρ')
            (polysAt frS shFull entry ρ) (polysAt frS shFull entry ρ')) C)
        (strAt frS shFull entry ρ, strAt frS shFull entry ρ')
        (drawnSL (ckP .two) dsFull ϱ)) = true :=
  Johnson.Prover.Link.link_yes _ _ _ _ (meant_ours entry ρ ρ' σ σ') C ϱ

end

end Bind.ForProver

end

#print axioms Bind.ForProver.meant_ours
#print axioms Bind.ForProver.link_yes_ours
