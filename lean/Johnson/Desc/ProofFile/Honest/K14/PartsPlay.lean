-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PartsPlay.lean: the rows of Honest/K14/Parts.lean PLAY, AT A
SUB-PROTOCOL THAT DECLARES ONE ROUND OF THE RIGHT FORM AND NO ORACLE MESSAGE (the round cuts no
item, for a quiet row; one element, for the row at "SPLIT"): there, at every coin, every input and
every challenge, the frame's function play returns at the row; the round as played and where the run
stands behind it are written out as terms. The kind lays three such rows, and a fourth where the
shape splits (halves_eq). Two definitions, and three statements with their proofs.

  liftK14, halves_eq   the lift by which proverSidesOfSharedRounds lays the parts, under a name
  askOf           the state as the kind's parts are handed it
  quiet_plays     a quiet row: the round as played holds no item and no table
  split_plays     the row at "SPLIT": the round as played holds the one element scalarAt
                  (Honest/K14/PartsFit.lean), at the coin that the row is handed

b is any sub-protocol that declares one round of the right form and no oracle message. That the
kind's own do: Honest/K14/Debts.lean. By one_plays (Honest/K14/Kit.lean). Both statements stand at
play's third argument [] alone: no stored run's rounds to fall back on (back, Honest/Frame.lean).

What is not claimed. That the book lends the row its coins; that the columns which "LOC" reads are
at hand; that a sub-protocol's step accepts. Where the run stands at fewer challenges heard than
"SPLIT" reads, the element is muAtE at shorter lists: play returns there too. Nothing on soundness
or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.PartsFit
import Johnson.Desc.ProofFile.Honest.K14.Kit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)

variable {S Cl W₀ Rc Ky X : Type}

/-- The lift by which proverSidesOfSharedRounds lays the kind's parts. -/
def liftK14 (A : Data) (weights : W₀ → Weights) (p : Part Empty Ask Unit) :
    Part Empty (Common W₀ Rc Ky) X :=
  p.lift (fun v => v) (fun c => ⟨entriesOf A.S (weights c.w₀)⟩) (fun _ => ()) fun x _ => x

/-- proverSidesOfSharedRounds, with the lift under its name. -/
theorem halves_eq (A : Data) (weights : W₀ → Weights) :
    (proverSidesOfSharedRounds A weights : List (Placed Empty (Common W₀ Rc Ky) X)) =
      [⟨place 1, [liftK14 A weights quietPart]⟩, ⟨place 4, [liftK14 A weights quietPart]⟩,
        ⟨place 7, [liftK14 A weights quietPart]⟩] ++
        if A.S.sharedSplitNeeded then [⟨place 8, [liftK14 A weights (splitPart A)]⟩] else [] := rfl

/-- The state as the kind's parts are handed it. -/
def askOf (A : Data) (weights : W₀ → Weights) (t : State (Common W₀ Rc Ky) X) : State Ask Unit :=
  t.narrow (fun c => ⟨entriesOf A.S (weights c.w₀)⟩) fun _ => ()

/-- **A quiet row plays**: at a sub-protocol that declares one round which cuts no item and has no
oracle message: at every coin, input and challenge. -/
theorem quiet_plays (A : Data) (weights : W₀ → Weights) (b : Block S Cl) (d : Fmt.DeclaredRound)
    (hb : b.rounds.zip b.oracles = [(d, [])]) (hd : d.items = []) (v : Option Empty)
    (c : RowCoins [(liftK14 A weights quietPart : Part Empty (Common W₀ Rc Ky) X)])
    (m : Mid (Common W₀ Rc Ky) X) (x : Fmt.Drawn) :
    play (({ place := b.place, parts := [liftK14 A weights quietPart] } :
        Placed Empty (Common W₀ Rc Ky) X).steps b v c) [x] [] m =
      .ok ([playedBy b [] [] x], pastOf m [] x) := by
  refine (one_plays b d [] hb _ _ rfl (fun _ _ => rfl) (fun w => nomatch w) v c m x ⟨[], []⟩ rfl
    (quiet_fits d hd)).trans ?_
  rfl

/-- **The row at "SPLIT" plays**: at a sub-protocol that declares one round which cuts one element
and has no oracle message: at every coin, input and challenge: the one element scalarAt. -/
theorem split_plays (A : Data) (weights : W₀ → Weights) (b : Block S Cl) (d : Fmt.DeclaredRound)
    (hb : b.rounds.zip b.oracles = [(d, [])]) (hd : d.items = [.e]) (v : Option Empty)
    (c : RowCoins [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X)])
    (m : Mid (Common W₀ Rc Ky) X) (x : Fmt.Drawn) :
    play (({ place := b.place, parts := [liftK14 A weights (splitPart A)] } :
        Placed Empty (Common W₀ Rc Ky) X).steps b v c) [x] [] m =
      .ok ([playedBy b [.e (OnBytes.Slice.ofE (scalarAt A c.1 (askOf A weights m.st)))] [] x],
        pastOf m [.e (OnBytes.Slice.ofE (scalarAt A c.1 (askOf A weights m.st)))] x) := by
  refine (one_plays b d [] hb _ _ rfl (fun _ _ => rfl) (fun w => nomatch w) v c m x
    ⟨[.e (scalarAt A c.1 (askOf A weights m.st))], []⟩ rfl (split_fits d hd _)).trans ?_
  rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.halves_eq
#print axioms ProofFile.Honest.K14.quiet_plays
#print axioms ProofFile.Honest.K14.split_plays
