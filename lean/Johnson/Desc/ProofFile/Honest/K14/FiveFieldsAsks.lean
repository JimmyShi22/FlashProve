-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FiveFieldsAsks.lean: kind K14: FiveFields
(Honest/K14/FiveFields.lean) AT THE LETTERS' OWN valid AND stored (L : SharedThread.Letters: the
shared chain's parameters, as one structure) IS WHAT K14Asks (Honest/K14/Asks.lean) ASKS IN ITS FIVE
FIELDS cols, tab, key, seeds, ans. Statements with their proofs.

  rw_holds2       the field Rw of holds2 is rowsK, at every run's coins: by unfolding
  five_gives      **FiveFields at L.valid and L.stored gives the five fields, in K14Asks' own text**
  five_of_asks    K14Asks gives FiveFields there (a run's coins are needed to read its two fields
                  that name them: any serve; Coins Bk has a member at every book: Honest/Frame.lean)
  asks_of_five    **K14Asks from FiveFields and its eleven other fields**

A LINE ON THIS FILE AND ITS FELLOW (Honest/K14/FiveFields.lean,
Honest/K14/FiveFieldsAsks.lean), set here to the letter (its "letters" are FiveFields' four free
parameters; the limit that it names is that head's paragraph "A limit on the coins, before the
others"): «K14's five fields on the committed table and the key, as one structure over letters
(valid · stored · weights · rand): the stored columns at their width, the table as the encoding of
the rows made of the weights and the committer's randomness, the key's sizes and seeds, and each
answer as its row's own: what an honest committer's outputs ARE, each an implication from valid;
completeness's kind; no run's coin is read; no measure, no simulator; NOT IN FRONT OF A LAW OVER
THE COMMITTER's RANDOMNESS UNLESS THE KEY AND THE STORED TABLE ARE MADE OF THE COINS: under a valid
that leaves them letters, ans and tab fix the pads and tails (the limit in
Johnson/Bind/ForProver/FiveAt.lean's head)»

What is not claimed. That FiveFields, or K14Asks, holds at any letters. (Who proves the five
sentences, and at which valid and stored: Honest/K14/FiveFields.lean's head, WHO MEETS THE FIVE; of
K14Asks no term is typed: Honest/K14/Asks.lean's head.) The limits at the five fields:
Honest/K14/FiveFields.lean's head, Limits. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.FiveFields
import Johnson.Desc.ProofFile.Honest.K14.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Own (keyFits)
open Desc.K14 (P14 St)
open Desc.K14.Honest
open Desc.K14.Law (genK)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Cl Wt : Type} {ℓ : WitLens Wt}
  {L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt} {Q : P14}
  {sentU : Array OracleNotice} {layO : TreeLay} {c : Model.Verify.Chains}
  {tests : List (Block St Unit)} {last : List (Block St Unit) → Block St Unit} {A : Data}
  {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- The rows that holds2 holds are rowsK, whatever the run's coins. -/
theorem rw_holds2 (Q : P14) (weights : W₀ → Weights) (rand : Rc → TableRand) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) : (holds2 Q weights rand k w).Rw = rowsK Q weights rand w := rfl

/-- **FiveFields at the letters' own valid and stored gives the five fields of K14Asks, in its own
text.** -/
theorem five_gives (F : FiveFields Q L.valid L.stored weights rand) :
    (∀ w, L.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
      ∃ u, L.stored w (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W) ∧
    (∀ (k : Coins Bk) w, L.valid w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        rdE.val (ofF (((L.stored w Q.item x).getD []).toArray.getD r 0)) =
          genK rdE Q.par.S.fold x ((holds2 Q weights rand k w).Rw r)) ∧
    (∀ w, L.valid w → keyFits w.key Q.par.S.fold.index = true) ∧
    (∀ w, L.valid w → noZeroFactor w.key = true) ∧
    ∀ (k : Coins Bk) w, L.valid w → OwnAnswers Q w.key (holds2 Q weights rand k w) :=
  ⟨F.cols, fun _ w hw => F.tab w hw, F.key, F.seeds,
    fun k w hw => ownAnswers_of F w hw _ (rw_holds2 Q weights rand k w)⟩

/-- K14Asks gives FiveFields at the letters' own valid and stored; k: any run's coins. -/
theorem five_of_asks (h : K14Asks ℓ L Q sentU layO c tests last A weights rand) (k : Coins Bk) :
    FiveFields Q L.valid L.stored weights rand :=
  ⟨h.cols, fun w hw => h.tab k w hw, h.key, h.seeds, fun w hw => h.ans k w hw⟩

/-- **K14Asks from FiveFields and its eleven other fields.** -/
theorem asks_of_five (F : FiveFields Q L.valid L.stored weights rand)
    (letters : Asked ℓ L Q sentU c tests last (holds2 Q weights rand))
    (plan : Plan2 Q sentU layO) (shapes : SendShapes Q) (point : A.atPoint = 0)
    (zeta : A.atZeta = 6)
    (halves : HalvesIn Q (othersOf ℓ L c tests last (holds2 Q weights rand)) A weights)
    (sends : SendsIn Q (othersOf ℓ L c tests last (holds2 Q weights rand)) A weights rand)
    (tenant : Function.Injective L.N.tenant)
    (treesU : TreesLaid L.thread 2 (jobU ⟨Q, 0⟩) (witOf Q weights rand))
    (treesO : TreesLaid L.thread 5 (jobOmega ⟨Q, 0⟩) (witOf Q weights rand))
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨Q, 0⟩).Q.codes
        (jobOmega ⟨Q, 0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort 1⟩) :
    K14Asks ℓ L Q sentU layO c tests last A weights rand :=
  { letters := letters, plan := plan, shapes := shapes, point := point, zeta := zeta
    halves := halves, sends := sends, tenant := tenant, treesU := treesU, treesO := treesO
    cols := (five_gives F).1, tab := (five_gives F).2.1, key := (five_gives F).2.2.1
    seeds := (five_gives F).2.2.2.1, ans := (five_gives F).2.2.2.2, book := book }

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.rw_holds2
#print axioms ProofFile.Honest.K14.five_gives
#print axioms ProofFile.Honest.K14.five_of_asks
#print axioms ProofFile.Honest.K14.asks_of_five
