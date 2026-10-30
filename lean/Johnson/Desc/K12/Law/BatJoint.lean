-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/BatJoint.lean: the joint between "the rows that the batching takes" and the
chain's "no witness", as propositions. Definitions, and one line by which the stronger form gives
the weaker. Neither form is proved here.

The statements are laid down so that whoever types the proof and whoever spends it use one form.
Main names:
  `NoneNear s e S' L rows y`: the relation in front, refuted: no witness whose encoding is within e
    positions of y holds words (its own tables' words: `wordsOf S' L (tabOf s w.1)`) of which all
    the rows hold. It hangs on y, e and the rows, not on the drawn x.
  `BadDraws s e S' g L rows y`: the values θ of the drawn element at which the batched claim has a
    witness: ∃ x row, readE x = θ ∧ Bat.combine S' g ⟨L, rows⟩ x = some row ∧ row.kept = #[] ∧ ∃ w,
    s.RIn e (stmG s row, y) w. ("No kept form" stands inside the set, not as a premise on every x:
    the law holds it of its own row.)
  `BatCatches … lst`: `NoneNear` gives that at most lst · (rows.size − 1) values of θ are bad draws.
    lst: a bound on the list of witnesses within e of y (`LdCode.ListAt`).
  `BatCatchesAt`: the statement to be proved (it is proved in
    Johnson/Desc/Means/BatCatchesProof.lean, `batCatchesAt`, which imports this file): under the
    premises of `rIn_rows` (Johnson/Desc/K12/Law/TabWords.lean) and `s.cIn.ListAt e lst`.
  `BatCatchesBare`, `batCatchesAt_of_bare`: by the road below, `s.Sized`, e < s.d and `RowsBlank`
    are spent by nothing: the statement without them is the stronger, and gives `BatCatchesAt`.
    Where the three do weigh: for whoever pays `NoneNear`: `wordsOf S' L (tabOf s w.1)` is 0 beyond
    the real rows (`Padded`) only on blank tables (`blank_of_near`), and "not all rows hold" of a
    near witness's words can be had from the block in front only for words of that kind.
The road, by reading, not by Lean: let ι be the witnesses within e of y: finite, at most lst by
`ListAt`, and fixed before x. For w in ι take the words m w := wordsOf S' L (tabOf s w.1). By
`rIn_iff`, `blank_of_near` and `laid_wordsOf` a witness of `RIn` at `stmG s row` gives `GroupSays …
row (tabOf s w.1)` at tables in which m w is laid. `combine_catches_many`
(Johnson/Desc/Means/CatchesMany.lean: a finite family of words, each with "not all rows hold")
bounds the draws by card ι · (rows.size − 1).
The spending: at a drawn x whose θ := readE x is no bad draw, with the row that the batching returns
and row.kept = #[]: ∀ w, ¬ s.RIn e (stmG s row, y) w, which is the premise of `chain_many`
(OnBytes/Slice/ManySem.lean), to the letter.
Against a false or empty statement, by reading: with no row at all `AllSay` holds of everything, so
`NoneNear` says that nothing is near y, and then no draw is bad: 0 ≤ 0. y, e, the rows and so the
list stand in front of θ. lst multiplies the count of a round that draws one element, not a round of
positions.
Limits:
Who pays `NoneNear`: it asks "not all rows hold" of every near witness's own words. At radii beyond
half the distance that is more than "the committed words fail a row": the block in front must hand
its claim over list-valued. That is the form of the joint that comes in, and it is not here.
The count is of values θ : GE; several raw x may read as one θ, so the number of x is not bounded by
it. The game's form (`Iop.Doomed` over the round "BAT", with its clause on work) and the law on the
reading of the draw (how many challenge values go to one θ) are not here: the library's `BatSem`
(OnBytes/Slice/ChainSem.lean) has both for a link's group.
No soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises.

-/
import Johnson.Desc.K12.Law.TabWords

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open OnBytes.Means

def NoneNear (s : Sg) (e : ℕ) (S' : Statement) (L : GroupLayout) (rows : Array Row) (y :
    s.cIn.Word) :
    Prop :=
  ∀ w : s.cIn.N.Wit, offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e →
    ¬ AllSay rdE S' rows.toList (wordsOf S' L (tabOf s w.1))

def BadDraws (s : Sg) (e : ℕ) (S' : Statement) (g : Nat) (L : GroupLayout) (rows : Array Row)
    (y : s.cIn.Word) (θ : GE) : Prop :=
  ∃ (x : E) (row : GroupRow), readE x = θ ∧ Bat.combine S' g ⟨L, rows⟩ x = some row ∧
    row.kept = #[] ∧ ∃ w, s.RIn e (stmG s row, y) w

def BatCatches (s : Sg) (e lst : ℕ) (S' : Statement) (g : Nat) (L : GroupLayout) (rows : Array Row)
    (y : s.cIn.Word) : Prop :=
  NoneNear s e S' L rows y → cnt (BadDraws s e S' g L rows y) ≤ lst * (rows.size - 1)

/-- The statement to be proved. -/
def BatCatchesAt : Prop :=
  ∀ (s : Sg) (e lst : ℕ) (S' : Statement) (g : Nat) (L : GroupLayout) (rows : Array Row)
    (y : s.cIn.Word), s.Sized → e < s.d → s.cIn.ListAt e lst → combineAt S' g ⟨L, rows⟩ = true →
    L.k = s.h + s.g → L.h = s.h → 2 ^ L.logEll = s.C.l → 2 ^ L.logEllZk = s.Z.l →
    RowsBlank s S' L y →
    BatCatches s e lst S' g L rows y

/-- The same without the three premises that the road by combine_catches_many does
not spend (its premise on tables, LaidOn, holds of wordsOf S' L T in T for every T): the stronger
statement. -/
def BatCatchesBare : Prop :=
  ∀ (s : Sg) (e lst : ℕ) (S' : Statement) (g : Nat) (L : GroupLayout) (rows : Array Row)
    (y : s.cIn.Word), s.cIn.ListAt e lst → combineAt S' g ⟨L, rows⟩ = true →
    L.k = s.h + s.g → L.h = s.h → 2 ^ L.logEll = s.C.l → 2 ^ L.logEllZk = s.Z.l →
    BatCatches s e lst S' g L rows y

theorem batCatchesAt_of_bare (h : BatCatchesBare) : BatCatchesAt :=
  fun s e lst S' g L rows y _ _ hl hc hk hh h1 h2 _ => h s e lst S' g L rows y hl hc hk hh h1 h2

end H2K.ClaimSays
