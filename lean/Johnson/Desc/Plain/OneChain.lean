-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/OneChain.lean: THE RULE OF COMPOSITION (this file and
Johnson/Desc/Plain/OneFile.lean) FOR A FILE OF ONE UNSEALED CHAIN OVER TWO
STORED TABLES (the entry file), in the plain form, of the chain's own decision (`chainAt`,
Johnson/Desc/Block.lean), DOWN TO THE CONDITION THAT THE TOP ASKS OF THE ENTRY FILE's DECISION:
`SoundAt` (OnBytes/Flat/LinkSib.lean), which gives `CompilerSoundnessConditionStatements.entrySound`.

Nothing of Johnson/Desc/Sound/'s pieces is used: they stand over one stored table and three chains.
The like rule over these pieces is `fold_chain` (Johnson/Desc/Plain/FoldChain.lean): `EachLeadsO`
here has the three clauses of its `EachLeads`.
The entry file's protocol is the library's written link over letters (`linkProtocolOfRoundData`: `skeletonOverBothExternalStrings`, `viewX`,
OnBytes/TypedOracleCompiler/Run/PlanQX.lean).

How a block becomes a reduction here. A STATEMENT is the carried record, with THE CHAIN's OWN TREES
THAT HAVE BEEN SENT (as a function from a tree's number and a leaf to its column) and their number.
The two stored tables y are fixed outside. `OPiece.out`: on a transcript σ of the block's own
rounds: THE SLOT's TEST OF THESE ROUNDS' WORK (`passT`: a block of the library's is carried only
where it has passed); the rounds as a view shows them (`rvT`); THE COLUMNS THAT THE BLOCK's OWN
DECLARED ROUNDS ASK (`groupsOf`), each looked up by its key and position in y, in the trees sent
before, or in σ's own; THE TEST THAT EVERY WORD OF THESE ROUNDS AND COLUMNS IS BELOW THE PRIME
(`viewWordsBelowPrime`: a one-chain file's decision asks it of the whole view); then
`Block.step` itself.
No cutting of the view's list of columns is needed: EVERY COLUMN OF THE VIEW IS THE ORACLE's COLUMN
AT ITS KEY AND POSITION (`view_true`), and `Block.step` tests keys and positions.

  `joinErr`, `doomed_join`, `col_join`: over two lists of rounds' data in a row, beside the
    library's `Fo.Peel.joinR` … (a piece's data are `RDT`s, the maker's rounds' data, so that the
    library's lemmas serve; `stored` is not read: the slot's stored openings are the letter xs).
  `EachLeadsO`, `chainRel`, `one_chain`: one `Leads` a block ⟹ the blocks in a row.
  In Johnson/Desc/Plain/OneFile.lean:
  `fold_row`: WHERE THE FOLD SAYS YES ON THE WHOLE VIEW, THE BLOCKS IN A ROW PUT OUT, with the
    fold's end.
  `linkW_sound`, `soundAt_of_chain`: the file's rule.
PREMISES of `soundAt_of_chain`, ALL BUT hdec OWED ONLY WHERE THE PUBLIC TESTS ON THE PLAN SAY YES
(the letter `pub`: where they say no the decision says no to all, and the errors 0 do): lens (each
piece's data are as many as its block's rounds) · back (a block opens no tree that is sent behind
it: `OpensBack`) · hdec (the decision's yes gives the public tests', the test on the instance, the
words' test on the view, the fold's yes and the last test's) · laws (`EachLeadsO`, at every instance
and pair of tables) · tie (under these yeses, "the first condition → the relations in a row" gives
the entry's language) · below.
Limits. A rule. Of the slot's own tests the rounds' work stands in a piece; the two others (full
draws, carried positions) are not spent in this file. A block's errors count against all of a
round's challenges. Nothing on acceptance.
Four small laws on Block.lean's texts where they go on (`bindOk`, `mapOk`, `foldConsOk`, `chainOk`)
are typed here after those of Johnson/Desc/Sound/FoldHeardProofs.lean, under this file's own
namespace: another file beneath the entry's link (Johnson/Desc/MadeOk.lean) holds a
`chainOk` of its own. `bindOk` IS A FURTHER
TEXT OF A FOUR-LINE LEMMA OF THE LIBRARY's (`OnBytes.K.bind_returns`,
OnBytes/K/ServedBlind.lean; privately `ok_bind2`,
OnBytes/Flat/LinksFreeHead.lean:281): kept, so
that this file need not import a file on served requests: to be struck if one home is wanted for it.

-/
import Johnson.Desc.Plain.Leads
import Johnson.Desc.Block
import OnBytes.Flat.LinkSib
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelJoinT
import OnBytes.TypedOracleCompiler.Run.PageIsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Plain.One
open TypedOracleCompiler.Run.PQ (viewX skeletonOverBothExternalStrings SOf)
open OnBytes.Maker (RDT toRDs uLT rvT rhoT passT colAtST)
open Fo.Peel (joinR fstR sndR joinR_split fstR_join sndR_join rvT_join rvT_length passT_join)
open _root_.Run.PQ (CK SgX XO storedKey xPos)
open _root_.Iop (Reduction Err Shape Doomed Tr twoExternalStrings)
open _root_.Prob (cnt cnt_mono cnt_false)

/-! ## 0 Block.lean's texts, where they go on -/

theorem bindOk {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapOk {ε α β : Type} {x : Except ε α} {f : α → β} {y : β}
    (h : x.map f = .ok y) : ∃ a, x = .ok a ∧ f a = y := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem foldConsOk {S Cl : Type} {ft : Nat} {b : Block S Cl} {l : List (Block S Cl)} {s : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (H : foldBlocks ft (b :: l) s rs cols = .ok out) :
    ∃ s' k, b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
      foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) = .ok out := by
  simp only [foldBlocks, List.splitAt_eq] at H
  split at H
  next => exact nomatch H
  next =>
    split at H
    next => exact nomatch H
    next s' k hst => exact ⟨s', k, hst, H⟩

theorem chainOk {S Cl : Type} {name : String} {ft : Nat} {bs : List (Block S Cl)} {s e : S}
    {v : Fmt.View} (H : chainAt name ft bs s v = .ok e) :
    foldBlocks ft bs s v.rounds v.opened = .ok (e, [], []) := by
  unfold chainAt at H
  split at H
  next => exact nomatch H
  next =>
    split at H
    next s' heq => exact (Except.ok.inj H) ▸ heq
    next => exact nomatch H
    next => exact nomatch H

/-! ## 1 Transcripts over two lists of rounds' data in a row

The joined transcript, its two parts, the view's rounds and the tests of work of a joined list ARE
THE LIBRARY's (`Fo.Peel.joinR`, `fstR`, `sndR`, `joinR_split`, `fstR_join`, `sndR_join`, `rvT_join`,
`rvT_length`, `passT_join`:
OnBytes/Tie/Pv/Lookup/Peel/FoPeelJoinT.lean). Here only what that file lacks: the errors of a joined
list, "the prover has lost" over it, and a joined transcript's trees. -/

section Tr
variable (C : CK)

def joinErr : (d₁ d₂ : List RDT) → Err (uLT C d₁) → Err (uLT C d₂) → Err (uLT C (d₁ ++ d₂))
  | [], _, _, ε₂ => ε₂
  | _ :: d₁, d₂, (e, ε₁), ε₂ => (e, joinErr d₁ d₂ ε₁ ε₂)

/-- `Doomed.append` (Iop/Rbr.lean) over a joined list of rounds' data, without a cast. -/
theorem doomed_join : ∀ (d₁ d₂ : List RDT) (ε₁ : Err (uLT C d₁)) (ε₂ : Err (uLT C d₂))
    (P : Tr (uLT C (d₁ ++ d₂)) → Prop),
    Doomed (uLT C d₁) ε₁ (fun τ₁ => Doomed (uLT C d₂) ε₂ fun τ₂ => P (joinR C d₁ d₂ τ₁ τ₂)) →
    Doomed (uLT C (d₁ ++ d₂)) (joinErr C d₁ d₂ ε₁ ε₂) P
  | [], _, _, _, _, h => h
  | _ :: d₁, d₂, (_, ε₁), ε₂, _, h => fun m =>
      le_trans (cnt_mono fun _ hc hd => hc (doomed_join d₁ d₂ ε₁ ε₂ _ hd)) (h m)

theorem below_join (κ : ℝ≥0∞) : ∀ (d₁ d₂ : List RDT) (ε₁ : Err (uLT C d₁)) (ε₂ : Err (uLT C d₂)),
    Err.Below ε₁ κ → Err.Below ε₂ κ → Err.Below (joinErr C d₁ d₂ ε₁ ε₂) κ
  | [], _, _, _, _, h => h
  | _ :: d₁, d₂, (_, ε₁), ε₂, h₁, h₂ => ⟨h₁.1, below_join κ d₁ d₂ ε₁ ε₂ h₁.2 h₂⟩

/-- The number of trees that the rounds send: the library's `nTrees`
(OnBytes/TypedOracleCompiler/Run/PageIsRows.lean) at the maker's data. -/
abbrev nT (ds : List RDT) : ℕ := TypedOracleCompiler.Run.PQ.nTrees (toRDs ds)

/-- A joined transcript's trees. For rounds with at most one tree: `colAtS_app_lt`, `colAtS_app_ge`
(OnBytes/Slice/ChainTop.lean). A NEAR TWIN: `colAtST_join` (Johnson/Desc/Sound/Cuts.lean) says the
same over another text of "the number of trees" (there the sum of the lists' lengths; here
`PQ.nTrees` of the library's rounds' data). -/
theorem col_join : ∀ (d₁ d₂ : List RDT) (τ₁ : Tr (uLT C d₁)) (τ₂ : Tr (uLT C d₂)) (n x : ℕ),
    colAtST C (d₁ ++ d₂) (joinR C d₁ d₂ τ₁ τ₂) n x =
      if n < nT d₁ then colAtST C d₁ τ₁ n x else colAtST C d₂ τ₂ (n - nT d₁) x
  | [], _, _, _, n, _ => by
      show _ = if n < 0 then _ else _
      rw [if_neg (Nat.not_lt_zero n)]
      rfl
  | d :: d₁, d₂, (m, c, τ₁), τ₂, n, x => by
      show (if n < d.trees.length then _ else
          colAtST C (d₁ ++ d₂) (joinR C d₁ d₂ τ₁ τ₂) (n - d.trees.length) x) =
        if n < d.trees.length + nT d₁ then
          (if n < d.trees.length then _ else colAtST C d₁ τ₁ (n - d.trees.length) x)
        else colAtST C d₂ τ₂ (n - (d.trees.length + nT d₁)) x
      by_cases h : n < d.trees.length
      · rw [if_pos h, if_pos (by omega), if_pos h]
      · rw [if_neg h, col_join d₁ d₂ τ₁ τ₂ (n - d.trees.length) x]
        by_cases h2 : n < d.trees.length + nT d₁
        · rw [if_pos (by omega), if_pos h2, if_neg h]
        · rw [if_neg (by omega), if_neg h2, Nat.sub_sub]

end Tr

/-! ## 2 Statements, pieces, the blocks in a row -/

/-- The chain's own trees that have been sent: from a tree's number and a leaf to its column. -/
abbrev Look : Type := ℕ → ℕ → Option (List UInt64)

/-- A statement: the carried record; the trees sent; their number. -/
abbrev Stm (S : Type) : Type := S × Look × ℕ

section Piece
variable {C : CK} {S Cl : Type} (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str) (ft : ℕ)

/-- A column by its key and position: in the first stored table, in the second, or in a tree. -/
def lookY (look : Look) (k p : ℕ) : Option (List UInt64) :=
  if k = storedKey false then
    (xPos (2 ^ a) (false, p)).map fun q => ((twoExternalStrings (2 ^ a) SgX).rd y q).2
  else if k = storedKey true then
    (xPos (2 ^ a) (true, p)).map fun q => ((twoExternalStrings (2 ^ a) SgX).rd y q).2
  else look k p

/-- Key, position and width of every column that the block's declared rounds ask. -/
def wantOf (b : Block S Cl) (rs : List Fmt.RoundView) : List (ℕ × ℕ × ℕ) :=
  (groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id

/-- These columns, looked up. -/
def colsFor (L : ℕ → ℕ → Option (List UInt64)) : List (ℕ × ℕ × ℕ) → Option (List OpenedColumn)
  | [] => some []
  | w :: ws =>
    match L w.1 w.2.1, colsFor L ws with
    | some c, some cs => some ((w.1, w.2.1, c) :: cs)
    | _, _ => none

/-- A block with the data of its own rounds and its errors. -/
structure OPiece (C : CK) (S Cl : Type) where
  b : Block S Cl
  ds : List RDT
  err : Err (uLT C ds)

/-- The trees behind a block. -/
def lookOn (p : OPiece C S Cl) (look : Look) (base : ℕ) (σ : Tr (uLT C p.ds)) : Look := fun n x =>
  if n < base then look n x else colAtST C p.ds σ (n - base) x

/-- **The block at its own rounds**, behind the slot's test of these rounds' work. -/
def OPiece.out (p : OPiece C S Cl) (t : Stm S) (σ : Tr (uLT C p.ds)) : Option (Stm S) :=
  if passT C p.ds (rhoT C p.ds σ) = true then (colsFor (lookY a y (lookOn p t.2.1 t.2.2 σ)) (wantOf
      ft p.b (rvT C p.ds σ))).bind fun cs =>
    if viewWordsBelowPrime ⟨rvT C p.ds σ, cs⟩ = true then
      (p.b.step ft t.1 (rvT C p.ds σ) cs).toOption.map fun r =>
        (r.1, lookOn p t.2.1 t.2.2 σ, t.2.2 + nT p.ds)
    else none
  else none

@[reducible] def OPiece.red (p : OPiece C S Cl) : Reduction (Stm S) (Stm S) :=
  ⟨uLT C p.ds, p.out a y ft⟩

def rowDs : List (OPiece C S Cl) → List RDT
  | [] => []
  | p :: l => p.ds ++ rowDs l

def rowErr : (l : List (OPiece C S Cl)) → Err (uLT C (rowDs l))
  | [] => ()
  | p :: l => joinErr C p.ds (rowDs l) p.err (rowErr l)

def rowOut : (l : List (OPiece C S Cl)) → Stm S → Tr (uLT C (rowDs l)) → Option (Stm S)
  | [], t, _ => some t
  | p :: l, t, τ =>
    (p.out a y ft t (fstR C p.ds (rowDs l) τ)).bind fun u =>
      rowOut l u (sndR C p.ds (rowDs l) τ)

/-- One premise for each block. -/
def EachLeadsO (on : ℕ → Stm S → Prop) (Q : ℕ → Stm S → Stm S → Prop) :
    ℕ → List (OPiece C S Cl) → Prop
  | _, [] => True
  | i, p :: l =>
    (p.red a y ft).Leads (on i) (Q i) p.err ∧ (∀ t u, on i t → Q i t u → on (i + 1) u) ∧
      EachLeadsO on Q (i + 1) l

/-- The relations in a row: there are statements at all the boundaries between. -/
def chainRel (Q : ℕ → Stm S → Stm S → Prop) : ℕ → ℕ → Stm S → Stm S → Prop
  | _, 0, t, e => t = e
  | i, n + 1, t, e => ∃ u, Q i t u ∧ chainRel Q (i + 1) n u e

/-- **The blocks in a row.** -/
theorem one_chain (on : ℕ → Stm S → Prop) (Q : ℕ → Stm S → Stm S → Prop) :
    ∀ (l : List (OPiece C S Cl)) (i : ℕ) (t : Stm S), on i t → EachLeadsO a y ft on Q i l →
      Doomed (uLT C (rowDs l)) (rowErr l) fun τ =>
        ∀ e, rowOut a y ft l t τ = some e → chainRel Q i l.length t e
  | [], _, _, _, _ => fun _ he => Option.some.inj he
  | p :: l, i, t, ht, h => by
      refine doomed_join C p.ds (rowDs l) p.err (rowErr l) _ (Doomed.mono _ _ ?_ (h.1 t ht))
      intro τ₁ hτ₁
      cases hp : p.out a y ft t τ₁ with
      | none =>
        refine Doomed.of_forall _ _ fun τ₂ e he => ?_
        have he' : (p.out a y ft t (fstR C p.ds (rowDs l) (joinR C p.ds (rowDs l) τ₁ τ₂))).bind
            (fun u => rowOut a y ft l u (sndR C p.ds (rowDs l)
              (joinR C p.ds (rowDs l) τ₁ τ₂))) = some e := he
        rw [fstR_join, hp] at he'
        cases he'
      | some u =>
        have hq := hτ₁ u hp
        refine Doomed.mono _ _ ?_ (one_chain on Q l (i + 1) u (h.2.1 t u ht hq) h.2.2)
        intro τ₂ hτ₂ e he
        have he' : (p.out a y ft t (fstR C p.ds (rowDs l) (joinR C p.ds (rowDs l) τ₁ τ₂))).bind
            (fun u => rowOut a y ft l u (sndR C p.ds (rowDs l)
              (joinR C p.ds (rowDs l) τ₁ τ₂))) = some e := he
        rw [fstR_join, sndR_join, hp] at he'
        exact ⟨u, hq, hτ₂ e he'⟩

end Piece

end VerifiableInference.Desc.Plain.One

#print axioms VerifiableInference.Desc.Plain.One.doomed_join
#print axioms VerifiableInference.Desc.Plain.One.col_join
#print axioms VerifiableInference.Desc.Plain.One.one_chain
