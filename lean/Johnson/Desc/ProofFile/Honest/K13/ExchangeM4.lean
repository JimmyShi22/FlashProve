-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ExchangeM4.lean: kind K13's share of the debt `Exchange`
(Johnson/Desc/ProofFile/Honest/Thread/Pays.lean) at the place "M:4" of the first chain's thread
(Honest/Thread/First.lean): CONDITIONAL STATEMENTS. Definitions; the statements are definitions of
type Prop. No theorem. The proofs: Honest/K13/ExchangeM4Proof.lean.

At W's sending the forward row owes four items (`owes_at_m4`, ExchangeM4Proof.lean): `pinV`,
`pileOne`, `pinW`, `wrow`. Two of them are kind K13's: `wrow`, the row (Eval) says its claim of the
witness's words; `pileOne`, the one row on the table is true of the witness. `pinV` speaks of W's
message and is not stated here; `pinW` speaks of the committed table: at the library's own
parameters it holds by unfolding (Honest/K13/ExchangeM4At.lean). WHICH ITEM STANDS UNDER WHAT.
`pileOne` (`PileOneAtM4`): under `IM.Open`, `TiedAtM4` and `PublicAtM4` from the thread in front.
NEITHER `WitnessHasW` NOR `ReplyRides` IS ASKED FOR IT: it is open in front, and it is carried over
the step. `wrow` (`WRowAtM4`): under these three AND `ReplyRides` AND `WitnessHasW`. WHAT THE
STATEMENTS DO WITH THE DEBT AT `wrow`. They do not meet it: they carry it back to these premises.
Given that W's message holds the claim's row weights times the matrix, "(Eval) says its claim" is
"the claim's row is true" (the library's `eval_back`, Johnson/Desc/K13/Law/Eval.lean), which is
`pileOne` behind. What is special to an honest prover, that W IS that vector, is the premise
`WitnessHasW`, whole. Words of the frame for the honest side, which are explained in the heads of
Honest/Thread/Thr.lean, Pays.lean and First.lean: a chain's thread (the sentence that stands at each
border between two members of the chain's flat list); its parameters (the structure `Letters`); a
debt (a statement that is owed at a member); the forward row of a member (which items it asks, owes
and shuts); the Script (the functions from which the witness is made).
Main names:
  `TiedAtM4`: what ties a thread's parameters to the proof file's IOP at this place, in six fields.
  `PublicAtM4 Pw s`: seven sentences on the verifier's public state in front.
  `WitnessHasW`: **the condition on the witness's message for W**: WHERE THE REPLY THAT THE STATE IN
    FRONT HOLDS IS THE ONE ASKED (`ReplyIs`, Honest/K13/FromThread.lean): behind the member's
    accepted step, at every continuation of the challenges, the witness's words, read through the
    book of the state behind, hold in the MAIN table of W's number, at the places of the vector's
    entries with a number below 2^kCol, the claim's row weights times the matrix off the witness's
    cells (`WIs`, Law/Eval.lean). W's number is the count of oracle messages in front. THE ROW
    WEIGHTS ARE READ OFF THE VERIFIER's STATE IN FRONT, AND THEY HOLD ONE SENT VALUE: the reply as
    heard, which the prover sends in the clear at kind K7's place: the Script's message is a
    function of coins, input and challenges: without the condition on the reply the premise would
    fix that sent value. NOTHING IS ASKED OF ANY OTHER ENTRY: not of a pad's place, of a row's tail,
    of an entry that the vector leaves free, or of a mask row.
  `PileOneAtM4`, `WRowAtM4`: **the two statements**, each `ExchangeOf` (Honest/K13/ExchangeOf.lean)
    at one item. `ExchangeAtM4`: the two items together, under all of `WRowAtM4`'s premises.
ON THE CONDITION ON THE REPLY. It gains no strength: `WitnessHasW` under the condition, with
`ReplyRides`, gives `WitnessHasW` without it. What is won: the tie can be shown with no word on what
was sent, and the one sentence on a sent value stands alone under its name. Behind the accepted step
a row (Eval) is made (`eval_at_accept`, Johnson/Desc/K13/Honest/EvalAtAccept.lean), so `WRow`, which
holds of all words where no row is made, does not hold idly there.

What is not claimed. Nothing is proved in this file. That the thread holds at any run. That the
member's step accepts anywhere. That the thread in front gives `PublicAtM4`: the library has the
like from its promise at the border, for its own theorems on soundness
(Johnson/Desc/K13/Law/OwedReader4.lean: "had from the promise in front"); for the honest side it is
not shown here. `ReplyRides`: no clause of the thread that has a text says it; it follows where it
stands among the clauses of the parameter `rides`. `WitnessHasW`: it hangs on the Script's message
for W, which is a parameter of the thread; nothing holds the Script against what a prover's part
sends. That any parameters but those of Honest/K13/ExchangeM4At.lean meet `TiedAtM4`. The item
`pinV`. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeOf
import Johnson.Desc.ProofFile.Honest.K13.FromThread
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Member.Statement
import Johnson.Desc.K13.Law.Reader4
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.K13.Law.Eval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.K13 (Where whereOf pileMasksC rowsWithinC)
open VerifiableInference.Desc.K13.Law (WRow RowsTrue rwBook WIs)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}

/-- **What ties a thread's parameters to the proof file's IOP at "M:4".** c: the IOP's first chain.
arr: the reader's numbers of the messages. mat: the matrix off the witness's cells. -/
structure TiedAtM4 (L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT) (b : Nat)
    (Z : Pub) (c : Chain S Cl) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE) : Prop where
  /-- the thread's flat list is the IOP's -/
  flat : L.bs = c.blocksInOrder
  /-- the member number b stands at "M:4" -/
  place : ∀ blk, L.bs[b]? = some blk → blk.place = ⟨1, none, 4, .K1⟩
  /-- so does number b of the thread's list of places, off which the forward row is read -/
  row : L.ps[b]? = some ⟨1, none, 4, .K1⟩
  /-- the meaning's field `wrow` is the library's sentence, at the words read through the book -/
  wrow : ∀ w, (L.Mg w).wrow =
    fun a _ v => WRow (whereOf Z) a.2 (wordsFirst arr a.2.st a.2.book v)
  /-- the meaning's field `pileOne` is the library's sentence, at the reader through the book -/
  pileOne : ∀ w, (L.Mg w).pileOne = fun a _ v => RowsTrue (rwBook arr mat a) a.2 v
  /-- `pileOne` is open in front -/
  opened : Item.pileOne ∈ L.thread.opened b

/-- **Seven sentences on the verifier's public state in front of "M:4".** Pw: the kind's numbers. -/
structure PublicAtM4 (Pw : Where) (s : S) : Prop where
  /-- it stands at the chain's end, with a claim made of a row and nothing else laid beside it -/
  claim : ∃ (msg : Array OracleNotice) (ids : Array ℕ) (row : TensorRow),
    s.here = .mem ⟨msg, ids, some { claim := memberClaim row }⟩
  /-- W's vector fits its table -/
  room : Pw.lin.kCol ≤ (linLayW s.st.codes Pw.lin).bits
  /-- the rows on the table name mask entries of the message of index masks alone -/
  masks : pileMasksC s = true
  /-- these entries lie within that message's mask table -/
  within : rowsWithinC s = true
  /-- that message is there -/
  there : s.out.indexMasks < s.st.oracles.size
  /-- the book of trees and the statement are in step -/
  book : s.book.place.size = s.st.oracles.size
  /-- the message's place in the book names a tree that is there -/
  tree : ∀ q, s.book.place[s.out.indexMasks]? = some q → q.1 < s.book.trees.size

/-- **The condition on the witness's message for W**: where the reply that the state in front holds
is the one asked: in the main table of W's number, which is the count of oracle messages in front,
at the places of the vector's entries below 2^kCol, the witness's words hold the row weights of the
claim that the state in front holds, times the matrix. Nothing is asked of a pad's place, of a row's
tail, of an entry that the vector leaves free, or of a mask row. asked: what an instance asks about.
-/
def WitnessHasW (L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT) (b : Nat) (Z : Pub)
    (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (asked : Xi → E) : Prop :=
  ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En ds y cols s', Thr L.thread b k s m En →
    ReplyIs asked m.st.input.x s →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m En ds y cols s' →
    ∀ (ds' : List Fmt.Drawn) (row : TensorRow), s.rows = [row] →
      WIs (mat (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')).cells)
        (wordsFirst arr s'.st s'.book (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))
        row.g s.st.oracles.size (linLayW s.st.codes (whereOf Z).lin)

/-- The statement that, at `onlineDescription` opened as `IM.Open` has it, under `TiedAtM4`, where the thread
in front of the member number b gives `PublicAtM4`, the item `pileOne` holds behind the member's
accepted step, at every run's coins and every continuation of the challenges. Neither `WitnessHasW`
nor `ReplyRides` is asked. Not proved here (proved: `pileOne_at_m4`,
Honest/K13/ExchangeM4Proof.lean); a lemma's statement, none of the library's goals. -/
def PileOneAtM4 : Prop :=
  ∀ {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
    (L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT) (b : Nat)
    (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat)
    (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE),
    IM.Open o pol lay KL F Z Bs base c A B → TiedAtM4 L b Z c arr mat →
    (∀ k s m En, Thr L.thread b k s m En → PublicAtM4 (whereOf Z) s) →
    ExchangeOf L.thread b [Item.pileOne]

/-- The statement that under the same three premises, where the thread in front gives `ReplyIs` too
and `WitnessHasW` holds, the item `wrow` holds behind the member's accepted step, at every run's
coins and every continuation of the challenges. Not proved here (proved: `wrow_at_m4`,
Honest/K13/ExchangeM4Proof.lean); a lemma's statement, none of the library's goals. -/
def WRowAtM4 : Prop :=
  ∀ {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
    (L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT) (b : Nat)
    (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat)
    (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (asked : Xi → E),
    IM.Open o pol lay KL F Z Bs base c A B → TiedAtM4 L b Z c arr mat →
    (∀ k s m En, Thr L.thread b k s m En → PublicAtM4 (whereOf Z) s) → ReplyRides L b asked →
    WitnessHasW L b Z arr mat asked → ExchangeOf L.thread b [Item.wrow]

/-- The two items together, under all of `WRowAtM4`'s premises; of these `pileOne` needs the first
three alone (`PileOneAtM4`). Not proved here (proved: `exchange_at_m4`,
Honest/K13/ExchangeM4Proof.lean); a lemma's statement, none of the library's goals. -/
def ExchangeAtM4 : Prop :=
  ∀ {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
    (L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT) (b : Nat)
    (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat)
    (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (asked : Xi → E),
    IM.Open o pol lay KL F Z Bs base c A B → TiedAtM4 L b Z c arr mat →
    (∀ k s m En, Thr L.thread b k s m En → PublicAtM4 (whereOf Z) s) → ReplyRides L b asked →
    WitnessHasW L b Z arr mat asked → ExchangeOf L.thread b [Item.wrow, Item.pileOne]

end ProofFile.Honest.K13
