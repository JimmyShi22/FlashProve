-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/WordIsDataHead.lean: THE SHARED "SENDING" (the kind K1):
word_is_data_behind (WordIsData.lean) AT THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD
(lettersHead, Honest/Thread/FirstHead.lean): ITS TWO PUBLIC PREMISES ON THE VERIFIER's BOOK BEHIND
THE STEP ARE PAID, AT ANY MEMBER WHOSE YES LEAVES NO MARK: SO AT W's SENDING TOO, NUMBER 356. One
theorem; no definition.

  - word_is_data_head: UNDER h (the library's head: A HYPOTHESIS) · R (the record at lettersHead:
    A PREMISE, WHOLE: THE TIE, msgs and pads, is spent) · hmark (a yes of the member leaves no mark
    of failure: public) · the pair, the challenges' form and the member's accepted step ·
    main_data_e's five: word_is_data_behind's end.

The road. hFits: ProofFile's head_bookFits_next (Honest/Thread/BookFitsAt.lean); hNum: ProofFile's
head_treeNumber_next (Honest/Thread/BookFacts.lean): each under "no mark behind the step", which
hmark gives at the step's own yes (K1.step_ok). exchange_rows_head (ExchangeAtHead.lean) goes by
head_bookFits_next_front, which stops in front of number 353: this goes by the form that reaches the
chain's last five.
Kin, too: the sealed Meaning.K2.atFirstFits_all (Johnson/IMR/AtReach.lean) gives BookFits at every
reached state without hmark (L25's word; by reading; not called here).

hmark lies at K1's 52: k1_two_noMark, k1_fifty_noMark (MemberInScope.lean), k1_w_noMark
(MemberAtW.lean).

ALOUD. THE TIE (msgs, pads) IS A PREMISE HERE. "none => 0" IS A DEFAULT AT A DATUM: NEVER AT A PLACE
AT WHICH THE MESSAGE's SHAPE SAYS "COIN": the law speaks in the main table alone, inside the
message's ranges, at a sampled message, and off padInMain's places (hr, hj, ha, hp): that these
leave no coin is main_data_e itself.
THAT R CAN BE MET AT W's SENDING IS NOT SAID.
NOT IN FRONT OF A LAW OVER COINS.

Limits. word_is_data_behind's, all. THE FULL SIZE ALONE; the format's second hash function alone. It stands
over files of L25's that are on no seal. Nothing on any property.
word_is_data_head stands under the record K1Seated, whose field hasCoins is the equation between the
book's count and the part's: AT A BOOK THAT DOES NOT COVER THE PART's COUNT IT HOLDS OF NOTHING.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WordIsData
import Johnson.Desc.ProofFile.Honest.Thread.BookFitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open Johnson.Prover.Send (shapeAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {b : Nat} {blk : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
  {J : SendJob (PlaceIn ProofFile.Inst) X} {own₀ : X} {sort : K1Sort} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **AT lettersHead THE TWO PREMISES ON THE BOOK ARE PAID**, at any member whose yes leaves no
mark. THE TIE (R.msgs, R.pads) IS SPENT. UNDER "Stepped": IT HOLDS OF NOTHING AT A BOOK THAT DOES
NOT COVER THE PART's COUNT. The 0 where the data are silent is a default at a datum. The data: at
the text's own record, where nothing seen and no column is handed (.bare []); at what a move is
handed in a run: where the job's data reads neither (heardOnly). (That clause is the second security
reviewer's.) -/
theorem word_is_data_head
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) b blk wit J own₀
      sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hmark : ∀ s rs gs t, blk.decide s rs gs = .ok t → t.failed = none)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hA : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s')
    (n : ℕ) (hn : n < J.P.sent.size) (ds' : List Fmt.Drawn) (r₀ j : ℕ)
    (hr : r₀ < (shapeAt J.P n).mainRows)
    (hj : j < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (ha : (shapeAt J.P n).answers ≠ 0)
    (hp : (r₀, j) ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n))
    (h3 : ((shapeAt J.P n).mainDeg == 3) = true) :
    Sound.wordsFirst arr s'.st s'.book (Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
        (s.st.oracles.size + n) .main (r₀ + 2 ^ k1 (shapeAt J.P n) * j) =
      match J.data (wit m.st.input)
          { heard := m.st.heard, own := own₀, seen := .bare [] } n r₀ j with
      | some (.inr x) => x
      | some (.inl x) => algebraMap GF GE x
      | none => 0 := by
  have hblk : cF.blocksInOrder[b]? = some blk := R.member
  obtain ⟨-, gs, hdec⟩ := K1.step_ok _ blk s s' _ _ _ hS.2
  have h0 : s'.failed = none := hmark _ _ _ _ hdec
  exact word_is_data_behind R Said hA hd hS
    (head_bookFits_next h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hA.1 hd hS h0)
    (head_treeNumber_next h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hA.1 hd hS h0)
    n hn ds' r₀ j hr hj ha hp h3

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.word_is_data_head
