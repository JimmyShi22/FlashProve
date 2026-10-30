-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJoint.lean: the joint between the last chain's first
block ("K14, second part", `batchLinearConstraintsSecondPart`) and that chain's proximity test, number 2 of the chain: TWO
THINGS THAT A STAND IN FRONT OF THE TEST GIVES. One definition; statements with their proofs.

  1 THE BLOCK's YES. `Thread.Made` (Honest/Thread/Thr.lean) holds the verifier's fold over the
    blocks in front of a border. At the library's description the last chain's first two blocks are
    `batchLinearConstraintsSecondPart` at the seat's parameters and a block without a round that leaves the state. So at
    the borders 1 and 2 of the last chain's thread at that description (`lettersLast`,
    Honest/Thread/LastHead.lean): there is a first state s₀ at which the chain began, and rounds and
    columns at which `batchLinearConstraintsSecondPart`'s decision returned the stand's own state: `made_one_yes`,
    `made_two_yes`; from the thread: `thr_two_yes`. General in every parameter of `lettersLast`.
    `p14N_is_p14At`: the two names under which the library has these parameters are one term.
  2 THE ITEM "rows". The library's sentence for that item (`LLT25.rowsOpen`,
    Johnson/LLT25R/LastRowsOpen.lean) says: the seat's way in returns, and every open row of the own
    group says of the words that the witness's tables give, read at the seats that the state's own
    book gives. `wordsAtOwn`: these words, as a term: THEY ARE A FUNCTION OF THE STATE AND THE
    WITNESS, not of the witness alone; where the codes are the statement's own they are the
    library's `wordsLast` (`wordsAtOwn_is_wordsLast`). `rows_of_rowsOpen`: the sentence gives "all
    rows of the own group say" of these words. `rows_at_two`: at a last chain's thread whose item
    "rows" is that sentence: from the thread at the border 2, at every continuation of the
    challenges.

For whom. The test's acceptance asks of a stand what the rows taken in say of some words m, in five
clauses on one m: the statement is in order; no open row is a sample row; the rows say of m; the
members' sample rows say of m; on the members' tables m is what the job's plain rows make. Where the
thread's item is the library's sentence, the third clause is had at m := `wordsAtOwn` …, so the
fourth and the fifth are to be shown at these same words.

Limits. Statements from a stand: where the thread stands nowhere they speak of nothing. Nothing says
that the block's yes is reached by a run: it is read off a fold that is a premise. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.LastHead
import Johnson.LLT25R.LastRowsOpen
import Johnson.Desc.Sound.WordsAt
import Johnson.ToldDescR.LastBlocks
import Johnson.Desc.K15.FoldInv
import Johnson.Desc.Third.Law.Keeps
import Johnson.Loose.H2K12.LaterSeatsN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open ProofFile.Honest
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllSay OpenSays wordsOn rowAt_iff)
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks Wit)
open VerifiableInference.Desc.Sound (MsgT tabAt)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart takenSources)
open VerifiableInference.Desc.Third.Law (takenSources_same)
open VerifiableInference.Desc.Last (ItemL MeaningL)
open ProofFile.Honest.LastThread (Letters lettersLast)
open ToldDesc (p14At ownAt)
open P5J (F0T TS)

/-! ## 1 The block's yes -/

/-- The two names of the last chain's public parameters are one term. -/
theorem p14N_is_p14At (Z : ProofFile.Pub) : H2K.JointK.p₁₄N Z = p14At Z := rfl

section
variable {S Cl : Type}

/-- One block's yes off a fold over it. -/
theorem fold_one_yes (ft : ℕ) (a : Block S Cl) (s₀ s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : foldBlocks ft [a] s₀ rs cols = .ok (s, [], [])) :
    ∃ r₁ g₁, a.decide s₀ r₁ g₁ = .ok s := by
  obtain ⟨s₁, k, -, h1, h⟩ := VerifiableInference.Desc.foldBlocks_cons ft a [] s₀ rs cols _ h
  have e : s₁ = s := congrArg (·.1) (Except.ok.inj h)
  subst e
  exact ⟨_, _, (VerifiableInference.Desc.step_inv _ _ _ _ _ _ _ h1).2.2.2⟩

/-- Two blocks behind one another: each one's yes. -/
theorem fold_two_yes (ft : ℕ) (a b : Block S Cl) (s₀ s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : foldBlocks ft [a, b] s₀ rs cols = .ok (s, [], [])) :
    ∃ s₁ r₁ g₁ r₂ g₂, a.decide s₀ r₁ g₁ = .ok s₁ ∧ b.decide s₁ r₂ g₂ = .ok s := by
  obtain ⟨s₁, k, -, h1, h⟩ := VerifiableInference.Desc.foldBlocks_cons ft a [b] s₀ rs cols _ h
  obtain ⟨r₂, g₂, h2⟩ := fold_one_yes ft b s₁ s _ _ h
  exact ⟨s₁, _, _, r₂, g₂, (VerifiableInference.Desc.step_inv _ _ _ _ _ _ _ h1).2.2.2, h2⟩

end

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- The description's last chain begins with these two blocks. -/
theorem second_take_two : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.take 2 =
    [((batchLinearConstraintsSecondPart (p14At Zp) : Block S₃ Unit).retype : Block S₃ ProofFile.Cl),
      ((takenSources (ownAt Np) : Block S₃ Unit).retype : Block S₃ ProofFile.Cl)] := by
  have e : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder =
      [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np,
        VerifiableInference.Desc.Third.end₃
          [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np]].map Block.retype :=
    ToldDesc.last_blocks_in OnBytes.secondHashFunction ProofFile.pureRoad.links Zp _ Np cF
  rw [e]
  rfl

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X Wt : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Local W₀ Rc ProofFile.Inst Tr →
    VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
  (order : S₃ → Prop) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  (fixed : Fmt.TreeSource → ℕ) (item n₁ n₂ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : ℕ → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop)
  (Kp : VerifiableInference.Desc.Place → S₃ → S₃ → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **BEHIND THE FIRST BLOCK: THE CHAIN's FIRST STATE AND THE BLOCK's YES**, off `Thread.Made` at
the border 1. -/
theorem made_one_yes {k : Coins Bk} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hM : (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
      item n₁ n₂ Vd Rd Kp w).thread.Made 1 k st m E) :
    ∃ s₀ rs gs, (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
      item n₁ n₂ Vd Rd Kp w).thread.begun k m.st.input
        (m.st.heard.take (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
          item n₁ n₂ Vd Rd Kp w).thread.front) s₀ ∧
      (batchLinearConstraintsSecondPart (Cl := Unit) (p14At Zp)).decide s₀ rs gs = .ok st := by
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hM
  have e : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.take 1 =
      [((batchLinearConstraintsSecondPart (p14At Zp) : Block S₃ Unit).retype : Block S₃ ProofFile.Cl)] := by
    have q := congrArg (List.take 1) (second_take_two Zp Np cF)
    rw [List.take_take] at q
    exact q
  have hf' := hf
  change foldBlocks (F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber
    ((F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.take 1) s₀ _ cols = .ok (st, [], []) at hf'
  rw [e] at hf'
  obtain ⟨r₁, g₁, h1⟩ := fold_one_yes _ _ _ _ _ _ hf'
  exact ⟨s₀, r₁, g₁, hbeg, h1⟩

/-- **IN FRONT OF THE TEST: THE CHAIN's FIRST STATE AND THE BLOCK's YES**, off `Thread.Made` at the
border 2: the block without a round between leaves the state. -/
theorem made_two_yes {k : Coins Bk} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hM : (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
      item n₁ n₂ Vd Rd Kp w).thread.Made 2 k st m E) :
    ∃ s₀ rs gs, (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
      item n₁ n₂ Vd Rd Kp w).thread.begun k m.st.input
        (m.st.heard.take (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
          item n₁ n₂ Vd Rd Kp w).thread.front) s₀ ∧
      (batchLinearConstraintsSecondPart (Cl := Unit) (p14At Zp)).decide s₀ rs gs = .ok st := by
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hM
  have hf' := hf
  change foldBlocks (F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber
    ((F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.take 2) s₀ _ cols = .ok (st, [], []) at hf'
  rw [second_take_two Zp Np cF] at hf'
  obtain ⟨s₁, r₁, g₁, r₂, g₂, h1, h2⟩ := fold_two_yes _ _ _ _ _ _ _ hf'
  have h2' : (takenSources (ownAt Np) : Block S₃ Unit).decide s₁ r₂ g₂ = .ok st := h2
  obtain rfl : st = s₁ := takenSources_same _ _ _ _ _ h2'
  exact ⟨s₀, r₁, g₁, hbeg, h1⟩

/-- The same from the thread at the border 2. -/
theorem thr_two_yes {k : Coins Bk} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
      item n₁ n₂ Vd Rd Kp w).thread 2 k st m E) :
    ∃ s₀ rs gs, (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
      item n₁ n₂ Vd Rd Kp w).thread.begun k m.st.input
        (m.st.heard.take (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
          item n₁ n₂ Vd Rd Kp w).thread.front) s₀ ∧
      (batchLinearConstraintsSecondPart (Cl := Unit) (p14At Zp)).decide s₀ rs gs = .ok st :=
  made_two_yes Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w
    u.2.2.2.2.1

end

/-! ## 2 The item "rows" -/

section
variable {Cells Tok : Type}

/-- **The words of which the library's sentence for the item "rows" speaks**: what the witness's
tables give, read at the seats that the state's own book gives. -/
noncomputable def wordsAtOwn (codes : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (s : S₃)
    (v : Wit Cells Tok MsgT) : OnBytes.Means.Words GE :=
  wordsOn s.st (tabAt codes arr
    (VerifiableInference.Desc.Sound.seatBy
      (VerifiableInference.Desc.Sound.noLast t₁ t₂ s.loc.firstTree) s.book) s.st v)

/-- Where the codes are the statement's own, these are the library's words of the last chain
(`wordsLast`, Johnson/Desc/Sound/WordsAt.lean). -/
theorem wordsAtOwn_is_wordsLast (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (s : S₃) (v : Wit Cells Tok MsgT) :
    wordsAtOwn s.st.codes arr t₁ t₂ s v =
      VerifiableInference.Desc.Sound.wordsLast arr t₁ t₂ s v := rfl

/-- **The library's sentence gives: all rows of the own group say of these words.** -/
theorem rows_of_rowsOpen (codes : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (s : S₃)
    (v : Wit Cells Tok MsgT) (h : LLT25.rowsOpen codes arr t₁ t₂ s v) :
    ∀ G, s.st.groups[s.loc.own]? = some G →
      AllSay rdE s.st G.rows.toList (wordsAtOwn codes arr t₁ t₂ s v) := by
  obtain ⟨t, ht, hs⟩ := h
  obtain rfl := Except.ok.inj ht
  intro G hG r hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
  rw [Array.getElem?_toList] at hi
  exact hs i r (rowAt_iff.2 ⟨G, hG, hi⟩)

variable {Bk : ProverCoinCounts} {S₂ Cl W₀ Rc Xi Tr X P₁ : Type}
  (L : Letters Bk S₂ S₃ Cl W₀ Rc Xi Tr X P₁ (Wit Cells Tok MsgT))

/-- **IN FRONT OF THE TEST ALL ROWS OF THE OWN GROUP SAY OF THESE WORDS**, at the thread's witness,
at every continuation of the challenges: at a last chain's thread whose item "rows" is the library's
sentence. -/
theorem rows_at_two (codes : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ)
    (hML : L.ML = ⟨LLT25.rowsOpen codes arr t₁ t₂⟩) {k : Coins Bk} {s : S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (u : Thr L.thread 2 k s m E) (ds : List Fmt.Drawn) :
    ∀ G, s.st.groups[s.loc.own]? = some G →
      AllSay rdE s.st G.rows.toList
        (wordsAtOwn codes arr t₁ t₂ s (L.wit k m.st.input (m.st.heard ++ ds))) := by
  have hm : ItemL.rows ∈ L.thread.opened 2 := by
    show ItemL.rows ∈ fwdOpen VerifiableInference.Desc.Last.startLast LastRows.rows 2
    decide
  have e := u.2.2.2.1 ds ItemL.rows hm
  change L.ML.rows s (L.wit k m.st.input (m.st.heard ++ ds)) at e
  rw [hML] at e
  exact rows_of_rowsOpen codes arr t₁ t₂ s _ e

end

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.p14N_is_p14At
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.fold_one_yes
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.fold_two_yes
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.second_take_two
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.made_one_yes
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.made_two_yes
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.thr_two_yes
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.wordsAtOwn_is_wordsLast
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.rows_of_rowsOpen
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.rows_at_two
