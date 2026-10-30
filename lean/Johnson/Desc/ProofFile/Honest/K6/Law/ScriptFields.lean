-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ScriptFields.lean: FOUR FIELDS OF `K6Script`
(Honest/K6/Law/OutAtThread.lean: left, keyTie, idn, keys) AT THE FIRST CHAIN's THREAD AS IT IS LAID
AT THE LIBRARY's HYPOTHESIS, BORDER 341: each from the law that ends in it, with the facts of
Honest/K6/Law/ScriptFront.lean laid in. The cut is `cutAtHead` (Honest/K6/Law/ShareAtHead.lean,
which is imported for that abbreviation and for `dofAtHead`, the data that it reads, alone): what
the head's law reads off the thread's witness.

WHAT IT IS NOT. NOTHING IS PROVED HERE BUT THAT THE PIECES FIT: each of the four is one call of
another file's law; two helpers state that law's letters at this family of threads. `K6Script` is
not met, AND IT IS NOT NAMED IN ANY STATEMENT HERE: that the four ends ARE its fields is held by
Lean only where they are laid into the structure: in another file; its fields cellsTie, maskTie and
guests are not spoken of. THE LOOKUP's POINTS STAY A PREMISE (hPts: what the seat reads as the
lookup's points is what the reader of the small input makes of the challenges heard): keyTie hangs
on it; idn, keys and left do not. It is shown of no run that the thread holds at any stand. THE FULL
SIZE ALONE, and at that family of threads alone; keys and idn at the mask's row 0 alone (so
`cutAtHead` has it). Nothing on any property.

What the file holds, and WHAT STAYS A PREMISE BESIDE THE HYPOTHESIS h. `k6_left_thr`: the field
left: nothing. `k6_keyTie_of_points`: the field keyTie: hb₀ (b₀ ≤ 341: the thread's rider on the
reply has begun); hq, hy (what the reader lays as its request and its token: `headWit'`,
Honest/K6/Wit.lean, meets both by unfolding); hPts. `k6_idn_thr`: the field idn: hq; hIn (the
script's cells are in range at valid inputs: whose it is to pay is not said here). `k6_keys_thr`:
the field keys: hIn. `k6_idnLetters_head`, `k6_keysLetters_head`: helpers: the structures of letters
that the two laws ask, at `lettersHead`: hIn. Said is a letter: nothing of it is spent.

Called. `keyTie_of_three` (Honest/K6/Law/KeyTieOfThree.lean); `idn_at_thread`
(Honest/K6/Law/IdnAtThread.lean); `keys_at_thread` (Honest/K6/Law/KeysAtThread.lean);
`keysLetters_at_head`, `idnLetters_at_head` (Honest/K6/Law/LettersAtHead.lean); `k6Fronted_at_head`
(Honest/K6/Law/FrontedAtHead.lean); `K6FrontItems.k6Left`
(Johnson/Desc/K6/Honest/Law/FrontItems.lean), `headLink_at` (Honest/K6/Law/FrontAt.lean);
`P5J.flat_ok` (Johnson/P5J/FoldJ1.lean); of ScriptFront.lean: `k6_front_thr`, `k6_keysFront`,
`k6_positions`, `k6_request_ask`, `k6_token_ask`.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ScriptFront
import Johnson.Desc.ProofFile.Honest.K6.Law.LettersAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.KeyTieOfThree
import Johnson.Desc.ProofFile.Honest.K6.Law.FrontedAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.ShareAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open VerifiableInference.Desc.Kinds (Head.Law.readsOf Head.Given)
open VerifiableInference.Desc.Kinds.Head (seatAt requestOf parOf given)
open VerifiableInference.Desc.Kinds.Head.Law (workOf K6Left KeysTrueInFront dataOf meanAt countAt)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (keys_at_thread idn_at_thread
  keysLetters_at_head idnLetters_at_head cutAtHead dofAtHead K6KeysLetters K6IdnLetters)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open scoped VerifiableInference.Desc.Kinds

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **THE FIELD left.** CONDITIONAL: the hypothesis h; the thread. -/
theorem k6_left_thr : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    K6Left (P5J.At.X Zp) s :=
  fun _ _ _ _ hT =>
    (k6_front_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1).2.1.k6Left (headLink_at h)

/-- **THE FIELD keyTie, FROM THE LOOKUP's POINTS ALONE**: the verifier's letters at the state are
the prover's. CONDITIONAL: the hypothesis h; the thread; hb₀; hq, hy: what the reader lays as its
request and its token; hPts: THE LOOKUP's POINTS: a premise. -/
theorem k6_keyTie_of_points (hb₀ : b₀ ≤ 341) (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk)
    (hq : ∀ v, (wit v).request = requestOf (ProofFile.startS Zp v.x.pub))
    (hy : ∀ v, (wit v).y = OnBytes.Desc.Reply.tokOf v.x.asked)
    (hPts : ∀ k s m E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
      (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).lookup s =
        some ((wit m.st.input).lookup m.st.heard)) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    given (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))
        (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))) s =
      .ok ((wit m.st.input).given (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) m.st.heard) := by
  intro k s m E hT
  obtain ⟨blk, p8, h8, -, -, -, Hf⟩ :=
    k6Fronted_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
  exact keyTie_of_three (P5J.At.X Zp) (Hf.front k s m E hT) (wit m.st.input) m.st.heard
    (k6_request_ask h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said wit hq k s m E hT)
    (k6_token_ask h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb₀ wit hy k s m E hT)
    (hPts k s m E hT)

/-- The letters that `idn_at_thread` asks, at this family of threads: `idnLetters_at_head`, with
`lettersHead` unfolded to `lettersAt` at its named letters. CONDITIONAL: the hypothesis h; hIn. -/
theorem k6_idnLetters_head
    (hIn : ∀ v, (v = w ∧ Vd v) → VerifiableInference.OnPublicFiles.Flat.InRange (Q.cells v)) :
    K6IdnLetters (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341
      (Item.constr 24 .idn) id id (dofAtHead h Q carryX) mgBase (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.num Zp 24 0) 0 := by
  delta lettersHead
  exact idnLetters_at_head h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hIn

/-- The letters that `keys_at_thread` asks, at this family of threads: `keysLetters_at_head`,
likewise. CONDITIONAL: the hypothesis h; hIn. -/
theorem k6_keysLetters_head
    (hIn : ∀ v, (v = w ∧ Vd v) → VerifiableInference.OnPublicFiles.Flat.InRange (Q.cells v)) :
    K6KeysLetters (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341
      (Item.worth 24 3 "keys") id id (dofAtHead h Q carryX) mgBase (P5J.At.layout Zp)
      (P5J.At.num Zp) (P5J.At.num Zp 24 0) x := by
  delta lettersHead
  exact keysLetters_at_head h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hIn

/-- **THE FIELD idn**: at the cells read off the witness: the row's identities, the mean's and the
count's forms. NOTHING OF THE LOOKUP's POINTS, OF THE TOKEN OR OF b₀ IS SPENT. CONDITIONAL: the
hypothesis h; the thread; hq: what the reader of the small input lays as its request; hIn. -/
theorem k6_idn_thr (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk)
    (hq : ∀ v, (wit v).request = requestOf (ProofFile.startS Zp v.x.pub))
    (hIn : ∀ v, (v = w ∧ Vd v) → VerifiableInference.OnPublicFiles.Flat.InRange (Q.cells v)) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E → ∀ ds,
    (letI : Head.Given :=
      (wit m.st.input).given (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) m.st.heard
     (dataOf (cutAtHead h Q carryX m.st.input
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (m.st.heard ++ ds))).1).Holds ∧
      meanAt (cutAtHead h Q carryX m.st.input
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (m.st.heard ++ ds))).1.toCells = 0 ∧
      countAt (cutAtHead h Q carryX m.st.input
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (m.st.heard ++ ds))).1.toCells = 0) := by
  have L := k6_idnLetters_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hIn
  have A := idn_at_thread wit L (k6_positions h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said)
    (k6_request_ask h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said wit hq)
  exact A

/-- **THE FIELD keys**: the keys' sentence in front of the member, at the cells and the mask's row
read off the witness, at every continuation. CONDITIONAL: the hypothesis h; the thread; hIn. -/
theorem k6_keys_thr
    (hIn : ∀ v, (v = w ∧ Vd v) → VerifiableInference.OnPublicFiles.Flat.InRange (Q.cells v)) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E → ∀ ds,
    KeysTrueInFront (P5J.At.X Zp) s
      (cutAtHead h Q carryX m.st.input
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (m.st.heard ++ ds))).1
      (cutAtHead h Q carryX m.st.input
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (m.st.heard ++ ds))).2 := by
  obtain ⟨blk, p8, h8, e, -, -, Hf⟩ :=
    k6Fronted_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
  have L := k6_keysLetters_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hIn
  have A := keys_at_thread L (k6_keysFront h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said) Hf
    (P5J.flat_ok h.toAtMg blk (List.mem_of_getElem? e))
  exact A

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_left_thr
#print axioms ProofFile.Honest.K6.k6_keyTie_of_points
#print axioms ProofFile.Honest.K6.k6_idnLetters_head
#print axioms ProofFile.Honest.K6.k6_keysLetters_head
#print axioms ProofFile.Honest.K6.k6_idn_thr
#print axioms ProofFile.Honest.K6.k6_keys_thr
