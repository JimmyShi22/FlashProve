-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ShareAtHead.lean.
WHAT IT IS NOT. NOT ExchangeS AT BORDER 341: THAT ROW OWES SEVEN ITEMS (exchangeS_iff,
Honest/Thread/SharesS.lean; rowAt, Honest/Thread/FirstRows.lean; the library's segRow,
Johnson/Desc/First/Borders.lean): THREE ARE HERE. formsT 24 3 "planes" is not: the relation K6Out
does not read the planes. pin 24 0, pinW and constr 24 small are read and left by the row: their
shares are in Honest/K6/Law/RidesPast.lean: two by exchangeAtS_again (Honest/Thread/SharesS.lean),
pinW's by exchangeAt_pinW (Honest/Thread/HeadPinW.lean); Honest/K6/Law/ExchangeAtHead.lean gathers
the seven. A JOIN: NO NEW MATHEMATICS. CONDITIONAL ON THE LIBRARY's HYPOTHESIS P5J.AtMgA AND ON
THREE NAMED PREMISES, EACH SHOWN HERE OF NOTHING: K6HalfAt (on the prover's halves), K6Script
(seven sentences that tie the prover's cells, coins and letters to what the law reads off the
thread's witness: ALL THE CONTENT ON VALUES LIES THERE) and K6FormsBehind (the table's test on the
forms at the head's four runs, at the state behind the step); in the last of the five statements a
premise on the letter Kp stands in the third's stead. (Of the hypothesis the library
has a member under four premises on the three public files: P5J.head_exists_at_name,
Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) That the thread holds at any run is
shown nowhere. ExchangeAtS is a definition (Honest/Thread/SharesS.lean): a premise's form: none of
the library's goals. That the verifier accepts is that debt's own premise: nothing here shows it.
The full size, the format's second hash function, border 341 and segment 24 alone. Nothing on soundness, on
completeness or on what a proof hides.
WHAT IT IS. THE SUB-PROTOCOL "the output head's own rounds": ITS SHARE OF THE DEBT ExchangeS
(Honest/Thread/PaysS.lean; at one item: ExchangeAtS) AT THREE ITEMS OF THE TABLE OF JOINTS,
formsT 24 4 "own", "join" and "weights", AT THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS
(lettersHead, Honest/Thread/FirstHead.lean), at every letter Said.
  dofAtHead            the composed meaning's data at the thread's input: the hypothesis' own, with
                       the decoder and the carried word's sentence turned, as lettersAt lays them
  cutAtHead            what the head's law reads off the thread's witness at these data: compCut
                       (Johnson/Desc/Kinds/Law/K6Cut.lean) at the mask row's message num 24 0, whose
                       mask rows are numbered by 0 bits
  K6FormsBehind        the third premise's form; general in the thread and the data
  k6_letters_head      the structure K6ShareLetters (Honest/K6/Law/Share.lean) at these letters
  k6_out_head          the field out of K6ShareDebts at these letters
  k6_debts_head        the structure K6ShareDebts at these letters
  k6_exchange_at_head  THE TOP
  k6_exchange_at_head_keeps   the same with the third premise paid, where the letter Kp takes the
                       sub-protocol's own clause of what its step keeps
WHO PAYS WHAT. The shell: k6_share (Honest/K6/Law/Share.lean). K6ShareLetters: k6_letters_full
(Honest/K6/Law/LettersFull.lean) at lettersAt's letters; lettersHead is lettersAt at named letters,
by unfolding. due: due_at_head (Honest/K6/Law/DueAtHead.lean). pubTest: the premise K6FormsBehind;
in the last theorem k6_forms_behindS (Honest/K6/Law/FormsBehind.lean). out: k6_out_at_thread
(Honest/K6/Law/OutAtThread.lean) from K6Seated and K6Fronted at these letters (k6Seated_at_head,
k6Fronted_at_head: Honest/K6/Law/SeatedAtHead.lean, FrontedAtHead.lean), the premise K6Script, and
the member's test on the plan (flat_ok, Johnson/P5J/FoldJ1.lean). That the first chain has a link
24: link24_at_head (Johnson/Desc/Kinds/Law/K6StateAtHead.lean).
OF THE FOLDER Johnson/Goal/ it names Meaning.sizesOf, as an argument of the library's compCut;
nothing else of that folder is called, and no module of it is imported by name.
Over files that have not yet landed in the library: the seven named above and what they import.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.LettersFull
import Johnson.Desc.ProofFile.Honest.K6.Law.DueAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.OutAtThread
import Johnson.Desc.ProofFile.Honest.K6.Law.SeatedAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.FormsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain Claim Link Place Strs)
open VerifiableInference.Desc.First (Item S)
open VerifiableInference.Desc.Sound (MgData MsgT mgBase)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open ProofFile.Honest (Thread ThrS ExchangeAtS ProverCoinCounts Coins Local Mid Prover drawsFit)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (HeadAsk K6Seated K6Fronted K6Script K6HalfAt k6Seated_at_head k6Fronted_at_head
  due_at_head k6_out_at_thread k6_forms_behindS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The composed meaning's data at the thread's input w: the hypothesis' own, with the decoder and
the carried word's sentence turned, as the first chain's letters lay them
(Honest/Thread/FirstAt.lean: the field Mg of lettersAt). -/
abbrev dofAtHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) :=
  { h.𝔇 with decT := fun _ _ => some (Q.cells w), cr1 := carryX }

/-- What the head's law reads off the thread's witness, at these data and the library's own public
numbers. -/
abbrev cutAtHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (v : WtF) : Pinned :=
  compCut (dofAtHead h Q carryX w).cs (dofAtHead h Q carryX w).arr (dofAtHead h Q carryX w).ms
    (dofAtHead h Q carryX w).N (Meaning.sizesOf (At.X Zp))
    (seatLay (At.X Zp) (At.layout Zp) (At.num Zp)) (At.X Zp) (plAt (At.num Zp 24 0) 0) v

/-- **THE TABLE's TEST ON THE FORMS, BEHIND THE MEMBER's STEP**: it accepts at each of the head's
four runs, at the state behind the step of member number b, at lists of challenges that fit: the
promise's own content at the next border. General in the thread and in the composed meaning's data.
A definition: a premise's form. Nothing is claimed of it. -/
def K6FormsBehind {Bk : ProverCoinCounts} {V W X Pb Xi P Tok : Type} {rows cols nR : ℕ}
    {Wp : OnBytes.Model.Verify.Public} (T : Thread Bk S Claim V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat)
    (Dt : MgData Xi P Tok rows cols nR Wp) : Prop :=
  ∀ blk k s m E ds y cl s', T.bs[b]? = some blk → ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cl s' → ∀ name, K6Name name →
      K9.formsInT (Dt.Rd 24) (Dt.N.sent 24 0) 3 name s' = true

/-- **WHAT THE SHELL ASKS OF THE THREAD's LETTERS, AT THE LIBRARY's OWN**, at every Lk that is the
first chain's link 24. CONDITIONAL on the one hypothesis. -/
theorem k6_letters_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Lk : Link S ProofFile.Cl) (hlk : cF.links[24]? = some Lk) :
    K6ShareLetters (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (Item.formsT 24 4 "own") (Item.formsT 24 4 "join") (Item.formsT 24 4 "weights") id id
      (dofAtHead h Q carryX) mgBase (At.layout Zp) (At.num Zp) (At.num Zp 24 0) 0 24 4
      (K9.statesOfLink Lk) := by
  delta lettersHead
  exact k6_letters_full h H.first Q _ _ test carryX item n₁ n₂ _ _ _ Lk hlk

/-- **THE ELDER RELATION K6Out BEHIND THE MEMBER's STEP, AT WHAT THE LAW READS OFF THE THREAD's
WITNESS, AT EVERY CONTINUATION.** CONDITIONAL on the hypothesis and on two named premises: on the
prover's halves; on what ties the prover's cells, coins and letters to what the law reads. -/
theorem k6_out_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX)) :
    ∀ blk k s m E ds y cl s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cl s' →
      ∀ ds', K6Out (At.X Zp) s' (cutAtHead h Q carryX m.st.input
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (y.2.st.heard ++ ds'))) := by
  obtain ⟨blk, e, Hs⟩ := k6Seated_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w wit hH
  obtain ⟨blk', _, _, e', _, _, Hf⟩ :=
    k6Fronted_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
  obtain rfl : blk = blk' := Option.some.inj (e.symm.trans e')
  have hpl : blk.planOk = true := P5J.flat_ok h.toAtMg blk (List.mem_of_getElem? e)
  intro blk₂ k s m E ds y cl s' hb hT hd hS ds'
  obtain rfl : blk = blk₂ := Option.some.inj (Hs.member.symm.trans hb)
  exact k6_out_at_thread Hs Hf Hc hpl k s m E ds y cl s' hT hd hS ds'

/-- **THE SHELL's THREE DEBTS, AT THE LIBRARY's OWN LETTERS**, at every Lk that is the first chain's
link 24. CONDITIONAL on the hypothesis and on the three named premises. -/
theorem k6_debts_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX))
    (Hp : K6FormsBehind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      h.𝔇)
    (Lk : Link S ProofFile.Cl) (hlk : cF.links[24]? = some Lk) :
    K6ShareDebts (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 id
      (dofAtHead h Q carryX) (At.layout Zp) (At.num Zp) (At.num Zp 24 0) 0 (p8K6 (At.X Zp) 24)
      (K9.statesOfLink Lk) :=
  { due := due_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Lk hlk
    pubTest := Hp
    out := k6_out_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w wit hH Said Hc }

/-- **THE SHARE OF ExchangeS AT THE HEAD's THREE ITEMS, AT THE LIBRARY's OWN LETTERS**, at every
letter Said. CONDITIONAL on the hypothesis that ties the table's letters to the IOP as written in
Lean, and on three named premises: on the prover's halves; on what ties the prover's cells, coins
and letters to what the law reads off the witness; on the table's test on the forms behind.
Three of the seven items that the row at border 341 owes. -/
theorem k6_exchange_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX))
    (Hp : K6FormsBehind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      h.𝔇) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "own") ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "join") ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "weights") := by
  obtain ⟨Lk, hlk⟩ := P4.link24_at_head h
  exact k6_share (k6_letters_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lk hlk)
    (k6_debts_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w wit hH Said Hc Hp Lk hlk)

/-- **THE SAME WITH THE THIRD PREMISE PAID**: where the letter Kp, at the sub-protocol's place,
takes the sub-protocol's own clause of what its step keeps (K6Keeps,
Johnson/Desc/K6/Honest/Law/Keeps.lean). CONDITIONAL on the hypothesis, on that and on the two other
named premises. -/
theorem k6_exchange_at_head_keeps (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hKp : ∀ s s', K6Keeps s s' → Kp plK6 s s')
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "own") ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "join") ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "weights") :=
  k6_exchange_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w wit hH Said Hc
    (k6_forms_behindS h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hKp Said)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_letters_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_out_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_debts_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchange_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchange_at_head_keeps
