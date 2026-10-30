-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/LastHead.lean: THE SECOND CHAIN's LETTERS AT THE LIBRARY's
DESCRIPTION, WITH WHAT HAS A TEXT LAID IN, AS A FAMILY IN THE RUN's INPUT: the sister of
`lettersHead` (Honest/Thread/FirstHead.lean) and `lettersShared` (SharedHead.lean). Of the
twenty-three fields of `LastThread.Letters` (Honest/Thread/Last.lean) ten get their text or their
form: the label of the chain's first own tree, the flat list and the first state are the
description's own (`P5J.F0T`: `lastChainFirstTreeNumber`, `second.blocksInOrder`, `start₃`); the halves and the stored
table's columns are a prover's own; the rounds ahead and how many of them are the first chain's are
the two earlier chains' declared rounds, in the terms in which `doorBehind_of`
(Honest/Thread/Door.lean) asks them; `valid` is "the input is this run's" and a letter; `rides` is a
letter; `keeps` goes BY THE MEMBER's PLACE (`lastPlaces`). What is handed to the chain has the type
(the public part, the first chain's last state, the shared chain's last state). THE TABLE's NUMBERS,
THE THREE MEANINGS, `order`, THE TREES TAKEN OVER, `ends` (the two earlier chains' last states as
functions of coins, input and challenges: NO COMPUTED TERM FOR IT LIES ANYWHERE; `endsBy`,
Honest/Thread/OneState.lean, gives the two states by choice), THE WITNESS, THE TABLES AND THE COUNTS
STAY LETTERS. One definition: a term; equations by unfolding; and `Sits` with all five premises on
the later chains' letters gone.

  `lettersLast`   THE TERM
  `last_ft`, `last_bs`, `last_hs`, `last_ahead`, `last_near`, `last_stored`, `last_valid`,
  `last_keeps`, `last_begun`   what each letter is there: by unfolding
  `sits_at_all`   `Sits` at the three terms: the three tests `fits` alone are left, beside the
  hypothesis `AtMgA`

Limits. Nothing shows that the thread can hold at any run. No author has laid or asked anything at
these letters yet. None is one of the library's goals. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.LastThread
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Last (MeaningL PromMeaningL lastPlaces)
open P5J (TS F0T)

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Local W₀ Rc ProofFile.Inst Tr → MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : MeaningL VerifiableInference.Desc.Third.S₃ Wt)
  (PL : PromMeaningL Desc.K14.St VerifiableInference.Desc.Third.S₃ (ProofFile.InstPub × TS))
  (order : VerifiableInference.Desc.Third.S₃ → Prop) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
  (fixed : Fmt.TreeSource → Nat) (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → VerifiableInference.Desc.Third.S₃ → Prop)
  (Kp : Place → VerifiableInference.Desc.Third.S₃ → VerifiableInference.Desc.Third.S₃ → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE SECOND CHAIN's LETTERS AT THE LIBRARY's DESCRIPTION.** w: the run's own input. Vd, Rd, Kp:
what is still to be laid of `valid`, `rides`, `keeps`. -/
noncomputable def lettersLast :
    Letters Bk Desc.K14.St VerifiableInference.Desc.Third.S₃ ProofFile.Cl W₀ Rc ProofFile.Inst Tr X
      (ProofFile.InstPub × TS) Wt :=
  { N := N, Mg := Mg, ML := ML, PL := PL, order := order
    ft := (F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber
    bs := (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder
    hs := H.second
    ahead := declsTo (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length ++
      declsTo (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
        (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length
    near := (declsTo (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length).length
    taken := taken, ends := ends
    first := fun a s₀ => (F0T OnBytes.secondHashFunction Zp Np cF).start₃ a.1.1 a.1.2 a.2 = .ok s₀
    wit := wit, table := table, fixed := fixed
    stored := fun v => H.storedWords v.w₀ v.rc
    item := item, n₁ := n₁, n₂ := n₂
    valid := fun v => v = w ∧ Vd v
    rides := Rd
    keeps := fun b s s' => ∀ p, lastPlaces[b]? = some p → Kp p s s' }

theorem last_ft :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).ft =
      (F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber := rfl

theorem last_bs :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).bs =
      (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder := rfl

theorem last_hs :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).hs =
      H.second := rfl

theorem last_ahead :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.ahead =
      declsTo (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
          (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length ++
        declsTo (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
          (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length := rfl

theorem last_near :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.near =
      (declsTo (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length).length := rfl

theorem last_stored (v : Local W₀ Rc ProofFile.Inst Tr) :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.stored v = H.storedWords v.w₀ v.rc := rfl

theorem last_valid (v : Local W₀ Rc ProofFile.Inst Tr) :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.valid v ↔ v = w ∧ Vd v := Iff.rfl

theorem last_keeps (b : Nat) (s s' : VerifiableInference.Desc.Third.S₃) :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.keeps b s s' ↔ ∀ p, lastPlaces[b]? = some p → Kp p s s' := Iff.rfl

/-- **THE CHAIN BEGINS WHERE THE DESCRIPTION's OWN start₃ SAYS YES**, at what is handed to it. -/
theorem last_begun (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn)
    (s₀ : VerifiableInference.Desc.Third.S₃) :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.begun k v hd s₀ ↔
      (F0T OnBytes.secondHashFunction Zp Np cF).start₃ (ends k v hd).1.1 (ends k v hd).1.2 (ends k v hd).2 =
        .ok s₀ := Iff.rfl

end ProofFile.Honest.LastThread

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Last (MeaningL PromMeaningL)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`Sits` WITH ALL THREE CHAINS' LETTERS LAID**: the three tests `fits` alone are left, beside
the hypothesis `AtMgA`. L₂, L₃: the two later chains' letters at the terms of SharedHead.lean and of
this file, at whatever is still a letter there. -/
theorem sits_at_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X₀ X Wt₂ Wt₃ : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (L₂ : SharedThread.Letters Bk Desc.K14.St ProofFile.Cl W₀ Rc OnBytes.TableKey X₀
      (ProofFile.InstPub × TS) Wt₂)
    (L₃ : LastThread.Letters Bk Desc.K14.St VerifiableInference.Desc.Third.S₃ ProofFile.Cl W₀ Rc ProofFile.Inst
      Tr X (ProofFile.InstPub × TS) Wt₃)
    (e₂ : ∃ N Mg shape nothingLeft order wit table fixed m₁ m₂ Vd₂ Rd₂ Kp₂ w₂, L₂ =
      SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed m₁ m₂ Vd₂
        Rd₂ Kp₂ w₂)
    (e₃ : ∃ N Mg ML PL order taken ends wit table fixed it m₁ m₂ Vd₃ Rd₃ Kp₃ w₃, L₃ =
      LastThread.lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed it m₁ m₂ Vd₃ Rd₃
        Kp₃ w₃)
    (f₁ : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fits
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (f₂ : L₂.thread.fits (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length = true)
    (f₃ : L₃.thread.fits (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.length = true) :
    Sits (F0T OnBytes.secondHashFunction Zp Np cF) H
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread L₂.thread L₃.thread := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := e₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := e₃
  exact sits_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _ rfl rfl rfl rfl rfl f₁ f₂ f₃

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.LastThread.last_ft
#print axioms ProofFile.Honest.LastThread.last_bs
#print axioms ProofFile.Honest.LastThread.last_hs
#print axioms ProofFile.Honest.LastThread.last_ahead
#print axioms ProofFile.Honest.LastThread.last_near
#print axioms ProofFile.Honest.LastThread.last_stored
#print axioms ProofFile.Honest.LastThread.last_valid
#print axioms ProofFile.Honest.LastThread.last_keeps
#print axioms ProofFile.Honest.LastThread.last_begun
#print axioms ProofFile.Honest.FirstThread.sits_at_all
