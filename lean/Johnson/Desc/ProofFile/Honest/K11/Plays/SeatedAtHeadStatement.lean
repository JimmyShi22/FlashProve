-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SeatedAtHeadStatement.lean: THE STRUCTURE `K11SeatedS`
(ShareSStatement.lean of this folder), WHOLE, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD; AND
SO, BY THE KIND's LAW ON ITS EXCHANGE, THE FRAME's `ExchangeAtS` AT NUMBER 346 AT THE TWO ITEMS THAT
THE MERGE's MEMBER OPENS: STATEMENTS ALONE: two definitions of propositions. NOTHING IS PROVED IN
THIS FILE, and neither is one of the library's goals: they are lemmas' statements.

WHAT STAYS A PREMISE OF BOTH, FIRST. The head · the maker's base Bs · b₀ ≤ 346 (a premise on a
letter: from that border on the thread's rider says that the state's reply is the one that the
instance asks about) · THE PROVER's HALF: the search by `IM.k11Place` in the prover's first chain
finds the kind's half, at the written text for claims · FOUR FACTS ON THE SCRIPT: `K11ScriptMsg`
(two, on its messages) and `K11CellsQ` (two, on its cells) (TiesAtHeadStatement.lean of this
folder): NO SCRIPT IS LAID ANYWHERE, AND NO PROVER: whoever lays them pays these.

  `K11SeatedAtHead` these premises: there are a name and a link with `K11SeatedS` at: SaidOk · 346 ·
                    the kind's numbers at Bs · claims := `headClaimsAt cF Zp Bs.G₀` · pl :=
                    `IM.k11Place` · coins := `headMergeCoins` at these · the items .forms 24 9
                    "merged" and .wo 24 · toP := id · toW := id · Dof := `dataAtHead` · `mgBase` ·
                    segment 24
  `ExchangeAtHead`    these premises: `ExchangeAtS` at 346 at each of the two items

Limits. AN ASSEMBLY: EVERY FIELD IS A LEMMA THAT LIES ALREADY: NOTHING NEW IS SHOWN BESIDE THEM, AND
IT HAS ALL THEIR LIMITS: among them: the last clause of the field front is no better than the
lookups' authors' file, which they call a reading copy; the claim's truth, in the field ties, is
taken out of the thread's own sentence on its open items, by another team's lemma at the reference
sizes alone; c₀ is a letter, read only where the book lends the kind's row nothing. THE FRAME's DEBT
AT 346 ASKS FIVE ITEMS (that the owed items are these five is the frame's authors' evaluation: no
theorem): THE TWO THAT THE MEMBER OPENS ARE TREATED HERE; the three that it reads and leaves open
are not: SO THAT DEBT IS NOT PAID BY THIS. THAT THE PAIR `ThrS` HOLDS AT ANY STAND IS NOT SAID:
`ExchangeAtS` is a sentence from that pair. IT DOES NOT SAY THAT THE VERIFIER ACCEPTS AN HONEST RUN,
NOR ANY RUN. The head is a premise here, at the earlier hash, at the full size. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.TiesAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontClaimStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Link)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open ProofFile.Honest.SumLaw (SumCoins)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the structure. Not proved here; a lemma's statement, none of the library's
goals. -/
def K11SeatedAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (weights : W₀ → Weights)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs → b₀ ≤ 346 →
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g =>
      g.place == IM.k11Place) =
        some (headMergeHalf (headClaimsAt cF Zp Bs.G₀) weights (_root_.K11.parOf Zp Bs.G₀)) →
    K11ScriptMsg (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24 →
    K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay weights Vd →
    ∃ (name : String) (Lk : Link TS ProofFile.Cl),
      K11SeatedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) weights name IM.k11Place
        (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) weights IM.k11Place c₀)
        (Item.forms 24 9 "merged") (Item.wo 24) id id (dataAtHead h Q carryX) mgBase 24 Lk

/-- The statement on the frame's debt at the two items. Not proved here; a lemma's statement, none
of the library's goals. -/
def ExchangeAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (weights : W₀ → Weights)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs → b₀ ≤ 346 →
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g =>
      g.place == IM.k11Place) =
        some (headMergeHalf (headClaimsAt cF Zp Bs.G₀) weights (_root_.K11.parOf Zp Bs.G₀)) →
    K11ScriptMsg (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24 →
    K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay weights Vd →
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
        (Item.forms 24 9 "merged") ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
        (Item.wo 24)

end ProofFile.Honest.K11
