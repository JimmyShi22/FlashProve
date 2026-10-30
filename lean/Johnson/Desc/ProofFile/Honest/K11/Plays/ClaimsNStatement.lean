-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ClaimsNStatement.lean: THAT THE TEXTS WHICH ARE GENERAL IN
THE SIZE (Honest/K11/KeysAtLink.lean · ClaimsN.lean) ARE THE ELDER ONES AT THE FULL SIZE: STATEMENTS
ALONE: seven definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the
library's goals: they are lemmas' statements.

  `KeysAtLinkIsHead`         at every chain c: the lookups' authors' `headKeysOfK3 c` is
                             `keysAtLink` at link 24 and the rounds in front of member 340
  `KeysAtLinkIsLayers`       at every chain c and group g: the field zk of their `lookOfK3 Z c g` is
                             `keysAtLink` at link 2 g and the rounds in front of member 28 g + 3
  `HeadClaimsNIs`            at every chain c: `headClaimsAt c Z G` is `headClaimsN` at 24 and the
                             rounds in front of members 340 and 341
  `HeadClaimsByPlaceAtHead`  under the library's head, at the maker's base Bs: `headClaimsByPlace Zp
                             Bs.G₀ = headClaimsAt cF Zp Bs.G₀`
  `FrontClaimByPlaceAtHead` · `K11SeatedByPlaceAtHead` · `ExchangeByPlaceAtHead`
                             the three statements of this folder that name `headClaimsAt cF Zp
                             Bs.G₀` (`FrontClaimAtHead` · `K11SeatedAtHead` · `ExchangeAtHead`),
                             with `headClaimsByPlace Zp Bs.G₀` in its place: one · four · two places

Limits. THE FIRST THREE HAVE NO PREMISE; THE LAST FOUR ARE UNDER THE HEAD: AT THE FULL SIZE, AT THE
EARLIER HASH. AT ANOTHER SIZE NOTHING IS SHOWN OF THE GENERAL TEXTS. THAT A FILLING's LOT IS LAID AT
ONE OF THEM IS SAID BY NOBODY. THREE TEXTS STAND FOR THE ONE LETTER claims: `headClaimsAt c` (a
chain in front) · `headClaimsPub` (ClaimsPubStatement.lean of this folder: no chain in front; the
full size's numbers) · `headClaimsByPlace`: under the head, at the ground of the maker's base, the
three are one. The three carried statements have all the limits of the three other ones, which
stand: among them: they rest on the lookups' files. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimsN
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatedAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LayersTieHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain Strs Place Link)
open VerifiableInference.Desc.First (HeadOwn Item)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open ProofFile.Honest.K3.Law.AtThr (headKeysOfK3 lookOfK3)
open ProofFile.Honest.SumLaw (SumCoins)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the head's key points. Not proved here; a lemma's statement, none of the
library's goals. -/
def KeysAtLinkIsHead : Prop :=
  ∀ c : Chain TS ProofFile.Cl, headKeysOfK3 c = keysAtLink 24 (roundsAhead c.blocksInOrder 340)

/-- The statement on the layers' key points. Not proved here; a lemma's statement, none of the
library's goals. -/
def KeysAtLinkIsLayers : Prop :=
  ∀ (Z : ProofFile.Pub) (G : ProofFile.Ground) (c : Chain TS ProofFile.Cl) (g : ℕ) (x : ProofFile.Inst)
    (hd : List Fmt.Drawn),
    (lookOfK3 Z c g x hd).zk = keysAtLink (2 * g) (roundsAhead c.blocksInOrder (28 * g + 3)) Z G hd

/-- The statement on the claims. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadClaimsNIs : Prop :=
  ∀ (c : Chain TS ProofFile.Cl) (Z : ProofFile.Pub) (G : ProofFile.Ground),
    headClaimsAt c Z G = headClaimsN 24 (roundsAhead c.blocksInOrder 340) (roundsAhead c.blocksInOrder 341) Z G

/-- The statement on the text by place. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadClaimsByPlaceAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    headClaimsByPlace Zp Bs.G₀ = headClaimsAt cF Zp Bs.G₀

/-- `FrontClaimAtHead` at the text by place. Not proved here; a lemma's statement, none of the
library's goals. -/
def FrontClaimByPlaceAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (Bs : ProofFile.PureBase) (a : HeadOwn)
    (claim : WsClaim),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs → b₀ ≤ 346 →
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E →
    s.here = .head a → a.claim = some claim →
    headClaimsByPlace Zp Bs.G₀ m.st.input.x m.st.heard = [claim]

/-- `K11SeatedAtHead` at the text by place. Not proved here; a lemma's statement, none of the
library's goals. -/
def K11SeatedByPlaceAtHead : Prop :=
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
        some (headMergeHalf (headClaimsByPlace Zp Bs.G₀) weights (_root_.K11.parOf Zp Bs.G₀)) →
    K11ScriptMsg (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsByPlace Zp Bs.G₀) weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24 →
    K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay weights Vd →
    ∃ (name : String) (Lk : Link TS ProofFile.Cl),
      K11SeatedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsByPlace Zp Bs.G₀) weights name IM.k11Place
        (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (_root_.K11.parOf Zp Bs.G₀) (headClaimsByPlace Zp Bs.G₀) weights IM.k11Place c₀)
        (Item.forms 24 9 "merged") (Item.wo 24) id id (dataAtHead h Q carryX) mgBase 24 Lk

/-- `ExchangeAtHead` at the text by place. Not proved here; a lemma's statement, none of the
library's goals. -/
def ExchangeByPlaceAtHead : Prop :=
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
        some (headMergeHalf (headClaimsByPlace Zp Bs.G₀) weights (_root_.K11.parOf Zp Bs.G₀)) →
    K11ScriptMsg (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsByPlace Zp Bs.G₀) weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24 →
    K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay weights Vd →
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
        (Item.forms 24 9 "merged") ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
        (Item.wo 24)

end ProofFile.Honest.K11
