-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskRoadStatement.lean: THE ROAD JOINED: THE KIND K11's
PREMISE ON THE SCRIPT's MESSAGE WITH THE MASK ROW (`K11MaskTieF`, MaskBridgeStatement.lean of this
folder: the field maskTie of `K11ScriptMsg`), AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD,
FROM ONE EQUATION ON THE SCRIPT AND THE FRAME's AUTHORS' OWN NAMED PREMISES ON THE SENDER AND THE
BOOK: IN ONE CALL: A STATEMENT ALONE: one definition of a proposition. NOTHING IS PROVED IN THIS
FILE, and it is none of the library's goals: it is a lemma's statement.

  `MaskTieOfRoad`   the base Bs · the prover's half found at `IM.k11Place` · THE PAD: below "free"
                    no entry of row 0 of the mask message's table is a pad's · 3531 + (2 lk + 2) ≤
                    free · THE SCRIPT: below "free" entry ν of row 0 of the mask table of message
                    number `P5J.At.num Zp 24 0` is the value of the sender's function rowOf at the
                    sender's own coins · and seven premises in the frame's authors' forms, at the
                    letters of their `maskTieOn_all` (Honest/Law/Rule/TiesAll.lean): `SenderLaysOwn`
                    · `OwnIs` · the numbers below the part's count · the book's entries for the row,
                    cut in two · the first cut is one stretch of 2 lk + 2 coins of the owner o from
                    s₀ on · s₀ = base + 3531 · the stretch lies inside the owner's coins:
                    `K11MaskTieF` at the kind's own coins, at every letter claims

Why. MaskBridgeStatement.lean has the road's two ends apart; MaskBridgeAllStatement.lean has the far
end at the letters of the frame's authors' own lemma, by reading. Here Lean sees the whole:
`readerAtBehind`, their `readerReads_one`, their `maskTieOn_all`, `maskTieOfAll`.

Limits. ALL TWELVE PREMISES STAY: NONE IS SHOWN HERE AT ANY SCRIPT, BOOK OR SENDER. THE EQUATION ON
THE SCRIPT IS SHOWN OF NO SCRIPT. THE PAD's PREMISE AND "3569 ≤ free" AT THE HEAD's OWN CODES: SHOWN
BY NOBODY. THE FIELD indexTie AND THE TWO FACTS ON THE CELLS ARE NOT TREATED. All the limits of
MaskBridgeStatement.lean. The head is a premise here, at the earlier hash, at the full size. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskBridgeAllStatement
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading WsClaim)
open VerifiableInference.Desc (Chain Strs Place padB)
open VerifiableInference.Desc.Sound (MsgT Mem xAt)
open ProofFile.Honest.SumLaw (SumCoins)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def MaskTieOfRoad : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay))
    (free : ℕ) (o : Addr) (d : Due) (rowOf : Cs d → ℕ → E) (own : Coins Bk → Cs d)
    (base s₀ : ℕ) (es₁ es₂ : List Ahead),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g =>
      g.place == IM.k11Place) =
        some (headMergeHalf claims weights (_root_.K11.parOf Zp Bs.G₀)) →
    (∀ xM : Mem, xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM →
      ∀ ν, ν < free → padB h.𝔇.cs (xM.1.l.get xM.2).1 true 0 ν = false) →
    3531 + (2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 2) ≤ free →
    (∀ k v hd ν, ν < free →
      Q.msg (P5J.At.num Zp 24 0) k v hd true 0 ν = Reading.gl.val (rowOf (own k) ν)) →
    SenderLaysOwn rowOf base (· < free) →
    OwnIs Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain o d own →
    (∀ ν, ν < free → base + ν < d.e) →
    rowEntries Bk IM.k11Place
      (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights
        (_root_.K11.parOf Zp Bs.G₀)).parts.length 0 = es₁ ++ es₂ →
    oneStretch es₁ = some (o, s₀, 2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 2) →
    s₀ = base + 3531 →
    (∀ k : Coins Bk, base + 3531 + (2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 2) ≤
      (k.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain o).1.e) →
    K11MaskTieF (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) claims weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24

end ProofFile.Honest.K11
