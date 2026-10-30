-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SeatFieldsStatement.lean: THREE FIELDS OF THE STRUCTURE
`K11SeatedS` (ShareSStatement.lean of this folder), EACH IN THE FIELD's OWN WORDS: steps, general in
the thread, from the premise on the prover's half, WITH THE LETTER coins LAID; merged and wo, at the
first chain's thread at the library's head: two definitions with code, and STATEMENTS: two
definitions of propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's
goals: they are lemmas' statements.

  `headMergeCoins`          (T P claims weights pl c₀) the coins of the sumcheck's part, of a run's
                            coins: what the frame's `lendRow` (Honest/Frame.lean) lends the row's
                            second part at the place pl; c₀ where it lends nothing
  `dataAtHead`              (h Q carryX) the composed meaning's data at an input, as the frame's
                            letters at the head lay it (`lettersAt`, Honest/Thread/FirstAt.lean):
                            the library's own, with the stored table's decoder at the input's cells
                            and the letter carryX
  `StepsOfHalfCoins`        the field steps at coins := `headMergeCoins`, at every c₀: where the
                            search by pl in the thread's halves finds the kind's half
  `MergedWoAtHead`          the fields merged and wo at the items .forms 24 9 "merged" and .wo 24,
                            at toP := id, toW := id, Dof := `dataAtHead`, Mg₀ := `mgBase`, seg := 24

Limits. THE PREMISE ON THE PROVER's HALF STAYS A PREMISE OF THE FIRST. c₀ IS A LETTER: it is read
only where the book lends the row nothing; there the frame lays no steps. THE LETTER coins STANDS IN
THE FIELD ties TOO: whoever lays the structure lays the same `headMergeCoins` there. The second says
what the thread's word "means" unfolds to at two items: nothing on whether either holds. THE OTHER
TEN FIELDS ARE NOT TREATED HERE: that they can be had at the same letters (toP := id, toW := id, Dof
:= `dataAtHead`, Mg₀ := `mgBase`) is not said. The head is a premise of the second, at the earlier
hash, at the full size: no example of it is shown here; the library's `head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean) has one under four premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ShareSStatement
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain Strs Place Claim)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open ProofFile.Honest.SumLaw (SumCoins)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- **The coins of the sumcheck's part, of a run's coins.** -/
def headMergeCoins {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (pl : Place)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay)) (k : Coins Bk) :
    SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay) :=
  match lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) pl
      (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts 0 with
  | .ok c => c.2.1
  | .error _ => c₀

/-- The statement on the field steps. Not proved here; a lemma's statement, none of the library's
goals. -/
def StepsOfHalfCoins : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay)),
    (T.hs.find? fun g => g.place == pl) = some (headMergeHalf claims weights P) →
    ∀ k w st,
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w)
          [IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl] T.hs = .ok st →
        ∃ v q, st = (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).steps
          (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) v
          ((q, (), ()), headMergeCoins T P claims weights pl c₀ k, ())

/-- **The composed meaning's data at an input, as the frame's letters at the head lay it.** -/
noncomputable def dataAtHead {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (v : Local W₀ Rc ProofFile.Inst Tr) :=
  { h.𝔇 with decT := fun _ _ => some (Q.cells v), cr1 := carryX }

/-- The statement on the fields merged and wo. Not proved here; a lemma's statement, none of the
library's goals. -/
def MergedWoAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr),
    (∀ v a y u, (mgAll (dataAtHead h Q carryX v) mgBase).forms 24 9 "merged" (id a.1, a.2) y
        (id u) →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means v
        (Item.forms 24 9 "merged") a y u) ∧
    ∀ v a y u, (mgAll (dataAtHead h Q carryX v) mgBase).wo 24 (id a.1, a.2) y (id u) →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means v (Item.wo 24) a
        y u

end ProofFile.Honest.K11
