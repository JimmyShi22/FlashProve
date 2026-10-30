-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/PlaysThrStatement.lean: THE THREAD's DEBT `Plays`
(Honest/Thread/Pays.lean) AT THE MEMBER THAT IS THE MERGE OF THE CLAIMS ON THE WEIGHTS: STATEMENTS
ALONE: two, each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and neither is one
of the library's goals: they are lemmas' statements.

THE THREAD T IS A VARIABLE. Two facts on its letters are spent, each a named premise: the fields
`member` and `steps` of `K11Seated` (Honest/K11/Plays/ShareStatement.lean), in these fields' own
words.

  `HeadMergePlaysThr`      under these two: `Plays T b`: from the thread in front, at every run's
                           coins and at all challenges that fit the member's rounds: the frame's
                           play and the laying of the columns return; no column is read; the member
                           sends no tree, so that nothing is asked of a new tree
  `HeadMergePlaysSeated`   so under `K11Seated`

Limits. The two premises are shown at no thread. Two premises of `Plays` are not spent: that nothing
of the member stops (this row has no stop), and THE THREAD IN FRONT: it plays from any stand.
Nothing on the verifier's step. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ShareStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Link Claim Place Wit)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MgData CellsQ MsgT)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open ProofFile.Honest.SumLaw (SumCoins)

/-- The statement, under the two premises. The letters: as in `K11Seated`. Not proved here; a
lemma's statement, none of the library's goals. -/
def HeadMergePlaysThr : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay)),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (∀ k w st,
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w)
          [IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl] T.hs = .ok st →
        ∃ v q, st = (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).steps
          (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) v ((q, (), ()), coins k, ())) →
    Plays T b

/-- The statement under the whole structure. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergePlaysSeated : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type) (rows cols nR : ℕ)
    (Xp : OnBytes.Model.Verify.Public)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (i₁ i₂ : T.ι) (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp)
    (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)) (seg : ℕ) (l : Link S Claim),
    K11Seated T b P claims weights name pl coins i₁ i₂ toP toW Dof Mg₀ seg l → Plays T b

end ProofFile.Honest.K11
