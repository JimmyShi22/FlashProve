-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SLotStatement.lean: THE ROW OF THE MERGE OF THE CLAIMS ON
THE WEIGHTS AS A LOT OF ROWS WITH THEIR SIMULATORS (`SLot`, Honest/Thread/Rows.lean); THAT IT IS THE
KIND's LOT OF HALVES; AND THE FRAME's `Good` AT THE SIDE THAT IS TAKEN OFF A LIST OF MEMBERS BY THE
ROW's PLACE (`Side.seated`, Honest/Side.lean): two definitions with code, and STATEMENTS: two, each
a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and neither statement is one of the
library's goals: they are lemmas' statements. WHAT FOLLOWS FROM `Good` IS NOT SAID HERE.

  `headMergeBare`         the kind's row without letters: the kind's place · each part with the
                          simulator beside it (`headMergeSided`, Honest/K11/Part.lean) ·
                          On := True · bud := True
  `headMergeSLot`         the lot: that one row, at the numbers at which the lot lays the kind's
                          block (`K11.parOf`, Johnson/Desc/ProofFile/Lot/K11.lean)
  `HeadMergeSLotIs`       its lot of halves is the kind's (`headMergeLot`, Honest/K11/Part.lean)
  `HeadMergeGoodSeated`   bs, the list of members, fs₀, the falls, and σ₀ are variables. Under
                            seated    σ₀ is the side that `Side.seated` takes off bs at the row's
                                      place, with the row, at fs₀
                            member    the first member of bs at that place is the kind's block as it
                                      stands alone at a seat at that place
                            unspent   no entry of the book lets any part spend a coin of a part of
                                      this row:
                          `Good pre φ σ₀ Bk ord chain firstTree A' B' On bud` at A' := B' := False
                          and the row's own On and bud; pre is tied to no description

Limits. The three premises are shown at no list and no book. plays and acc hold from False: nothing
is shown by them. Of exact: all that GoodAllStatement.lean of this folder says in its Limits holds
here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.GoodAllStatement
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Block Claim Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)

/-- **The kind's row without letters.** -/
def headMergeBare {W₀ Rc Xi Tr X : Type} (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) :
    Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { place := headMergePlace P, row := headMergeSided P claims weights
    On := fun _ _ _ _ => True, bud := fun _ _ _ => True }

/-- **The lot of rows.** The name is the kind's lot's. -/
def headMergeSLot {W₀ Rc Tr X : Type}
    (claims : Pub → Ground → Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) :
    SLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  { name := "the merge of the weights' claims"
    rows := fun Z G => [headMergeBare (_root_.K11.parOf Z G) (claims Z G) weights] }

/-- The statement that the lot of halves is the kind's. Not proved here; a lemma's statement, none
of the library's goals. -/
def HeadMergeSLotIs : Prop :=
  ∀ (W₀ Rc Tr X : Type) (claims : Pub → Ground → Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights),
    (headMergeSLot (Rc := Rc) (Tr := Tr) (X := X) claims weights).toHLot =
      headMergeLot claims weights

/-- The statement at the side that is taken off a list. Not proved here; a lemma's statement, none
of the library's goals. -/
def HeadMergeGoodSeated : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (bs : List (Block S Claim)) (fs₀ : List (Fall S))
    (σ₀ : Side S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (name : String),
    Side.seated bs (headMergeBare (Rc := Rc) (Tr := Tr) (X := X) P claims weights).place
      (headMergeBare P claims weights).row fs₀ = some σ₀ →
    (bs.find? fun b => b.place == headMergePlace P) =
      some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name (headMergePlace P)) →
    (∀ j q, Bk.spentBy ⟨headMergePlace P, j⟩ q = []) →
    Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (headMergeBare (Rc := Rc) (Tr := Tr) (X := X) P claims weights).On
      (headMergeBare (Rc := Rc) (Tr := Tr) (X := X) P claims weights).bud

end ProofFile.Honest.K11
