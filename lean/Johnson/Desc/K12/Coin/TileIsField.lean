-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Sound.DataRounds
import Johnson.EntryRec.OkcFiles
/-
Johnson/Desc/K12/Coin/TileIsField.lean: THE LETTERS AT WHICH OUR LAW WITH A KEY STANDS (a piece of piecesAt … at the data D that F.data returns; the window's lower end F.t₁) AGAINST THE LETTERS OF THE RULE THAT TAKES A DESCRIPTION's PIECES TO THE PROOF FILE's GOAL (proofSound_at_descB, Johnson/Desc/Plain/BothAtDesc.lean: (atDesc F T).p₂ :: (atDesc F T).l₂ · DP.at a · (DP.at a).t₁). EQUATIONS ON VALUES; no law on a game. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
  (E1), that atDesc leaves the rows of pieces as they are (by rfl), is atDesc_row₂ of Johnson/Desc/K12/Coin/ReadsKey.lean: not here.
  at_self · at_of_depth  (E2) D.at D.a = D by rfl; D.at a = D where a = D.a
  data_depth             what F.data returns has the description's own depth of the stored table
  data_at                (E2) F.data file = .ok D · a = F.tableDepth ⇒ F.data file = .ok (D.at a): THE PREMISE a = F.tableDepth IS NOT BY TYPE: it ties the index of the rule's letters to the description's field
  at_not                 and it is spent: where a ≠ D.a, D.at a ≠ D
  t₁_at | t₂_at          (D.at a).t₁ = D.t₁: by rfl
  lo_is_field            (E3) F.data file = .ok D ⇒ F.t₁ = (D.at a).t₁ (by opensShaped, Johnson/Desc/Sound/DataRounds.lean)
  numAt_own0             numAt t₁ t₂ 1 (.own 0) = t₁
  frame_str              the strings over the frame at D are the rule's: (frameAt D all key ft).E = EAll D all: by rfl
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound

theorem at_self (D : WholeD) : D.at D.a = D := rfl

theorem at_of_depth (D : WholeD) (a : ℕ) (h : a = D.a) : D.at a = D := by
  subst h
  rfl

theorem at_not (D : WholeD) (a : ℕ) (h : a ≠ D.a) : D.at a ≠ D := fun e =>
  h (congrArg WholeD.a e)

theorem data_depth {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) : D.a = F.tableDepth := by
  obtain ⟨_, _, _, rfl⟩ := data_ok h
  rfl

/-- (E2) -/
theorem data_at {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (a : ℕ) (ha : a = F.tableDepth) : F.data file = .ok (D.at a) := by
  rw [at_of_depth D a (ha.trans (data_depth F file D h).symm)]
  exact h

theorem t₁_at (D : WholeD) (a : ℕ) : (D.at a).t₁ = D.t₁ := rfl
theorem t₂_at (D : WholeD) (a : ℕ) : (D.at a).t₂ = D.t₂ := rfl

/-- (E3) -/
theorem lo_is_field {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (a : ℕ) : F.t₁ = (D.at a).t₁ :=
  (opensShaped F file D h).2.1.symm

theorem numAt_own0 (t₁ t₂ : ℕ) : numAt t₁ t₂ 1 (.own 0) = t₁ := rfl

theorem frame_str (D : WholeD) (all : List LeftT) (key : ℕ → ℕ) (ft : ℕ) :
    (frameAt D all key ft).E = EAll D all := rfl

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.data_at
#print axioms VerifiableInference.Desc.K12.Coin.at_not
#print axioms VerifiableInference.Desc.K12.Coin.lo_is_field
#print axioms VerifiableInference.Desc.K12.Coin.numAt_own0
#print axioms VerifiableInference.Desc.K12.Coin.frame_str
