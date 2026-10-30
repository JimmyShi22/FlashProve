-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnSayAll.lean: the clause `say` of `OwnAsks` at a stand of the last thread at border 2: the rows that the own test takes in hold of the job's
words. The open rows come from the item `rows`; the first chain's sample rows from the pins' sentences 'srow 0', 'srow 2'; Omega's from the shared
chain's sample sentence, at its new number.

  `tidy_border_A0`, `below_A0`: closed lines.
  `srow_says`: a first chain's sample row holds of the chain's words.

What stays open. `say_stand`, the assembly at a stand, is not here yet.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnSayStand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (wordsAt PlainRows)
open OnBytes (TableKey Part Oracle Group)
open OnBytes.Means (Words Says tableSize AllSay RowOn layoutOf)
open OnBytes.Slice (GE rdE readE begun runRows)
open VerifiableInference.Desc (Place Wit OpenedColumn Strs)
open VerifiableInference.Desc.Ground.Sh (stTidyB tidy_of stSh grpSh grp_get)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ Border)
open VerifiableInference.Desc.Third.Law (RowsHold says_congr law_k14Second)
open VerifiableInference.Desc.Last (ItemL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar valOf RowHolds
  rowHolds_iff_says_of_rowIn)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped Sh₃ sh₃ SF CF)
open AtPublicFiles.AtFiles.Full (A0)
open Johnson.RunOne.KeyRows1 (plan₁)

/-- The shared statement in the border is tidy, at the written shape. -/
theorem tidy_border_A0 : A0.2.border.map (·.tidy) = some true := by decide +kernel

/-- The shared statement's codes, at the written shape. -/
theorem codes_border_A0 : A0.2.border.map (·.st.codes) = some CF := by decide +kernel

/-- Omega's number in the shared chain, at the written shape. -/
theorem omega_border_A0 : A0.2.border.map (·.omega) = some 2 := by decide +kernel

/-- Numbers 0 and 9 lie below the statement's size, at the written shape. -/
theorem below_A0 : 9 < A0.1.st.oracles.length := by decide +kernel

section
variable {Wt₁ : Type} (val₁ : Wt₁ → Nat → Part → Nat → GE)

/-- **A first chain's sample row holds of the chain's words**, from the sentence at the reading val. -/
theorem srow_says (T : OnBytes.Statement) (s : S₃) (u : Wt₁ × Words GE) (val : Nat → Part → Nat → OnBytes.E)
    (hv : ∀ o pt i, val₁ u.1 o pt i = readE (val o pt i)) (hI : OnBytes.Means.InOrder T) (o : Nat) (x : Oracle)
    (hx : T.oracles[o]? = some x) (hn : ∀ z < T.oracles.size, z ≠ s.loc.omega) (r : OnBytes.Row)
    (hr : r ∈ x.sampleRows.toList) (hh : RowHolds (fun a b => readE a = readE b) T val r) :
    Says rdE T r (wordsKey val₁ s u) := by
  have hin : OnBytes.Means.RowIn T ({ code := 0, members := #[o] } : Group) r :=
    (hI.samples o x hx r hr).isIn (by simp)
  refine (says_congr rdE T r _ _ fun z hz pt i => ?_).2
    ((rowHolds_iff_says_of_rowIn rdE T _ val r hin).1 hh)
  unfold wordsKey
  rw [if_neg (hn z hz), hv]
  rfl

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.tidy_border_A0
#print axioms AtPublicFiles.KeyLastChain.below_A0
#print axioms AtPublicFiles.KeyLastChain.codes_border_A0
#print axioms AtPublicFiles.KeyLastChain.omega_border_A0
#print axioms AtPublicFiles.KeyLastChain.srow_says
