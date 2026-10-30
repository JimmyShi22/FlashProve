-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/MeansIn.lean: AT THE FIRST CHAIN'S THREAD (Honest/Thread/
First.lean: Letters.thread), WHERE THE LETTER FOR THE ITEMS' MEANING IS THE COMPOSED MEANING: WHAT
THE THREAD'S ITEM SAYS GIVES THE COMPOSED MEANING'S FIELD, for the items "worth" and "constr": the
fields "means" of K6KeysLetters (KeysAtThread.lean) and K6IdnLetters (IdnAtThread.lean), at
toP := id and toW := id.
WHAT IT IS NOT. By unfolding: the honest letters over a meaning (First.lean: honest) turn five of
its fields (pin, noColl, shown, decodes, totalB) and neither of these two. CONDITIONAL: hMg. The
mirror of Share.lean's k6_means_at, which goes the other way for the items that the member owes.
Nothing on any property.
OF THE FOLDER Johnson/Goal/ it names nothing and imports no module directly.

-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (Meaning Item)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll)
open ProofFile.Honest (ProverCoinCounts Local)

variable {Bk : ProverCoinCounts} {W₀ Rc Xj Tr X Xi P Tok : Type} {rows cols nR : ℕ}
  {Wp : OnBytes.Model.Verify.Public}
  (L : ProofFile.Honest.FirstThread.Letters Bk Claim W₀ Rc Xj Tr X P (Fin rows → Fin cols → GE) Tok MsgT)
  {Dof : Local W₀ Rc Xj Tr → MgData Xi P Tok rows cols nR Wp}
  {Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)}

/-- The item worth m k r. -/
theorem k6_means_worth (hMg : ∀ w, L.Mg w = mgAll (Dof w) Mg₀) (m k : ℕ) (r : String) :
    ∀ w a y v, L.thread.means w (Item.worth m k r) a y v →
      (mgAll (Dof w) Mg₀).worth m k r (id a.1, a.2) y (id v) := by
  intro w a y v h
  have h' : Item.holds L.N (L.mg w) (Item.worth m k r) a y v := h
  unfold ProofFile.Honest.FirstThread.Letters.mg at h'
  rw [hMg w] at h'
  exact h'

/-- The item constr m p. -/
theorem k6_means_constr (hMg : ∀ w, L.Mg w = mgAll (Dof w) Mg₀) (m : ℕ) (p : P5J.TPart) :
    ∀ w a y v, L.thread.means w (Item.constr m p) a y v →
      (mgAll (Dof w) Mg₀).constr m p (id a.1, a.2) y (id v) := by
  intro w a y v h
  have h' : Item.holds L.N (L.mg w) (Item.constr m p) a y v := h
  unfold ProofFile.Honest.FirstThread.Letters.mg at h'
  rw [hMg w] at h'
  exact h'

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_means_worth
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_means_constr
