-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyCodesLater.lean: THEOREMS. **THE CARRIED CODES ARE THE PLAN's AT EVERY RECORD THAT THE KEY FILE's SHARED AND LAST CHAINS REACH; AND ALL THREE CHAINS OF Key.descriptionFromSource KEEP «A STATEMENT ONLY GROWS».** Over k12_grows (Johnson/Desc/K12/Law/GrowsTest.lean) the two later chains' laws have NO PREMISE; chain 1's neither (KeyCodesPaid.lean). With
KeyCodesPaid.lean: the codes' half of the row «the carried codes (and group layout) are the plan's at every step of Key.descriptionFromSource's chains», whole.
OBJECT. (Key.descriptionFromSource X N P).shared | .second: their flat lists as a piece holds them, and start₂ | start₃; «reached» is LPFD.Hist₂ | Hist₃ (Johnson/Top/Fire/Code/RowsWoven.lean). USER. Whoever reads d.st.codes on these chains (K14.linPointL · K14's SPLIT: linLayOmega d.st.codes · Third.batchLinearConstraintsSecondPart:
linLayOmega | linLayW a.2.st.codes); Spec.statement_grows | file_covered (Johnson/Desc/StatementGrows.lean), whose three owed premises these are. LETTERS. X · N · P · D · k · a.
  shared_growsBy · second_growsBy     ChainKeeps (GrowsBy (·.st)) (Key.descriptionFromSource X N P).shared | .second
  three_grow         **the three premises of Spec.statement_grows at Key.descriptionFromSource X N P, together**
  codes_at_reached₂  **Hist₂ … k a → a.2.st.codes = X.chains.made.sized.key.codes, for every k**
  start₃_codes       a yes of the last chain's start lays a record with these codes (the start TESTS both ends': start₃E_inv | start₃_inv, Johnson/Desc/Third/Law/AtDoor.lean)
  codes_at_reached₃  **Hist₃ … k a → a.2.st.codes = X.chains.made.sized.key.codes, for every k**
What is not claimed. That the sized key's codes are those read back (the shared chain's front's fourth clause; on chain 1 the clause «cut»). The groups' members against the plan. NOTHING ON ROWS. Nothing on soundness.

-/
import Johnson.RunOne.KeyKeepsLater
import Johnson.RunOne.KeyCodesMid
import Johnson.Desc.Third.Law.AtDoor

set_option autoImplicit false

namespace Johnson.RunOne.KeyCodes

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc (Block Chain Grows)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.Keeps (Decides ChainKeeps chain_flat_keeps named_ok ebind_ok)
open VerifiableInference.Desc.ChainEnd (GrowsBy bind_ok)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Third (S₃)
open LPFD (Hist₂ Hist₃)

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

theorem shared_growsBy : ChainKeeps (GrowsBy st₂) (descriptionFromSource X N P).shared :=
  retype_keeps (shared_grows X.chains P)

theorem second_growsBy : ChainKeeps (GrowsBy st₃) (descriptionFromSource X N P).second :=
  retype_keeps (third_grows X.chains P)

/-- **The three premises of Spec.statement_grows, at the key file's description.** -/
theorem three_grow :
    ChainKeeps (GrowsBy (st₁ (β := LookupRecord))) (descriptionFromSource X N P).first ∧ ChainKeeps (GrowsBy st₂) (descriptionFromSource X N P).shared ∧ ChainKeeps (GrowsBy st₃) (descriptionFromSource X N P).second :=
  ⟨first_growsBy, shared_growsBy, second_growsBy⟩

/-- **The carried codes are the plan's at every record that the shared chain reaches.** -/
theorem codes_at_reached₂ (D : OnBytes.Maker.WholeD) (k : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D k a) :
    (st₂ (show _root_.Desc.K14.St from a.2)).codes = X.chains.made.sized.key.codes := by
  refine reached_inv _ _ _ (fun a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂ => (st₂ (show _root_.Desc.K14.St from a.2)).codes = X.chains.made.sized.key.codes)
    (fun a ha => ?_) (fun b hb a rs gs a' hI hd => ?_) k a h
  · have e : a.2 = (descriptionFromSource X N P).start₂ a.1.1 := (show LPFD.st₂ (descriptionFromSource X N P) D a from ha).2
    exact congrArg (fun s : (descriptionFromSource X N P).S₂ => (st₂ (show _root_.Desc.K14.St from s)).codes) e
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    have h2 := (VerifiableInference.Desc.Plain.held_decide b₀ a rs gs a' hd).2
    have g : Grows (st₂ (show _root_.Desc.K14.St from a.2)) (st₂ (show _root_.Desc.K14.St from a'.2)) :=
      chain_flat_keeps (GrowsBy st₂) (fun _ => Grows.refl _) (fun _ _ _ x y => Grows.trans x y) _ shared_growsBy b₀ hb₀ _ _ _ _ h2
    exact g.1.trans hI

/-- A yes of the last chain's start lays a record with the sized key's codes: the start tests both ends'. -/
theorem start₃_codes {x : (descriptionFromSource X N P).XiPub} {s₁ : (descriptionFromSource X N P).S₁} {s₂ : (descriptionFromSource X N P).S₂} {s₃ : (descriptionFromSource X N P).S₃} (h : (descriptionFromSource X N P).start₃ x s₁ s₂ = .ok s₃) :
    (st₃ (show S₃ from s₃)).codes = X.chains.made.sized.key.codes := by
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨f, _, hs⟩ := VerifiableInference.Desc.Third.Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨hc, _, e⟩ := VerifiableInference.Desc.Third.Law.start₃_inv _ _ _ _ hs
  rw [e]
  exact hc

/-- **The carried codes are the plan's at every record that the last chain reaches.** -/
theorem codes_at_reached₃ (D : OnBytes.Maker.WholeD) (k : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) :
    (st₃ (show S₃ from a.2)).codes = X.chains.made.sized.key.codes := by
  refine reached_inv _ _ _ (fun a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃ => (st₃ (show S₃ from a.2)).codes = X.chains.made.sized.key.codes)
    (fun a ha => ?_) (fun b hb a rs gs a' hI hd => ?_) k a h
  · have e : ((descriptionFromSource X N P).start₃ a.1.1 a.1.2.1 a.1.2.2).toOption = some a.2 := (show LPFD.st₃ (descriptionFromSource X N P) D a from ha).2
    cases hs : (descriptionFromSource X N P).start₃ a.1.1 a.1.2.1 a.1.2.2 with
    | error m => rw [hs] at e; cases e
    | ok s =>
      rw [hs] at e
      have e' : s = a.2 := Option.some.inj e
      exact (congrArg (fun s : (descriptionFromSource X N P).S₃ => (st₃ (show S₃ from s)).codes) e').symm.trans (start₃_codes hs)
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    have h2 := (VerifiableInference.Desc.Plain.held_decide b₀ a rs gs a' hd).2
    have g : Grows (st₃ (show S₃ from a.2)) (st₃ (show S₃ from a'.2)) :=
      chain_flat_keeps (GrowsBy st₃) (fun _ => Grows.refl _) (fun _ _ _ x y => Grows.trans x y) _ second_growsBy b₀ hb₀ _ _ _ _ h2
    exact g.1.trans hI

end Johnson.RunOne.KeyCodes

#print axioms Johnson.RunOne.KeyCodes.shared_growsBy
#print axioms Johnson.RunOne.KeyCodes.second_growsBy
#print axioms Johnson.RunOne.KeyCodes.three_grow
#print axioms Johnson.RunOne.KeyCodes.codes_at_reached₂
#print axioms Johnson.RunOne.KeyCodes.start₃_codes
#print axioms Johnson.RunOne.KeyCodes.codes_at_reached₃
