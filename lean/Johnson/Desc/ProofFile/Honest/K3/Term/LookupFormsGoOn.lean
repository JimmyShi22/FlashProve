-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupFormsGoOn.lean: the kind "lookup" (K3): the sentence of an
item "forms" passes FORWARD from a state s to a state s': what it says at s it says at s'. The
library has these laws backward (`forms_back`, Johnson/Desc/Reads/FormsPass.lean; `formsQA_back`,
Johnson/Desc/Sound/FormsAhead.lean; `mgAll_forms_back_any`, Johnson/Desc/Sound/MgAt/K3RidesDigFull.lean).
An honest prover's invariant needs them forward.

What is shown.
  `formsSentenceGoesOn`: `formsQ` at s gives `formsQ` at s'.
  `formsSentenceAheadGoesOn`: the like for `formsQA`, where a form may name what is ahead.
  `lookupFormsItemGoesOn`: the field `forms` of the composed meaning `mgAll` at s gives it at s'.

Hypotheses that remain, at `lookupFormsItemGoesOn`.
  `hParts`: link, statement and book stay and the ledger behind is a later one.
  `hStay`: what the link's reader answers at s, at each of the item's runs, it answers at s'.
  `hTest`: the item's public test holds at s'.
  `hWeights`: at the name "weights" alone: the sentence on the weights passes.

Limits. On two states and a meaning's letters alone: no thread, no step. Nothing shows here that the
hypotheses hold at any two states.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.Sound.MgAt.K3RidesDigFull
import Johnson.Desc.Sound.MgAt.K3RidesDigFwd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K3.Term
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.K9 (segAt? lateOk affIn affInA Read Readers formsIn formsInA mergeOf)
open VerifiableInference.Desc.Sound (MsgQ MsgT formsQ formsQA dataQA dataQA_same Rides value_rides
  value_ridesW MgData mgAll mgAll_forms mgAll_formsIn_at mgAll_formsInA_at CellsQ)
open VerifiableInference.Reads.Pass (Fwd)
open VerifiableInference.OnPublicFiles (rides_of_parts)

/-! ## 1 The sentence goes on -/

section
variable (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s s' : S)
  (a b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ)

/-- **"forms" in front gives "forms" behind.** -/
theorem formsSentenceGoesOn (ha : segAt? s = some a) (hb : segAt? s' = some b)
    (hf : Fwd Rd piece run s s') (hin : formsIn Rd own piece run s' = true) (hr : Rides own a b)
    (h : formsQ Rd own piece run s rd) : formsQ Rd own piece run s' rd := by
  obtain ⟨a', R, ha', hR, _, hfm⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hR' := hf R hR
  unfold formsIn at hin
  rw [hb, hR'] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨b, R, hb, hR', hlate, fun f hm => ⟨List.all_eq_true.1 hall f hm, ?_⟩⟩
  rw [value_rides own (mergeOf s) R.late a' b rd hr f (hfm f hm).1]
  exact (hfm f hm).2

/-- **The like where a form may name what is ahead.** -/
theorem formsSentenceAheadGoesOn (sent : ℕ → List (ℕ × ℕ)) (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hf : Fwd Rd piece run s s')
    (hin : formsInA Rd sent own piece run s' = true) (hL : b.L = a.L) (hst : b.d.st = a.d.st)
    (hbk : b.d.book = a.d.book)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (h : formsQA sent own Rd piece run s rd) : formsQA sent own Rd piece run s' rd := by
  obtain ⟨a', R, ha', hR, _, hfm⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hR' := hf R hR
  unfold formsInA at hin
  rw [hb, hR'] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨b, R, hb, hR', hlate, fun f hm => ⟨List.all_eq_true.1 hall f hm, ?_⟩⟩
  have h2 := (hfm f hm).1
  unfold affInA at h2
  obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  have eD := dataQA_same sent own hL hst hbk rd
  rw [value_ridesW own (mergeOf s) R.late a' b (dataQA sent own a' rd) (dataQA sent own b rd)
    (by rw [hL]) hfill f (List.all_eq_true.1 h3) (fun _ _ _ _ => by rw [eD])
    (fun _ _ => by rw [eD])]
  exact (hfm f hm).2

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE COMPOSED SENTENCE "forms" GOES ON.** hParts: link, statement and book stay and the ledger
behind is later: what the lookups' own clause has. hStay: the readers' answers stay.
hTest: the item's public test holds behind. hWeights: at the name "weights" alone. -/
theorem lookupFormsItemGoesOn {l kk : ℕ} {r : String} {s s' : S} (z : P) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT)
    (hParts : ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book ∧ _root_.Fo.Later a.F b.F)
    (hStay : ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 s s')
    (hTest : (mgAll Dm Mg).pub (.formsIn l kk r) (z, s') = true)
    (hWeights : r = "weights" → Dm.wt l (z, s) y w → Dm.wt l (z, s') y' w)
    (h : (mgAll Dm Mg).forms l kk r (z, s) y w) : (mgAll Dm Mg).forms l kk r (z, s') y' w := by
  rw [mgAll_forms] at h ⊢
  refine ⟨fun p hp => ?_, fun e => hWeights e (h.2 e)⟩
  have h1 := h.1 p hp
  by_cases e : Dm.ah p.1 p.2 = true
  · rw [if_pos e] at h1 ⊢
    obtain ⟨a, R, ha, hR, hl, hfm⟩ := h1
    obtain ⟨b, hb, eL, est, ebk, hLater⟩ := hParts a ha
    exact formsSentenceAheadGoesOn (Dm.Rd l) (Dm.N.group l) p.1 p.2 s s' a b _ (Dm.N.sent l) ha hb
      (hStay p hp) (mgAll_formsInA_at Dm Mg hTest hp e) eL est ebk
      (rides_of_parts (Dm.N.group l) eL est ebk hLater).filled ⟨a, R, ha, hR, hl, hfm⟩
  · rw [if_neg e] at h1 ⊢
    have e' : Dm.ah p.1 p.2 = false := by
      cases h0 : Dm.ah p.1 p.2 with
      | false => rfl
      | true => exact absurd h0 e
    obtain ⟨a, R, ha, hR, hl, hfm⟩ := h1
    obtain ⟨b, hb, eL, est, ebk, hLater⟩ := hParts a ha
    exact formsSentenceGoesOn (Dm.Rd l) (Dm.N.group l) p.1 p.2 s s' a b _ ha hb (hStay p hp)
      (mgAll_formsIn_at Dm Mg hTest hp e') (rides_of_parts (Dm.N.group l) eL est ebk hLater)
      ⟨a, R, ha, hR, hl, hfm⟩

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.formsSentenceGoesOn
#print axioms ProofFile.Honest.K3.Term.formsSentenceAheadGoesOn
#print axioms ProofFile.Honest.K3.Term.lookupFormsItemGoesOn
