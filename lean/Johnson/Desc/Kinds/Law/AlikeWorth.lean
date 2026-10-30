-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/AlikeWorth.lean.
WHAT IT DOES NOT SHOW. No soundness. NOT THAT ANY ENTRY IS WORTH ANYTHING: that the two fillings'
entries are worth the same below the lengths spent is a premise (EntriesAlike): at a seat's reads
and
the reads in truth it is "every sent read's entry is its true sum of cells": other laws'. That the
heard variables name no entry: a premise (HeardBare): Law/CoveredAt.lean and Law/CoveredNormAt.lean
have it at a hearing's return. The form of "join" is not here: its nine keys are.
LETTERS. N, R and N', R': two fillings of the reads' places · W, W': two worlds with the same slots
(hs) · under "there is": fs, f: the list of that name at (N, R), pinned by the lookup, and a member.
OBJECT. Desc/Kinds/Head.lean's claims (35 forms in three named runs), key (five) and FinalNorm.key
21
(four), each at two fillings of the classes FinalNorm.Reads and Reads.
USER. Whoever holds "the claims that a seat's runs state are worth 0 in the witness's world" and
must
reach Law/RowAtDecide.lean's OpenedAt, which speaks of the same forms at the reads in truth, in a
world that looks at no entry.
WHAT IT IS. THE SAME 35 FORMS AND NINE KEYS, MADE AT TWO FILLINGS OF THE READS' PLACES, ARE WORTH
THE
SAME IN TWO WORLDS WITH THE SAME SLOTS, IF THE ENTRIES ARE, BELOW EACH READ's LENGTH.
  SameWorth W W'    the relation: the first form's value in W is the second's in W'.
  kept_worth        it is kept by the forms' arithmetic, and holds of a form without an entry and
                    itself, where the two worlds have the same slots.
  alike_claims      for any kept relation: to each member of a run at (N', R') a member of the run
  of
                    that name at (N, R).
  worth_claims      so at SameWorth.
  zero_claims       so: where every form of every run at (N, R) is worth 0 in W, every form of every
                    run at (N', R') is worth 0 in W'.
  worth_key, worth_keyN   the nine keys.

-/
import Johnson.Desc.Kinds.Law.AlikeNorm
import Johnson.Desc.Kinds.Law.Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff World Reading)
open Norm (lt ls d lPd T S2)

/-- The first form's value in the first world is the second's in the second. -/
def SameWorth (W W' : World K) (f f' : Form) : Prop := vW W f = vW W' f'

/-- **It is kept by the forms' arithmetic**, where the two worlds have the same slots. -/
theorem kept_worth (W W' : World K) (hs : ∀ j, W.slot j = W'.slot j) : Kept2 (SameWorth W W') where
  addMul := by
    intro a a' b b' k ha hb
    unfold SameWorth vW at ha hb ⊢
    rw [Aff.value_addMul, Aff.value_addMul, ha, hb]
  bare := by
    intro f hf
    unfold SameWorth vW Aff.value
    rw [hf]
    have e : f.slots.toList.map (OnBytes.Model.slotValue Reading.gl W) =
        f.slots.toList.map (OnBytes.Model.slotValue Reading.gl W') :=
      List.map_congr_left fun x _ => by unfold OnBytes.Model.slotValue; rw [hs]
    rw [e]
    rfl

section All

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard]

/-- The 35 forms in their three runs, as a function of the two fillings. -/
abbrev claimsAt (N : FinalNorm.Reads) (R : Reads) : List (String × List Form) :=
  letI := N
  letI := R
  claims

/-- **FOR ANY KEPT RELATION: ALL 35, RUN BY RUN.** -/
theorem alike_claims {Q : Form → Form → Prop} (C : Kept2 Q) (N N' : FinalNorm.Reads)
    (R R' : Reads) (hN : ∀ r i, i < readLenN r → Q (N.entry r i) (N'.entry r i))
    (hR : ∀ r i, i < readLen r → Q (R.entry r i) (R'.entry r i)) (hd : S2 ∣ d)
    (H : HeardAlike Q) (hl : ∀ S0, Q (logits.left S0) (logits.left S0))
    (he : Q (logits.end_ 0).var (logits.end_ 0).var) :
    ∀ name fs', (claimsAt N' R').lookup name = some fs' → ∀ f', f' ∈ fs' →
      ∃ fs f, (claimsAt N R).lookup name = some fs ∧ f ∈ fs ∧ Q f f' := by
  intro name fs' hlk f' hf'
  unfold claimsAt claims at hlk ⊢
  simp only [List.lookup_cons, List.lookup_nil] at hlk ⊢
  cases h1 : name == "norm" with
  | true =>
    rw [h1] at hlk
    obtain rfl := Option.some.inj hlk
    obtain ⟨f, g1, g2⟩ := alikeN_forms C N N' hN hd H f' hf'
    exact ⟨_, f, rfl, g1, g2⟩
  | false =>
    rw [h1] at hlk
    cases h2 : name == "policy" with
    | true =>
      rw [h2] at hlk
      obtain rfl := Option.some.inj hlk
      obtain ⟨f, g1, g2⟩ := rel_policy C R R' hR f' hf'
      exact ⟨_, f, rfl, g1, g2⟩
    | false =>
      rw [h2] at hlk
      cases h3 : name == "logits" with
      | true =>
        rw [h3] at hlk
        obtain rfl := Option.some.inj hlk
        obtain ⟨f, g1, g2⟩ := rel_logitForms C R R' hR hl he f' hf'
        exact ⟨_, f, rfl, g1, g2⟩
      | false =>
        rw [h3] at hlk
        cases hlk

/-- The two fillings' entries are worth the same, below the lengths spent. -/
structure EntriesAlike (W W' : World K) (N N' : FinalNorm.Reads) (R R' : Reads) : Prop where
  norm : ∀ r i, i < readLenN r → vW W (N.entry r i) = vW W' (N'.entry r i)
  wide : ∀ i, i < wideLenN → vW W (N.wide i) = vW W' (N'.wide i)
  head : ∀ r i, i < readLen r → vW W (R.entry r i) = vW W' (R'.entry r i)

/-- The variables of what was heard, as far as the forms and keys name them, name no entry. -/
structure HeardBare : Prop where
  W : ∀ s, s < 9 → (Norm.W.getD s {}).var.ents = #[]
  P : ∀ n, n < 7 → (Norm.P.getD n {}).var.ents = #[]
  sqLeft : ∀ S0, (Norm.squares.left S0).ents = #[]
  sqEnd : ∀ j, j < 2 → (Norm.squares.end_ j).var.ents = #[]
  prLeft : ∀ S0, (Norm.products.left S0).ents = #[]
  prClaimed : Norm.products.claimed.var.ents = #[]
  prEnd : ∀ j, j < 4 → (Norm.products.end_ j).var.ents = #[]
  nmLeft : ∀ S0, (FinalNorm.normed.left S0).ents = #[]
  nmClaimed : FinalNorm.normed.claimed.var.ents = #[]
  nmEnd : ∀ j, j < 2 → (FinalNorm.normed.end_ j).var.ents = #[]
  lgLeft : ∀ S0, (logits.left S0).ents = #[]
  lgClaimed : logits.claimed.var.ents = #[]
  lgEnd : (logits.end_ 0).var.ents = #[]

theorem heardAlike_of_bare {Q : Form → Form → Prop} (C : Kept2 Q) (B : HeardBare) :
    HeardAlike Q :=
  ⟨fun s h => C.bare _ (B.W s h), fun n h => C.bare _ (B.P n h), fun S0 => C.bare _ (B.sqLeft S0),
    fun j h => C.bare _ (B.sqEnd j h), fun S0 => C.bare _ (B.prLeft S0), C.bare _ B.prClaimed,
    fun j h => C.bare _ (B.prEnd j h), fun S0 => C.bare _ (B.nmLeft S0), C.bare _ B.nmClaimed,
    fun j h => C.bare _ (B.nmEnd j h)⟩

variable (W W' : World K) (hs : ∀ j, W.slot j = W'.slot j) (N N' : FinalNorm.Reads)
  (R R' : Reads) (A : EntriesAlike W W' N N' R R') (B : HeardBare)
include hs A B

/-- **ALL 35 ARE WORTH THE SAME.** -/
theorem worth_claims (hd : S2 ∣ d) :
    ∀ name fs', (claimsAt N' R').lookup name = some fs' → ∀ f', f' ∈ fs' →
      ∃ fs f, (claimsAt N R).lookup name = some fs ∧ f ∈ fs ∧ vW W f = vW W' f' :=
  alike_claims (kept_worth W W' hs) N N' R R' A.norm A.head hd
    (heardAlike_of_bare (kept_worth W W' hs) B) (fun S0 => (kept_worth W W' hs).bare _ (B.lgLeft
    S0))
    ((kept_worth W W' hs).bare _ B.lgEnd)

/-- **WHERE ALL ARE WORTH 0 AT THE ONE FILLING, ALL ARE AT THE OTHER.** -/
theorem zero_claims (hd : S2 ∣ d)
    (h0 : ∀ name fs, (claimsAt N R).lookup name = some fs → ∀ f, f ∈ fs → vW W f = 0) :
    ∀ name fs', (claimsAt N' R').lookup name = some fs' → ∀ f', f' ∈ fs' → vW W' f' = 0 := by
  intro name fs' hl f' hf'
  obtain ⟨fs, f, g1, g2, g3⟩ := worth_claims W W' hs N N' R R' A B hd name fs' hl f' hf'
  rw [← g3]
  exact h0 name fs g1 f g2

/-- **The head's five keys.** -/
theorem worth_key (hJ : JVa ≤ JV) (k : Key) :
    vW W (letI := R; key k) = vW W' (letI := R'; key k) :=
  rel_key (kept_worth W W' hs) R R' A.head hJ ((kept_worth W W' hs).bare _ B.lgClaimed) k

/-- **The normalization's four keys.** -/
theorem worth_keyN (hd : S2 ∣ d) (k : FinalNorm.Key) :
    vW W (letI := N; FinalNorm.key 21 k) = vW W' (letI := N'; FinalNorm.key 21 k) :=
  alikeN_key (kept_worth W W' hs) N N' A.norm A.wide hd
    (heardAlike_of_bare (kept_worth W W' hs) B) k

end All

end VerifiableInference.Desc.Kinds.Head.Law
