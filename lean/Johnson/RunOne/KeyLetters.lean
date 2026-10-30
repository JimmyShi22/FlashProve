-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyLetters.lean: DEFINITIONS AND THEOREMS. **A decoder and its condition for the oracle messages that a chain has sent, in the library's own terms**: from what the law of a sending leaves behind
(Sealed: the statement's record holds the kind's one sample row at a seed, and no two members of the library's list of the word sent answer alike at that seed).
  Cand      a candidate for message o at a statement St and a word f: a member of the library's list of f (OMsg.InList at the radius e) of which, read as the message's two tables (tabOf), every sample row that the record holds under o says its claim
  decAt     the decoder: a candidate if there is one (a choice); none otherwise
  cand_unique   **under Sealed there is at most one candidate** (unique_port')
  decAt_eq      so under Sealed the decoder returns EVERY candidate that anybody exhibits: whoever extracts a member of the list that meets the sample row has extracted the decoder's value
  decAt_cand    what the decoder returns is a candidate
  Two, dec₂, cond₂, wd₂   two messages side by side, with a third part (the committed matrix) whose own decoder is a letter: the letters M | dec | cond | wd | mx of a row that rides through the lookups
  dec₂_blind | cond₂_blind   they read of the riding part the statement alone
  dec₂_low | cond₂_low       they read of the strings what the two readers of words and the third part's decoder read
  dec₂_eq       **under cond₂: dec₂ returns the triple of any two candidates and the third decoder's value**
What is not claimed. That a candidate exists (an honest prover's word has one: not shown here). How a frame's strings are read as the typed words (f₀, f₁: letters). The third part's decoder. Nothing on soundness.

-/
import Johnson.RunOne.KeySendGood

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1

/-- A candidate. -/
def Cand (cs : Codes) (s : OracleShape) (e : Nat) (f : (portOmZ cs s e).Str) (St : Statement) (o : Nat) (msg : (portCode cs s).J → GE) : Prop :=
  (portOmZ cs s e).InList f msg ∧ ∃ w : Means.Words GE, w o = tabOf cs s msg ∧ ∀ x, St.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, Means.Says rdE St r w

/-- The decoder. -/
def decAt (cs : Codes) (s : OracleShape) (e : Nat) (f : (portOmZ cs s e).Str) (St : Statement) (o : Nat) : Option ((portCode cs s).J → GE) :=
  open Classical in if h : ∃ msg, Cand cs s e f St o msg then some h.choose else none

variable {cs : Codes} {s : OracleShape} {e : Nat} {f : (portOmZ cs s e).Str} {St : Statement} {o : Nat}

theorem cand_unique (hT : Tie cs s) (hS : Sealed cs s e f St o) {msg msg' : (portCode cs s).J → GE} (h : Cand cs s e f St o msg) (h' : Cand cs s e f St o msg') : msg = msg' := by
  obtain ⟨ρ, y, ⟨hc, x, z, β, t, hx, hs, _, hr, hread, _⟩, hno⟩ := hS
  obtain ⟨hl, w, hw, hsay⟩ := h
  obtain ⟨hl', w', hw', hsay'⟩ := h'
  have hm : sampleRow (Msg.of cs s) o z β 0 t ∈ x.sampleRows.toList := by rw [hr]; simp
  exact unique_port' St o x hx cs s hc hs hT e f z β t ρ hread hno w w' msg msg' hw hw' hl hl' (hsay x hx _ hm) (hsay' x hx _ hm)

theorem decAt_cand {msg : (portCode cs s).J → GE} (h : decAt cs s e f St o = some msg) : Cand cs s e f St o msg := by
  unfold decAt at h
  split at h
  · rename_i hh
    rw [← Option.some.inj h]
    exact hh.choose_spec
  · cases h

theorem decAt_eq (hT : Tie cs s) (hS : Sealed cs s e f St o) {msg : (portCode cs s).J → GE} (h : Cand cs s e f St o msg) : decAt cs s e f St o = some msg := by
  have hh : ∃ m, Cand cs s e f St o m := ⟨msg, h⟩
  unfold decAt
  rw [dif_pos hh]
  exact congrArg some (cand_unique hT hS hh.choose_spec h)

/-! ## Two messages and a third part -/

section two
variable (cs : Codes) (s₀ s₁ : OracleShape) (e₀ e₁ o₀ o₁ : Nat) {X Y MW : Type} (stOf : X → Statement)
  (f₀ : Y → (portOmZ cs s₀ e₀).Str) (f₁ : Y → (portOmZ cs s₁ e₁).Str) (decW : Y → Option MW)

/-- What is decoded: the two messages and the third part. -/
abbrev Two (cs : Codes) (s₀ s₁ : OracleShape) (MW : Type) : Type := ((portCode cs s₀).J → GE) × ((portCode cs s₁).J → GE) × MW

def dec₂ (a : X × Y) : Option (Two cs s₀ s₁ MW) :=
  (decAt cs s₀ e₀ (f₀ a.2) (stOf a.1) o₀).bind fun u₀ => (decAt cs s₁ e₁ (f₁ a.2) (stOf a.1) o₁).bind fun u₁ => (decW a.2).map fun m => (u₀, u₁, m)

def cond₂ (a : X × Y) : Prop := Sealed cs s₀ e₀ (f₀ a.2) (stOf a.1) o₀ ∧ Sealed cs s₁ e₁ (f₁ a.2) (stOf a.1) o₁

/-- The words of what is decoded: the two messages' tables under their numbers; 0 elsewhere. -/
def wd₂ (u : Two cs s₀ s₁ MW) : Means.Words GE := fun o => if o = o₀ then tabOf cs s₀ u.1 else if o = o₁ then tabOf cs s₁ u.2.1 else fun _ _ => 0

variable {cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW}

theorem dec₂_blind {x x' : X} (y : Y) (h : stOf x = stOf x') : dec₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW (x, y) = dec₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW (x', y) := by
  unfold dec₂
  simp only [h]

theorem cond₂_blind {x x' : X} (y : Y) (h : stOf x = stOf x') : cond₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (x, y) ↔ cond₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (x', y) := by
  unfold cond₂
  simp only [h]

theorem dec₂_low (x : X) {y y' : Y} (h₀ : f₀ y = f₀ y') (h₁ : f₁ y = f₁ y') (hW : decW y = decW y') :
    dec₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW (x, y) = dec₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW (x, y') := by
  unfold dec₂
  simp only [h₀, h₁, hW]

theorem cond₂_low (x : X) {y y' : Y} (h₀ : f₀ y = f₀ y') (h₁ : f₁ y = f₁ y') : cond₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (x, y) ↔ cond₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (x, y') := by
  unfold cond₂
  simp only [h₀, h₁]

theorem dec₂_eq (hT₀ : Tie cs s₀) (hT₁ : Tie cs s₁) {a : X × Y} (hc : cond₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ a) {u₀ : (portCode cs s₀).J → GE} {u₁ : (portCode cs s₁).J → GE} {m : MW}
    (h₀ : Cand cs s₀ e₀ (f₀ a.2) (stOf a.1) o₀ u₀) (h₁ : Cand cs s₁ e₁ (f₁ a.2) (stOf a.1) o₁ u₁) (hW : decW a.2 = some m) :
    dec₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW a = some (u₀, u₁, m) := by
  unfold dec₂
  rw [decAt_eq hT₀ hc.1 h₀, decAt_eq hT₁ hc.2 h₁, hW]
  rfl

end two

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.cand_unique
#print axioms Johnson.RunOne.KeyLetters.decAt_cand
#print axioms Johnson.RunOne.KeyLetters.decAt_eq
#print axioms Johnson.RunOne.KeyLetters.dec₂_blind
#print axioms Johnson.RunOne.KeyLetters.cond₂_blind
#print axioms Johnson.RunOne.KeyLetters.dec₂_low
#print axioms Johnson.RunOne.KeyLetters.cond₂_low
#print axioms Johnson.RunOne.KeyLetters.dec₂_eq
