-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastWords.lean: the words of the key file's last chain, read off its witness, a pair: at Omega's number the shared half's words
at number 2, at every other number the first half's. So the first chain's items and the shared chain's meet in one family.

Main names.
  `wordsKey`, `omK`, `wvK`, `OkKey`: the family of `Reads` (Johnson/Desc/Third/Law/Row0Words.lean) and its fence.
  `mlKey`: the letter of the last chain's own item.
  `reads_key`: `Reads` at this family.
  `ok_A0`, `ok_of_shape`: the fence at the written shape.
  `dotSem_key`: (Dot) in the last chain's form, from the shared chain's `DotOmAt`.

What stays open. val₁: the reader of the first half. vW: W's number.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastExchangeW
import E2E.KeyLastValues
import Johnson.Desc.Third.Law.Row0DotOm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open OnBytes.Slice (GE rdE)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law (Says Reads DotSem RowsHold BorderIs omOf dotSem_of_dotOmAt)
open VerifiableInference.Desc.Last (MeaningL)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt omegaOf)
open AtPublicFiles.AtFiles (Sh₃ sh₃ SF CF)
open AtPublicFiles.AtFiles.Full (A0)

section
variable {Wt₁ : Type} (val₁ : Wt₁ → Nat → Part → Nat → GE)

/-- **The words at a record.** -/
def wordsKey (s : S₃) (u : Wt₁ × Words GE) : Words GE := fun o pt i =>
  if o = s.loc.omega then u.2 2 pt i else val₁ u.1 o pt i

/-- Omega's reader. -/
def omK (S : LinShape) (cs : Codes) : Wt₁ × Words GE → Nat → GE := fun u y =>
  u.2 2 .main ((linLayOmega cs S).index y)

/-- W's reader. -/
def wvK (S : LinShape) (cs : Codes) (vW : Nat) : Wt₁ × Words GE → Nat → GE := fun u c =>
  val₁ u.1 vW .main ((linLayW cs S).index c)

/-- The fence: what the records in front hold. -/
def OkKey (cs : Codes) (vW : Nat) (s _s' : S₃) : Prop :=
  s.st.codes = cs ∧ s.loc.w = vW ∧ s.loc.w < s.st.oracles.size ∧ s.st.oracles.size ≤ s.loc.omega

/-- The letter of the chain's own item. -/
def mlKey : MeaningL S₃ (Wt₁ × Words GE) := ⟨fun s u => RowsHold rdE s (wordsKey val₁ s u)⟩

/-- **The family reads.** -/
theorem reads_key (p : P₁₄) (cs : Codes) (vW : Nat) :
    Reads p (OkKey cs vW) (wordsKey val₁) (omK p.S cs) (wvK val₁ p.S cs vW) := by
  have hom : ∀ s s', Says p s s' → s'.loc.omega = s.st.oracles.size := fun s s' h => by
    obtain ⟨_, _, _, _, _, hl, _⟩ := h
    rw [hl]
  refine ⟨fun s s' u ok h o ho part i => ?_, fun s s' u ok h y _ => ?_, fun s s' u ok h c _ => ?_⟩
  · obtain ⟨-, -, -, h4⟩ := ok
    have a : o ≠ s'.loc.omega := by
      rw [hom s s' h]
      omega
    have b : o ≠ s.loc.omega := by omega
    unfold wordsKey
    rw [if_neg a, if_neg b]
  · obtain ⟨h1, -, -, -⟩ := ok
    unfold wordsKey omK
    rw [if_pos (hom s s' h).symm, h1]
  · obtain ⟨h1, h2, h3, -⟩ := ok
    have a : s.loc.w ≠ s'.loc.omega := by
      rw [hom s s' h]
      omega
    unfold wordsKey wvK
    rw [if_neg a, h1, h2]

/-- **(Dot) in the last chain's form.** -/
theorem dotSem_key (p : P₁₄) (cs : Codes) (vW : Nat) (g : Nat → GE) (d : St) (s : S₃) (b : VerifiableInference.Desc.Third.Border)
    (hb : s.loc.border = some b) (T : BorderIs g d s) (u : Wt₁ × Words GE)
    (h : DotOmAt p.S g d u.2 (wvK val₁ p.S cs vW u)) (h2 : d.loc.oOmega = 2) (hc : d.st.codes = cs) :
    DotSem rdE p (omK p.S cs) (wvK val₁ p.S cs vW) s u := by
  have e : omOf p.S d (fun w : Wt₁ × Words GE => w.2) = omK p.S cs := by
    funext w y
    show w.2 d.loc.oOmega .main ((linLayOmega d.st.codes p.S).index y) = _
    rw [h2, hc]
    rfl
  have r := dotSem_of_dotOmAt p g d s (fun w : Wt₁ × Words GE => w.2) (wvK val₁ p.S cs vW) u T b hb h
  rw [e] at r
  exact r

end

theorem ok_A0 : A0.2.w < A0.1.st.oracles.length ∧ A0.1.st.oracles.length ≤ A0.2.omega := by decide +kernel

/-- **The fence at the written shape.** -/
theorem ok_of_shape {s s' : S₃} (hsh : sh₃ SF s = A0) : OkKey CF A0.2.w s s' := by
  have hc : s.st.codes = CF := (congrArg (fun a : Sh₃ => a.1.st.codes) hsh).trans codes_A0
  have hw : s.loc.w = A0.2.w := congrArg (fun a : Sh₃ => a.2.w) hsh
  have ho : s.loc.omega = A0.2.omega := congrArg (fun a : Sh₃ => a.2.omega) hsh
  have hl : s.st.oracles.size = A0.1.st.oracles.length := by
    have q : (stSh s.st).oracles.length = A0.1.st.oracles.length :=
      congrArg (fun a : Sh₃ => a.1.st.oracles.length) hsh
    rw [← q]
    show _ = (s.st.oracles.toList.map orcSh).length
    simp
  refine ⟨hc, hw, ?_, ?_⟩
  · rw [hw, hl]
    exact ok_A0.1
  · rw [hl, ho]
    exact ok_A0.2

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.reads_key
#print axioms AtPublicFiles.KeyLastChain.dotSem_key
#print axioms AtPublicFiles.KeyLastChain.ok_A0
#print axioms AtPublicFiles.KeyLastChain.ok_of_shape
