-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorBeside.lean: SH₃ WITH BOTH LETTERS LAID AS TERMS: PLm := `fillZ …`, and
the shared table's promise := whatever stands there with `doorX p K` laid beside its `shape`
(`besideP`, Johnson/Desc/Sound/LedgerBeside.lean), K the chain's last border as the table writes it.
Statements and proofs; no definition. FIVE NAMED PREMISES ARE LEFT, PAID NOWHERE; AND THE LAYING HAS
ITS PRICE.

Main names (namespace `VerifiableInference.Desc.Last`).
  `doorX_at`: at the border K the test by borders is the text. `doorX_off`: at every other border it
    says yes: so every block but the last hands it on for nothing.
  `bears_beside`: `(besideP Pm₀ (doorX p K)).shape K d = true` gives `doorSharedB p d = true`: the
    premise hPm of `sh₃_at_texts` (Johnson/Desc/Last/ShapeDoorAtTexts.lean), by the make.
  **`sh₃_at_beside`**: SH₃'s line at PLm := `fillZ p R fun q => (get q).2`, Pm := `besideP Pm₀
    (doorX p (1 + T.l₂.length))`, Oc := `ocEnd get N₁ Mg₁ links ps`, under the other five: hitem,
    hopen, hmark, hstart, ahead.

THE PRICE OF THE LAYING. Whoever lays a test beside `shape` owes, block by block, that it is handed
on for certain (`clause_beside`'s hX). For `doorX p K` that is nothing at every block but the last
(`doorX_off`); THE SHARED CHAIN'S LAST BLOCK OWES: inside the promise in front, at its yes,
`doorSharedB p` holds of the record behind: the five tests where the chain has ended: NOT TYPED.
Limits. Those of ShapeDoorAtTexts.lean. Pm₀ is a letter still: what else stands in the shared
promise is other files' to say. NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorAtTexts
import Johnson.Desc.Sound.LedgerBeside

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (Meaning Numbers ModelPart moreItem nDoor pubSets)
open _root_.Desc.K14 (St)

/-- At the border K the test by borders is the text. -/
theorem doorX_at (p : P₁₄) (K : ℕ) (d : St) : doorX p K K d = doorSharedB p d := by
  simp [doorX]

/-- At every other border it says yes. -/
theorem doorX_off (p : P₁₄) {K k : ℕ} (h : k ≠ K) (d : St) : doorX p K k d = true := by
  simp [doorX, h]

/-- With the test laid beside, the shared table's `shape` at K bears the text. -/
theorem bears_beside (p : P₁₄) (K : ℕ) (Pm₀ : PromMeaning St) (d : St)
    (h : (besideP Pm₀ (doorX p K)).shape K d = true) : doorSharedB p d = true := by
  have h' : (Pm₀.shape K d && doorX p K K d) = true := h
  rw [doorX_at] at h'
  exact (Bool.and_eq_true_iff.1 h').2

/-- **SH₃ WITH BOTH LETTERS LAID, UNDER FIVE PREMISES.** -/
theorem sh₃_at_beside {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁ P₀ X₁ X₂ Cl Wt W₁ : Type}
    (p : P₁₄) (R : List Fmt.DeclaredRound) (get : P × S₁ → P₀ × First.S)
    (start₃ : P → S₁ → St → Option S₃)
    (T : Three C D all Y (P × S₁) ((P × S₁) × St) ((P × S₁ × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm₀ : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place)
    (hitem : ∀ a, Mg₁.pub (moreItem nDoor) a = doorFirstB a.2)
    (hopen : moreItem nDoor ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hmark : ∀ q s₁ d s, start₃ q s₁ d = some s → (get (q, s₁)).2.failed = none)
    (hstart : ∀ q s₁ d s, start₃ q s₁ d = some s →
      ∃ e, _root_.Desc.K14.ended d = some e ∧ startAtEnds p q (get (q, s₁)).2 e = .ok s)
    (ahead : p.S.masksAhead = true)
    (b : ((P × S₁) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N (besideP Pm₀ (doorX p (1 + T.l₂.length))) (ocEnd get N₁ Mg₁ links ps) split T.p₂
      T.l₂ (1 + T.l₂.length) b)
    (hs : start₃ b.1.1.1 b.1.1.2 b.1.2 = some s) :
    (fillZ p R fun q => (get q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true :=
  sh₃_at_texts p R get start₃ T N _ split N₁ Mg₁ links ps
    (bears_beside p (1 + T.l₂.length) Pm₀) hitem hopen hmark hstart ahead b s hb hs

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.doorX_at
#print axioms VerifiableInference.Desc.Last.doorX_off
#print axioms VerifiableInference.Desc.Last.bears_beside
#print axioms VerifiableInference.Desc.Last.sh₃_at_beside
