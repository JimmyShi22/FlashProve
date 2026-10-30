-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TieFourPays.lean: code switching: THREE SMALL PREMISES OF THE FOURTH TIE AT
A PLACE (`k02_t4R`, K2Caller/TieFourR.lean), each with the end of its binder there to the letter.
Three theorems with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  fit_fam         (its FtF) `Fit` at every frame that is the written frame W with other numbers of
                  messages, at the law's own three readings memK · rowK · plK: from two tests with
                  code at W (r.keptAt W · fitAt r W). After the pattern of `caller_fam`
                  (K2Caller/OnTopFacts.lean)
  olds_at_frame   (its ho) at the written frame with the place's own numbers (`placeFrame`,
                  K2Hands/FrontB2.lean) the entry of a held member has, as its old number, the
                  entry of olds at the member's place in r.kept: from r.keptAt W and
                  olds.length = r.kept.length
  positions_pos   (its hpos) the count of positions at r is positive: from `P2At r p`
                  (K2Caller/P2At.lean) and the kind's test on the list of rounds at p
LIMITS. r.keptAt W, fitAt r W, olds.length = r.kept.length, P2At r p and the kind's test are
premises: facts on public data, shown by nobody here. The tie's other premises are not touched. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.OnTopFacts
import Johnson.Top.H0.K2Caller.SmpK2
import Johnson.Top.H0.K2Caller.SlotIs
import Johnson.Top.H0.K2Caller.P2At
import Johnson.Top.H0.K2Hands.FrontB2
import Johnson.Top.H0.K2Hands.AtYes
import Johnson.G.SwitchSampleTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands

/-- **`Fit` at every frame of the family, at the law's own three readings.** -/
theorem fit_fam {r : SwRow} (H : r.OK) {W : SwitchFrame} (hk : r.keptAt W = true)
    (hf : fitAt r W = true) (W₀ : SwitchFrame) (hW : Renumbered W W₀) :
    Fit r.cs r.l (plainR r H).s W₀ (memK (r := r) (H := H)) rowK (plK W₀) := by
  obtain ⟨g, olds, anew, rfl⟩ := hW
  have F := (fit_renumber W g olds anew _ _ _ _ _ _).2
    (fit_idx H hk (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ hf)
  rw [plRe_idx H hk (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ g olds
      anew] at F
  exact F

/-- **The old number of a held member's entry, at the written frame with the place's own
numbers.** -/
theorem olds_at_frame {r : SwRow} (H : r.OK) {W : SwitchFrame} {n0 : ℕ} {olds : List ℕ}
    (hk : r.keptAt W = true) (hl : olds.length = r.kept.length)
    (κ : {a // (plainHd r H).cl a}) :
    olds[r.kept.idxOf κ.1.1.val]? = some (keptK2 r H (placeFrame W n0 olds) κ).old := by
  have hm : κ.1.1.val ∈ r.kept := κ.2.snd
  obtain ⟨hn, -⟩ := List.getElem?_eq_some_iff.1 (List.getElem?_idxOf hm)
  obtain ⟨k0, hk0⟩ : ∃ k0, W.kept[r.kept.idxOf κ.1.1.val]? = some k0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [Johnson.G.kept_len hk]; exact hn)⟩
  obtain ⟨o, ho⟩ : ∃ o, olds[r.kept.idxOf κ.1.1.val]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by rw [hl]; exact hn)⟩
  have e : keptK2 r H (placeFrame W n0 olds) κ =
      reAt olds.toArray (newsAt n0 W.kept.length) (r.kept.idxOf κ.1.1.val) k0 := by
    show (placeFrame W n0 olds).kept.getD (r.kept.idxOf κ.1.1.val) _ = _
    unfold placeFrame
    rw [List.getD_eq_getElem?_getD, renumber_kept, hk0]
    rfl
  rw [e, ho]
  show some o = some (olds.toArray.getD (r.kept.idxOf κ.1.1.val) noId)
  simp [Array.getD_eq_getD_getElem?, ho]

/-- **The count of positions is positive.** -/
theorem positions_pos {Cl : Type} {r : SwRow} {p : K2.P2} (hP : P2At r p)
    (h : (K2.codeSwitchKind (Cl := Cl) p).planOk = true) : 0 < baseCount r.set .request r.g := by
  have h1 : ∀ a b c d : Bool, (a && b && c && d) = true → a = true := by
    intro a b c d e
    cases a
    · simp at e
    · rfl
  have h0 : 0 < p.positions := of_decide_eq_true (h1 _ _ _ _ h)
  rw [← hP.positions]
  exact h0

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.fit_fam
#print axioms VerifiableInference.Desc.First.K2Caller.olds_at_frame
#print axioms VerifiableInference.Desc.First.K2Caller.positions_pos
