-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ConstrBackAt9.lean: "THE CONSTRAINTS' SENTENCE GOES BACK"
(the premise hconstr of the tie at the first segment's opening) AT THE COMPOSED FILLING `mgAll 𝔇
Mg`, AT EVERY SEGMENT AND CONSTRAINT, OUT OF PLAIN SENTENCES ON FOUR OF ITS LETTERS. One statement
with its proof. WHY. hconstr is bound at every segment m and constraint c, though the row lets
pass only what is open. By the composed term's own text (`mgAll_constr`;
`P5J.constrQAt`, Johnson/P5J/MeansQ.lean) the sentence reads the verifier's state through four
letters alone: the decoder, `H.req`, `headPart`, `digitsPart`. So the wide binding is harmless
wherever these four do not mind the step. `constr_back_at9`: between two statements x, x' with one
  public part and two strings y, y' with the same cells: WHERE the decoder reads the public part
  alone (hdec); `𝔇.H.req` answers alike at x and x' (hreq); `𝔇.digitsPart` and `𝔇.headPart` go
  back from (x', y') to (x, y) (hdig, hhead).
What is not claimed. The four at any data. [By reading, at the closed letters of Johnson/P5J/:
`digitsPartK3` reads neither the state nor the strings; `headPartK6` reads the state through
`H.req` and, at one part alone, through the token of the reply that the state has heard.] Nothing
on soundness.
-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.K13.Law.SigDecodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MgData mgAll mgAll_constr CellsQ MsgT)
open VerifiableInference.Desc.K13.Law (DecBlind)

/-- **The constraints' sentence goes back.** -/
theorem constr_back_at9 {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    (hdec : DecBlind 𝔇.decT) {x x' : P × S} {y y' : Strs}
    {w : Wit (CellsQ rows cols) Tok MsgT} (h1 : x'.1 = x.1) (hc : y'.cell = y.cell)
    (hreq : 𝔇.H.req x' = 𝔇.H.req x)
    (hdig : ∀ k, 𝔇.digitsPart k x' y' w → 𝔇.digitsPart k x y w)
    (hhead : ∀ p i, 𝔇.headPart p i x' y' w → 𝔇.headPart p i x y w) (m : ℕ) (c : P5J.TPart)
    (h : (mgAll 𝔇 Mg).constr m c x' y' w) : (mgAll 𝔇 Mg).constr m c x y w := by
  rw [mgAll_constr] at h ⊢
  unfold P5J.constrQAt at h ⊢
  have hd : 𝔇.decT y'.cell x' = 𝔇.decT y.cell x := by
    obtain ⟨z, s⟩ := x
    obtain ⟨z', s'⟩ := x'
    obtain rfl : z' = z := h1
    rw [hc]
    exact hdec _ _ _ _
  split at h
  · rename_i hp
    rw [if_pos hp]
    exact hdig m h
  · rename_i hp
    rw [if_neg hp]
    refine ⟨h.1, fun M i hM hH => ?_⟩
    have h2 := h.2 M i (hd.trans hM) hH
    split at h2
    · rename_i hk
      rw [if_pos hk]
      exact hhead c i h2
    · rename_i hk
      rw [if_neg hk]
      have e : (Sound.oneDec 𝔇.decT 𝔇.H).req x' = (Sound.oneDec 𝔇.decT 𝔇.H).req x := hreq
      rw [e] at h2
      exact h2

end HashBuild
