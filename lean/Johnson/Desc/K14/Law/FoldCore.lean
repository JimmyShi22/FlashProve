-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/FoldCore.lean: THE CHANCE OF "LIN zeta", WITH NO KIND NAMED: a block at one
stretch whose written round reads as one typed draw of a point z; two vectors omega and u that the
statement in front pins; behind the block (fold)'s equation at z. Then, but for the points that the
count foldCatches bounds, omega is col_psi_lo(u) on the rows of M. In the form of the rule of
composition (Piece.GoodIn), by the bridge goodIn_of_count (Johnson/Desc/K14/Law/Bridge.lean).

EVERYTHING THAT READS A RECORD IS A LETTER: psiLo, zfd (the lower part of the shared point; the
point noted), om, u (the two vectors, off a statement and a witness), the two promises on | on', the
two pins PinA | PinB. So the law can be called at any record, at any type of claims, over any text
of the block.

  ColIs S psiLo om u   omega is col_psi_lo(u) on the rows of M.
  fold_core            **the law.**
What is not claimed. PREMISES. Under the promise in front: a yes keeps the promise (hon); a witness
pinned behind is pinned in front (hback); two witnesses pinned by one statement give the same two
vectors (hdet); a yes turns neither psiLo nor the two vectors (hstay); the point noted behind is the
point drawn, read off the written round as one typed draw (G, hread). BARE, at every statement: the
extractor is the identity (hext); the errors fit the count (fits). ON THE PLAN: M has at most
2 ^ kRow rows (hR); the count c is at least kRow * q ^ (kRow - 1) (hc): c, and with it the piece's
errors, are bounded FROM BELOW alone: a larger count is a weaker law. All are letters: no member is
shown here. A block that refuses all has GoodIn too. No
soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Catches
import Johnson.Desc.K14.Law.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open Iop Prob OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)
open Iop.IOR (drawRound)

variable {K : Type} [Field K]

/-- omega is col_psi_lo(u) on the rows of M. -/
def ColIs (S : LinShape) (psiLo : List K) (om u : Nat → K) : Prop :=
  ∀ j < S.matrixRows, om j = ∑ t ∈ Finset.range (2 ^ S.kLo), eqK psiLo t * u (t + 2 ^ S.kLo * j)

variable {T Cl W : Type} {C : CK} {F : Frame}

open Classical in
/-- **The chance of "LIN zeta", with no kind named.** -/
theorem fold_core [Fintype K] (pc : Piece C F T Cl W) (S : LinShape)
    (hR : S.matrixRows ≤ 2 ^ S.kRow) (hext : ∀ a τ w, pc.ext a τ w = w)
    (on on' : T × F.E.Str → Prop) (PinA PinB : T × F.E.Str → W → Prop)
    (psiLo zfd : T × F.E.Str → List K) (om u : T × F.E.Str → W → Nat → K)
    (hon : ∀ a τ b, on a → pc.ior.red.out a τ = some b → on' b)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → PinB b w → PinA a w)
    (hdet : ∀ a w w', on a → PinA a w → PinA a w' → om a w' = om a w ∧ u a w' = u a w)
    (hstay : ∀ a τ b w, on a → pc.ior.red.out a τ = some b →
      psiLo b = psiLo a ∧ om b w = om a w ∧ u b w = u a w)
    (c : Nat) (hc : S.kRow * Fintype.card K ^ (S.kRow - 1) ≤ c)
    (G : T × F.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin S.kRow → K)])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ a τ b, on a → pc.ior.red.out a τ = some b →
      ∃ z, (G a).tr τ = some (((), ()), z, ()) ∧ zfd b = List.ofFn z) :
    pc.GoodIn on on' (fun a w => PinA a w ∧ ColIs S (psiLo a) (om a w) (u a w))
      (fun b w => PinB b w ∧ FoldEq S (psiLo b) (zfd b) (om b w) (u b w)) := by
  refine goodIn_of_count pc _ _ _ _ (Fin S.kRow → K) c G fits
    (fun a z => ∃ w, PinA a w ∧ ¬ ColIs S (psiLo a) (om a w) (u a w) ∧
      FoldEq S (psiLo a) (List.ofFn z) (om a w) (u a w)) ?_ ?_
  · intro a ha
    by_cases hw0 : ∃ w0, PinA a w0 ∧ ¬ ColIs S (psiLo a) (om a w0) (u a w0)
    · obtain ⟨w0, hp0, hn0⟩ := hw0
      have hgap : ∃ j < S.matrixRows, om a w0 j ≠
          ∑ t ∈ Finset.range (2 ^ S.kLo), eqK (psiLo a) t * u a w0 (t + 2 ^ S.kLo * j) := by
        unfold ColIs at hn0
        push Not at hn0
        exact hn0
      refine le_trans (cnt_mono fun z hzl => ?_) (le_trans (le_trans (le_of_eq (cnt_eq_card _))
        (foldCatches S (psiLo a) (om a w0) (u a w0) hR hgap)) hc)
      obtain ⟨w, hp, _, hf⟩ := hzl
      obtain ⟨eO, eU⟩ := hdet a w0 w ha hp0 hp
      rw [← eO, ← eU]
      exact hf
    · rw [cnt_false fun z hzl => hw0 (by obtain ⟨w, hp, hn, _⟩ := hzl; exact ⟨w, hp, hn⟩)]
      exact Nat.zero_le _
  · intro a τ b ha hout
    obtain ⟨z, htr, hzs⟩ := hread a τ b ha hout
    refine ⟨_, htr, fun hnl => ⟨hon a τ b ha hout, fun w hw => ?_⟩⟩
    obtain ⟨hpin, hf⟩ := hw
    have hpa := hback a τ b w ha hout hpin
    obtain ⟨e1, e2, e3⟩ := hstay a τ b w ha hout
    rw [hext]
    refine ⟨hpa, ?_⟩
    by_contra hn
    refine hnl ⟨w, hpa, hn, ?_⟩
    rw [e1, e2, e3, hzs] at hf
    exact hf

end Desc.K14.Law
