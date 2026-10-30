-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoOut.lean.
What the typed verifier of the sub-proofs' lookup puts out, in the record of end values, with no
hypothesis but on public
numbers and on the caller's layout.

* `OutIs h L lm jLK ι Ex a τ`: on the statement a and the transcript τ the verifier `forB` (the
short sumcheck filled by `V₀`,
  `V₀C`) does not refuse, copies the oracles, and with En the end values `endsOf` at the transcript
    read as plain data:
  the state put out is the caller's with En.theta; the rows are En's tie rows, key rows and table
  rows (each group in the reverse order), then the leaves' row, En.bitU, the bits' end row and the
  row of the counts' sum, the places renamed along ι, each sparse row spread; the masked claim
    on the keys has the weights
  of the point (En.zy, En.zx), the form En.cEndF on the mask entries, and the target En.alpha -
    En.cEndC.
* `HCout1E`: a closed proposition: `OutIs` at every lawful shape (`FoNums.ok h`), every layout whose
mask places and cells are
  given by two maps mk, pl, every statement and every transcript. `hcOut1E`: its proof.
* `hcOut1E_made`: the hypotheses on the layout are met by the layout that is made from mk and pl, so
the statement is not empty.

Not claimed here: that the byte-level routine returns the same end values (`Fo.HCout2`, stated in
OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean, proved in OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoRead
import OnBytes.Tie.Pv.Lookup.Forest.FoEnds
import OnBytes.Tie.Pv.Lookup.Forest.FoNumsEq

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- The out-statement, in the record of end values. -/
def OutIs (h : FoNums.Sh) (L : Lay E St₀ J₀) (lm jLK : ℕ) (ι : Pl → Option J₀) (Ex : ExtSpec)
    (a : St₀ × Ex.Str) (τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape) : Prop :=
  ∃ x : TX (St₀ × E) E (Option J₀),
    (forB E h L V₀ V₀C (Ex := Ex)).R.red.out a τ = some (x, a.2) ∧
    x.1 = (a.1, (endsOf h lm jLK (forFl h L Ex τ)).theta) ∧
    x.2.2 = (((endsOf h lm jLK (forFl h L Ex τ)).tieRows.reverse ++
      ((endsOf h lm jLK (forFl h L Ex τ)).keyRows.reverse ++
        (((endsOf h lm jLK (forFl h L Ex τ)).tabRows.reverse ++
          [rowEnd (forN h lm jLK (forFl h L Ex τ)) (forTrace h lm jLK (forFl h L Ex τ)),
            (endsOf h lm jLK (forFl h L Ex τ)).bitU,
            rowBitE (forN h lm jLK (forFl h L Ex τ)) (forTrace h lm jLK (forFl h L Ex τ))]) ++
          [rowNum (forN h lm jLK (forFl h L Ex τ))]))).map (rowMap ι)).map toRow ∧
    (∀ X < 2 ^ (FoNums.v' h + 1), Blocks.eqN (FoNums.v' h + 1) 0 x.2.1.pt X =
      TwV.eqN ((endsOf h lm jLK (forFl h L Ex τ)).zy.reverse ++
        (endsOf h lm jLK (forFl h L Ex τ)).zx.reverse) X) ∧
    (∀ j, x.2.1.mf j = dense (mapL ι (endsOf h lm jLK (forFl h L Ex τ)).cEndF) j) ∧
    x.2.1.tg = (endsOf h lm jLK (forFl h L Ex τ)).alpha - (endsOf h lm jLK (forFl h L Ex τ)).cEndC

theorem outIs_of (h : FoNums.Sh) (L : Lay E St₀ J₀) (lm jLK : ℕ) (ι : Pl → Option J₀)
    (hN : ∀ (st : St₀) (θ : E), PlacesAre (forA E h L) (st, θ) ι (numsF h lm jLK θ)) (Ex : ExtSpec)
    (a : St₀ × Ex.Str) (τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape) :
    OutIs h L lm jLK ι Ex a τ := by
  obtain ⟨x, h1, h2, h3, h4, h5, h6⟩ := hcOut1 E St₀ J₀ h L lm jLK ι hN Ex a τ
  refine ⟨x, h1, h2, ?_, ?_, h5, h6⟩
  · rw [h3, ← ends_r16]
    rfl
  · intro X hX
    rw [h4 X hX]
    show _ = TwV.eqN (((pntK _ _).take h.rK).reverse.reverse ++ ((pntK _ _).drop
        h.rK).reverse.reverse) X
    rw [List.reverse_reverse, List.reverse_reverse, List.take_append_drop]

end

/-- The typed verifier's out-statement is the flat function's record of end values: a closed
proposition. -/
def HCout1E : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh)
    (L : Lay E St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀),
    FoNums.ok h = true → (∀ s, L.mkS s = mk (jLK + s)) →
    (∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2) →
    ∀ (Ex : ExtSpec) (a : St₀ × Ex.Str) (τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape),
      OutIs h L lm jLK (placeOf mk pl) Ex a τ

theorem hcOut1E : HCout1E := by
  intro E _ _ St₀ J₀ _ _ h L lm jLK mk pl H hmk hbc Ex a τ
  exact outIs_of h L lm jLK (placeOf mk pl)
    (fun st θ => numsOf_forA E h L lm jLK mk pl (ok_parts H).1.1 hmk hbc st θ _) Ex a τ

/-- The hypotheses on the layout are met by the layout made from the two maps. -/
theorem hcOut1E_made (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀]
    (h : FoNums.Sh) (K : St₀ → (J₀ → E) → ℕ → ℕ → E) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (H : FoNums.ok h = true) (Ex : ExtSpec) (a : St₀ × Ex.Str)
    (τ : Tr (forB E h (⟨K, fun t c j => pl (FoNums.cellRC h lm (t, c, j)).1
      (FoNums.cellRC h lm (t, c, j)).2, fun s => mk (jLK + s)⟩ : Lay E St₀ J₀) V₀ V₀C (Ex :=
          Ex)).R.shape) :
    OutIs h (⟨K, fun t c j => pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2,
      fun s => mk (jLK + s)⟩ : Lay E St₀ J₀) lm jLK (placeOf mk pl) Ex a τ :=
  hcOut1E E St₀ J₀ h _ lm jLK mk pl H (fun _ => rfl) (fun _ _ _ _ => rfl) Ex a τ

end Fo
