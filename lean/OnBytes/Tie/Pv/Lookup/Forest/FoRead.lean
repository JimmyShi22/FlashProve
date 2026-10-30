-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoRead.lean.
What the verifier of "the shift, then the whole lookup" puts out, as a flat function of the
transcript.

The typed verifier is the block `ShiftQ.allK` (one round that draws the shift if there are several
calls, then the
lookup's chain of sumchecks and draws) with the short sumcheck filled by `V₀`, `V₀C`. Its
out-statement holds the
caller's state with the shift, a masked claim on the keys (a point, a form on the mask entries, a
target), and a list of
linear rows on the entries.

Main statements.
* `flAll`: a typed transcript read as plain data: for each round the scalars sent and the values
drawn, the shift's
  round first. `theta_flAll`, `after_flAll`: the flat reader of the shift and of the rounds behind
    it give back the
  typed ones.
* `all_read`: for every assembly, every shift, with the shift's round and without it, every
statement and every transcript: the
verifier does not
  refuse; the state put out is the caller's with the shift; the rows are the flat function's rows
    (all kinds but the
  keys'), with the places renamed along `ι` and each sparse row spread; the three fields of the
    claim on the keys are
  read off the same flat trace.
* `HCout1`: the same as one closed proposition at the sub-proofs' lookup `forB`, in the words of the
flat function
  `Fo.forN`, `Fo.forTrace`, `Fo.rows16`. `hcOut1`: its proof.

The one hypothesis, `PlacesAre`: the public numbers and places of the assembly are those of the flat
record, renamed
along `ι` (an equation of records, the two fields on the keys left out). It speaks of public data
alone. At the sub-proofs' lookup it holds under the hypotheses of `numsOf_forA`
(OnBytes/Tie/Pv/Lookup/Forest/FoNumsEq.lean). `theta_flAll` and `after_flAll` ask instead that the
flag `several` is the shape's.

Not claimed here: that the flat function is what the byte-level verifier computes; anything on the
honest prover.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoState
import Cb.Pv.Lookup.Forest.FoNat
import OnBytes.Tie.Pv.Lookup.Shift.ShiftKOut
import OnBytes.Tie.Pv.Lookup.Forest.FoV
import OnBytes.Tie.Pv.Lookup.Forest.FoHole

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw

noncomputable section
variable {E St : Type} [Field E] [Fintype E] (Ex : ExtSpec) (A0 : LkAsmH E)
  (P : ShiftQ E St (A0.J → E)) (several : Bool)

/-- The shift that a transcript holds. -/
abbrev thT (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape) : E :=
  Tw.thetaOf P several ((P.asmH A0).baseKS (SK₀ E Ex)) τ

/-- The chain's transcript behind the shift's round. -/
abbrev reT (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape) :
    Tr ((P.asmH A0).chnK (SK₀ E Ex)).R.shape :=
  Tw.restOf P several ((P.asmH A0).baseKS (SK₀ E Ex)) τ

/-- The whole transcript as plain data, the shift's round first. -/
def flAll (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape) : Rounds E :=
  (if several then [([], [thT Ex A0 P several τ])] else []) ++
    flChn Ex (P.asmH A0) (reT Ex A0 P several τ)

theorem theta_flAll (h : FoNums.Sh) (hs : FoNums.several h = several)
    (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape) :
    Fo.thetaOf h (flAll Ex A0 P several τ) = thT Ex A0 P several τ := by
  unfold Fo.thetaOf flAll
  rw [hs]
  cases several <;> rfl

theorem after_flAll (h : FoNums.Sh) (hs : FoNums.several h = several)
    (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape) :
    Fo.afterShift h (flAll Ex A0 P several τ) = flChn Ex (P.asmH A0) (reT Ex A0 P several τ) := by
  unfold Fo.afterShift flAll
  rw [hs]
  cases several <;> rfl

/-- The assembly's public numbers and places are the flat record's, renamed along ι. -/
def PlacesAre {P' : Type} (A : LkAsmH E) (st : A.St) (ι : P' → A.J) (N : Nums P' E) : Prop :=
  noKey (numsA A st) = noKey (numsMap ι N)

/-- The hypothesis is not empty: every assembly's own record meets it, with the places as they are.
-/
theorem placesAre_self (A : LkAsmH E) (st : A.St) : PlacesAre A st id (numsA A st) := rfl

/-- What does not read the two fields on the keys is the same at both records. -/
theorem PlacesAre.same {P' : Type} {A : LkAsmH E} {st : A.St} {ι : P' → A.J} {N : Nums P' E}
    (h : PlacesAre A st ι N) {β : Type} (f : Nums A.J E → β) (hf : ∀ M, f (noKey M) = f M) :
    f (numsA A st) = f (numsMap ι N) := by
  rw [← hf (numsA A st), h, hf]

/-- The out-statement at a last state of the chain, read off the flat trace. -/
theorem rd_read {P' : Type} (A : LkAsmH E) (st : A.St) (ι : P' → A.J) (N : Nums P' E)
    (hN : PlacesAre A st ι N) (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    (A.rd (chnV (SV₀ E Ex) A st τ)).1 = st ∧
    (A.rd (chnV (SV₀ E Ex) A st τ)).2.2 =
      ((r16 N (traceOfFlat N (flChn Ex A τ))).map (rowMap ι)).map toRow ∧
    (∀ X < 2 ^ (A.v' + 1), Blocks.eqN (A.v' + 1) 0 (A.rd (chnV (SV₀ E Ex) A st τ)).2.1.pt X =
      TwV.eqN (pntTop N.oK [] (traceOfFlat N (flChn Ex A τ)).keys.reverse) X) ∧
    (∀ j, (A.rd (chnV (SV₀ E Ex) A st τ)).2.1.mf j =
      dense (mapL ι (scale (-1) (incTop N.ledK (TwV.fK N (traceOfFlat N (flChn Ex A τ)))
        (traceOfFlat N (flChn Ex A τ)).keys.reverse))) j) ∧
    (A.rd (chnV (SV₀ E Ex) A st τ)).2.1.tg =
      (traceOfFlat N (flChn Ex A τ)).lam - (traceOfFlat N (flChn Ex A τ)).kT := by
  have ht : traceOf A (chnV (SV₀ E Ex) A st τ) = traceOfFlat N (flChn Ex A τ) :=
    (state_eq Ex A st (fun _ => Sum.inr 0) τ).trans
      (hN.same (fun M => traceOfFlat M (flChn Ex A τ)) fun _ => rfl)
  have hst := run_st Ex A st τ
  refine ⟨hst, ?_, ?_, ?_, ?_⟩
  · rw [rows16A, hst, ← r16_eq, ht, hN.same (fun M => r16 M _) fun M => r16_noKey M _, r16_map]
  · intro X hX
    have h := clK_wt A st (chnV (SV₀ E Ex) A st τ) X hX
    rw [ht, hN.same (fun M => M.oK) fun _ => rfl] at h
    exact h
  · intro j
    have h := clK_mf A st (chnV (SV₀ E Ex) A st τ) j
    rw [ht, hN.same (fun M => incTop M.ledK (TwV.fK M (traceOfFlat N (flChn Ex A τ)))
      (traceOfFlat N (flChn Ex A τ)).keys.reverse) fun _ => rfl] at h
    refine h.trans ?_
    rw [← scale_mapL, ← incTop_map]
    rfl
  · rw [← ht]
    exact clK_tg A (chnV (SV₀ E Ex) A st τ)

/-- The shift, then the whole lookup: what is put out, for all inputs. -/
theorem all_read {P' : Type} (ι : P' → A0.J) (N : E → Nums P' E)
    (hN : ∀ (st : St) (θ : E), PlacesAre (P.asmH A0) (st, θ) ι (N θ)) (a : St × Ex.Str)
    (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape) :
    ∃ x : TX (St × E) E A0.J,
      (P.allK A0 several V₀ V₀C (Ex := Ex)).R.red.out a τ = some (x, a.2) ∧
      x.1 = (a.1, thT Ex A0 P several τ) ∧
      x.2.2 = ((r16 (N (thT Ex A0 P several τ)) (traceOfFlat (N (thT Ex A0 P several τ))
        (flChn Ex (P.asmH A0) (reT Ex A0 P several τ)))).map (rowMap ι)).map toRow ∧
      (∀ X < 2 ^ (A0.v' + 1), Blocks.eqN (A0.v' + 1) 0 x.2.1.pt X =
        TwV.eqN (pntTop (N (thT Ex A0 P several τ)).oK [] (traceOfFlat (N (thT Ex A0 P several τ))
          (flChn Ex (P.asmH A0) (reT Ex A0 P several τ))).keys.reverse) X) ∧
      (∀ j, x.2.1.mf j = dense (mapL ι (scale (-1) (incTop (N (thT Ex A0 P several τ)).ledK
        (TwV.fK (N (thT Ex A0 P several τ)) (traceOfFlat (N (thT Ex A0 P several τ))
          (flChn Ex (P.asmH A0) (reT Ex A0 P several τ))))
        (traceOfFlat (N (thT Ex A0 P several τ))
          (flChn Ex (P.asmH A0) (reT Ex A0 P several τ))).keys.reverse))) j) ∧
      x.2.1.tg = (traceOfFlat (N (thT Ex A0 P several τ))
          (flChn Ex (P.asmH A0) (reT Ex A0 P several τ))).lam -
        (traceOfFlat (N (thT Ex A0 P several τ))
          (flChn Ex (P.asmH A0) (reT Ex A0 P several τ))).kT :=
  ⟨_, allK₀_out Ex A0 P several a τ,
    rd_read Ex (P.asmH A0) (a.1, thT Ex A0 P several τ) ι (N (thT Ex A0 P several τ))
      (hN a.1 _) (reT Ex A0 P several τ)⟩

end

/-! ### at the sub-proofs' lookup -/

open Cb.Fo in
/-- A transcript of the sub-proofs' lookup as plain data. -/
noncomputable def forFl {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq
    J₀]
    (h : FoNums.Sh) (L : Lay E St₀ J₀) (Ex : ExtSpec) (τ : Tr (forB E h L V₀ V₀C (Ex :=
        Ex)).R.shape) :
    Rounds E :=
  flAll Ex (forA E h L) (forP E h L) (FoNums.several h) τ

open Cb.Fo in
/-- What the typed verifier of the sub-proofs' lookup puts out is the flat function at the
transcript read as plain data:
a closed proposition. -/
def HCout1 : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh)
    (L : Lay E St₀ J₀) (lm jLK : ℕ) (ι : Pl → Option J₀),
    (∀ (st : St₀) (θ : E), PlacesAre (forA E h L) (st, θ) ι (numsF h lm jLK θ)) →
    ∀ (Ex : ExtSpec) (a : St₀ × Ex.Str) (τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape),
    ∃ x : TX (St₀ × E) E (Option J₀),
      (forB E h L V₀ V₀C (Ex := Ex)).R.red.out a τ = some (x, a.2) ∧
      x.1 = (a.1, Fo.thetaOf h (forFl h L Ex τ)) ∧
      x.2.2 = ((rows16 (forN h lm jLK (forFl h L Ex τ)) (forTrace h lm jLK (forFl h L Ex τ))).map
        (rowMap ι)).map toRow ∧
      (∀ X < 2 ^ (FoNums.v' h + 1), Blocks.eqN (FoNums.v' h + 1) 0 x.2.1.pt X =
        TwV.eqN (pntK (forN h lm jLK (forFl h L Ex τ)) (forTrace h lm jLK (forFl h L Ex τ))) X) ∧
      (∀ j, x.2.1.mf j = dense (mapL ι (scale (-1) (incTop (forN h lm jLK (forFl h L Ex τ)).ledK
        (TwV.fK (forN h lm jLK (forFl h L Ex τ)) (forTrace h lm jLK (forFl h L Ex τ)))
        (forTrace h lm jLK (forFl h L Ex τ)).keys.reverse))) j) ∧
      x.2.1.tg = (forTrace h lm jLK (forFl h L Ex τ)).lam - (forTrace h lm jLK (forFl h L Ex τ)).kT

open Cb.Fo in
theorem hcOut1 : HCout1 := by
  intro E _ _ St₀ J₀ _ _ h L lm jLK ι hN Ex a τ
  have hθ : Fo.thetaOf h (forFl h L Ex τ) = _ :=
    theta_flAll Ex (forA E h L) (forP E h L) (FoNums.several h) h rfl τ
  have hr : Fo.afterShift h (forFl h L Ex τ) = _ :=
    after_flAll Ex (forA E h L) (forP E h L) (FoNums.several h) h rfl τ
  unfold forTrace forN pntK
  rw [hθ, hr]
  exact all_read Ex (forA E h L) (forP E h L) (FoNums.several h) ι (numsF h lm jLK) hN a τ

end Fo
