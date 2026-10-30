-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Every statement of this file has the premise `Cb.BCHKS46At F E` (Cb/Gen/CodeListRSAt.lean), which
this file does not prove.
`Gl.AgreeJ` follows from that premise by `Gl.glAg_ofAt`
(Cb/Gl/GlFinalAg.lean), which is `glAt_rows0` of this file. `GlJ` does not ask a radius within half
the distance (Cb/Gl/GlLdJ.lean).
Cb/Gl/GlLdJAt.lean: mutual correlated agreement of codes built from interleaved Reed-Solomon codes
over p = 2^64 - 2^32 + 1 (words over its cubic extension E), below the Johnson radius, and what
follows from it for a fold, a tower and a whole proximity test, under the hypothesis `Cb.BCHKS46At F
E`, which is stated at one field.

Exactly: below the Johnson radius, over p: agreement of the codes built from plain Reed-Solomon
families (`GlJ`: Cb/Gl/GlLdJ.lean), of folds, towers and tests on groups, from the statement on
codes (`Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean) at one field.

Statements (in `Cb.Gl.Spec`) and proofs. The statements are the analogues of statements of
Cb/Gl/GlCodesLdF.lean, Cb/Gl/GlLdJ.lean, Cb/GlVal/GlJohn.lean, Cb/Gl/GlGroupJohn.lean,
Cb/Gl/GlObjMix.lean, with BCHKS46At F E in the place of BCHKS46F F; the proofs rest on
`Cb.rsAt_group_prox` (Cb/Gen/CodeListRSAtProofs.lean). No notion is defined here: `GlJ`, `TowGlJ`,
`TowGGlJ`, `RunGlJAt` are those files'.

The hypothesis. Cb.BCHKS46At F E (Cb/Gen/CodeListRSAt.lean): mutual correlated agreement of
Reed-Solomon codes below the Johnson radius, for two words, over E alone, points in F: by reading,
the write-up's own restatement of the assumed theorem. It follows from BCHKS46F F
(`Cb.bchks46At_of_F`), so it is the weaker hypothesis. Stated, as a case, in Cryptology ePrint
Archive 2025/2055 (Theorem 4.6), with an outline of a proof; NOT proved here; NO axiom: it stands in
the text of each statement.

Main names (each under BCHKS46At F E and the hypotheses of its statement):
  `Spec.glAt_group_prox`: for a i ≤ 32, 0 < k i < 2^(a i), D ≤ mult i · (2^(a i) - k i): families
    under an even reading: lists and agreement, at the radii e with InJohnson |P| D e and mult i ≤ e
    (analogue of `gl_group_proxF`).
  `Spec.glAt_mca`: `GlJ C d t e bad`, InJohnson |P| d e ⇒ `C.MCArows e bad` ∧ `C.MCAat e bad`
    (analogue of `glJ_mca`).
  `Spec.glAt_fold`, `Spec.glAt_tower`, `Spec.glAt_towerG`: a fold; a whole tower; a tower on a
    group's complex (analogues of `glJ_fold`, `glJ_tower`, `glJ_towerG`).
  `Spec.glAt_runAt`: a test on a group with its tower given (analogue of `glJ_runAt`);
    `Spec.glAt_groupPar`: a closing's fold (analogue of `glGroupJohn_par`).

Limits: what the heads of Cb/Gl/GlCodesLdF.lean, Cb/Gl/GlLdJ.lean, Cb/GlVal/GlJohn.lean,
Cb/Gl/GlGroupJohn.lean, Cb/Gl/GlObjMix.lean and Cb/Gen/CodeListRSAt.lean list as not said is not
said here either. Nor does this file say that any table of parameters lies within half the distance
(at the numbers of the copy's file the radius lies beyond it, reckoned by hand: lean/GAPS.md, (61);
what follows within a half: Cb/Gl/GlAgreeHalf.lean). The counts are the same; lists are never
assumed.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gen.CodeListRSAtProofs
import Cb.Gl.GlObjMix
import Cb.Gl.GlGroupJohn

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR

namespace Spec

def glAt_group_prox : Prop :=
  Cb.BCHKS46At F E →
  ∀ (A : Type) [Fintype A] (a k msg r : A → ℕ), (∀ i, a i ≤ 32) →
    (∀ i, 0 < k i) → (∀ i, k i < 2 ^ a i) →
    ∀ T : Reading (grp a k msg r), T.Even →
      ∀ D : ℕ, (∀ i, D ≤ T.mult i * (2 ^ a i - k i)) →
        ∀ (R : A → Type) [∀ i, Finite (R i)], T.Prox E R
          (fun e => InJohnson (Fintype.card T.P) D e ∧ ∀ i, T.mult i ≤ e)
          (fun e => listMax (Fintype.card T.P) D e)
          (fun e => ∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / T.mult i)⌋₊)

/-- Agreement: under the statement on codes (`Cb.BCHKS46At`) at one field, by name.
(not all hypotheses are named here: see the statement below) -/
def glAt_mca : Prop :=
  Cb.BCHKS46At F E →
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ),
    GlJ C d t e bad → InJohnson (Fintype.card P) d e → C.MCArows e bad ∧ C.MCAat e bad

def glAt_fold : Prop :=
  Cb.BCHKS46At F E →
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e t bC bZ bW : ℕ), GlJ Y.C d 0 e bC →
    GlJ Y.Z d 0 e bZ → GlJ Y.Zw d t e bW → InJohnson (Fintype.card P) d e →
    Function.Injective Y.val → 2 ≤ Y.n → Y.PackOK → Y.QwDeg → Y.John d e t bC bZ bW

def glAt_tower : Prop := Cb.BCHKS46At F E → ∀ (a : LdJoint E) (T : LdTowJ a), TowGlJ T → T.John

def glAt_towerG : Prop :=
  Cb.BCHKS46At F E →
  ∀ (B : Type) [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    TowGGlJ T → T.John

def glAt_runAt : Prop :=
  Cb.BCHKS46At F E →
  ∀ (S : Sig E) (D : LdRunD S) (Tw : D.TowJ) (d : ℕ), RunGlJAt D Tw d → D.PreJ Tw d

def glAt_groupPar : Prop :=
  Cb.BCHKS46At F E →
  ∀ (S : Sig E) (G : Grp S) (Sh : GShape G) (d t bC bZ bW : ℕ), GlJ Sh.Cb d 0 G.e bC →
    GlJ Sh.Zb d 0 G.e bZ → GlJ Sh.par.Zw d t G.e bW →
    InJohnson (Fintype.card G.P) d G.e → Function.Injective Sh.val → 2 ≤ Sh.n →
    Sh.par.PackOK → Sh.par.QwDeg → Sh.par.John d G.e t bC bZ bW

end Spec

theorem glAt_group_prox : Spec.glAt_group_prox := fun H A _ a k msg r ha hk0 hk T hT D hD R _ =>
  rsAt_group_prox F E H A (fun i => 2 ^ a i) k msg r (fun i => pts (a i))
    (fun i => gl_pts_inj (a i) (ha i)) hk0 hk T hT D hD R

/-- the families whose message and randomness fill the dimension. `glAt_rows0` rests on the
statement on codes `Cb.BCHKS46At Gl.F Gl.E` (Cb/Gen/CodeListRSAt.lean), which this file does not
prove. -/
theorem glAt_rows0 (H : Cb.BCHKS46At F E) (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ)
    (h : IsGlJ C d t e bad) (hJ : InJohnson (Fintype.card P) d e) : C.MCArows e bad := by
  obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk0, hk, hp, hE, hd, -, hm, hb⟩ :=
    h
  exact ld_rows_mono E P _ _ _ _ hb
    (ld_rows_ld F E A (grp a k msg r) (⟨P, pos, mult⟩ : Reading (grp a k msg r)) _ _ hp
      (fun R' _ _ =>
        (glAt_group_prox H A a k msg r ha hk0 hk
            (⟨P, pos, mult⟩ : Reading (grp a k msg r)) hE _ hd R').mca
          _ ⟨hJ, hm⟩) R)

/-- a proper subcode: one more term. `glAt_rowsS` rests on the statement on codes `Cb.BCHKS46At Gl.F
Gl.E` (Cb/Gen/CodeListRSAt.lean), which this file does not prove. -/
theorem glAt_rowsS (H : Cb.BCHKS46At F E) (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ)
    (h : IsGlS C d t e bad) (hJ : InJohnson (Fintype.card P) d e) : C.MCArows e bad := by
  obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk0, hk,
      hp, hE, hd, ht, hm, hb⟩ := h
  have hW : IsGlJ ((⟨P, pos, mult⟩ : Reading (grp a k msg fun i => k i + 1 - msg i)).ld E R) d 0 e
      (∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / mult i)⌋₊) :=
    ⟨A, iA, dA, a, k, msg, fun i => k i + 1 - msg i, pos, mult, R, fR, dR, rfl, ha, hk0, hk, fun i => by
      have := hp i
      show msg i + (k i + 1 - msg i) = k i + 1
      omega, hE, hd, fun _ => Nat.zero_le _, hm, le_rfl⟩
  have gW := glC_code P _ d 0 (.base
    ⟨A, iA, dA, a, k, msg, fun i => k i + 1 - msg i, pos, mult, R, fR, dR, rfl, ha, hk, fun i => by
      have := hp i
      show msg i + (k i + 1 - msg i) ≤ k i + 1
      omega, hE, hd, fun _ => Nat.zero_le _⟩)
  have gS := glC_code P _ d t
    (.base ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk, hp, hE, hd, ht⟩)
  have hsub : ((⟨P, pos, mult⟩ : Reading (grp a k msg fun i => k i + 1 - msg i)).ld E R).SubOf
      ((⟨P, pos, mult⟩ : Reading (grp a k msg r)).ld E R) fun α => α :=
    ld_sub_ld F E A (grp a k msg r) (fun i => k i + 1 - msg i) P pos mult R fun i => by
      have := hp i
      show r i ≤ k i + 1 - msg i
      omega
  exact ld_rows_mono E P _ _ _ _ hb
    (ld_sub_rows E P _ _ _ d e _ _ hsub gW.1 gS.1 gW.2.2.2.1 (john_lt hJ)
      (glAt_rows0 H P _ d 0 e _ hW hJ) fun R' _ _ =>
        ld_list_johnson E P _ d e (ld_laws_il E P _ Bool (ld_laws_il E P _ R' gW.1))
          (ld_dist_il E P _ Bool d (ld_dist_il E P _ R' d gW.2.2.2.1)) hJ)

theorem glAt_rows (H : Cb.BCHKS46At F E) (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ)
    (h : GlJ C d t e bad) (hJ : InJohnson (Fintype.card P) d e) : C.MCArows e bad := by
  induction h with
  | base h => exact glAt_rows0 H P _ _ _ _ _ h hJ
  | sub h => exact glAt_rowsS H P _ _ _ _ _ h hJ
  | copy h => exact glCp_rows_of (fun P _ C d t e bad h hJ => glAt_rows0 H P C d t e bad h hJ) P _ _ _ _ _ h hJ
  | il R _ ih => exact ld_rows_il E P _ R _ _ (ih hJ)
  | pair _ _ ih₁ ih₂ => exact ld_rows_pair E P _ _ _ _ _ (ih₁ hJ) (ih₂ hJ)
  | fam _ ih => exact ld_rows_fam E P _ _ _ _ fun a => ih a hJ
  | up _ hb ih => exact ld_rows_mono E P _ _ _ _ hb (ih hJ)

theorem glAt_mca : Spec.glAt_mca := fun H P _ C d t e bad h hJ =>
  ⟨glAt_rows H P C d t e bad h hJ, ld_rows_self E P C e bad (glAt_rows H P C d t e bad h hJ)⟩

theorem glAt_fold : Spec.glAt_fold := fun H P _ Y d e t bC bZ bW hC hZ hW hJ hi hn hp hq =>
  have gC := glC_code P _ d 0 (glJ_glC P _ d 0 e bC hC)
  have gZ := glC_code P _ d 0 (glJ_glC P _ d 0 e bZ hZ)
  have gW := glC_code P _ d t (glJ_glC P _ d t e bW hW)
  { lawsC := gC.1, lawsZ := gZ.1, lawsW := gW.1, distC := gC.2.2.2.1, distZ := gZ.2.2.2.1,
    distW := gW.2.2.2.1, john := hJ
    mcaC := glAt_rows H P _ d 0 e bC hC hJ,
      mcaZ := glAt_rows H P _ d 0 e bZ hZ hJ,
      mcaW := glAt_rows H P _ d t e bW hW hJ
    inj := hi, deg := hn, pack := hp, qw := hq,
      zk := (glC_code P Y.Cw d t (.il _ (glJ_glC P _ d t e bW hW))).2.2.2.2 }

theorem glAt_tower : Spec.glAt_tower := by
  intro H a T
  induction T with
  | base a t cov d b =>
    rintro ⟨h, hJ⟩
    have g := glC_code a.P a.C d 0 (glJ_glC a.P a.C d 0 a.e b h)
    exact ⟨g.1, g.2.2.2.1, hJ, (glAt_mca H a.P a.C d 0 a.e b h hJ).2, g.2.1⟩
  | step Y sl e S d bC bZ bW e' d' rest ih =>
    rintro ⟨⟨hC, hZ, hW, hJ, hi, hn, hp, hq⟩, ⟨hN, hJ', hZo, hZb, hP⟩, hr⟩
    refine ⟨glAt_fold H _ (Y.reform sl) d e S.ts bC bZ bW hC hZ hW hJ hi hn hp hq,
      glJ_switch _ _ _ (S.D e) d' e' rest.toC.q hN ?_ hJ' hZo hZb hP,
      ih hr⟩
    exact glC_mono _ _ d 0 0 0
      (.pair (glJ_glC _ _ d 0 e bC hC)
        (.pair (glJ_glC _ _ d 0 e bZ hZ)
          (glC_mono _ _ d S.ts d 0 (glJ_glC _ _ d S.ts e bW hW) le_rfl (Nat.zero_le _))))
      (Nat.zero_le _) le_rfl

theorem glAt_towerG : Spec.glAt_towerG := by
  intro H B _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact glAt_tower H _ T h
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    obtain ⟨⟨hv, hm1, hm2, hz, h1⟩, ⟨hB, hZ, hW, hJ, hi, hn, hp, hq⟩,
        ⟨hN, hJ', hZo, hZb, hP⟩, hr⟩ := h
    have hC : GlJ Sh.par.C d 0 G.e bC := .il _ hB
    have hI : GlC (Sw.D G.e).Cin 0 0 :=
      glC_mono _ _ d 0 0 0
        (.pair (glJ_glC _ _ d 0 G.e bC hC)
          (.pair (glJ_glC _ _ d 0 G.e bZ hZ)
            (glC_mono _ _ d Sw.ts d 0 (glJ_glC _ _ d Sw.ts G.e bW hW) le_rfl (Nat.zero_le _))))
        (Nat.zero_le _) le_rfl
    exact ⟨⟨hv,
      (glC_code _ _ d 0 (glJ_glC _ _ d 0 G.e bC hB)).1,
      (glC_code _ _ d 0 (glJ_glC _ _ d 0 G.e bZ hZ)).1,
      fun r => by
        split
        · next b hb => exact hm1 r b hb
        · next j hj => exact hm2 r j hj, hz, h1⟩, glAt_fold H _ Sh.par d G.e Sw.ts bC bZ bW hC hZ hW hJ hi hn hp hq, glJ_switch _ _ _ (Sw.D G.e) d' e' rest.toC.q hN hI hJ' hZo hZb hP, glAt_tower H _ rest hr⟩

theorem glAt_runAt : Spec.glAt_runAt := by
  rintro H S D Tw d ⟨h1, h2, h3, hG, hJ, hF, hZ, hT⟩
  exact ⟨h1, h2, h3, fun a => (glC_code D.G.P _ d 0 (hG a)).1,
    fun a => (glC_code D.G.P _ d 0 (hG a)).2.2.2.1, hJ, hZ, hF,
    glAt_towerG H _ S D.G D.Sb D.sl D.Z Tw hT⟩

theorem glAt_groupPar : Spec.glAt_groupPar := fun H _ G Sh d t bC bZ bW hC hZ hW hJ hi hn hp hq =>
  glAt_fold H G.P Sh.par d G.e t bC bZ bW (.il _ hC) hZ hW hJ hi hn hp hq

end Cb.Gl
