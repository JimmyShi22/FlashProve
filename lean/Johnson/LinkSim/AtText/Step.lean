-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Step.lean: at one switch, under the premises AtSwitch, two runs side by side
send and open the same values and reach the same verifier state; their prover states differ by
dNext.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Take the honest run (coins Kr, prover state Pr, columns colr) and the other
run (Ks, Ps, cols) at the same verifier challenges D, at a stage that is not the last. AtSwitch
collects what is assumed of them at that stage's switch:
  - the states differ by d (Pr = Ps + d);
  - the trees in hand have equal columns at the positions at which they are opened;
  - the fold's coefficients, the free entries of the new mask table and the new coins given to
    the switch differ by the shifts that ShiftDefs.lean defines, and so do the next fold's
    coefficients where the switch is not the last;
  - the next tree is opened at no more positions than its rows' tails are long.
Under AtSwitch each of the following is an equation between the two runs.
  sRF_same, sGam_same   the fold's rounds are the same, and so is the fold's point, made of the
                 challenges of the fold's rounds.
  sT1_same       the verifier's state after the fold is the same.
  sAns_same      the prover's answer at the switch is the same.
  sRS_same       the switch's two rounds are the same.
  sGS_same       the group of columns at the switch's opening is the same.
  sT3_same       the verifier's state after the switch and the batching is the same.
  sNext_add      the honest run's next state is the other run's plus the next difference dNext.
  sCol_same      the next trees have equal columns at the positions at which they are opened.
The proofs use foldRV_shift, ansAt_shift, symG_shift, mask_sym_same and the additivity lemmas of
State.lean.

How it fits. Induct.lean applies these lemmas once per stage, with Walk.lean, to prove
Spec.bodyShiftOr and Spec.walkSame (SpecShiftIn.lean, SpecStage.lean).

The other names.
  symG_tailAt, symG_tailAt_zero   if Q has at most C.r positions, then at each of them the
                 message m + dm with the tail t has the symbol of the message m with the tail
                 t + tailAt C red Q dm; so dm with the negative of that tail has symbol 0 there.
  stage_col_eq   a later tree's columns agree at the positions of Q, for two states whose tables
                 differ by dT and dF and whose tails differ by the compensating tails.
  last_col_eq    the last tree's columns agree at the positions of Q, for two states whose last
                 messages differ by (dm0, dm1), whose tails differ by the compensating tails, and
                 whose masking words differ by a multiple of both.
  sNext_tM, sNext_tZ, sNext_fT, sNext_sM, sNext_sT, sNext_tabM, sNext_tabZ, muOf_dNext
                 the fields of the next state and of the next difference, written out.

Limits.
  - These lemmas are about one switch.
Notes.
  - Nothing here says how AtSwitch's premises come about: Induct.lean derives them from AtStage.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SpecStage

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link

/-- What is assumed of the two runs at one switch. -/
structure AtSwitch (p : P12) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
    (t : T12) (Kr Ks : BCoins) (Pr Ps d : PS) (colr cols : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) :
    Prop where
  st : Pr = addPS Ps d
  col : ∀ x ∈ Fmt.listOf
    (openAt (sgOf cur).C.a (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss), colr x = cols x
  foldW : Ks.W (sgOf cur) j = Kr.W (sgOf cur) j +
    foldShift (sgOf cur) (vecG (sgOf cur) (rowOf t)) (μOf (sgOf cur) d) fun n => D (o + n)
  fr : Ks.fr j = Kr.fr j + shFr p Kr j cur next l o t Pr D d
  new : Ks.new j = addPS (Kr.new j) (shNew p Kr last j cur next l o t Pr colr D d)
  nextW : last = false → Ks.W (sgOf next) (j + 1) = Kr.W (sgOf next) (j + 1) +
    shWAt p Kr last j cur next l o t Pr colr D d (sgOf next)
  qC : (qNext last cur next o D).length ≤ (sgOf next).C.r
  qZ : (qNext last cur next o D).length ≤ (sgOf next).Z.r

open Classical in
theorem symG_tailAt (C : Fmt.M1.Code) (Q : List ℕ) (red : ℕ → ℕ) (hQ : Q.length ≤ C.r)
    (m dm t : ℕ → GE) {x : ℕ} (hx : x ∈ Q) :
    symG C (red x) (m + dm) t = symG C (red x) m (t + tailAt C red Q dm) :=
  symG_shift C Q red hQ m dm t hx

/-- With the negative of tailAt's tail as its tail, the change dm has the symbol 0 at the
positions of Q. -/
theorem symG_tailAt_zero (C : Fmt.M1.Code) (Q : List ℕ) (red : ℕ → ℕ) (hQ : Q.length ≤ C.r)
    (dm : ℕ → GE) {x : ℕ} (hx : x ∈ Q) :
    symG C (red x) dm (fun q => -tailAt C red Q dm q) = 0 := by
  have h := symG_tailAt C Q red hQ 0 dm (fun q => -tailAt C red Q dm q) hx
  rw [zero_add] at h
  rw [h]
  have z : (fun q => -tailAt C red Q dm q) + tailAt C red Q dm = 0 := by
    funext q
    exact neg_add_cancel _
  rw [z]
  unfold symG
  simp

section
variable {p : P12} {last : Bool} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
  {Kr Ks : BCoins} {Pr Ps d : PS} {colr cols : ℕ → List UInt64} {D : ℕ → Fmt.Drawn}

theorem sRF_same (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sRF Kr j cur o Pr (rowOf t) D = sRF Ks j cur o Ps (rowOf t) D := by
  unfold sRF
  rw [h.st, muOf_add, foldRV_shift, ← h.foldW]

theorem sGam_same (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sGam Kr j cur o Pr (rowOf t) D = sGam Ks j cur o Ps (rowOf t) D := by
  unfold sGam
  rw [sRF_same h]

theorem sT1_same (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sT1 p Kr j cur l o t Pr (rowOf t) D = sT1 p Ks j cur l o t Ps (rowOf t) D := by
  unfold sT1
  rw [sRF_same h]

theorem sAns_same (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sAns p Kr j cur next l o t Pr (rowOf t) D = sAns p Ks j cur next l o t Ps (rowOf t) D := by
  have e : sAns p Kr j cur next l o t Pr (rowOf t) D =
      ansAt (sgOf cur) (sgOf next)
        (foldMsg (sgOf cur) (μOf (sgOf cur) Ps) (φOf (sgOf cur) Ps)
            (sGam Kr j cur o Pr (rowOf t) D) + dMu Kr j cur o t Pr D d)
        (foldTl (sgOf cur) (ρOf (sgOf cur) Ps) (ψOf (sgOf cur) Ps)
            (sGam Kr j cur o Pr (rowOf t) D) + dTl Kr j cur o t Pr D d)
        (Kr.fr j) (sEls cur o D) (sBits p Kr j cur next l o t Pr D) := by
    unfold dMu dTl
    rw [← foldMsg_add, ← foldTl_add, ← muOf_add, ← phiOf_add, ← rhoOf_add, ← psiOf_add, ← h.st]
    rfl
  rw [e, ansAt_shift]
  have f : Kr.fr j + Pi.single (padIx (sgOf next))
      (ansShift (sgOf cur) (sgOf next) (dMu Kr j cur o t Pr D d) (dTl Kr j cur o t Pr D d)
        (sEls cur o D) (sBits p Kr j cur next l o t Pr D)) = Ks.fr j := h.fr.symm
  rw [f, sGam_same h]
  unfold sBits
  rw [sT1_same h]
  rfl

theorem sRS_same (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sRS p Kr j cur next l o t Pr (rowOf t) D = sRS p Ks j cur next l o t Ps (rowOf t) D := by
  unfold sRS
  rw [sAns_same h]

theorem sGS_same (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sGS cur o colr D = sGS cur o cols D := by
  unfold sGS groupAt
  exact congrArg (fun g => [g]) (List.map_congr_left fun x hx => by rw [h.col x hx])

theorem sT3_same (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sT3 p Kr last j cur next l o t Pr colr (rowOf t) D =
      sT3 p Ks last j cur next l o t Ps cols (rowOf t) D := by
  unfold sT3
  rw [sT1_same h, sRS_same h, sGS_same h]

end

/-! ## The next state -/

theorem sNext_tM (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    (sNext K last j cur next o P row D).tM = (K.new j).tM := by
  cases last <;> rfl

theorem sNext_tZ (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    (sNext K last j cur next o P row D).tZ = (K.new j).tZ := by
  cases last <;> rfl

theorem sNext_fT (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    (sNext K last j cur next o P row D).fT = (K.new j).fT := by
  cases last <;> rfl

theorem sNext_sM (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    (sNext K last j cur next o P row D).sM = (K.new j).sM := by
  cases last <;> rfl

theorem sNext_sT (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    (sNext K last j cur next o P row D).sT = (K.new j).sT := by
  cases last <;> rfl

theorem sNext_tabM (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    (sNext K last j cur next o P row D).tabM =
      gMain (sgOf cur) (foldMsg (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P)
        (sGam K j cur o P row D)) := rfl

theorem sNext_tabZ (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    (sNext K last j cur next o P row D).tabZ =
      gMask (sgOf cur) (foldMsg (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P)
          (sGam K j cur o P row D))
        (foldTl (sgOf cur) (ρOf (sgOf cur) P) (ψOf (sgOf cur) P) (sGam K j cur o P row D))
        (K.fr j) := rfl

section
variable {p : P12} {last : Bool} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
  {Kr Ks : BCoins} {Pr Ps d : PS} {colr cols : ℕ → List UInt64} {D : ℕ → Fmt.Drawn}

/-- The honest run's next state is the other run's next state plus dNext. -/
theorem sNext_add (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sNext Kr last j cur next o Pr (rowOf t) D =
      addPS (sNext Ks last j cur next o Ps (rowOf t) D)
        (dNext p Kr last j cur next l o t Pr colr D d) := by
  have hγ := sGam_same h
  have hfr : Kr.fr j = Ks.fr j + -shFr p Kr j cur next l o t Pr D d := by
    rw [h.fr]
    exact (add_neg_cancel_right _ _).symm
  have hμ : μOf (sgOf cur) Pr = μOf (sgOf cur) Ps + μOf (sgOf cur) d :=
    (congrArg _ h.st).trans (muOf_add _ _ _)
  have hφ : φOf (sgOf cur) Pr = φOf (sgOf cur) Ps + φOf (sgOf cur) d :=
    (congrArg _ h.st).trans (phiOf_add _ _ _)
  have hρ : ρOf (sgOf cur) Pr = ρOf (sgOf cur) Ps + ρOf (sgOf cur) d :=
    (congrArg _ h.st).trans (rhoOf_add _ _ _)
  have hψ : ψOf (sgOf cur) Pr = ψOf (sgOf cur) Ps + ψOf (sgOf cur) d :=
    (congrArg _ h.st).trans (psiOf_add _ _ _)
  refine ps_ext (funext fun i => ?_) (funext fun i => ?_) (funext fun b => funext fun q => ?_)
    (funext fun b => funext fun q => ?_) (funext fun b => funext fun i => ?_)
    (funext fun b => funext fun q => ?_) (funext fun i => ?_) (funext fun q => ?_)
  · show (sNext Kr last j cur next o Pr (rowOf t) D).tabM i =
      (sNext Ks last j cur next o Ps (rowOf t) D).tabM i +
        gMain (sgOf cur) (foldMsg (sgOf cur) (μOf (sgOf cur) d) (φOf (sgOf cur) d)
          (sGam Kr j cur o Pr (rowOf t) D)) i
    rw [sNext_tabM, sNext_tabM, hμ, hφ, foldMsg_add, gMain_add, hγ]
  · show (sNext Kr last j cur next o Pr (rowOf t) D).tabZ i =
      (sNext Ks last j cur next o Ps (rowOf t) D).tabZ i +
        gMask (sgOf cur) (foldMsg (sgOf cur) (μOf (sgOf cur) d) (φOf (sgOf cur) d)
            (sGam Kr j cur o Pr (rowOf t) D))
          (foldTl (sgOf cur) (ρOf (sgOf cur) d) (ψOf (sgOf cur) d)
            (sGam Kr j cur o Pr (rowOf t) D)) (-shFr p Kr j cur next l o t Pr D d) i
    rw [sNext_tabZ, sNext_tabZ, hμ, hφ, hρ, hψ, foldMsg_add, foldTl_add]
    conv_lhs => rw [hfr]
    rw [gMask_add, hγ]
  · show (sNext Kr last j cur next o Pr (rowOf t) D).tM b q =
      (sNext Ks last j cur next o Ps (rowOf t) D).tM b q +
        -(shNew p Kr last j cur next l o t Pr colr D d).tM b q
    rw [sNext_tM, sNext_tM, h.new]
    exact (add_neg_cancel_right _ _).symm
  · show (sNext Kr last j cur next o Pr (rowOf t) D).tZ b q =
      (sNext Ks last j cur next o Ps (rowOf t) D).tZ b q +
        -(shNew p Kr last j cur next l o t Pr colr D d).tZ b q
    rw [sNext_tZ, sNext_tZ, h.new]
    exact (add_neg_cancel_right _ _).symm
  · cases last
    · show packedN (sgOf next) (Kr.W (sgOf next) (j + 1)) b i =
        packedN (sgOf next) (Ks.W (sgOf next) (j + 1)) b i +
          -packedN (sgOf next) (shWAt p Kr false j cur next l o t Pr colr D d (sgOf next)) b i
      rw [h.nextW rfl, packedN_add]
      exact (add_neg_cancel_right _ _).symm
    · show (Kr.new j).fM b i = (Ks.new j).fM b i +
        -(shNew p Kr true j cur next l o t Pr colr D d).fM b i
      rw [h.new]
      exact (add_neg_cancel_right _ _).symm
  · show (sNext Kr last j cur next o Pr (rowOf t) D).fT b q =
      (sNext Ks last j cur next o Ps (rowOf t) D).fT b q +
        -(shNew p Kr last j cur next l o t Pr colr D d).fT b q
    rw [sNext_fT, sNext_fT, h.new]
    exact (add_neg_cancel_right _ _).symm
  · show (sNext Kr last j cur next o Pr (rowOf t) D).sM i =
      (sNext Ks last j cur next o Ps (rowOf t) D).sM i +
        -(shNew p Kr last j cur next l o t Pr colr D d).sM i
    rw [sNext_sM, sNext_sM, h.new]
    exact (add_neg_cancel_right _ _).symm
  · show (sNext Kr last j cur next o Pr (rowOf t) D).sT q =
      (sNext Ks last j cur next o Ps (rowOf t) D).sT q +
        -(shNew p Kr last j cur next l o t Pr colr D d).sT q
    rw [sNext_sT, sNext_sT, h.new]
    exact (add_neg_cancel_right _ _).symm

end

/-! ## The next tree's columns -/

/-- A later tree's columns agree at the positions of Q, for two states whose tables differ by dT
and dF and whose tails differ by the compensating tails. -/
theorem stage_col_eq (s : Sg) (Q : List ℕ) (hC : Q.length ≤ s.C.r) (hZ : Q.length ≤ s.Z.r)
    (Nr Ns dT : PS) (dF : ℕ → ℕ → GE) (hM : ∀ i, Nr.tabM i = Ns.tabM i + dT.tabM i)
    (hZt : ∀ i, Nr.tabZ i = Ns.tabZ i + dT.tabZ i) (hF : ∀ b i, Nr.fM b i = Ns.fM b i + dF b i)
    (htM : ∀ b, b < 2 ^ (s.h + s.g) →
      Ns.tM b = Nr.tM b + tailAt s.C id Q fun i => dT.tabM (b + 2 ^ (s.h + s.g) * i))
    (htZ : ∀ b, b < 2 ^ s.h →
      Ns.tZ b = Nr.tZ b + tailAt s.Z (· % 2 ^ s.Z.a) Q fun i => dT.tabZ (b + 2 ^ s.h * i))
    (hfT : ∀ b, b < 2 ^ s.h → Ns.fT b = Nr.fT b + tailAt s.Z (· % 2 ^ s.Z.a) Q (dF b)) {x : ℕ}
    (hx : x ∈ Q) :
    stageColW s Nr.tabM Nr.tabZ Nr.tM Nr.tZ Nr.fM Nr.fT x =
      stageColW s Ns.tabM Ns.tabZ Ns.tM Ns.tZ Ns.fM Ns.fT x := by
  refine stageColW_congr s _ _ _ _ _ _ _ _ _ _ _ _ x (fun b hb => ?_) (fun b hb => ?_)
    fun b hb => ?_
  · unfold mainSym
    have e : (fun i => Nr.tabM (b + 2 ^ (s.h + s.g) * i)) =
        (fun i => Ns.tabM (b + 2 ^ (s.h + s.g) * i)) +
          fun i => dT.tabM (b + 2 ^ (s.h + s.g) * i) := funext fun i => hM _
    rw [e, htM b hb]
    exact symG_tailAt s.C Q id hC _ _ _ hx
  · unfold maskSym
    have e : (fun i => Nr.tabZ (b + 2 ^ s.h * i)) =
        (fun i => Ns.tabZ (b + 2 ^ s.h * i)) + fun i => dT.tabZ (b + 2 ^ s.h * i) :=
      funext fun i => hZt _
    rw [e, htZ b hb]
    exact symG_tailAt s.Z Q (· % 2 ^ s.Z.a) hZ _ _ _ hx
  · unfold freshSym
    have e : Nr.fM b = Ns.fM b + dF b := funext fun i => hF b i
    rw [e, hfT b hb]
    exact symG_tailAt s.Z Q (· % 2 ^ s.Z.a) hZ _ _ _ hx

/-- The last tree's columns agree at the positions of Q, for two states whose last messages differ
by (dm0, dm1), whose tails differ by the compensating tails, and whose masking words differ by a
multiple of both. -/
theorem last_col_eq (s : Sg) (Q : List ℕ) (hC : Q.length ≤ s.C.r) (hZ : Q.length ≤ s.Z.r)
    (Nr Ns : PS) (dm0 dm1 : ℕ → GE) (c : GE)
    (h0 : mainOf s (μOf s Nr) = mainOf s (μOf s Ns) + dm0)
    (h1 : maskOf s (μOf s Nr) = maskOf s (μOf s Ns) + dm1)
    (htM : Ns.tM 0 = Nr.tM 0 + tailAt s.C id Q dm0)
    (htZ : Ns.tZ 0 = Nr.tZ 0 + tailAt s.Z (· % 2 ^ s.Z.a) Q dm1)
    (hsM : Ns.sM = fun i => Nr.sM i + c * dm0 i)
    (hsT : Ns.sT = fun q => Nr.sT q + c * -tailAt s.C id Q dm0 q)
    (hfM : Ns.fM 0 = fun i => Nr.fM 0 i + c * dm1 i)
    (hfT : Ns.fT 0 = fun q => Nr.fT 0 q + c * -tailAt s.Z (· % 2 ^ s.Z.a) Q dm1 q) {x : ℕ}
    (hx : x ∈ Q) : lastCol s Nr x = lastCol s Ns x := by
  unfold lastCol
  refine congrArg words12 (baseColW_congr s.C s.Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x ?_ ?_ ?_ ?_)
  · rw [h0, htM]
    exact symG_tailAt s.C Q id hC _ _ _ hx
  · rw [hsM, hsT]
    exact (mask_sym_same s.C x _ _ dm0 (fun q => -tailAt s.C id Q dm0 q) c
      (symG_tailAt_zero s.C Q id hC dm0 hx)).symm
  · rw [h1, htZ]
    exact symG_tailAt s.Z Q (· % 2 ^ s.Z.a) hZ _ _ _ hx
  · rw [hfM, hfT]
    exact (mask_sym_same s.Z (x % 2 ^ s.Z.a) _ _ dm1
      (fun q => -tailAt s.Z (· % 2 ^ s.Z.a) Q dm1 q) c
      (symG_tailAt_zero s.Z Q (· % 2 ^ s.Z.a) hZ dm1 hx)).symm

theorem muOf_dNext (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (d : PS) (σ : Sg) :
    μOf σ (dNext p K last j cur next l o t P col D d) =
      μOf σ (dTab p K j cur next l o t P D d) := by
  funext x
  cases x <;> rfl

section
variable {p : P12} {last : Bool} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
  {Kr Ks : BCoins} {Pr Ps d : PS} {colr cols : ℕ → List UInt64} {D : ℕ → Fmt.Drawn}

/-- The next trees have equal columns at the positions at which they are opened. -/
theorem sCol_same (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) {x : ℕ}
    (hx : x ∈ Fmt.listOf (qNext last cur next o D)) :
    sCol Kr last j cur next o Pr (rowOf t) D x = sCol Ks last j cur next o Ps (rowOf t) D x := by
  have hxQ : x ∈ qNext last cur next o D := (Fmt.listOf_mem _ _).mp hx
  have hN := sNext_add h
  have htM : (sNext Ks last j cur next o Ps (rowOf t) D).tM =
      fun b q => (sNext Kr last j cur next o Pr (rowOf t) D).tM b q +
        (shNew p Kr last j cur next l o t Pr colr D d).tM b q := by
    rw [sNext_tM, sNext_tM, h.new]
    rfl
  have htZ : (sNext Ks last j cur next o Ps (rowOf t) D).tZ =
      fun b q => (sNext Kr last j cur next o Pr (rowOf t) D).tZ b q +
        (shNew p Kr last j cur next l o t Pr colr D d).tZ b q := by
    rw [sNext_tZ, sNext_tZ, h.new]
    rfl
  have hfT : (sNext Ks last j cur next o Ps (rowOf t) D).fT =
      fun b q => (sNext Kr last j cur next o Pr (rowOf t) D).fT b q +
        (shNew p Kr last j cur next l o t Pr colr D d).fT b q := by
    rw [sNext_fT, sNext_fT, h.new]
    rfl
  have hsM : (sNext Ks last j cur next o Ps (rowOf t) D).sM =
      fun i => (sNext Kr last j cur next o Pr (rowOf t) D).sM i +
        (shNew p Kr last j cur next l o t Pr colr D d).sM i := by
    rw [sNext_sM, sNext_sM, h.new]
    rfl
  have hsT : (sNext Ks last j cur next o Ps (rowOf t) D).sT =
      fun q => (sNext Kr last j cur next o Pr (rowOf t) D).sT q +
        (shNew p Kr last j cur next l o t Pr colr D d).sT q := by
    rw [sNext_sT, sNext_sT, h.new]
    rfl
  cases last
  · refine stage_col_eq (sgOf next) _ h.qC h.qZ _ _ (dTab p Kr j cur next l o t Pr D d)
      (dFresh p Kr false j cur next l o t Pr colr D d)
      (fun i => congrFun (congrArg PS.tabM hN) i) (fun i => congrFun (congrArg PS.tabZ hN) i)
      (fun b i => congrFun (congrFun (congrArg PS.fM hN) b) i) (fun b hb => ?_) (fun b hb => ?_)
      (fun b hb => ?_) hxQ
    · rw [htM]
      funext q
      show _ + (if b < 2 ^ ((sgOf next).h + (sgOf next).g) then _ else (0 : ℕ → GE)) q = _
      rw [if_pos hb]
      rfl
    · rw [htZ]
      funext q
      show _ + (if b < 2 ^ (sgOf next).h then _ else (0 : ℕ → GE)) q = _
      rw [if_pos hb]
      rfl
    · rw [hfT]
      funext q
      show _ + (if b < 2 ^ (sgOf next).h then _ else (0 : ℕ → GE)) q = _
      rw [if_pos hb]
      rfl
  · have hμ : μOf (sgOf next) (sNext Kr true j cur next o Pr (rowOf t) D) =
        μOf (sgOf next) (sNext Ks true j cur next o Ps (rowOf t) D) +
          μOf (sgOf next) (dTab p Kr j cur next l o t Pr D d) := by
      rw [hN, muOf_add, muOf_dNext]
    have hfM : (sNext Ks true j cur next o Ps (rowOf t) D).fM =
        fun b i => (sNext Kr true j cur next o Pr (rowOf t) D).fM b i +
          (shNew p Kr true j cur next l o t Pr colr D d).fM b i := by
      show (Ks.new j).fM = fun b i => (Kr.new j).fM b i + _
      rw [h.new]
      rfl
    refine last_col_eq (sgOf next) _ h.qC h.qZ _ _
      (mainOf (sgOf next) (μOf (sgOf next) (dTab p Kr j cur next l o t Pr D d)))
      (maskOf (sgOf next) (μOf (sgOf next) (dTab p Kr j cur next l o t Pr D d)))
      (lamNext cur o D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hxQ
    · rw [hμ]
      exact funext fun i => mainOf_add _ _ _ i
    · rw [hμ]
      exact funext fun i => maskOf_add _ _ _ i
    · rw [htM]
      rfl
    · rw [htZ]
      rfl
    · rw [hsM]
      rfl
    · rw [hsT]
      rfl
    · rw [hfM]
      rfl
    · rw [hfT]
      rfl

end

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.sRF_same
#print axioms OnBytes.LinkSim.AtText.sAns_same
#print axioms OnBytes.LinkSim.AtText.sT3_same
#print axioms OnBytes.LinkSim.AtText.sNext_add
#print axioms OnBytes.LinkSim.AtText.sCol_same
