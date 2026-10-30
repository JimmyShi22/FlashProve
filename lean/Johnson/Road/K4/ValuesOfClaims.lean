-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ValuesOfClaims.lean: the ports from the claims of the layers' own rounds to the
library-side claims on the norms, the terms, the gated products and the selectors, laid together:
where the list of forms that K4's run "front" returns (with or without the lookup's own claims,
group 1: no port reads them) is worth 0 form by form, the library-side
forms of five parts of the chain's ledger are worth 0, but for the claims that the sumchecks
themselves leave.

The ports lie one by one in Johnson/Road/Rows/LayerTermsPort.lean,
LayerHotPort.lean, LayerGatedPort.lean, LayerNormsPort.lean and
Johnson/Road/K4/LedPort.lean, each with premises of its own. OnBytes/Desc/First/K4/ClaimsLaws.lean
(formsFrontWith_some, front_some) and Johnson/Road/K4/ListsTie.lean | ListsTie2.lean say which lists
K4's run returns. Here the premises are gathered in one record, and the ports are called on the
members of that list.
Main names:
  `FrontDict`: the ports' premises, at a run's record o and at library-side names and records
    NN | eN (norms), NT | eT (terms), NG | eG (gated products) and entries y: how numerals are
    read; sizes; the hidden values under slots; the verifier's tables of weights against the
    library's equality weights; the entries of the reads against the library-side entries.
  `values_of_front`: cSame, cEnd (the part sq without its head), cBatch (bat), clLedger without its
    head (led), termsCl (terms), gatedCl (gated without the two layers' own claims) and clHot (hot)
    are worth 0 at y.
Limits. FrontDict is a premise: no run, world and entries are shown at which it holds. Among its
size clauses: the group has 2^lL layers, half of them with routed experts, and the blocks of a
layer's gated products are a power of two in number (so f and fe are powers of two): the library's
own limits (the head of Cb/Pv/Lay/End/GatedCl.lean). With routed experts and a second product layer
alone. The claims that the sumchecks themselves leave, the batched sumcheck's part and the merge's
are not spoken of here. Implications in one world: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.FrontLaw
import Johnson.Road.K4.NormsReads
import Johnson.Road.K4.LedPort
import Johnson.Road.Rows.LayerNormsPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World Aff Fork Level tenCell hiTab)
open OnBytes.Model.Layer (Pub Own)
open OnBytes.Road.Rows (readAtW TermsDict HotDict termsL_port oneHotL_port endsL_port same_val
  batch_val sqEnd_val)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim lF lFe)
open Cb.Pv.Lay.End (NormsNames NormsE cSame cBatch clLedger clHot TermsNames TermsE termsCl)
open Cb.Pv.Lay.End.Gated (GatedNames GatedE gatedCl)
open Blocks (Form eqN)

variable {K : Type} [Field K] {J : Type} [Fintype J] [DecidableEq J]

/-- The premises of the ports, at a run's record. b, B: the bits and the number of the blocks of the
stream's width; sG: the bits of a feature in its block. -/
structure FrontDict [scl : Scl] (ρ : Reading K) (W : World K) (P : Pub) (o : Own) (D : Dim)
    (NN : NormsNames J) (eN : NormsE K) (NT : TermsNames J) (eT : TermsE K) (NG : GatedNames J)
    (eG : GatedE K) (b B sG : ℕ) (y : J → K) : Prop where
  /-- how numerals are read -/
  num : Numerals ρ
  /-- the product layer of the squares: the two hidden end values -/
  sqL : W.slot o.H.wpl.sL = eN.shL - eN.β1 * y NN.mL
  sqR : W.slot o.H.wpl.sR = eN.shR - eN.β1 * y NN.mR
  /-- sizes of the norms -/
  nl5 : P.y.xb.nl = 5
  hB : P.y.h.d / P.y.S2 = B
  hNI : P.y.NI = D.nNu
  hNP : Model.ledNP P.y.h.xl * P.y.NI = 7 * D.nNu
  /-- the weights of the blocks at the squares' point; the powers that batch the limbs -/
  sqW : ∀ e, (hiTab o.H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption = some e →
    ∀ i kh, i < D.nNu → kh < B →
      ρ.val (e.getD (i * P.y.Pd / P.y.S2 + kh) zeroE) = eqN (D.lL + 1 + b) 0 eN.r1 (i * 2 ^ b + kh)
  sqG : ∀ l, l < 5 → ρ.val (o.H.gp.getD l zeroE) = eN.γ ^ l
  /-- the reads of the stream's limbs at the squares' point -/
  sqI : ∀ tI, o.v.tabAt "xbI@Z_V" = some tI → ∀ l kh, l < 5 → kh < B →
    readAtW W o.v tI (tenCell P.y.xb l 0 0 / P.y.S2 + kh) = y (NN.uXi 0 l kh)
  sqA : ∀ tA txs, o.v.tabAt "af@Z_V" = some tA → P.y.T_ "xs" = some txs →
    ∀ i l kh, 0 < i → i < D.nNu → l < 5 → kh < B →
      readAtW W o.v tA (tenCell txs.place l (i - 1) 0 / P.y.S2 + kh) = y (NN.uXi i l kh)
  /-- the hidden sum of the token sumcheck of the row products; the powers that batch -/
  batCl : W.slot o.H.tV.sCl = eN.shCl - y NN.mCl
  batW : ∀ x, x < 7 * D.nNu → ρ.val (o.H.omV.getD x zeroE) = eN.ω ^ x
  /-- the norms' rows -/
  led : LedDict ρ W o.v o.H D NN eN y
  /-- the end values of the sumcheck of the terms -/
  terms : ∀ tT, o.H.tT = some tT → TermsDict ρ W o.v tT.sEnd D NT eT y
  /-- the selectors' sums -/
  hot : HotDict ρ W o.v D NN y
  /-- sizes of the gated products -/
  gLam : P.y.Lam = 2 ^ D.lL
  gF : P.y.h.f / P.y.S2 = 2 ^ (lF D - sG)
  gLamM : P.y.LamM = 2 ^ (D.lL - 1)
  gFe : P.y.h.fe / P.y.S2 = 2 ^ (lFe D - sG)
  /-- the first product layer of the gated products -/
  g5L : W.slot o.hd.sL = eG.shL5 - eG.β5 * y NG.mL5
  g5R : W.slot o.hd.sR = eG.shR5 - eG.β5 * y NG.mR5
  g5W : ∀ e, (hiTab o.hd.r P.y.h.la (P.y.h.ll + P.y.lPf - P.y.ls)).toOption = some e →
    ∀ x, x < 2 ^ D.lL * 2 ^ (lF D - sG) →
      ρ.val (e.getD (x / 2 ^ (lF D - sG) * (P.y.Pf / P.y.S2) + x % 2 ^ (lF D - sG)) zeroE) =
        eqN (D.lL + lF D - sG) 0 eG.r5 x
  g5S : ∀ t, o.v.tabAt "af@Z_a" = some t → ∀ X, o.v.y.T_ "s" = some X → X.nl = 2 ∧
    ∀ x, x < 2 ^ D.lL * 2 ^ (lF D - sG) → ∀ l, l < 2 →
      readAtW W o.v t (tenCell X.place l (id (x / 2 ^ (lF D - sG))) 0 / o.v.y.S2 +
          (0 + x % 2 ^ (lF D - sG))) =
        y (NG.uS5 l (id (x / 2 ^ (lF D - sG))) (0 + x % 2 ^ (lF D - sG)))
  g5U : ∀ t, o.v.tabAt "af@Z_a" = some t → ∀ X, o.v.y.T_ "u" = some X → X.nl = 2 ∧
    ∀ x, x < 2 ^ D.lL * 2 ^ (lF D - sG) → ∀ l, l < 2 →
      readAtW W o.v t (tenCell X.place l (id (x / 2 ^ (lF D - sG))) 0 / o.v.y.S2 +
          (0 + x % 2 ^ (lF D - sG))) =
        y (NG.uU5 l (id (x / 2 ^ (lF D - sG))) (0 + x % 2 ^ (lF D - sG)))
  /-- the second product layer -/
  g6L : ∀ o2, o.hd2 = some o2 → W.slot o2.sL = eG.shL6 - eG.β6 * y NG.mL6
  g6R : ∀ o2, o.hd2 = some o2 → W.slot o2.sR = eG.shR6 - eG.β6 * y NG.mR6
  g6W : ∀ o2 e, o.hd2 = some o2 →
    (hiTab o2.r P.y.h.la (P.y.h.ll - 1 + P.y.lfe - P.y.ls)).toOption = some e →
    ∀ x, x < 2 ^ (D.lL - 1) * 2 ^ (lFe D - sG) →
      ρ.val (e.getD (x / 2 ^ (lFe D - sG) * 2 ^ (lFe D - sG) + x % 2 ^ (lFe D - sG)) zeroE) =
        eqN (D.lL - 1 + lFe D - sG) 0 eG.r6 x
  g6S : ∀ t, o.v.tabAt "af@Z_b" = some t → ∀ X, o.v.y.T_ "s" = some X → X.nl = 2 ∧
    ∀ x, x < 2 ^ (D.lL - 1) * 2 ^ (lFe D - sG) → ∀ l, l < 2 →
      readAtW W o.v t (tenCell X.place l (2 * (x / 2 ^ (lFe D - sG)) + 1) 0 / o.v.y.S2 +
          (2 ^ (lFe D - sG) + x % 2 ^ (lFe D - sG))) =
        y (NG.uS6 l (2 * (x / 2 ^ (lFe D - sG)) + 1) (2 ^ (lFe D - sG) + x % 2 ^ (lFe D - sG)))
  g6U : ∀ t, o.v.tabAt "af@Z_b" = some t → ∀ X, o.v.y.T_ "u" = some X → X.nl = 2 ∧
    ∀ x, x < 2 ^ (D.lL - 1) * 2 ^ (lFe D - sG) → ∀ l, l < 2 →
      readAtW W o.v t (tenCell X.place l (2 * (x / 2 ^ (lFe D - sG)) + 1) 0 / o.v.y.S2 +
          (2 ^ (lFe D - sG) + x % 2 ^ (lFe D - sG))) =
        y (NG.uU6 l (2 * (x / 2 ^ (lFe D - sG)) + 1) (2 ^ (lFe D - sG) + x % 2 ^ (lFe D - sG)))

variable [scl : Scl] {ρ : Reading K} {W : World K} {P : Pub} {o : Own} {D : Dim}
  {NN : NormsNames J} {eN : NormsE K} {NT : TermsNames J} {eT : TermsE K} {NG : GatedNames J}
  {eG : GatedE K} {b B sG : ℕ} {y : J → K}

/-- The four claims on the gated products' end values. -/
theorem gated_of_list (Dc : FrontDict ρ W P o D NN eN NT eT NG eG b B sG y) {o2 : Level}
    (h2 : o.hd2 = some o2) {l : List Aff} (h : Rows.gatedL P o.v o.hd o.hd2 = some l)
    (hz : ∀ q ∈ l, q.value ρ W = 0) : ∀ q ∈ gatedCl NG eG D sG, Form.val y q = 0 := by
  rw [h2] at h
  unfold Rows.gatedL at h
  obtain ⟨x0, l1, -, h1, rfl⟩ := appL_some h
  obtain ⟨e5, he5, h3⟩ := bind_some h1
  obtain ⟨t5, ht5, h4⟩ := bind_some h3
  obtain ⟨l5, l6', a5, a6, rfl⟩ := appL_some h4
  unfold Rows.gatedL2 at a6
  obtain ⟨x1, l6, -, k6, rfl⟩ := appL_some a6
  obtain ⟨e6, he6, k7⟩ := bind_some k6
  obtain ⟨t6, ht6, k8⟩ := bind_some k7
  rw [Dc.gLam, Dc.gF] at a5
  rw [Dc.gLamM, Dc.gFe] at k8
  have z5 : ∀ q ∈ l5, q.value ρ W = 0 := fun q hq => hz q (by simp [hq])
  have z6 : ∀ q ∈ l6, q.value ρ W = 0 := fun q hq => hz q (by simp [hq])
  have c5 := endsL_port (rows := 2 ^ D.lL) (blocks := 2 ^ (lF D - sG))
    (stride := P.y.Pf / P.y.S2) (first := 0) (lamOf := id) (g := D.lL + lF D - sG) (r := eG.r5)
    (uS := NG.uS5) (uU := NG.uU5) Dc.num Dc.g5L Dc.g5R (Dc.g5W e5 he5) (Dc.g5S t5 ht5)
    (Dc.g5U t5 ht5) a5 z5
  have c6 := endsL_port (rows := 2 ^ (D.lL - 1)) (blocks := 2 ^ (lFe D - sG))
    (stride := 2 ^ (lFe D - sG)) (first := 2 ^ (lFe D - sG)) (lamOf := fun lm => 2 * lm + 1)
    (g := D.lL - 1 + lFe D - sG) (r := eG.r6) (uS := NG.uS6) (uU := NG.uU6) Dc.num
    (Dc.g6L o2 h2) (Dc.g6R o2 h2) (Dc.g6W o2 e6 h2 he6) (Dc.g6S t6 ht6) (Dc.g6U t6 ht6) k8 z6
  intro q hq
  simp only [gatedCl, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact c5.1
  · exact c5.2
  · exact c6.1
  · exact c6.2

/-- **The ports laid together.** -/
theorem values_of_front (Dc : FrontDict ρ W P o D NN eN NT eT NG eG b B sG y) {g : ℕ}
    {rows : Bool} {F G : Fork} {fs : Array Aff} (hp : o.v.y.h.p3 = true) {o2 : Level}
    (h2 : o.hd2 = some o2) (h : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    (hz : ∀ f ∈ fs.toList, f.value ρ W = 0) (u2 : Blocks.Form J K) :
    Form.val y (cSame NN eN) = 0 ∧
      Form.val y (Cb.Pv.Lay.End.cEnd NN eN (D.lL + 1) b B D.nNu) = 0 ∧
      Form.val y (cBatch NN eN D.nNu) = 0 ∧
      (∀ q ∈ (clLedger NN eN u2 D).tail, Form.val y q = 0) ∧
      (∀ q ∈ termsCl NT eT D, Form.val y q = 0) ∧
      (∀ q ∈ gatedCl NG eG D sG, Form.val y q = 0) ∧
      ∀ q ∈ clHot (E := K) NN D, Form.val y q = 0 := by
  obtain ⟨sh, pp, l, -, -, -, -, k3, k4, -, -, -⟩ := Desc.First.K4.formsFrontWith_some h
  obtain ⟨l2, g46, l7, l89, l10, g11, g12, c1, a46, c3, c4, c5, -, -, e⟩ :=
    Desc.First.K4.front_some k3
  obtain ⟨tT, hT⟩ := termsForms_tT c3
  rw [oneHotForms_oneHotL o.v hp] at c5
  have a2 := normsForms_normsL c1
  have a7 := termsForms_termsL hT hp c3
  have a89 := gatedForms_gatedL c4
  have a10 := c5
  rw [k4, e, rowBatchForm_eq] at hz
  obtain ⟨txs, tI, tA, eS, sum, b1, b2, b3, b4, b5, rfl⟩ := Desc.First.K4.normsL_shape a2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← same_val (ρ := ρ) Dc.sqL Dc.sqR]
    exact hz _ (by simp)
  · rw [← sqEnd_val Dc.num Dc.nl5 Dc.hB Dc.hNI Dc.sqL (Dc.sqW eS b4) Dc.sqG (Dc.sqI tI b2)
      (Dc.sqA tA txs b3 b1) b5]
    exact hz _ (by simp)
  · rw [← batch_val Dc.num P.y o.H Dc.hNP Dc.batCl Dc.led.slotP Dc.batW]
    exact hz _ (by simp)
  · exact led_port Dc.led a46 (fun f hf => hz f (by simp [hf])) u2
  · exact termsL_port (Dc.terms tT hT) a7 fun f hf => hz f (by simp [hf])
  · exact gated_of_list Dc h2 a89 fun f hf => hz f (by simp [hf])
  · exact oneHotL_port Dc.hot a10 fun f hf => hz f (by simp [hf])

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.values_of_front
