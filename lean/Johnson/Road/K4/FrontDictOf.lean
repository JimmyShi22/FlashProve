-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FrontDictOf.lean: the dictionary FrontDict (Johnson/Road/K4/ValuesOfClaims.lean)
with all its clauses on the reads concluded: on true reads, at library-side entries that are true
of the same cells, at points that agree.

FrontDict asks of twelve families of entries of the reads that each is worth a library-side entry.
Johnson/Road/K4/ReadsThere2.lean says what the verifier's entry is worth on cells, from the
records of true tables and TrueAt4, where the verifier's lists return. The library's records
TablesTrue, TermsTrue and GatedTables (Cb/Pv/Lay/End/NormsCl.lean, TermsCl.lean, GatedCl.lean) say
what the library-side entry is worth on cells (Johnson/Road/K4/LateMeet.lean has them at the late
entries' forms' values). Here the two are joined, family by family.

Main names:
  `PointTies`: the points of the verifier's tables agree, coordinate by coordinate, with the points
    in the library's records.
  `long_join`: two sums over a block's features agree, if the points do.
  `SlotTies`: the clauses of FrontDict and of its three inner dictionaries that are not on the
    reads or on sizes, gathered: the hidden values under slots, the tables of weights, the powers
    that batch, two constants of each norm.
  `frontDict_of`: FrontDict.
Limits. The records of true tables (Fits, PortFits, TrueAt2, TrueAt3, TrueAt4), the library's three
records, PointTies, SlotTies and the sizes are premises. It is asked that K4's run "front" returns:
only then can the verifier name the entries. With routed experts and a second product layer alone.
Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.ValuesOfClaims
import Johnson.Road.K4.ReadsThere2
import Johnson.Road.K4.TrueAt4
import Johnson.Road.K4.LateMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff Fork Level tenCell hiTab)
open OnBytes.Model.Layer (Pub Own epsOf twoM)
open OnBytes.Road.Rows (readAtW TermsDict HotDict)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell lF lFe npOf)
open Cb.Pv.Lay.End (NormsNames NormsE TermsNames TermsE TablesTrue TermsTrue)
open Cb.Pv.Lay.End.Gated (GatedNames GatedE GatedTables)
open Blocks (eqN ext)

variable {K : Type} [Field K] {J : Type} [Fintype J] [DecidableEq J]

/-- Two sums over a block's features agree, if the points do. -/
theorem long_join {s lT : ℕ} {lo lo' uu uu' : ℕ → K} (f : ℕ → ℕ → K)
    (h1 : ∀ j, j < s → lo j = lo' j) (h2 : ∀ j, j < lT → uu j = uu' j) :
    ∑ r ∈ range (2 ^ s), eqN s 0 lo r * ext lT (f r) uu =
      ∑ r ∈ range (2 ^ s), eqN s 0 lo' r * ext lT (f r) uu' :=
  sum_congr rfl fun r _ => by
    rw [eqN_congr' s 0 (a := lo) (a' := lo') (fun j hj => by rw [Nat.zero_add]; exact h1 j hj) r,
      Desc.First.K4.ext_pt (f r) h2]

/-- The points of the verifier's tables against the points in the library's records. u: the
lookup's token point; u', zh: the end point of the sumcheck of the terms, as TrueAt2 and PortFits
have it; lowV, uV: the squares' point; uP, uR: the norms' token point and the end point of the token
sumcheck of the row products; lowA, uA, lowB, uB: the two product layers' points. -/
structure PointTies (D : Dim) (eN : NormsE K) (eT : TermsE K) (eG : GatedE K) (b sG : ℕ)
    (u u' zh lowV uV uP uR lowA uA lowB uB : ℕ → K) : Prop where
  zt : ∀ j, j < D.lT → u j = eN.zt j
  rt : ∀ j, j < D.lT → u' j = eT.rt j
  rt' : ∀ j, j < D.lT → zh j = eT.rt j
  pV : ∀ j, j < D.lT → uP j = eN.pV j
  r2 : ∀ j, j < D.lT → uR j = eN.r2 j
  lowV : ∀ j, j < sG → lowV j = eN.r1 (D.lL + 1 + b + j)
  uV : ∀ j, j < D.lT → uV j = eN.r1 (D.lL + 1 + (b + sG) + j)
  lowA : ∀ j, j < sG → lowA j = eG.r5 (D.lL + lF D - sG + j)
  uA : ∀ j, j < D.lT → uA j = eG.r5 (D.lL + lF D - sG + sG + j)
  lowB : ∀ j, j < sG → lowB j = eG.r6 (D.lL - 1 + lFe D - sG + j)
  uB : ∀ j, j < D.lT → uB j = eG.r6 (D.lL - 1 + lFe D - sG + sG + j)

/-- The clauses of FrontDict, LedDict and TermsDict that are neither on the reads nor on sizes. -/
structure SlotTies [scl : Scl] (ρ : Reading K) (W : World K) (P : Pub) (o : Own) (D : Dim)
    (NN : NormsNames J) (eN : NormsE K) (NT : TermsNames J) (eT : TermsE K) (NG : GatedNames J)
    (eG : GatedE K) (b B sG : ℕ) (y : J → K) : Prop where
  sqL : W.slot o.H.wpl.sL = eN.shL - eN.β1 * y NN.mL
  sqR : W.slot o.H.wpl.sR = eN.shR - eN.β1 * y NN.mR
  sqW : ∀ e, (hiTab o.H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption = some e →
    ∀ i kh, i < D.nNu → kh < B →
      ρ.val (e.getD (i * P.y.Pd / P.y.S2 + kh) zeroE) = eqN (D.lL + 1 + b) 0 eN.r1 (i * 2 ^ b + kh)
  sqG : ∀ l, l < 5 → ρ.val (o.H.gp.getD l zeroE) = eN.γ ^ l
  batCl : W.slot o.H.tV.sCl = eN.shCl - y NN.mCl
  batW : ∀ x, x < 7 * D.nNu → ρ.val (o.H.omV.getD x zeroE) = eN.ω ^ x
  slot2 : ∀ x, x < 4 * D.nNu → W.slot (o.H.tV.sEnd + x) = eN.sh2 x - eN.β2 * y (NN.m2 x)
  slotW : ∀ x, x < 9 * D.nNu → W.slot (o.H.sW + x) = eN.shW x - y (NN.mW x)
  slotP : ∀ x, x < 7 * D.nNu → W.slot (o.H.sPv + x) = eN.shP x - y (NN.mP x)
  eps : ∀ i, i < D.nNu → ρ.val (epsOf o.v.y i) = ((npOf D i).eps : K)
  two : ∀ i, i < D.nNu → (twoM o.v i).value ρ W = 2 ^ ((npOf D i).M + 1)
  slotT : ∀ tT, o.H.tT = some tT → ∀ x, x < D.nNu + D.ne + D.ne * D.nx →
    W.slot (tT.sEnd + x) = eT.sh x - eT.β * y (NT.mT x)
  g5L : W.slot o.hd.sL = eG.shL5 - eG.β5 * y NG.mL5
  g5R : W.slot o.hd.sR = eG.shR5 - eG.β5 * y NG.mR5
  g5W : ∀ e, (hiTab o.hd.r P.y.h.la (P.y.h.ll + P.y.lPf - P.y.ls)).toOption = some e →
    ∀ x, x < 2 ^ D.lL * 2 ^ (lF D - sG) →
      ρ.val (e.getD (x / 2 ^ (lF D - sG) * (P.y.Pf / P.y.S2) + x % 2 ^ (lF D - sG)) zeroE) =
        eqN (D.lL + lF D - sG) 0 eG.r5 x
  g6L : ∀ o2, o.hd2 = some o2 → W.slot o2.sL = eG.shL6 - eG.β6 * y NG.mL6
  g6R : ∀ o2, o.hd2 = some o2 → W.slot o2.sR = eG.shR6 - eG.β6 * y NG.mR6
  g6W : ∀ o2 e, o.hd2 = some o2 →
    (hiTab o2.r P.y.h.la (P.y.h.ll - 1 + P.y.lfe - P.y.ls)).toOption = some e →
    ∀ x, x < 2 ^ (D.lL - 1) * 2 ^ (lFe D - sG) →
      ρ.val (e.getD (x / 2 ^ (lFe D - sG) * 2 ^ (lFe D - sG) + x % 2 ^ (lFe D - sG)) zeroE) =
        eqN (D.lL - 1 + lFe D - sG) 0 eG.r6 x

variable [scl : Scl] {ρ : Reading K} {W : World K} {P : Pub} {o : Own} {D : Dim}
  {NN : NormsNames J} {eN : NormsE K} {NT : TermsNames J} {eT : TermsE K} {NG : GatedNames J}
  {eG : GatedE K} {b B sG : ℕ} {y : J → K} {c : Cells K} {t : Cell → K}
  {low u low' u' z zh lowV uV uP uR lowE uE lowA uA lowB uB : ℕ → K}

omit [Fintype J] [DecidableEq J] scl in
/-- One family of the gated products' reads, joined. A: the array; uN: the library-side names. -/
theorem gated_join {A : Inst.Model.FFSeg.Arr} {tb : ℕ} {X : Model.Layer.Ten} {rows blocks : ℕ}
    {lamOf : ℕ → ℕ} {first g : ℕ} {lo uu r : ℕ → K} {uN : ℕ → ℕ → ℕ → J} (hls : o.v.y.ls = sG)
    (hV : X.nl = 2 ∧ ∀ x, x < rows * blocks → ∀ l, l < 2 →
      readAtW W o.v tb (tenCell X.place l (lamOf (x / blocks)) 0 / o.v.y.S2 +
          (first + x % blocks)) =
        ∑ q ∈ range (2 ^ o.v.y.ls), eqN o.v.y.ls 0 lo q * ext D.lT (fun p =>
          t ⟨A, l, lamOf (x / blocks), (first + x % blocks) * 2 ^ o.v.y.ls + q, p⟩) uu)
    (hL : ∀ x, x < rows * blocks → ∀ l, l < 2 →
      y (uN l (lamOf (x / blocks)) (first + x % blocks)) =
        Cb.Pv.Lay.End.Gated.readAt D t A r g sG l (lamOf (x / blocks)) (first + x % blocks))
    (p1 : ∀ j, j < sG → lo j = r (g + j)) (p2 : ∀ j, j < D.lT → uu j = r (g + sG + j)) :
    X.nl = 2 ∧ ∀ x, x < rows * blocks → ∀ l, l < 2 →
      readAtW W o.v tb (tenCell X.place l (lamOf (x / blocks)) 0 / o.v.y.S2 +
          (first + x % blocks)) = y (uN l (lamOf (x / blocks)) (first + x % blocks)) := by
  refine ⟨hV.1, fun x hx l hl => ?_⟩
  rw [hV.2 x hx l hl, hL x hx l hl, readAt_off, hls]
  exact long_join _ p1 p2

omit scl in
/-- Where the two claims on a product layer's end values are listed, the two forms are there. -/
theorem endsL_forms {v : Model.Layer.Env} {lv : Level} {e : Array E} {tb rows blocks stride : ℕ}
    {lamOf : ℕ → ℕ} {first : ℕ} {l : List Aff}
    (h : Rows.endsL v lv e tb rows blocks stride lamOf first = some l) :
    ∃ ts tu aS aU, v.y.T_ "s" = some ts ∧ v.y.T_ "u" = some tu ∧
      Rows.endForm v tb ts e rows blocks stride lamOf first = some aS ∧
      Rows.endForm v tb tu e rows blocks stride lamOf first = some aU := by
  unfold Rows.endsL at h
  obtain ⟨ts, hts, h1⟩ := bind_some h
  obtain ⟨tu, htu, h3⟩ := bind_some h1
  obtain ⟨aS, haS, h4⟩ := bind_some h3
  obtain ⟨la, lb, -, hb, -⟩ := appL_some h4
  obtain ⟨aU, haU, -⟩ := bind_some hb
  exact ⟨ts, tu, aS, aU, hts, htu, haS, haU⟩

omit [Fintype J] [DecidableEq J] in
/-- **FrontDict, with its clauses on the reads concluded.** -/
theorem frontDict_of (hyv : o.v.y = P.y) (hls : o.v.y.ls = sG)
    (Z : P.y.Lam = 2 ^ D.lL ∧ P.y.h.f / P.y.S2 = 2 ^ (lF D - P.y.ls) ∧
      P.y.LamM = 2 ^ (D.lL - 1) ∧ P.y.h.fe / P.y.S2 = 2 ^ (lFe D - P.y.ls) ∧ P.y.xb.nl = 5 ∧
      Model.ledNP P.y.h.xl * P.y.NI = 7 * D.nNu ∧ P.y.NI = D.nNu)
    (hB : P.y.h.d / P.y.S2 = B) (h0 : 0 < D.nNu)
    (F : Fits ρ W o.v D c t low u) (T2 : TrueAt2 ρ W o.v D.lT c low' u')
    (T3 : TrueAt3 ρ W o.v D.lT c lowV uV uP uR lowE uE)
    (T4 : TrueAt4 ρ W o.v D.lT c lowA uA lowB uB) (PF : PortFits ρ W o.v D c t low z zh)
    (L : Laid o.v.y) (S : Switches o.v.y.h) (TN : TablesTrue NN eN D t (D.lL + 1) b sG B y)
    (TT : TermsTrue NT eT D t y) (TG : GatedTables NG eG D t sG y)
    (Pt : PointTies D eN eT eG b sG u u' zh lowV uV uP uR lowA uA lowB uB)
    (Sl : SlotTies ρ W P o D NN eN NT eT NG eG b B sG y) {g : ℕ} {rows : Bool} {F0 G : Fork}
    {fs : Array Aff} {o2 : Level} (h2 : o.hd2 = some o2)
    (h : Desc.First.K4.formsFrontWith rows P g o F0 = some (fs, G)) :
    FrontDict ρ W P o D NN eN NT eT NG eG b B sG y := by
  obtain ⟨zLam, zF, zLamM, zFe, znl, zNP, zNI⟩ := Z
  have hlsP : P.y.ls = sG := by rw [← hyv]; exact hls
  rw [hlsP] at zF zFe
  obtain ⟨sh, pp, l, -, -, -, -, k3, -, -, -, -⟩ := Desc.First.K4.formsFrontWith_some h
  obtain ⟨l2, g46, l7, l89, l10, g11, g12, c1, a46, c3, c4, c5, -, -, -⟩ :=
    Desc.First.K4.front_some k3
  obtain ⟨tT, hT⟩ := termsForms_tT c3
  rw [oneHotForms_oneHotL o.v F.p3] at c5
  have a7 := termsForms_termsL hT F.p3 c3
  obtain ⟨txs, tI, tA, eS, sum, b1, b2, b3, -, b5, -⟩ :=
    Desc.First.K4.normsL_shape (normsForms_normsL c1)
  have a89 := gatedForms_gatedL c4
  rw [h2] at a89
  unfold Rows.gatedL at a89
  obtain ⟨x0, l1, -, d1, -⟩ := appL_some a89
  obtain ⟨e5, -, d2⟩ := bind_some d1
  obtain ⟨t5, ht5, d3⟩ := bind_some d2
  obtain ⟨l5, l6', a5, a6, -⟩ := appL_some d3
  unfold Rows.gatedL2 at a6
  obtain ⟨x1, l6, -, k6, -⟩ := appL_some a6
  obtain ⟨e6, -, k7⟩ := bind_some k6
  obtain ⟨t6, ht6, k8⟩ := bind_some k7
  rw [zLam, zF] at a5
  rw [zLamM, zFe] at k8
  obtain ⟨ts, tu, aS5, aU5, hts, htu, hS5, hU5⟩ := endsL_forms a5
  obtain ⟨ts', tu', aS6, aU6, hts', htu', hS6, hU6⟩ := endsL_forms k8
  rw [← hyv] at b1 b5 znl zNI hB
  have hN : o.v.y.NN * o.v.y.Lam = D.nNu := by
    rw [F.NN, F.Lam]
    rfl
  have hp5 : 0 < 2 ^ (lF D - sG) := Nat.two_pow_pos _
  have hp6 : 0 < 2 ^ (lFe D - sG) := Nat.two_pow_pos _
  have zNI' : P.y.NI = D.nNu := by rw [← hyv]; exact zNI
  have znl' : P.y.xb.nl = 5 := by rw [← hyv]; exact znl
  have hB' : P.y.h.d / P.y.S2 = B := by rw [← hyv]; exact hB
  exact
    { num := F.num
      sqL := Sl.sqL
      sqR := Sl.sqR
      nl5 := znl'
      hB := hB'
      hNI := zNI'
      hNP := zNP
      sqW := Sl.sqW
      sqG := Sl.sqG
      sqI := fun tI' hI' l kh hl hk => by
        rw [← hyv, sqI_dict F T3 b2 b5 zNI h0 znl hB tI' hI' l kh hl hk,
          tables_uXi0 TN h0 hl hk, hls]
        exact long_join _ Pt.lowV Pt.uV
      sqA := fun tA' txs' hA' hx' i l kh hi0 hi hl hk => by
        rw [← hyv] at hx'
        rw [← hyv, sqA_dict F T3 b3 b1 b5 zNI znl hB tA' txs' hA' hx' i l kh hi0 hi hl hk,
          tables_uXi TN hi0 hi hl hk, hls]
        exact long_join _ Pt.lowV Pt.uV
      batCl := Sl.batCl
      batW := Sl.batW
      led :=
        { nNu := zNI
          slot2 := Sl.slot2
          slotW := Sl.slotW
          slotP := Sl.slotP
          rowR := fun tb tr q1 q2 ν n hν hn => by
            rw [(rows_meet_of_forms F T3 a46).1 tb tr q1 q2 ν n (by rw [zNI]; exact hν) hn,
              tables_uR TN hν hn]
            exact Desc.First.K4.ext_pt _ Pt.r2
          rowP := fun tb tr q1 q2 ν n hν hn => by
            rw [(rows_meet_of_forms F T3 a46).2 tb tr q1 q2 ν n (by rw [zNI]; exact hν) hn,
              tables_uP TN hν hn]
            exact Desc.First.K4.ext_pt _ Pt.pV
          eps := Sl.eps
          two := Sl.two }
      terms := fun tT' hT' =>
        { num := F.num
          nNu := hN
          ne := F.LamM
          nx := F.NE
          p3 := F.p3
          xl := F.xl
          slot := Sl.slotT tT' hT'
          row := fun tb tr q1 q2 ν n hν hn => by
            rw [termsRow_dict F T2 hN a7 tb tr q1 q2 ν n hν hn, TT.row ν n hν hn]
            exact Desc.First.K4.ext_pt _ Pt.rt
          sc := fun X tb hX => ⟨(termsSc_dict PF L S a7 X tb hX).1, fun lm k hl hk => by
            rw [(termsSc_dict PF L S a7 X tb hX).2 lm k hl hk, TT.sc lm k hl hk]
            exact Desc.First.K4.ext_pt _ Pt.rt'⟩
          sel := fun X tb hX => ⟨(termsSel_dict PF L S a7 X tb hX).1, fun lm x k hl hx hk => by
            rw [(termsSel_dict PF L S a7 X tb hX).2 lm x k hl hx hk, TT.sel lm x k hl hx hk]
            exact Desc.First.K4.ext_pt _ Pt.rt'⟩ }
      hot :=
        { num := F.num
          ne := F.LamM
          nx := F.NE
          p3 := F.p3
          sel := fun X tb hX => ⟨(hotSel_dict F L S c5 X tb hX).1, fun lm x hl hx => by
            rw [(hotSel_dict F L S c5 X tb hX).2 lm x hl hx, tables_uSel TN hl hx]
            exact Desc.First.K4.ext_pt _ Pt.zt⟩ }
      gLam := zLam
      gF := zF
      gLamM := zLamM
      gFe := zFe
      g5L := Sl.g5L
      g5R := Sl.g5R
      g5W := Sl.g5W
      g5S := fun tb hb X hX => by
        obtain rfl : t5 = tb := Option.some.inj (ht5.symm.trans hb)
        obtain rfl : ts = X := Option.some.inj (hts.symm.trans hX)
        exact gated_join (rows := 2 ^ D.lL) (blocks := 2 ^ (lF D - sG)) (lamOf := id) (first := 0)
          (g := D.lL + lF D - sG) (r := eG.r5) (uN := NG.uS5) hls
          (gS_dict F L S hX (T4.afA _ hb) hS5)
          (fun x hx l hl => TG.s5 l hl _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)) _
            (by rw [Nat.zero_add]; exact Nat.mod_lt _ hp5)) Pt.lowA Pt.uA
      g5U := fun tb hb X hX => by
        obtain rfl : t5 = tb := Option.some.inj (ht5.symm.trans hb)
        obtain rfl : tu = X := Option.some.inj (htu.symm.trans hX)
        exact gated_join (rows := 2 ^ D.lL) (blocks := 2 ^ (lF D - sG)) (lamOf := id) (first := 0)
          (g := D.lL + lF D - sG) (r := eG.r5) (uN := NG.uU5) hls
          (gU_dict F L S hX (T4.afA _ hb) hU5)
          (fun x hx l hl => TG.u5 l hl _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)) _
            (by rw [Nat.zero_add]; exact Nat.mod_lt _ hp5)) Pt.lowA Pt.uA
      g6L := Sl.g6L
      g6R := Sl.g6R
      g6W := Sl.g6W
      g6S := fun tb hb X hX => by
        obtain rfl : t6 = tb := Option.some.inj (ht6.symm.trans hb)
        obtain rfl : ts' = X := Option.some.inj (hts'.symm.trans hX)
        exact gated_join (rows := 2 ^ (D.lL - 1)) (blocks := 2 ^ (lFe D - sG))
          (lamOf := fun lm => 2 * lm + 1) (first := 2 ^ (lFe D - sG))
          (g := D.lL - 1 + lFe D - sG) (r := eG.r6) (uN := NG.uS6) hls
          (gS_dict F L S hX (T4.afB _ hb) hS6)
          (fun x hx l hl => TG.s6 l hl _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)) _
            (Nat.mod_lt _ hp6)) Pt.lowB Pt.uB
      g6U := fun tb hb X hX => by
        obtain rfl : t6 = tb := Option.some.inj (ht6.symm.trans hb)
        obtain rfl : tu' = X := Option.some.inj (htu'.symm.trans hX)
        exact gated_join (rows := 2 ^ (D.lL - 1)) (blocks := 2 ^ (lFe D - sG))
          (lamOf := fun lm => 2 * lm + 1) (first := 2 ^ (lFe D - sG))
          (g := D.lL - 1 + lFe D - sG) (r := eG.r6) (uN := NG.uU6) hls
          (gU_dict F L S hX (T4.afB _ hb) hU6)
          (fun x hx l hl => TG.u6 l hl _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)) _
            (Nat.mod_lt _ hp6)) Pt.lowB Pt.uB }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.frontDict_of
