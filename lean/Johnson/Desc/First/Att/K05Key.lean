-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Key.lean: K05_law at the library's letters: RowPrem of the sumcheck for
the key at the
index (P.sD: step 18's plain sumcheck, read at states that carry its incoming form), at the row that
leftP
makes (leftKey).

Main names:
  `ptOf_ini`, `lstOf_read`: the library's point of a sumcheck's output, on the data made of what was
    heard, is
    ldPartIni of the typed output's point; its further challenge is the reading of beta.
  `key_prem`: RowPrem from leftKey's return, the place's five numbers, the state's two points and
    factors, the
    end values under scdNum, (D1), (D2).
  `value_key_prem`: at the data made of the lists the state's premises are lemmas, and (D2) is
    proved in the
    ledger's world; what stays: (D1), the places of the second end values of the score at the index,
      the five
    numbers.
  `closed_key_prem`: at the closed parameters: no place left.

Sources: Cb/Pv/Att/OwnSteps.lean (sD, ptOf, lstOf, PlainSc.pull); Step18.lean;
Cb/Part/LdPartVars.lean
(ldPartVars_ini, ldPartVars_last); OnBytes/Tie/Pv/Att (plain_last, keyFlat_read, scdNum, scdNum_lt).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Units
import Johnson.Desc.First.Att.K05OwF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf plain_last plain_vals scdNum scdNum_lt keyFlat keyFlat_read)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- The library's point of a sumcheck's output is ldPartIni of the output's point. -/
theorem ptOf_ini {X : Type} (S : SumL K M X) (D : SumH ρ S) (x : X) :
    S.ptOf (D.nx x) = ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt :=
  ldPartVars_ini K S.T.nv S.T.deg S.T.dat (pDummy K S.T.DY) (pDummyD K S.T.DY) D.out.pt

/-- The library's further challenge of a sumcheck's output is the reading of beta. -/
theorem lstOf_read {X : Type} (S : SumL K M X) (D : SumH ρ S) (x : X) : S.lstOf (D.nx x) = ρ.val D.H.beta :=
  (ldPartVars_last K S.T.nv S.T.deg S.T.dat (pDummy K S.T.DY) (pDummyD K S.T.DY) D.out.pt).trans
    (plain_last ρ S.T D.st D.t D.H.mu D.H.eps D.H.rs D.H.sentY D.H.beta D.b D.v)

variable {X : Type}

/-- **The key at the index: RowPrem.** -/
theorem key_prem (P : OwnPar K M X) (d : SumH ρ P.sD) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP P.sD st) (hD : OfP d riders H hh)
    (h : SumAt C st riders H hh Gf) (W : World K) (m : M) {g : Geo} {rho om' : Array E} {f : Aff}
    (hf : leftKey g Gf hh rho om' = some f)
    (g1 : g.lt = (size18 P.D).lt) (g2 : g.lgk = (size18 P.D).lgk) (g3 : g.Lam = (size18 P.D).Lam)
    (g4 : g.HA = (size18 P.D).HA) (g5 : g.NP = (size18 P.D).pairs)
    (hrho : (size18 P.D).lt + (size18 P.D).lgk ≤ rho.size)
    (hn : (size18 P.D).Lam + (size18 P.D).pairs * (size18 P.D).lt ≤ H.v.length)
    (hv : d.v = fun a => ρ.val (H.v.getD (scdNum (size18 P.D) a) zeroE))
    (hri : ∀ a : Fin (size18 P.D).lt, d.st.1.fi a.1 = ρ.val (rho.getD a.1 zeroE))
    (hrg : ∀ a : Fin (size18 P.D).lgk, d.st.1.fg a.1 = ρ.val (rho.getD ((size18 P.D).lt + a.1) zeroE))
    (hom : ∀ b : Fin (size18 P.D).pairs, d.st.1.o' b.1 = ρ.val (om'.getD b.1 zeroE))
    (D1 : P.sD.T.our.par.W d.st (P.msg m) = OnBytes.Road.Hd.place W.slot (P.sD.T.our.par.vars d.st) hh.first)
    (D2 : P.sD.T.our.par.inc d.st (P.msg m) = ρ.val hh.target - C.value ρ W) :
    RowPrem P.sD d C hh f W m := by
  refine ⟨_, leftKey_spec hf, D1, D2, ?_⟩
  have hini := out_ini P.sD d hs hD h
  have hvals : d.out.vals = d.v := plain_vals ρ _ d.st _ _ _ d.H.rs d.H.sentY d.H.beta d.b _
  obtain ⟨vs, e, F, G, used, _, sd, hst⟩ := h
  rw [g1, g2, g3, g4, g5]
  have hz1 : (rho.extract 0 (size18 P.D).lt).size = (size18 P.D).lt := by
    rw [Array.size_extract]
    omega
  have hz2 : (rho.extract (size18 P.D).lt ((size18 P.D).lt + (size18 P.D).lgk)).size = (size18 P.D).lgk := by
    rw [Array.size_extract]
    omega
  rw [keyFlat_read ρ (size18 P.D) _ _ _ _ _ om' _ hz1 hz2
    (ldPartIni (size18 P.D).k (size18 P.D).deg (pDummy K ((size18 P.D).lt + 1)) d.out.pt)
    (fun a => by
      rw [extract_getD _ _ _ _ (by have := a.2; omega)]
      exact (hini ((size18 P.D).jAt a)).trans (by simp [ScdSize.jAt]))
    (fun a => by
      rw [extract_getD _ _ _ _ (by have := a.2; omega)]
      exact hini ((size18 P.D).gAt a))
    (fun a => by
      rw [extract_getD _ _ _ _ (by have := a.2; omega)]
      exact hini ((size18 P.D).iAt a))]
  show scdS (size18 P.D) (fun a => d.st.1.fi a.1) (fun a => d.st.1.fg a.1) (fun b => d.st.1.o' b.1) _ d.out.vals = _
  rw [hvals, hv]
  congr 1
  · funext a
    rw [hri, extract_getD _ _ _ _ (by have := a.2; omega), Nat.zero_add]
  · funext a
    rw [hrg, extract_getD _ _ _ _ (by have := a.2; omega)]
  · funext b
    exact hom b
  · funext a
    have hlt := scdNum_lt (size18 P.D) a
    rw [(hst _ _ _ (sd.ends (scdNum (size18 P.D) a) (by rw [← sd.lenV]; omega))).2.1]

/-- **The key at the index, at the data made of the lists**: RowPrem under (D1), the places of the
second end values of the
score at the index, and the place's five numbers. -/
theorem value_key_prem (P : OwnPar K M X) (Mn : Means K P.D P.C P.kap) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (hs : Said (recOf P rows) h G L) (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail)
    (hnD : ∀ a : (size18 P.D).A, nm.nD a = scdNum (size18 P.D) a) (x0 : Seen K X) (g : Geo)
    (g1 : g.lt = (size18 P.D).lt) (g2 : g.lgk = (size18 P.D).lgk) (g3 : g.Lam = (size18 P.D).Lam)
    (g4 : g.HA = (size18 P.D).HA) (g5 : g.NP = (size18 P.D).pairs)
    (ho : TailOfP (tailData (P.tail Mn).toTail L h nz nm x0) (recOf P rows) h L) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (m : M) {f : Aff} (hf : leftKey g G h.key (chal h.atIndex) h.om' = some f)
    (hc : ∀ i : Fin P.D.nb, P.msg m (P.cAt .s16 (i, true)) = mask (h.atIndex.sEnd + (2 * i.1 + 1)))
    (D1 : P.sD.T.our.par.W (tailData (P.tail Mn).toTail L h nz nm x0).dD.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot
        (P.sD.T.our.par.vars (tailData (P.tail Mn).toTail L h nz nm x0).dD.st) h.key.first) :
    RowPrem (P.tail Mn).toTail.sD (tailData (P.tail Mn).toTail L h nz nm x0).dD
      (batched (recOf P rows).pairs h.om' h.atIndex.sEnd 2 1) h.key f (G.worldOf ρ mask entry) m := by
  have hpt : Blocks.nat (P.sF.ptOf ((tailData (P.tail Mn).toTail L h nz nm x0).dF.nx
      (y6 (P.tail Mn).toTail L h nz nm x0))) = fun j => ρ.val ((chal h.atIndex).getD j zeroE) := by
    exact (congrArg Blocks.nat (ptOf_ini (P.tail Mn).toTail.sF (tailData (P.tail Mn).toTail L h nz nm x0).dF
      (y6 (P.tail Mn).toTail L h nz nm x0))).trans (nat_ini _ _ ho.zF ho.oF hs.sF)
  have hcs : (chal h.atIndex).size = AttSeg.Step.s16.g P.D := chal_size _ _ ho.zF ho.oF hs.sF
  refine key_prem P (tailData (P.tail Mn).toTail L h nz nm x0).dD ho.zD ho.oD hs.sD _ m hf g1 g2 g3 g4 g5 ?_ ?_ ?_ ?_ ?_
    ?_ D1 ?_
  · rw [hcs]
    show P.D.lT + P.D.lg ≤ P.D.lT + P.D.lg + P.D.ln
    omega
  · rw [sumAt_lenV hs.sD]
    exact le_refl _
  · funext a
    show ρ.val (L.HD.v.getD (nm.nD a) zeroE) = _
    rw [hnD]
  · intro a
    exact congrFun hpt a.1
  · intro a
    exact congrFun hpt (P.D.lT + a.1)
  · intro b
    rw [hs.om', powers_getD ρ _ (recOf P rows).pairs _ b.2]
    rfl
  · show ∑ j, incAt (fun i => P.cAt .s16 (i, true)) (fun i : Fin P.D.nb => ρ.val L.xD ^ (i : ℕ) *
      P.sF.lstOf ((tailData (P.tail Mn).toTail L h nz nm x0).dF.nx (y6 (P.tail Mn).toTail L h nz nm x0))) j *
        P.msg m j = _
    have el : P.sF.lstOf ((tailData (P.tail Mn).toTail L h nz nm x0).dF.nx (y6 (P.tail Mn).toTail L h nz nm x0)) =
        ρ.val L.HF.beta := lstOf_read (P.tail Mn).toTail.sF (tailData (P.tail Mn).toTail L h nz nm x0).dF _
    rw [incAt_sum, el, hs.tD K ρ, batched_value, Finset.sum_range, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp := (end_put hs.sF (i := 2 * i.1 + 1) (by show 2 * i.1 + 1 < 2 * P.D.nb; have := i.2; omega)).world ρ mask
      entry
    rw [hp, hc, hs.om', powers_getD ρ _ (recOf P rows).pairs _ i.2]
    ring

/-- **The key at the index at the closed parameters: no place left.** -/
theorem closed_key_prem {M0 : Type} (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C (closedOf P0 Λ G.ns (numsOf h)).kap)
    (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (hz : Sized G)
    (nz : BetasNz ρ L) (nm : TailNums ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail)
    (hnD : ∀ a : (size18 P0.D).A, nm.nD a = scdNum (size18 P0.D) a) (x0 : Seen K X) (g : Geo)
    (g1 : g.lt = (size18 P0.D).lt) (g2 : g.lgk = (size18 P0.D).lgk) (g3 : g.Lam = (size18 P0.D).Lam)
    (g4 : g.HA = (size18 P0.D).HA) (g5 : g.NP = (size18 P0.D).pairs)
    (ho : TailOfP (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) {f : Aff}
    (hf : leftKey g G h.key (chal h.atIndex) h.om' = some f) :
    RowPrem ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sD
      (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0).dD
      (batched (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).pairs h.om' h.atIndex.sEnd 2 1) h.key f
      (G.worldOf ρ (Λ.maskOf m) entry) m :=
  value_key_prem (closedOf P0 Λ G.ns (numsOf h)) Mn rows hs nz nm hnD x0 g g1 g2 g3 g4 g5 ho (Λ.maskOf m) entry m hf
    (fun i => by
      have := (closed_ends P0 Λ rows hs hz m).2.2.2.1 (i, true)
      simpa [OnBytes.Tie.Pv.Att.sc3Num] using this)
    (D1_at ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sD _ ho.zD hs.sD (Λ.maskOf m) entry m fun i =>
      closed_w18 P0 Λ G.ns (numsOf h) m i
        (le_of_lt (put_lt hz (coef_put ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sD ho.zD hs.sD i))))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.closed_key_prem
#print axioms VerifiableInference.Desc.First.Att.P.value_key_prem
#print axioms VerifiableInference.Desc.First.Att.P.ptOf_ini
#print axioms VerifiableInference.Desc.First.Att.P.lstOf_read
#print axioms VerifiableInference.Desc.First.Att.P.key_prem
