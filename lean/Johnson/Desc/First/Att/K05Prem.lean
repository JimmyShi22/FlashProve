-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Prem.lean: K05_law at the library's letters: the rows' premise RowPrem
(Att/K5Law.lean), paid as far as the kind's own rounds reach.

Main names:
  `left3_prem`: for letters made of a sumcheck of products: left has returned f at weights Wt, hW,
    hv, (D1),
    (D2): then RowPrem.
  `value_cells_prem`: the bits' sumcheck: RowPrem under (D1) alone; (D2) is 0 = 0 there: its
    incoming form
    is 0 and it starts from the constant 0.
  `batched_value`, `value_atIndex_prem`: the score at the index: RowPrem under (D1) and the places
    of the
    pairs' scalars' mask entries; (D2) is proved in the ledger's world.

Still a premise here: (D1): the hiding polynomial's coefficients are the world's values under the
slots from
the record's first on (Att/K05SlotsAt.lean gives it from the places).
Sources: what Att/K05WeightsAt.lean and Att/K5Law.lean name; OnBytes/Model/HideLaws.lean
(Aff.value_ofConst).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05WeightsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf sc3Flat sc3Flat_read sc3Num sc3Vals plain_vals)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- **RowPrem at a sumcheck of products.** -/
theorem left3_prem {X : Type} (T3 : Sc3 K) (n : ℕ) (cl : X → (Fin n → K) → K × T3.St) (msg : M → T3.J → K)
    (Lc : X → (Fin n → K) → M → Prop) (D : SumH ρ (SumL.of3 T3 n cl msg Lc)) {C : Aff} {nv : Nat}
    {riders : List E} {H : PscH} {hh : MaskedSum.Heard} {Gf : Fork}
    (h : SumAt C (products nv T3.nb) riders H hh Gf) (W : World K) (m : M) {Wt : Array E} {f : Aff}
    (hf : left Gf hh Wt = some f) (hsz : Wt.size = T3.nb) (hv : D.v = sc3Vals ρ T3.nb H.v)
    (hW : ∀ b : Fin T3.nb, T3.W D.st b (ldPartIni T3.nv (fun _ => 3) (pDummy K 2) D.out.pt) = ρ.val (Wt.getD b.1 zeroE))
    (D1 : T3.plain.our.par.W D.st (msg m) = OnBytes.Road.Hd.place W.slot (T3.plain.our.par.vars D.st) hh.first)
    (D2 : T3.plain.our.par.inc D.st (msg m) = ρ.val hh.target - C.value ρ W) :
    RowPrem (SumL.of3 T3 n cl msg Lc) D C hh f W m := by
  refine ⟨_, left_spec hf, D1, D2, ?_⟩
  obtain ⟨vs, e, F, G, used, e1, sd, hst⟩ := h
  injection e1 with _ e3
  subst e3
  have hvals : D.out.vals = D.v := plain_vals ρ _ D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _
  show ∑ b, T3.W D.st b _ * D.out.vals (b, false) * D.out.vals (b, true) = _
  rw [hsz, sc3Flat_read, hvals, hv]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb := b.2
  have p0 := (hst _ _ _ (sd.ends (2 * b.1) (by show 2 * b.1 < 2 * T3.nb; omega))).2.1
  have p1 := (hst _ _ _ (sd.ends (2 * b.1 + 1) (by show 2 * b.1 + 1 < 2 * T3.nb; omega))).2.1
  rw [p0, p1]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (hW b) ?_) ?_
  · simp [sc3Vals, sc3Num]
  · simp [sc3Vals, sc3Num]

variable {X : Type} (P : OwnPar K M X) (Mn : Means K P.D P.C P.kap)

/-- **The bits' sumcheck at the library's letters: RowPrem under (D1) alone.** -/
theorem value_cells_prem (hk4 : P.kap = 4) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (hs : Said (recOf P rows) h G L) (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail)
    (hnH : ∀ a : Fin P.D.nb × Bool, nm.nH a = sc3Num a) (x0 : Seen K X) (g : Geo) (g1 : g.lt = P.D.lT)
    (g2 : g.lgk = P.D.lg) (ho : TailOfP (tailData (P.tail Mn).toTail L h nz nm x0) (recOf P rows) h L) (W : World K)
    (m : M) {f : Aff} (hf : left G h.cells (wCells g h) = some f)
    (D1 : (bitsSc3 P.kap P.D P.rd (fun _ _ => 0) P.wH P.cH).plain.our.par.W
        (tailData (P.tail Mn).toTail L h nz nm x0).dH.st (P.msg m) =
      OnBytes.Road.Hd.place W.slot ((bitsSc3 P.kap P.D P.rd (fun _ _ => 0) P.wH P.cH).plain.our.par.vars
        (tailData (P.tail Mn).toTail L h nz nm x0).dH.st) h.cells.first) :
    RowPrem (P.tail Mn).toTail.sH (tailData (P.tail Mn).toTail L h nz nm x0).dH (.ofConst zeroE) h.cells f W m := by
  refine left3_prem (bitsSc3 P.kap P.D P.rd (fun _ _ => 0) P.wH P.cH) 0 _ P.msg _
    (tailData (P.tail Mn).toTail L h nz nm x0).dH hs.sH W m hf ?_ ?_
    (value_cells_hW P Mn hk4 rows hs nz nm x0 g g1 g2 ho) D1 ?_
  · unfold wCells
    rw [Array.size_map, hs.om'']
    simp [powersFrom_length]
    rfl
  · funext a
    show ρ.val (L.HH.v.getD (nm.nH a) zeroE) = _
    rw [hnH]
    rfl
  · show ∑ j, (0 : K) * P.msg m j = _
    rw [hs.tH, Aff.value_ofConst, ρ.zero]
    simp

/-! ## The score at the index -/

omit [Fintype K] in
/-- What a batched start form is worth. -/
theorem batched_value (ρ : Reading K) (W : World K) (n : ℕ) (w : Array E) (first step off : ℕ) :
    (batched n w first step off).value ρ W =
      ∑ b ∈ Finset.range n, ρ.val (w.getD b zeroE) * W.slot (first + (step * b + off)) := by
  unfold batched
  induction n with
  | zero => simp [Aff.value_ofConst, ρ.zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Aff.value_addMul, ih,
      Finset.sum_range_succ, Aff.value_slot]

/-- **The score at the index at the library's letters: RowPrem under (D1) and the places of the
pairs' scalars' mask entries.** -/
theorem value_atIndex_prem (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L)
    (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (hnF : ∀ a : Fin P.D.nb × Bool, nm.nF a = sc3Num a)
    (x0 : Seen K X) (g : Geo) (g1 : g.lt = P.D.lT) (g2 : g.lgk = P.D.lg)
    (ho : TailOfP (tailData (P.tail Mn).toTail L h nz nm x0) (recOf P rows) h L) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (m : M) {f : Aff} (hf : left G h.atIndex (wAtIndex g h) = some f)
    (hkF : ∀ i : Fin P.D.nb, P.msg m (P.kF i) = mask (h.maxima + i.1))
    (D1 : (P.st3 .s16 fun p => incAt P.kF fun b => p.o b).plain.our.par.W
        (tailData (P.tail Mn).toTail L h nz nm x0).dF.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot
        ((P.st3 .s16 fun p => incAt P.kF fun b => p.o b).plain.our.par.vars
          (tailData (P.tail Mn).toTail L h nz nm x0).dF.st) h.atIndex.first) :
    RowPrem (P.tail Mn).toTail.sF (tailData (P.tail Mn).toTail L h nz nm x0).dF
      (batched (recOf P rows).pairs h.om h.maxima 1 0) h.atIndex f (G.worldOf ρ mask entry) m := by
  refine left3_prem (P.st3 .s16 fun p => incAt P.kF fun b => p.o b) 0 _ P.msg _
    (tailData (P.tail Mn).toTail L h nz nm x0).dF hs.sF _ m hf ?_ ?_
    (value_atIndex_hW P Mn rows hs nz nm x0 g g1 g2 ho) D1 ?_
  · unfold wAtIndex
    rw [Array.size_map, hs.om]
    simp [powersFrom_length]
    rfl
  · funext a
    show ρ.val (L.HF.v.getD (nm.nF a) zeroE) = _
    rw [hnF]
    rfl
  · show ∑ j, incAt P.kF (fun b : Fin P.D.nb => ρ.val L.xF ^ (b : ℕ)) j * P.msg m j = _
    rw [incAt_sum, hs.tF K ρ, batched_value, Finset.sum_range, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp := (hs.pM i.1 (by rw [hs.lM]; exact i.2)).world ρ mask entry
    rw [show h.maxima + (1 * i.1 + 0) = h.maxima + i.1 by omega, hp, hkF, hs.om,
      powers_getD ρ _ (recOf P rows).pairs _ i.2, ρ.one]
    ring

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.value_atIndex_prem
#print axioms VerifiableInference.Desc.First.Att.P.left3_prem
#print axioms VerifiableInference.Desc.First.Att.P.value_cells_prem
