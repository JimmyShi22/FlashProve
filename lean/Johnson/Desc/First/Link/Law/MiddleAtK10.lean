-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MiddleAtK10.lean: "Middle"
(Johnson/Desc/First/Close/Law/SampleTie.lean: SampleFits' second debt: the member's view's form of
the library's sample row at the seed, at (row, place), is the program's sample row's coefficient on
the entry that belongs to the index) AT THE GROUPS THAT THE PROGRAMS HAVE ((rowsPort …).keep kp,
Johnson/Top/H/SwitchKept.lean: groupFullLayK is one), FOR KIND K1's SAMPLE ROW AT A SEED THAT IT
READS AS. A definition, a statement and its proof.

How. The view of a member of a shape of the programs moves nothing (membPort_fm_main | _mask,
Close/Law/ViewAt.lean). On a real entry K1's sample row has the coefficient of the library's row
(K1's coef_port_main | _mask, Johnson/Desc/K1/Law/Port4.lean). What is left is where the index's
entry lies.

  BackAt           THE NAMED PREMISE: the layout against the arrangement, on indices: at a vertex
                   that holds the member's row r, the entry that belongs to the index (vertex, place
                   x) is r + 2 ^ ‹row bits› · x: main · kept slot · mask
  middle_of        K1.Tie · ReadsOne … ρ · BackAt ⊢ Middle N T L ‹K1's sample row› o a ‹the
                   member's own form at ρ›

Limits. BackAt is a premise: shown of nothing (it stands beside BlockAt: CubeFits |
cubeFits_full are near). SampleFits' other debt BlockAt is not touched. No soundness statement.

-/
import Johnson.Top.H.SwitchKept
import Johnson.Desc.First.Close.Law.ViewAt
import Johnson.Desc.First.Close.Law.SampleTie
import Johnson.Desc.K1.Law.Port4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Cb Cb.Pv Johnson.Pack Johnson.Top.H KObj
open VerifiableInference.Desc.First.Close (SlotNames Middle atMem_self membPort_fm_main
  membPort_fm_mask)

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]

/-- **The layout against the arrangement, on indices.** -/
structure BackAt (N : SlotNames ((rowsPort cs l mem s e oM oZ hM hZ).keep kp)) (T : Statement)
    (L : GroupLayout) (o : ℕ) (a : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).G.A) : Prop where
  main : ∀ (b : Fin (s.h + s.g) → Bool) (r : Fin (l.get a.1).1.mainRows) (x : Fin s.C.l),
    ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh.am.src (b, none) = some ⟨a, r⟩ →
    mainBack T L o (Sz.rowNo b + 2 ^ (s.h + s.g) * x.val) =
      r.val + 2 ^ k1 (l.get a.1).1 * x.val
  kept : ∀ (q : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp)
    (r : Fin (l.get a.1).1.mainRows) (x : Fin s.C.l),
    ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).kept q = ⟨a, r⟩ →
    N.idx q x = r.val + 2 ^ k1 (l.get a.1).1 * x.val
  mask : ∀ (b : Fin s.h → Bool) (r : Fin (l.get a.1).1.maskRows) (y : Fin s.Z.l),
    ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh.az.src b = some ⟨a, r⟩ →
    maskBack T L o (Sz.rowNo b + 2 ^ s.h * y.val) = r.val + 2 ^ k2 (l.get a.1).1 * y.val

/-- **Middle, for kind K1's sample row at a seed that it reads as.** -/
theorem middle_of (N : SlotNames ((rowsPort cs l mem s e oM oZ hM hZ).keep kp)) (T : Statement)
    (L : GroupLayout) (o : ℕ) (a : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).G.A)
    (hT : K1.Tie cs (l.get a.1).1) (z : List E) (β y : E)
    (ρ : (Fin (bitsZ cs (l.get a.1).1) → GE) × GEˣ) (rd : K1.ReadsOne cs (l.get a.1).1 z β ρ)
    (u : ((sigOf cs l).om a.1).Z.S) (hB : BackAt cs l mem s e oM oZ hM hZ kp N T L o a) :
    Middle N T L (K1.sampleRow (K1.Msg.of cs (l.get a.1).1) o z β 0 y) o a
      (Slf.atMem (Jf := fun a : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).G.A =>
        ((sigOf cs l).om a.1).C.J) a (((sigOf cs l).om a.1).row u) ρ) where
  main := fun b r x hs => by
    have hr : r.val < (l.get a.1).1.mainRows := r.isLt
    have hx : x.val < s.C.l := x.isLt
    have h0 : (l.get a.1).1.mainRows ≠ 0 := by omega
    have hc := hM a.1 a.2 h0
    have e1 := atMem_self (Jf := fun a : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).G.A =>
      ((sigOf cs l).om a.1).C.J) a (((sigOf cs l).om a.1).row u) ρ
    refine (congrArg (fun v => (((rowsPort cs l mem s e oM oZ hM hZ).keep kp).view a).fm v
      (Sum.inl (r, x))) e1).trans ?_
    refine Eq.trans ?_ (congrArg (fun i => readE ((K1.sampleRow (K1.Msg.of cs (l.get a.1).1) o z β
      0 y).coefficient o .main i)) (hB.main b r x hs)).symm
    exact (membPort_fm_main cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2)
      (hZ a.1 a.2) _ r x ⟨x.val, by rw [hc]; exact hx⟩ rfl).trans
      (K1.coef_port_main hT (l.get a.1).2 o z β y ρ rd (r, ⟨x.val, by
        have := hx; rw [← hc] at this; exact this⟩)).symm
  kept := fun q r x hq => by
    have hr : r.val < (l.get a.1).1.mainRows := r.isLt
    have hx : x.val < s.C.l := x.isLt
    have h0 : (l.get a.1).1.mainRows ≠ 0 := by omega
    have hc := hM a.1 a.2 h0
    have e1 := atMem_self (Jf := fun a : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).G.A =>
      ((sigOf cs l).om a.1).C.J) a (((sigOf cs l).om a.1).row u) ρ
    refine (congrArg (fun v => (((rowsPort cs l mem s e oM oZ hM hZ).keep kp).view a).fm v
      (Sum.inl (r, x))) e1).trans ?_
    refine Eq.trans ?_ (congrArg (fun i => readE ((K1.sampleRow (K1.Msg.of cs (l.get a.1).1) o z β
      0 y).coefficient o .main i)) (hB.kept q r x hq)).symm
    exact (membPort_fm_main cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2)
      (hZ a.1 a.2) _ r x ⟨x.val, by rw [hc]; exact hx⟩ rfl).trans
      (K1.coef_port_main hT (l.get a.1).2 o z β y ρ rd (r, ⟨x.val, by
        have := hx; rw [← hc] at this; exact this⟩)).symm
  mask := fun b r x hs => by
    have hr : r.val < (l.get a.1).1.maskRows := r.isLt
    have hx : x.val < s.Z.l := x.isLt
    have h0 : (l.get a.1).1.maskRows ≠ 0 := by omega
    have hc := hZ a.1 a.2 h0
    have e1 := atMem_self (Jf := fun a : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).G.A =>
      ((sigOf cs l).om a.1).C.J) a (((sigOf cs l).om a.1).row u) ρ
    refine (congrArg (fun v => (((rowsPort cs l mem s e oM oZ hM hZ).keep kp).view a).fm v
      (Sum.inr (r, x))) e1).trans ?_
    refine Eq.trans ?_ (congrArg (fun i => readE ((K1.sampleRow (K1.Msg.of cs (l.get a.1).1) o z β
      0 y).coefficient o .mask i)) (hB.mask b r x hs)).symm
    exact (membPort_fm_mask cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2)
      (hZ a.1 a.2) _ r x ⟨x.val, by rw [hc]; exact hx⟩ rfl).trans
      (K1.coef_port_mask hT (l.get a.1).2 o z β y ρ rd (r, ⟨x.val, by
        have := hx; rw [← hc] at this; exact this⟩)).symm

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.middle_of
