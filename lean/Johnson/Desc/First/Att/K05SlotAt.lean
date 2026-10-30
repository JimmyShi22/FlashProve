-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SlotAt.lean: the dictionary between the typed places and the ledger's
slots, at the closed parameters (Johnson/Desc/First/Att/K05Closed.lean) and the world of the
message's own mask: for every further scalar and every end value of the own rounds of the kind K5,
the hidden value under its slot is what was sent, less the factor times the mask entry at the typed
place.

Definitions, statements and proofs, in the two forms in which the files
Johnson/Road/Rows/AttPortCl*.lean ask it: (A) W.slot s = r - m k (the premise hs of `lin_holds`,
Johnson/Road/Rows/AttPortClLin.lean); (B) `SlotAt` W T o x j a (Johnson/Road/Rows/AttPortCl.lean).
Main names:
  `hid_slot`: `Put.world` (Johnson/Desc/First/Att/K5Said.lean) at the factor 1: W.slot j is y, read,
    less the mask at j.
  `planes_put`: scalar number j of the plane messages, numbered through, lies under slot plane (j /
    3) + j % 3.
  `slotM`, `slotE`: the numbers of the slots of the further scalars.
  `putE`, `rE_slot`, `rV_slot`, `rF_slot`, `rMD_slot`: (A) for the 5 + lT + 2 scalars of the
    denominator times the output, the two sums of the value product, the pairs' scalars, the 3 npl +
    7 scalars of the unit below the diagonal and the 7 of the unit on it.
  `slotAt_sum`: (B) for one sumcheck, at any letters: from what lies under the end value's slot, the
    typed output's reading (`OutIsP`), the values' tie (`ValsOf`) and the place of the mask entry.
  `tail_slotAt`, `units_slotAt`: (B) for the eight sumchecks at the closed parameters, at numberings
    that are `sc3Num` and `scdNum`.
  `SlotsAt P Mn N W m du dt`, `slot_at`: the dictionary gathered, in thirteen fields, at closedOf P0
    Λ ns N with ns = G.ns and N = numsOf h. `slot_at_landed`: the same at the numberings
    `landedUnits` and `landedTail` (Johnson/Desc/First/Att/K05Cap.lean), where the eight equations
    on the numberings hold by unfolding.
Premises of `slot_at`: `Said`; `Sized` G; `UnitsOfP`, `TailOfP`; `UnitsAreP`, `TailIsP`;
`UnitsVals`, `TailVals`; the eight equations on the numberings.
Used: plain records, pure functions and lemmas on them alone; no routine in a context:
`SlotAt`, `ldPartVars_last`, `sc3Num_lt`, `scdNum_lt`, `beta_last`, `end_put`, `put_lt`, `msg_slot`,
`closed_kV`, `closed_kF`, `closed_c`, `closed_c18`, `closed_ends`, `units_two`, `units_ne`,
`planes_length`.
Limits: nothing on late entries (`LateAt`), and nothing on what the value under a slot means. The
numbers are those of the hearing's record. The places of the hiding polynomials' coefficients are
treated in Johnson/Desc/First/Att/K05SlotsAt.lean. Nothing is claimed on soundness, completeness or
hiding.

-/
import Johnson.Road.Rows.AttPortCl
import Johnson.Desc.First.Att.K05Cap
import Johnson.Desc.First.Att.K05Nz

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH SameRead recOf sc3Num sc3Num_lt scdNum scdNum_lt)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 X : Type}

omit [Fintype K] in
/-- Put.world (Johnson/Desc/First/Att/K5Said.lean) at the factor 1: the hidden value is y, read,
less the mask at j. -/
theorem hid_slot {G : Fork} {j : ℕ} {y : E} (hp : Put G j y oneE) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) :
    (G.worldOf ρ mask entry).slot j = ρ.val y - mask j := by
  rw [hp.world ρ mask entry, ρ.one, one_mul]

/-- The plane messages' scalars, numbered through. -/
theorem planes_put {G : Fork} : ∀ (js : List ℕ) (vs : List (List E)), PlanesAt js vs G →
    ∀ j, j < 3 * vs.length → Put G (js.getD (j / 3) 0 + j % 3) (vs.flatten.getD j zeroE) oneE
  | [], [], _, j, hj => absurd hj (by simp)
  | a :: js, v :: vs, ⟨l3, pv, rest⟩, j, hj => by
    by_cases h3 : j < 3
    · rw [Nat.div_eq_of_lt h3, Nat.mod_eq_of_lt h3, List.flatten_cons,
        List.getD_append _ _ _ _ (by rw [l3]; exact h3)]
      exact pv j (by rw [l3]; exact h3)
    · have hl : (v :: vs).length = vs.length + 1 := rfl
      have e1 : j / 3 = (j - 3) / 3 + 1 := by omega
      have e2 : j % 3 = (j - 3) % 3 := by omega
      rw [e1, e2, List.flatten_cons, List.getD_append_right _ _ _ _ (by rw [l3]; omega), l3]
      exact planes_put js vs rest (j - 3) (by omega)
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- The slot of further scalar number j of the unit below the diagonal. -/
def slotM (N : Nums) (npl j : ℕ) : ℕ := if j < 3 * npl then N.plane (j / 3) + j % 3 else N.seven 0 + (j - 3 * npl)

/-- The slot of further scalar number j of the denominator times the output. -/
def slotE (N : Nums) (lT j : ℕ) : ℕ :=
  if j < 5 then N.five + j else if j < 5 + lT then N.bits + (j - 5) else N.two + (j - (5 + lT))

/-- **(B), for one sumcheck**: `SlotAt` (Johnson/Road/Rows/AttPortCl.lean) at the data heard, from
what lies under the end value's slot, the typed output's reading, the values' tie and the place of
the mask entry. -/
theorem slotAt_sum {M : Type} {Y : Type} (S : SumL K M Y) (D : SumH ρ S) {C : Aff} {vs : List MaskedSum.Var}
    {e : MaskedSum.Ends} {pre : List E} {H : PscH} {hh : MaskedSum.Heard} {G : Fork}
    (hsum : SumAt C (.sum vs e) pre H hh G) (hD : OfP D pre H hh) (hi : OutIsP S D hh) (a : Add S)
    (hv : ValsOf D a) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (μ : S.T.J → K) {J₂ : Type} (u : J₂ → K)
    (y : S.T.A) (hn : a.num y < e.n) (hk : μ (S.T.cAt y) = mask (hh.sEnd + a.num y)) :
    OnBytes.Road.Rows.SlotAt (G.worldOf ρ mask entry) S.T D.out (Sum.elim μ u) (hh.sEnd + a.num y) y := by
  have hb : hh.r.getLastD zeroE = H.beta := beta_last hsum
  have hl : S.T.our.lst D.out.st (S.T.our.par.hp D.out.st D.out.pt) = ρ.val H.beta :=
    (ldPartVars_last K S.T.nv S.T.deg S.T.dat (pDummy K S.T.DY) (pDummyD K S.T.DY) D.out.pt).trans
      (hi.last.trans (by rw [hb]))
  unfold OnBytes.Road.Rows.SlotAt
  rw [(end_put hsum hn).world ρ mask entry, hi.vals, hv.1 y, hD.H, hl]
  show _ = _ - _ * μ (S.T.cAt y)
  rw [hk]

section Closed
variable (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
  (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C
    (closedOf P0 Λ G.ns (numsOf h)).kap)
  (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (hz : Sized G)
  (entry : ℕ → ℕ → ℕ → K) (m : Mg)
include hs hz

omit hz in
/-- What lies under the slot of further scalar number j of the denominator times the output. -/
theorem putE (j : ℕ) (hj : j < 5 + P0.D.lT + 2) :
    Put G (slotE (numsOf h) P0.D.lT j) (L.ridersE.getD j zeroE) oneE := by
  have hI : L.vI.length = P0.D.lT := hs.lI
  unfold Lists.ridersE slotE
  rw [units_ne hs.units (by simp [recOf]), List.nil_append]
  by_cases h5 : j < 5
  · rw [if_pos h5, List.getD_append _ _ _ _ (by rw [hs.l5]; exact h5)]
    exact hs.p5 j (by rw [hs.l5]; exact h5)
  · rw [if_neg h5, List.getD_append_right _ _ _ _ (by rw [hs.l5]; omega), hs.l5]
    by_cases hb : j < 5 + P0.D.lT
    · rw [if_pos hb, List.getD_append _ _ _ _ (by rw [hI]; omega)]
      exact hs.pI (j - 5) (by rw [hI]; omega)
    · rw [if_neg hb, List.getD_append_right _ _ _ _ (by rw [hI]; omega), hI,
        show j - 5 - P0.D.lT = j - (5 + P0.D.lT) by omega]
      exact hs.p2 (j - (5 + P0.D.lT)) (by rw [hs.l2]; omega)

/-- **(A) The further scalars of the denominator times the output.** -/
theorem rE_slot (dt : TailH ρ ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail)
    (ho : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L) (j : Fin (5 + P0.D.lT + 2)) :
    (G.worldOf ρ (Λ.maskOf m) entry).slot (slotE (numsOf h) P0.D.lT j.1) =
      dt.dE.rd j - (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).kE j) := by
  have hp := putE P0 Λ rows hs j.1 j.2
  have e : dt.dE.rd j = ρ.val (L.ridersE.getD j.1 zeroE) := by
    show ρ.val (dt.dE.r.getD j.1 zeroE) = _
    rw [ho.oE.r]
  have k : (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).kE j) =
      Λ.maskOf m (slotE (numsOf h) P0.D.lT j.1) :=
    msg_slot P0 Λ G.ns (numsOf h) m (le_of_lt (put_lt hz hp))
  rw [hid_slot hp, e, k]

/-- **(A) The two sums of the value product.** -/
theorem rV_slot (dt : TailH ρ ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail)
    (ho : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L) (j : Fin 2) :
    (G.worldOf ρ (Λ.maskOf m) entry).slot (h.values + j.1) =
      dt.dVM.rd j - (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).kV j) := by
  have hp := hs.pC j.1 (by rw [hs.lC]; exact j.2)
  have e : dt.dVM.rd j = ρ.val (L.vC.getD j.1 zeroE) := by
    show ρ.val (dt.dVM.r.getD j.1 zeroE) = _
    rw [ho.oM.r]
  rw [hid_slot hp, e, closed_kV P0 Λ G.ns (numsOf h) m j (le_of_lt (put_lt hz hp))]
  rfl

/-- **(A) The pairs' scalars.** -/
theorem rF_slot (dt : TailH ρ ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail)
    (ho : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L) (b : Fin P0.D.nb) :
    (G.worldOf ρ (Λ.maskOf m) entry).slot (h.maxima + b.1) =
      ρ.val (dt.mx.getD b.1 zeroE) -
        (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).kF b) := by
  have hM : L.vM.length = P0.D.nb := hs.lM
  have hp := hs.pM b.1 (by rw [hM]; exact b.2)
  rw [hid_slot hp, ho.mx, closed_kF P0 Λ G.ns (numsOf h) m b (le_of_lt (put_lt hz hp))]
  rfl

/-- **(A) The further scalars of the two units of the scores.** -/
theorem rMD_slot (du : UnitsH ρ ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units)
    (hu : UnitsOfP ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units du
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score h.scores.toList L.planes.flatten L.units) :
    (∀ j : Fin (3 * P0.npl + 7), (G.worldOf ρ (Λ.maskOf m) entry).slot (slotM (numsOf h) P0.npl j.1) =
      du.1.rd j - (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).kM j)) ∧
    ∀ j : Fin 7, (G.worldOf ρ (Λ.maskOf m) entry).slot ((numsOf h).seven 1 + j.1) =
      du.2.1.rd j - (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).kD j) := by
  obtain ⟨o1, o2, v1, H1, v2, H2, e1, e2, ⟨a1, a2, _, _⟩, ⟨b1, b2, _, _⟩⟩ := units_two hs.units
  rw [e1, e2] at hu
  obtain ⟨_, u1, _, u2, _⟩ := hu
  have hn : L.planes.length = P0.npl := hs.nPlanes
  have hl : L.planes.flatten.length = 3 * P0.npl := by rw [planes_length hs.planes, hn]
  have s0 : (numsOf h).seven 0 = o1.1 := by simp [Nums.seven, numsOf, e1]
  have s1 : (numsOf h).seven 1 = o2.1 := by simp [Nums.seven, numsOf, e1]
  constructor
  · intro j
    have hp : Put G (slotM (numsOf h) P0.npl j.1) ((L.planes.flatten ++ v1).getD j.1 zeroE) oneE := by
      unfold slotM
      by_cases hj : j.1 < 3 * P0.npl
      · rw [if_pos hj, List.getD_append _ _ _ _ (by rw [hl]; exact hj)]
        exact planes_put _ _ hs.planes j.1 (by rw [hn]; exact hj)
      · rw [if_neg hj, List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, s0]
        exact a2 (j.1 - 3 * P0.npl) (by rw [a1]; have := j.2; omega)
    have e : du.1.rd j = ρ.val ((L.planes.flatten ++ v1).getD j.1 zeroE) := by
      show ρ.val (du.1.r.getD j.1 zeroE) = _
      rw [u1.r]
    have k : (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).kM j) =
        Λ.maskOf m (slotM (numsOf h) P0.npl j.1) :=
      msg_slot P0 Λ G.ns (numsOf h) m (le_of_lt (put_lt hz hp))
    rw [hid_slot hp, e, k]
  · intro j
    have hp : Put G ((numsOf h).seven 1 + j.1) (([] ++ v2).getD j.1 zeroE) oneE := by
      rw [s1, List.nil_append]
      exact b2 j.1 (by rw [b1]; exact j.2)
    have e : du.2.1.rd j = ρ.val (([] ++ v2).getD j.1 zeroE) := by
      show ρ.val (du.2.1.r.getD j.1 zeroE) = _
      rw [u2.r]
    have k : (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).kD j) =
        Λ.maskOf m ((numsOf h).seven 1 + j.1) :=
      msg_slot P0 Λ G.ns (numsOf h) m (le_of_lt (put_lt hz hp))
    rw [hid_slot hp, e, k]

/-- **(B) The end values of the tail's six sumchecks**, at any numberings that are the library's. -/
theorem tail_slotAt (dt : TailH ρ ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail)
    (ho : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (hi : TailIsP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (A : TailAdd ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail) (hv : TailVals dt A)
    (nE : ∀ y : Fin P0.D.nb × Bool, A.aE.num y = sc3Num y) (nM : ∀ y : Fin P0.D.nb × Bool, A.aM.num y = sc3Num y)
    (nVD : ∀ y : Fin P0.D.nb × Bool, A.aVD.num y = sc3Num y) (nF : ∀ y : Fin P0.D.nb × Bool, A.aF.num y = sc3Num y)
    (nD : ∀ y : (size18 P0.D).A, A.aD.num y = scdNum (size18 P0.D) y)
    (nH : ∀ y : Fin P0.D.nb × Bool, A.aH.num y = sc3Num y) {J₂ : Type} (u : J₂ → K) :
    (∀ y : Fin P0.D.nb × Bool, OnBytes.Road.Rows.SlotAt (G.worldOf ρ (Λ.maskOf m) entry)
      ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail.sE.T dt.dE.out
      (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m) u) (h.division.sEnd + sc3Num y) y) ∧
    (∀ y : Fin P0.D.nb × Bool, OnBytes.Road.Rows.SlotAt (G.worldOf ρ (Λ.maskOf m) entry)
      ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail.sVM.T dt.dVM.out
      (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m) u) (h.below.sEnd + sc3Num y) y) ∧
    (∀ y : Fin P0.D.nb × Bool, OnBytes.Road.Rows.SlotAt (G.worldOf ρ (Λ.maskOf m) entry)
      ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail.sVD.T dt.dVD.out
      (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m) u) (h.on.sEnd + sc3Num y) y) ∧
    (∀ y : Fin P0.D.nb × Bool, OnBytes.Road.Rows.SlotAt (G.worldOf ρ (Λ.maskOf m) entry)
      ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail.sF.T dt.dF.out
      (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m) u) (h.atIndex.sEnd + sc3Num y) y) ∧
    (∀ y : (size18 P0.D).A, OnBytes.Road.Rows.SlotAt (G.worldOf ρ (Λ.maskOf m) entry)
      ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail.sD.T dt.dD.out
      (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m) u) (h.key.sEnd + scdNum (size18 P0.D) y) y) ∧
    ∀ y : Fin P0.D.nb × Bool, OnBytes.Road.Rows.SlotAt (G.worldOf ρ (Λ.maskOf m) entry)
      ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail.sH.T dt.dH.out
      (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m) u) (h.cells.sEnd + sc3Num y) y := by
  obtain ⟨cE, cM, cVD, cF, cH⟩ := closed_ends P0 Λ rows hs hz m
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · have t := slotAt_sum _ dt.dE hs.sE ho.oE hi.iE A.aE hv.vE (Λ.maskOf m) entry
      ((closedOf P0 Λ G.ns (numsOf h)).msg m) u y (by rw [nE]; exact sc3Num_lt y) (by rw [nE]; exact cE y)
    rwa [nE] at t
  · have t := slotAt_sum _ dt.dVM hs.sM ho.oM hi.iM A.aM hv.vM (Λ.maskOf m) entry
      ((closedOf P0 Λ G.ns (numsOf h)).msg m) u y (by rw [nM]; exact sc3Num_lt y) (by rw [nM]; exact cM y)
    rwa [nM] at t
  · have t := slotAt_sum _ dt.dVD hs.sVD ho.oVD hi.iVD A.aVD hv.vVD (Λ.maskOf m) entry
      ((closedOf P0 Λ G.ns (numsOf h)).msg m) u y (by rw [nVD]; exact sc3Num_lt y) (by rw [nVD]; exact cVD y)
    rwa [nVD] at t
  · have t := slotAt_sum _ dt.dF hs.sF ho.oF hi.iF A.aF hv.vF (Λ.maskOf m) entry
      ((closedOf P0 Λ G.ns (numsOf h)).msg m) u y (by rw [nF]; exact sc3Num_lt y) (by rw [nF]; exact cF y)
    rwa [nF] at t
  · have cD := closed_c18 P0 Λ G.ns (numsOf h) m y
      (le_of_lt (put_lt hz (end_put hs.sD (scdNum_lt (size18 P0.D) y))))
    have t := slotAt_sum _ dt.dD hs.sD ho.oD hi.iD A.aD hv.vD (Λ.maskOf m) entry
      ((closedOf P0 Λ G.ns (numsOf h)).msg m) u y (by rw [nD]; exact scdNum_lt (size18 P0.D) y)
      (by rw [nD]; exact cD)
    rwa [nD] at t
  · have t := slotAt_sum _ dt.dH hs.sH ho.oH hi.iH A.aH hv.vH (Λ.maskOf m) entry
      ((closedOf P0 Λ G.ns (numsOf h)).msg m) u y (by rw [nH]; exact sc3Num_lt y) (by rw [nH]; exact cH y)
    rwa [nH] at t

/-- **(B) The end values of the two units of the scores.** -/
theorem units_slotAt (du : UnitsH ρ ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units)
    (hu : UnitsOfP ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units du
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score h.scores.toList L.planes.flatten L.units)
    (hi : UnitsAreP ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units du h.scores.toList)
    (A : UnitsAdd ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units)
    (hv : UnitsVals ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units du A)
    (n1 : ∀ y : Fin P0.D.nb × Bool, A.1.num y = sc3Num y) (n2 : ∀ y : Fin P0.D.nb × Bool, A.2.1.num y = sc3Num y)
    {J₂ : Type} (u : J₂ → K) :
    (∀ y : Fin P0.D.nb × Bool, OnBytes.Road.Rows.SlotAt (G.worldOf ρ (Λ.maskOf m) entry)
      (closedOf P0 Λ G.ns (numsOf h)).uM.T du.1.out
      (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m) u) ((numsOf h).uEnd 0 + sc3Num y) y) ∧
    ∀ y : Fin P0.D.nb × Bool, OnBytes.Road.Rows.SlotAt (G.worldOf ρ (Λ.maskOf m) entry)
      (closedOf P0 Λ G.ns (numsOf h)).uD.T du.2.1.out
      (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m) u) ((numsOf h).uEnd 1 + sc3Num y) y := by
  obtain ⟨o1, o2, v1, H1, v2, H2, e1, e2, ⟨_, _, a3, _⟩, ⟨_, _, b3, _⟩⟩ := units_two hs.units
  rw [e1, e2] at hu
  rw [e1] at hi
  obtain ⟨_, u1, _, u2, _⟩ := hu
  obtain ⟨i1, _, i2, _, _⟩ := hi
  have s0 : (numsOf h).uEnd 0 = o1.2.sEnd := by simp [Nums.uEnd, numsOf, e1]
  have s1 : (numsOf h).uEnd 1 = o2.2.sEnd := by simp [Nums.uEnd, numsOf, e1]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · have hp := end_put a3 (sc3Num_lt y)
    have t := slotAt_sum _ du.1 a3 u1 i1 A.1 hv.1 (Λ.maskOf m) entry
      ((closedOf P0 Λ G.ns (numsOf h)).msg m) u y (by rw [n1]; exact sc3Num_lt y) (by
        rw [n1, ← s0]
        exact closed_c P0 Λ G.ns (numsOf h) m .s6b y (by
          show (numsOf h).uEnd 0 + sc3Num y ≤ G.ns
          rw [s0]
          exact le_of_lt (put_lt hz hp)))
    rw [n1, ← s0] at t
    exact t
  · have hp := end_put b3 (sc3Num_lt y)
    have t := slotAt_sum _ du.2.1 b3 u2 i2 A.2.1 hv.2.1 (Λ.maskOf m) entry
      ((closedOf P0 Λ G.ns (numsOf h)).msg m) u y (by rw [n2]; exact sc3Num_lt y) (by
        rw [n2, ← s1]
        exact closed_c P0 Λ G.ns (numsOf h) m .s6d y (by
          show (numsOf h).uEnd 1 + sc3Num y ≤ G.ns
          rw [s1]
          exact le_of_lt (put_lt hz hp)))
    rw [n2, ← s1] at t
    exact t

end Closed

/-- **The dictionary, gathered.** N: the slots' numbers. (A) the further scalars; (B) the end
values. -/
structure SlotsAt {Mg : Type} (P : OwnPar K Mg X) (Mn : Means K P.D P.C P.kap) (N : Nums) (W : World K) (m : Mg)
    (du : UnitsH ρ (P.own Mn).units) (dt : TailH ρ (P.own Mn).tail) : Prop where
  rM : ∀ j : Fin (3 * P.npl + 7), W.slot (slotM N P.npl j.1) = du.1.rd j - P.msg m (P.kM j)
  rD : ∀ j : Fin 7, W.slot (N.seven 1 + j.1) = du.2.1.rd j - P.msg m (P.kD j)
  rE : ∀ j : Fin (5 + P.D.lT + 2), W.slot (slotE N P.D.lT j.1) = dt.dE.rd j - P.msg m (P.kE j)
  rV : ∀ j : Fin 2, W.slot (N.values + j.1) = dt.dVM.rd j - P.msg m (P.kV j)
  rF : ∀ b : Fin P.D.nb, W.slot (N.maxima + b.1) = ρ.val (dt.mx.getD b.1 zeroE) - P.msg m (P.kF b)
  eUM : ∀ (J₂ : Type) (u : J₂ → K) (y : Fin P.D.nb × Bool), OnBytes.Road.Rows.SlotAt W P.uM.T du.1.out
    (Sum.elim (P.msg m) u) (N.uEnd 0 + sc3Num y) y
  eUD : ∀ (J₂ : Type) (u : J₂ → K) (y : Fin P.D.nb × Bool), OnBytes.Road.Rows.SlotAt W P.uD.T du.2.1.out
    (Sum.elim (P.msg m) u) (N.uEnd 1 + sc3Num y) y
  eE : ∀ (J₂ : Type) (u : J₂ → K) (y : Fin P.D.nb × Bool), OnBytes.Road.Rows.SlotAt W (P.own Mn).tail.sE.T
    dt.dE.out (Sum.elim (P.msg m) u) (N.eE + sc3Num y) y
  eVM : ∀ (J₂ : Type) (u : J₂ → K) (y : Fin P.D.nb × Bool), OnBytes.Road.Rows.SlotAt W (P.own Mn).tail.sVM.T
    dt.dVM.out (Sum.elim (P.msg m) u) (N.eM + sc3Num y) y
  eVD : ∀ (J₂ : Type) (u : J₂ → K) (y : Fin P.D.nb × Bool), OnBytes.Road.Rows.SlotAt W (P.own Mn).tail.sVD.T
    dt.dVD.out (Sum.elim (P.msg m) u) (N.eVD + sc3Num y) y
  eF : ∀ (J₂ : Type) (u : J₂ → K) (y : Fin P.D.nb × Bool), OnBytes.Road.Rows.SlotAt W (P.own Mn).tail.sF.T
    dt.dF.out (Sum.elim (P.msg m) u) (N.eF + sc3Num y) y
  eK : ∀ (J₂ : Type) (u : J₂ → K) (y : (size18 P.D).A), OnBytes.Road.Rows.SlotAt W (P.own Mn).tail.sD.T
    dt.dD.out (Sum.elim (P.msg m) u) (N.eD + scdNum (size18 P.D) y) y
  eH : ∀ (J₂ : Type) (u : J₂ → K) (y : Fin P.D.nb × Bool), OnBytes.Road.Rows.SlotAt W (P.own Mn).tail.sH.T
    dt.dH.out (Sum.elim (P.msg m) u) (N.eH + sc3Num y) y

/-- **slot_at**: at the closed parameters whose numbers are the hearing's and whose ledger has G's
slots, in the world of the message's own mask, the dictionary holds of the data made of what was
heard. -/
theorem slot_at (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) {h : Heard} {G : Fork}
    (hns : ns = G.ns) (hN : N = numsOf h)
    (Mn : Means K (closedOf P0 Λ ns N).D (closedOf P0 Λ ns N).C (closedOf P0 Λ ns N).kap) (rows : ℕ) {L : Lists}
    (hs : Said (recOf (closedOf P0 Λ ns N) rows) h G L) (hz : Sized G) (entry : ℕ → ℕ → ℕ → K) (m : Mg)
    (du : UnitsH ρ ((closedOf P0 Λ ns N).own Mn).units) (dt : TailH ρ ((closedOf P0 Λ ns N).own Mn).tail)
    (hu : UnitsOfP ((closedOf P0 Λ ns N).own Mn).units du (recOf (closedOf P0 Λ ns N) rows).score
      h.scores.toList L.planes.flatten L.units)
    (ho : TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L)
    (iu : UnitsAreP ((closedOf P0 Λ ns N).own Mn).units du h.scores.toList)
    (it : TailIsP dt (recOf (closedOf P0 Λ ns N) rows) h L)
    (Au : UnitsAdd ((closedOf P0 Λ ns N).own Mn).units)
    (vu : UnitsVals ((closedOf P0 Λ ns N).own Mn).units du Au)
    (At : TailAdd ((closedOf P0 Λ ns N).own Mn).tail) (vt : TailVals dt At)
    (n1 : ∀ y : Fin P0.D.nb × Bool, Au.1.num y = sc3Num y) (n2 : ∀ y : Fin P0.D.nb × Bool, Au.2.1.num y = sc3Num y)
    (nE : ∀ y : Fin P0.D.nb × Bool, At.aE.num y = sc3Num y) (nM : ∀ y : Fin P0.D.nb × Bool, At.aM.num y = sc3Num y)
    (nVD : ∀ y : Fin P0.D.nb × Bool, At.aVD.num y = sc3Num y)
    (nF : ∀ y : Fin P0.D.nb × Bool, At.aF.num y = sc3Num y)
    (nD : ∀ y : (size18 P0.D).A, At.aD.num y = scdNum (size18 P0.D) y)
    (nH : ∀ y : Fin P0.D.nb × Bool, At.aH.num y = sc3Num y) :
    SlotsAt (closedOf P0 Λ ns N) Mn N (G.worldOf ρ (Λ.maskOf m) entry) m du dt := by
  subst hns hN
  have a := rMD_slot P0 Λ Mn rows hs hz entry m du hu
  exact ⟨a.1, a.2, rE_slot P0 Λ Mn rows hs hz entry m dt ho, rV_slot P0 Λ Mn rows hs hz entry m dt ho,
    rF_slot P0 Λ Mn rows hs hz entry m dt ho,
    fun _ u => (units_slotAt P0 Λ Mn rows hs hz entry m du hu iu Au vu n1 n2 u).1,
    fun _ u => (units_slotAt P0 Λ Mn rows hs hz entry m du hu iu Au vu n1 n2 u).2,
    fun _ u => (tail_slotAt P0 Λ Mn rows hs hz entry m dt ho it At vt nE nM nVD nF nD nH u).1,
    fun _ u => (tail_slotAt P0 Λ Mn rows hs hz entry m dt ho it At vt nE nM nVD nF nD nH u).2.1,
    fun _ u => (tail_slotAt P0 Λ Mn rows hs hz entry m dt ho it At vt nE nM nVD nF nD nH u).2.2.1,
    fun _ u => (tail_slotAt P0 Λ Mn rows hs hz entry m dt ho it At vt nE nM nVD nF nD nH u).2.2.2.1,
    fun _ u => (tail_slotAt P0 Λ Mn rows hs hz entry m dt ho it At vt nE nM nVD nF nD nH u).2.2.2.2.1,
    fun _ u => (tail_slotAt P0 Λ Mn rows hs hz entry m dt ho it At vt nE nM nVD nF nD nH u).2.2.2.2.2⟩

/-- **`slot_at` at the library's numberings**, as `CapSays` and `RowSays` hold the values' ties: the
eight equations hold by unfolding. -/
theorem slot_at_landed (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) {h : Heard} {G : Fork}
    (hns : ns = G.ns) (hN : N = numsOf h)
    (Mn : Means K (closedOf P0 Λ ns N).D (closedOf P0 Λ ns N).C (closedOf P0 Λ ns N).kap) (rows : ℕ) {L : Lists}
    (hs : Said (recOf (closedOf P0 Λ ns N) rows) h G L) (hz : Sized G) (nz : BetasNz ρ L)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) (s0 s1 : Seen K X)
    (du : UnitsH ρ ((closedOf P0 Λ ns N).own Mn).units) (dt : TailH ρ ((closedOf P0 Λ ns N).own Mn).tail)
    (hu : UnitsOfP ((closedOf P0 Λ ns N).own Mn).units du (recOf (closedOf P0 Λ ns N) rows).score
      h.scores.toList L.planes.flatten L.units)
    (ho : TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L)
    (vu : UnitsVals ((closedOf P0 Λ ns N).own Mn).units du
      (unitsAdd (ρ := ρ) ((closedOf P0 Λ ns N).own Mn).units (landedUnits (closedOf P0 Λ ns N) Mn)
        L.planes.flatten L.units s0))
    (vt : TailVals dt (tailAdd ((closedOf P0 Λ ns N).own Mn).tail L h nz (landedTail (closedOf P0 Λ ns N) Mn) s1))
    (iu : UnitsAreP ((closedOf P0 Λ ns N).own Mn).units du h.scores.toList)
    (it : TailIsP dt (recOf (closedOf P0 Λ ns N) rows) h L) :
    SlotsAt (closedOf P0 Λ ns N) Mn N (G.worldOf ρ (Λ.maskOf m) entry) m du dt :=
  slot_at P0 Λ ns N hns hN Mn rows hs hz entry m du dt hu ho iu it _ vu _ vt (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

end VerifiableInference.Desc.First.Att.P
