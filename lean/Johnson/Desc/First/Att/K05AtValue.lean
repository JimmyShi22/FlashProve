-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05AtValue.lean: K05_law at the library's letters A := P.own Mn
(Cb/Pv/Att/OwnSteps.lean: the letters of an attention sub-proof's own rounds at the library's
description
of a segment; Cb/Pv/Att/OwnAt.lean proves that chain knowledge sound without a premise).

Paid here, as lemmas at these letters: the letters' numbers (ownAt_fits, where the plan's record is
recOf P rows and P.kap = 4), and the letters' claims, all eight: each claim's first part is the
reading of
the part's record's target.

Main names:
  `powersFrom_read`, `powers_getD`: the part's powersFrom, read.
  `value_tail_targets`; `LastRider`, `units_targets_of_last`, `last_uM`, `last_uD`, `last_own`.
  `K05_at_value`: the data exist, the letters' claims hold of them, and the chain's last claim on
    the run
    holds exactly if the kind's bill is paid, under UnitsPrem and TailPrem alone.

Still premises here: the rows' three equations (Att/K05Cap.lean pays them at parameters whose places
are
the slots' numbers, under the lookup's points' premises).
Sources: Cb/Pv/Att/OwnSteps.lean; Gaps.lean (TailG.toTail); OnBytes/Tie/Pv/Att/OwnAtFits.lean
(recOf,
ownAt_fits); OnBytes/Tie/Pv/Psc/PscRead.lean (rd).
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Att.OwnAtFits
import Johnson.Desc.First.Att.K5Claims
import Johnson.Desc.First.Att.K05Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf plain_vals)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type}

omit [Fintype K] in
theorem powersFrom_read (ρ : Reading K) (x : E) : ∀ (n : Nat) (a : E) (i : Nat), i < n →
    ρ.val ((MaskedSum.powersFrom x n a).getD i zeroE) = ρ.val a * ρ.val x ^ i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, 0, _ => by simp [MaskedSum.powersFrom]
  | n + 1, a, i + 1, h => by
    rw [MaskedSum.powersFrom, List.getD_cons_succ, powersFrom_read ρ x n _ i (by omega), ρ.mul]
    ring

omit [Fintype K] in
theorem powers_getD (ρ : Reading K) (x : E) (n i : Nat) (h : i < n) :
    ρ.val ((MaskedSum.powersFrom x n oneE).toArray.getD i zeroE) = ρ.val x ^ i := by
  have := powersFrom_read ρ x n oneE i h
  rw [ρ.one, one_mul] at this
  rw [← this]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

variable (P : OwnPar K M X) (Mn : Means K P.D P.C P.kap)

/-- The tail's six targets, at the library's letters. -/
theorem value_tail_targets (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L)
    (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (hnF : ∀ i : Fin P.D.nb, nm.nF (i, true) = 2 * i.1 + 1)
    (x0 : Seen K X) :
    TailTargets (P.tail Mn).toTail (tailData (P.tail Mn).toTail L h nz nm x0) x0 where
  tE := by
    show ρ.val (L.ridersE.getD 1 zeroE) = ρ.val h.division.target
    rw [hs.tE K ρ]
    unfold Lists.ridersE
    rw [units_ne hs.units (by simp [recOf]), List.nil_append, List.getD_append _ _ _ _ (by rw [hs.l5]; omega)]
  tM := (hs.tM K ρ).symm
  tVD := (hs.tVD K ρ).symm
  tF := by
    show ∑ i : Fin P.D.nb, ρ.val L.xF ^ (i : ℕ) * ρ.val (L.vM.getD i.1 zeroE) = ρ.val h.atIndex.target
    rw [hs.tF K ρ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs.om, powers_getD ρ _ (recOf P rows).pairs _ i.2]
  tD := by
    show ∑ i : Fin P.D.nb, ρ.val L.xD ^ (i : ℕ) *
      (dF (P.tail Mn).toTail L h nz nm x0).out.vals (P.iB i) = ρ.val h.key.target
    rw [hs.tD K ρ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs.om', powers_getD ρ _ (recOf P rows).pairs _ i.2]
    congr 1
    have hv : (dF (P.tail Mn).toTail L h nz nm x0).out.vals = (dF (P.tail Mn).toTail L h nz nm x0).v :=
      plain_vals ρ _ _ _ _ _ _ _ _ _ _
    rw [hv]
    show ρ.val (L.HF.v.getD (nm.nF (i, true)) zeroE) = _
    rw [hnF]
  tH := by
    show (0 : K) = ρ.val h.cells.target
    rw [hs.tH, ρ.zero]

/-- The letters of a unit start from the last of their further scalars. -/
def LastRider (u : SumL K M (Seen K X)) : Prop :=
  ∀ s (r : Fin u.n → K), ∃ hl : u.n - 1 < u.n, (u.cl s r).1 = r ⟨u.n - 1, hl⟩

/-- Units that start from their last rider have their targets. -/
theorem units_targets_of_last {G : Fork} : ∀ (us : List (SumL K M (Seen K X))) (du : UnitsH ρ us)
    (ps : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (pre : List E) (l : List (List E × PscH))
    (s : Seen K X), (∀ u ∈ us, LastRider u) → UnitsAt ps os pre l G → UnitsOfP us du ps os pre l →
    UnitsTargets us du s
  | [], _, _, _, _, _, _, _, _, _ => trivial
  | u :: us, d, p :: ps, o :: os, pre, (v7, H) :: l, s, hu, ⟨a1, _, _, a4, a5⟩, ⟨_, of, hn⟩ => by
    refine ⟨?_, units_targets_of_last us d.2 ps os [] l _ (fun w hw => hu w (List.mem_cons_of_mem _ hw)) a5 hn⟩
    obtain ⟨hl, hc⟩ := hu u List.mem_cons_self s d.1.rd
    show (u.cl s d.1.rd).1 = ρ.val d.1.t
    rw [hc]
    show ρ.val (d.1.r.getD (u.n - 1) zeroE) = _
    rw [of.t, a4 K ρ, of.r, of.n, List.length_append, a1, show pre.length + 7 - 1 = pre.length + 6 by omega,
      List.getD_append_right _ _ _ _ (by omega), show pre.length + 6 - pre.length = 6 by omega]
  | _ :: _, _, [], _, _, _, _, _, _, ho => ho.elim
  | _ :: _, _, _ :: _, [], _, _, _, _, _, ho => ho.elim
  | _ :: _, _, _ :: _, _ :: _, _, [], _, _, _, ho => ho.elim

theorem last_uM : LastRider P.uM := fun _ _ => ⟨by show 3 * P.npl + 7 - 1 < 3 * P.npl + 7; omega, rfl⟩
theorem last_uD : LastRider P.uD := fun _ _ => ⟨by show 7 - 1 < 7; omega, rfl⟩

theorem last_own : ∀ u ∈ (P.own Mn).units, LastRider u := fun u hu => by
  have : u = P.uM ∨ u = P.uD := by simpa [OwnPar.own] using hu
  rcases this with rfl | rfl
  · exact last_uM P
  · exact last_uD P

open OnBytes.Tie.Pv.Att (ownTrs own_out ownAt_fits) in
open VerifiableInference.Desc.Part.MaskedSum (Fits PartHearLaw PartRowLaw) in
/-- **K05_law at the library's letters**: the letters' numbers and the letters' claims are PAID;
what is left of (c3)'s
premises is the rows' three equations. -/
theorem K05_at_value (hearLaw : PartHearLaw) (rowLaw : PartRowLaw) {S : Type} (seat : Seat S) (p : Par)
    (s s' : S) (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s')
    (hz : ∀ F, seat.ledger s = some F → Sized F) (hk : P.kap = 4) (rows : ℕ) (hrec : p.own = recOf P rows) :
    ∃ (F G : Fork) (h : Heard) (L : Lists),
      (seat.ledger s = some F ∧ seat.lay s h G = some s' ∧ RoundsAre L.rounds rs ∧ Sized G ∧ Stays F G) ∧
      (∀ G', Stays G G' → Said p.own h G' L) ∧
      ∀ (ρ : Reading K) (nz : BetasNz ρ L) (um : UnitsNums (P.own Mn).units) (nm : TailNums (P.own Mn).tail),
        (∀ i : Fin P.D.nb, nm.nF (i, true) = 2 * i.1 + 1) → ∀ x0 : X,
        ∃ (du : UnitsH ρ (P.own Mn).units) (dt : TailH ρ (P.own Mn).tail),
          (UnitsOfP (P.own Mn).units du p.own.score h.scores.toList L.planes.flatten L.units ∧
            TailOfP dt p.own h L ∧
            UnitsVals (P.own Mn).units du
              (unitsAdd (ρ := ρ) (P.own Mn).units um L.planes.flatten L.units (x0, [])) ∧
            TailVals dt (tailAdd (P.own Mn).tail L h nz nm (seenAfter (P.own Mn).units du (x0, [])))) ∧
          (UnitsClaims (P.own Mn).units du (x0, []) ∧ dt.Claims (seenAfter (P.own Mn).units du (x0, []))) ∧
          (UnitsAreP (P.own Mn).units du h.scores.toList ∧ TailIsP dt p.own h L) ∧
          (∀ (Ex : ExtSpec) (y : Ex.Str), ((P.own Mn).ch.R Ex).red.out (x0, y)
            ((P.own Mn).ch.join Ex (ownTrs (P.own Mn) du dt)) =
              some ((P.own Mn).ch.run x0 (ownTrs (P.own Mn) du dt), y)) ∧
          ∀ (Dn : X → M → Prop) (m : M) (l : Left) (W : World K),
            UnitsPrem (P.own Mn).units du h.scores.toList l.scores.toList W m → TailPrem dt p.own h l W m →
            ((P.own Mn).ch.Last Dn ((P.own Mn).ch.run x0 (ownTrs (P.own Mn) du dt)) m ↔
              Dn x0 m ∧ UnitsBill (P.own Mn).units du (x0, []) l.scores.toList W m ∧
                TailBill dt (seenAfter (P.own Mn).units du (x0, [])) l W m) := by
  obtain ⟨_, F, h, G, a1, a2, a3⟩ := (decide_lays seat p s s' rs).1 hd
  obtain ⟨L, b1, b2, b3, b4, b5⟩ := hear_law hearLaw a2 (hz F a1)
  have hne : p.own.score ≠ [] := by rw [hrec]; simp [recOf]
  refine ⟨F, G, h, L, ⟨a1, a3, b1, b3, b4⟩, fun G' hs => b2.mono hs, ?_⟩
  intro ρ nz um nm hnF x0
  obtain ⟨fu, ft⟩ := fits_of_own (P.own Mn) p.own (by rw [hrec]; exact ownAt_fits P Mn hk rows) hne
  rw [← b2.nPlanes, ← planes_length b2.planes] at fu
  obtain ⟨du, d1, d3⟩ := units_exist (P.own Mn).units _ _ _ _ b2.units fu nz.units
    (unitsAdd (ρ := ρ) (P.own Mn).units um L.planes.flatten L.units (x0, []))
  obtain ⟨e1, e2⟩ := tail_exists (P.own Mn).tail b2 hne nz ft
    (tailAdd (P.own Mn).tail L h nz nm (seenAfter (P.own Mn).units du (x0, [])))
  have cu : UnitsClaims (P.own Mn).units du (x0, []) :=
    (units_claims _ du _ _ _ _ um _ d1 d3).2 (units_targets_of_last _ du _ _ _ _ _ (last_own P Mn) b2.units d1)
  have ct : (tailData (P.own Mn).tail L h nz nm (seenAfter (P.own Mn).units du (x0, []))).Claims
      (seenAfter (P.own Mn).units du (x0, [])) :=
    (tail_claims _ L h nz nm _).2 (value_tail_targets P Mn rows (by rw [← hrec]; exact b2) nz nm hnF _)
  exact ⟨du, _, ⟨d1, e1, d3, e2⟩, ⟨cu, ct⟩, b5 K ρ M X (P.own Mn) du _ d1 e1, fun Ex y => own_out (P.own Mn) du _ Ex x0 y,
    fun Dn m l W pu pt => k5_last rowLaw (P.own Mn) du _ b2 d1 e1 Dn x0 m cu ct pu pt⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_at_value
#print axioms VerifiableInference.Desc.First.Att.P.value_tail_targets
#print axioms VerifiableInference.Desc.First.Att.P.units_targets_of_last
#print axioms VerifiableInference.Desc.First.Att.P.last_uM
