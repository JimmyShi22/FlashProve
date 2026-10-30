-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/EqPort/EqBits.lean: what a yes of `eqCounts`
(Johnson/Desc/First/TailClaims/Equations.lean: the three claims on the planes of the lookup's counts
at the smallness test's digits) is made of, and what its three claims are worth.

`bits9_claim`: A CARRIED COPY of the library's declaration of that name
(OnBytes/Tie/Pv/Lookup/Ends/FoTailBits.lean), under a table that is not in this library: the
sumcheck's closing routine becomes the flat function Fl.pscRow on a tape. It says the three claims
one by one, each as a form's value plus a run's value, under three premises on totals. By hand:
`pscRow_of`: the flat function returns where its test holds and the ledger takes the values;
`eqPscRow_ok`, `eqCounts_cut`: the routines of EqM, step by step (after the library's linBits9_cut).

Limits. Nothing is said where a routine refuses. A tie: no error term. If a source turns, the copy
does not follow by itself.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailBits
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.EqPort.EqKit

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie Cb.Fo.PlaneClaims
open Cb.Fo

/-- The flat function for a sumcheck's closing returns where its test holds and the ledger takes the
hiding coefficients. -/
theorem pscRow_of (p : Psc) (S0 : E) (kept : Aff) (F G : Fork) (c : Tape)
    (hg : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true)
    (hG : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    Fl.pscRow p S0 kept F c = .ok (((p.rowForm S0 kept, { p with rowMade := true }), G), c) := by
  unfold Fl.pscRow
  exact (bind_ok _ _ F c _).2 ⟨(), F, c, (must_ok _ F c _).2 ⟨hg, rfl⟩,
    (bind_ok _ _ F c _).2 ⟨(), G, c, (change_ok _ F c _).2 ⟨G, hG, rfl⟩,
      (pure_ok _ G c _).2 rfl⟩⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The three claims, each a form and a run, are worth the flat list's three, in its order and with
its signs. F0: the state with which the record holds the end values. F1: the state behind
Fl.pscRow. -/
theorem bits9_claim (tl : HTailF2) (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (F0 F F1 : Fork)
    (c c1 : Tape) (row : Aff) (p' : Psc) (hs : tl.f9 = g.shape)
    (h : Fl.pscRow g.leaves oneE {} F c = .ok (((row, p'), F1), c1))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F) :
    c1 = c ∧ Later F F1 ∧ Sized F1 ∧ F1.next = F.next ∧
      ∀ H, Later F1 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K) (bit0 bit1 pin : ℕ → K),
        planesK g.shape lm (endsOf g.shape lm jLK rsK).zb0 bit0 =
          runK (H.worldOf ρ (fun j => ν (.mask j)) entry) tl 0
            (fun i => (eqTabK (exL (endsOf g.shape lm jLK rsK).zb0 5
              (5 + g.shape.kT + g.shape.cK))).getD i 0) →
        planesK g.shape lm (endsOf g.shape lm jLK rsK).zb1 bit1 =
          runK (H.worldOf ρ (fun j => ν (.mask j)) entry) tl 1
            (fun i => (eqTabK (exL (endsOf g.shape lm jLK rsK).zb1 5
              (5 + g.shape.kT + g.shape.cK))).getD i 0) →
        Pin.countK g.shape lm pin = -((2 ^ g.shape.v - g.shape.padding : ℕ) : K) +
          runK (H.worldOf ρ (fun j => ν (.mask j)) entry) tl 2 (fun i => (rdL ρ (pinW tl)).getD i 0)
              →
        [row.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
            Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)
              (bzRun tl 0 (mulE g.leaves.eps g.leavesA)
                (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))),
          (Aff.slot g.sBit).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
            Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)
              (bzRun tl 1 (subE zeroE oneE) (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))),
          (Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding)))).value ρ
              (H.worldOf ρ (fun j => ν (.mask j)) entry) +
            Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (bzRun tl 2 oneE (pinW tl))] =
        [claimLeaves g.shape lm jLK rsK ν bit0, claimBits g.shape lm jLK rsK ν bit1,
          Pin.countK g.shape lm pin] := by
  obtain ⟨mu, zd, rs, hRan, _, hdg⟩ := hI.lvRan
  have hdg' : dgOf zd = dgE (numsF g.shape lm jLK (thetaOf g.shape rsK)) := by
    have e1 : dgOf zd = (zd.map fun p => p.2).map (· - 1) := by
      unfold dgOf
      rw [List.map_map]
      rfl
    rw [e1, hdg, List.map_map]
    have e2 : ((fun x : ℕ => x - 1) ∘ fun x => x + 1) = id := funext fun x => by simp
    rw [e2, List.map_id]
    rfl
  have hL : LedAt (ledF jLK (FoNums.S g.shape).pEndC) (jLK + (FoNums.S g.shape).fEnd)
      (dgOf zd) 0 := by
    rw [hdg', (nums_led g.shape jLK lm (thetaOf g.shape rsK)).2.2.2.2.2.2]
    exact ledAt_end g.shape jLK
  obtain ⟨a1, a2, a3, a4, _, a6⟩ := row_form ρ hRan h hI.lvStart hI.lvTg h0 hF hL []
  refine ⟨a1, a2, a3, a4, fun H hH ν entry bit0 bit1 pin hb0 hb1 hpn => ?_⟩
  have hM : OnMasks (hide (ledF jLK (FoNums.S g.shape).pEndC)
      (dgE (numsF g.shape lm jLK (thetaOf g.shape rsK))) (endsOf g.shape lm jLK rsK).lvXs ++
        scale (endsOf g.shape lm jLK rsK).lvEps (endsOf g.shape lm jLK rsK).lvInc) :=
    onMasks_append (onMasks_hide _ (fun _ _ => ⟨_, rfl⟩) ⟨_, rfl⟩ _ _)
      (onMasks_scale _ (onMasks_incTop g.shape lm jLK _ _))
  have hA : (endsOf g.shape lm jLK rsK).leavesA =
      leavesAK g.shape (endsOf g.shape lm jLK rsK).theta (endsOf g.shape lm jLK rsK).alpha
        (endsOf g.shape lm jLK rsK).zb0 := ends_leavesA g.shape hok lm jLK rsK
  have hS := (hI.sBitAt H ((h0.trans a2).trans hH)).2 (fun j => ν (.mask j)) entry
  rw [Aff.value_slot, evalL_muOf (onMasks_one ⟨_, rfl⟩ _) ν] at hS
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))
  · rw [a6 H hH _ entry, bzRun_value, Aff.value_empty, mul_zero, add_zero, eqTab_val, rdL_extract,
      show rdL ρ g.zb0 = _ from hI.zb0, hs, ← hb0, ρ.mul, hdg', hI.lvEps, hI.lvFin,
      show g.leaves.r.toList.map ρ.val = _ from hI.lvXs, hI.leavesA, hA, ρ.one]
    unfold rowRes rowU claimLeaves
    simp only
    rw [evalL_muOf hM ν, evalL_append, evalL_scale]
    show _ = evalL ν _ + _ * evalL ν _ + _ - _
    rw [show hide (forN g.shape lm jLK rsK).ledE (dgE (forN g.shape lm jLK rsK))
        (endsOf g.shape lm jLK rsK).lvXs =
      hide (ledF jLK (FoNums.S g.shape).pEndC) (dgE (numsF g.shape lm jLK (thetaOf g.shape rsK)))
        (endsOf g.shape lm jLK rsK).lvXs from rfl]
    ring
  · rw [Aff.value_slot, hS, bzRun_value, eqTab_val, rdL_extract, show rdL ρ g.zb1 = _ from hI.zb1,
      hs, ← hb1, ρ.sub, ρ.zero, ρ.one]
    unfold claimBits
    show _ - ((endsOf g.shape lm jLK rsK).bitBe * ν
        (Pl.mask (endsOf g.shape lm jLK rsK).sBit) + 0) + _ = _
    rw [add_zero]
    show _ = (endsOf g.shape lm jLK rsK).bitV - (endsOf g.shape lm jLK rsK).bitBe * ν
        (Pl.mask (endsOf g.shape lm jLK rsK).sBit) - _
    ring
  · rw [Aff.value_ofConst, ρ.sub, ρ.zero, natE_val, bzRun_value, ρ.one, one_mul, hpn, hs, zero_sub]


end
end Fo.Tp

namespace Fo.Eq
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First.TailClaims

variable {front : ℕ}

local notation:65 x:66 " ⟫ " F:max c:max => EqM.at x front F c

/-- The closing of a sumcheck in EqM, step by step. -/
theorem eqPscRow_ok (p : Psc) (S0 : E) (kept : Aff) (F G : Fork) (c c' : Array Claim) (row : Aff)
    (p' : Psc) (h : eqPscRow p S0 kept ⟫ F c = .ok (((row, p'), G), c')) :
    (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true ∧
      F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G ∧
      c' = c ∧ row = p.rowForm S0 kept ∧ p' = { p with rowMade := true } := by
  unfold eqPscRow at h
  obtain ⟨_, A1, a1, r1, k1⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨t1, e1⟩ := (mustAs_ok _ _ F c _).1 r1
  have x2 : A1 = F := congrArg (fun x : (Unit × Fork) × Array Claim => x.1.2) e1
  have x3 : a1 = c := congrArg (fun x : (Unit × Fork) × Array Claim => x.2) e1
  rw [x2, x3] at k1
  obtain ⟨_, A2, a2, r2, k2⟩ := (bind_ok _ _ F c _).1 k1
  obtain ⟨G2, hG, e2⟩ := (change_ok _ F c _).1 r2
  have y2 : A2 = G2 := congrArg (fun x : (Unit × Fork) × Array Claim => x.1.2) e2
  have y3 : a2 = c := congrArg (fun x : (Unit × Fork) × Array Claim => x.2) e2
  have e3 := (pure_ok _ A2 a2 _).1 k2
  have z1 : (row, p') = _ := congrArg (fun x : ((Aff × Psc) × Fork) × Array Claim => x.1.1) e3
  have z2 : G = A2 := congrArg (fun x : ((Aff × Psc) × Fork) × Array Claim => x.1.2) e3
  have z3 : c' = a2 := congrArg (fun x : ((Aff × Psc) × Fork) × Array Claim => x.2) e3
  exact ⟨t1, by rw [z2, y2]; exact hG, z3.trans y3, congrArg Prod.fst z1, congrArg Prod.snd z1⟩

/-- A yes of eqCounts, step by step. -/
theorem eqCounts_cut (tl tl' : HTailF2) (F G : Fork) (c c' : Array Claim)
    (h : eqCounts tl ⟫ F c = .ok ((tl', G), c')) :
    ∃ (g : Heard) (F1 : Fork),
      tl.heard = some g ∧
      (!g.leaves.rowMade && g.leaves.started && !g.leaves.vars.isEmpty &&
        g.leaves.r.size == g.leaves.vars.size) = true ∧
      F.hideRun g.leaves.first (Array.replicate g.leaves.walk.1.length zeroE)
        (subE zeroE oneE) = some F1 ∧
      c' = ((c.push { form := g.leaves.rowForm oneE {},
                      runs := #[bzRun tl 0 (mulE g.leaves.eps g.leavesA)
                        (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] }).push
              { form := Aff.slot g.sBit,
                runs := #[bzRun tl 1 (subE zeroE oneE)
                  (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] }).push
            { form := Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))),
              runs := #[bzRun tl 2 oneE (pinW tl)] } ∧
      G = F1.paid g.owedPlanes ∧
      tl' = { tl with bitFactor9 := mulE g.leaves.eps g.leavesA } := by
  unfold eqCounts at h
  obtain ⟨g, A1, a1, r1, k1⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨g', s1, e1⟩ := (get_ok _ F c _).1 r1
  have x1 : g = g' := congrArg (fun x : (Heard × Fork) × Array Claim => x.1.1) e1
  have x2 : A1 = F := congrArg (fun x : (Heard × Fork) × Array Claim => x.1.2) e1
  have x3 : a1 = c := congrArg (fun x : (Heard × Fork) × Array Claim => x.2) e1
  rw [← x1] at s1
  rw [x2, x3] at k1
  obtain ⟨⟨row, p'⟩, F1, c1, r2, k2⟩ := (bind_ok _ _ F c _).1 k1
  obtain ⟨t1, hG, w1, w2, _⟩ := eqPscRow_ok _ _ _ _ _ _ _ _ _ r2
  obtain ⟨_, F2, c2, r3, k3⟩ := (bind_ok _ _ F1 c1 _).1 k2
  obtain ⟨_, F3, c3, r4, k4⟩ := (bind_ok _ _ F2 c2 _).1 k3
  obtain ⟨_, F4, c4, r5, k5⟩ := (bind_ok _ _ F3 c3 _).1 k4
  obtain ⟨_, F5, c5, r6, k6⟩ := (bind_ok _ _ F4 c4 _).1 k5
  have e3 := (emit_ok _ F1 c1 _).1 r3
  have e4 := (emit_ok _ F2 c2 _).1 r4
  have e5 := (emit_ok _ F3 c3 _).1 r5
  unfold eqPlanesAdded at r6
  have e6 := (paid_ok _ F4 c4 _).1 r6
  have e7 := (pure_ok _ F5 c5 _).1 k6
  have f2 : F2 = F1 := congrArg (fun x : (Unit × Fork) × Array Claim => x.1.2) e3
  have d2 : c2 = _ := congrArg (fun x : (Unit × Fork) × Array Claim => x.2) e3
  have f3 : F3 = F2 := congrArg (fun x : (Unit × Fork) × Array Claim => x.1.2) e4
  have d3 : c3 = _ := congrArg (fun x : (Unit × Fork) × Array Claim => x.2) e4
  have f4 : F4 = F3 := congrArg (fun x : (Unit × Fork) × Array Claim => x.1.2) e5
  have d4 : c4 = _ := congrArg (fun x : (Unit × Fork) × Array Claim => x.2) e5
  have f5 : F5 = F4.paid g.owedPlanes := congrArg (fun x : (Unit × Fork) × Array Claim => x.1.2) e6
  have d5 : c5 = c4 := congrArg (fun x : (Unit × Fork) × Array Claim => x.2) e6
  have y1 : tl' = _ := congrArg (fun x : (HTailF2 × Fork) × Array Claim => x.1.1) e7
  have y2 : G = F5 := congrArg (fun x : (HTailF2 × Fork) × Array Claim => x.1.2) e7
  have y3 : c' = c5 := congrArg (fun x : (HTailF2 × Fork) × Array Claim => x.2) e7
  refine ⟨g, F1, s1, t1, hG, ?_, by rw [y2, f5, f4, f3, f2], y1⟩
  rw [y3, d5, d4, d3, d2, w1, w2]
  rfl

end Fo.Eq
