-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoClaimsMeet.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoClaimsMeet.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  planes_claim, claims_port
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  HeardIs, Later, LedAt, OnMasks, Sized, byVar_len, claimBits, claimLeaves, claimsOf, countK,
  dgOf, endsOf, evalL, evalL_append, evalL_muOf, evalL_scale, forN, joinForm, join_claim, leaves,
  leavesAK, ledAt_end, ledF, numsF, nums_led, ok_parts, onMasks_append, onMasks_hide,
  onMasks_incTop, onMasks_keyTop, onMasks_one, onMasks_scale, ordE_len, rdL_getD, rowRes,
  rows_claim, tab_ext_g, thetaOf
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoClaimsMeet
import Johnson.Top.H.FlPort.Kit
import Johnson.Desc.First.Look.LookPlanes
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoJoinRun
import Johnson.Top.H.FlPort.FoPlaneHeard
import Johnson.Top.H.FlPort.FoPlaneAt
import Johnson.Top.H.FlPort.FoPlaneRead
import Johnson.Top.H.FlPort.FoPlaneClaims

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.PlaneClaims VerifiableInference.Desc.First.Look
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K]

variable (h : Forest.Shape) (lm jLK : ℕ) (rsK : Rounds K)

end

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- **The three forms that read the planes, at the values of the caller's forms.** -/
theorem planes_claim (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F0 F G : Fork) (c c' : Tape) (rows : Array Aff)
    (h : planeClaimsF g lm bit pin F c = .ok ((rows, G), c'))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F) :
    c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∀ H, Later G H → ∀ (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K),
        (rows.toList.map fun a => a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
          [claimLeaves g.shape lm jLK rsK ν fun col =>
              (got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
            claimBits g.shape lm jLK rsK ν fun col =>
              (got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
            Pin.countK g.shape lm fun col =>
              (got (pin col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)] := by
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
  have hv : g.shape.v < 64 := lt_trans (Cb.Fo.ok_parts hok).1.2.2.2.2.1 (by decide)
  obtain ⟨_, a1, a2, a3, a4, r0, r1, r2, hr, hval⟩ :=
    planeClaims_rows ρ g lm bit pin hb hp F0 F G c c' rows h hRan hI.lvStart hI.lvTg h0 hF hL hv []
  refine ⟨a1, a2, a3, a4, fun H hH ν entry => ?_⟩
  obtain ⟨v0, v1, v2⟩ := hval H hH (fun j => ν (.mask j)) entry
  rw [hr]
  show [r0.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
    r1.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
    r2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)] = _
  rw [v0, v1, v2]
  have hM : OnMasks (hide (ledF jLK (FoNums.S g.shape).pEndC)
      (dgE (numsF g.shape lm jLK (thetaOf g.shape rsK))) (endsOf g.shape lm jLK rsK).lvXs ++
        scale (endsOf g.shape lm jLK rsK).lvEps (endsOf g.shape lm jLK rsK).lvInc) :=
    onMasks_append (onMasks_hide _ (fun _ _ => ⟨_, rfl⟩) ⟨_, rfl⟩ _ _)
      (onMasks_scale _ (onMasks_incTop g.shape lm jLK _ _))
  have hA : (endsOf g.shape lm jLK rsK).leavesA =
      leavesAK g.shape (endsOf g.shape lm jLK rsK).theta (endsOf g.shape lm jLK rsK).alpha
        (endsOf g.shape lm jLK rsK).zb0 :=
    tab_ext_g g.shape hok _ _ _ (by
      rw [byVar_len]
      exact ordE_len g.shape)
  have hS := (hI.sBitAt H ((h0.trans a2).trans hH)).2 (fun j => ν (.mask j)) entry
  rw [Aff.value_slot, evalL_muOf (onMasks_one ⟨_, rfl⟩ _) ν] at hS
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)
  · rw [hdg', hI.lvEps, hI.lvFin, show g.leaves.r.toList.map ρ.val = _ from hI.lvXs, hI.leavesA,
      show rdL ρ g.zb0 = _ from hI.zb0, hA]
    unfold rowRes rowU claimLeaves
    simp only
    rw [evalL_muOf hM ν, evalL_append, evalL_scale]
    show _ = evalL ν _ + _ * evalL ν _ + _ - _
    rw [show hide (forN g.shape lm jLK rsK).ledE (dgE (forN g.shape lm jLK rsK))
        (endsOf g.shape lm jLK rsK).lvXs =
      hide (ledF jLK (FoNums.S g.shape).pEndC) (dgE (numsF g.shape lm jLK (thetaOf g.shape rsK)))
        (endsOf g.shape lm jLK rsK).lvXs from rfl]
    ring
  · rw [hS, show rdL ρ g.zb1 = _ from hI.zb1]
    unfold claimBits
    show _ - ((endsOf g.shape lm jLK rsK).bitBe * ν
        (_root_.Fo.Pl.mask (endsOf g.shape lm jLK rsK).sBit) + 0) -
      _ = _
    rw [add_zero]
    rfl

/-- **The byte-level verifier's forms are worth the list of claims, number by number.** -/
theorem claims_port (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F0 F G : Fork) (c c' : Tape) (rows : Array Aff)
    (h : planeClaimsF g lm bit pin F c = .ok ((rows, G), c'))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F) (KF : Array Aff) (hs : KF.size = g.shape.NC)
        (H : Fork) (hH : Later G H)
    (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) :
    ((g.rows.toList ++ rows.toList ++ [joinForm g KF]).map fun a =>
        a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
      claimsOf g.shape lm jLK rsK ν
        (fun col => (got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
        (fun col => (got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
        (fun col => (got (pin col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
        (fun k => (KF.getD k (Aff.ofConst zeroE)).value ρ
          (H.worldOf ρ (fun j => ν (.mask j)) entry)) := by
  obtain ⟨_, a2, _, _, hpl⟩ :=
    planes_claim ρ g lm jLK rsK bit pin hb hp F0 F G c c' rows h hI h0 hok hF
  have hcE : g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      AffK.val ((endsOf g.shape lm jLK rsK).cEndF, (endsOf g.shape lm jLK rsK).cEndC) ν := by
    rw [(hI.cEnd H ((h0.trans a2).trans hH)).2 (fun j => ν (.mask j)) entry,
      evalL_muOf (onMasks_keyTop g.shape lm jLK rsK) ν]
    show _ = evalL ν (scale (-1) (endsOf g.shape lm jLK rsK).cEndInc) + _
    rw [evalL_scale]
    ring
  have hJ := join_claim ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) g KF hok hs lm jLK rsK ν
    hI.theta hI.alpha (fun k _ => by
      rw [rdL_getD, show rdL ρ g.e = _ from hI.e]) hI.zy hcE
  unfold claimsOf
  rw [List.map_append, List.map_append, rows_claim ρ g lm jLK rsK F0 hI H ((h0.trans a2).trans hH) ν
      entry,
    hpl H hH ν entry, List.map_singleton, hJ, List.append_assoc]
  rfl

end

end Fo.Tp
