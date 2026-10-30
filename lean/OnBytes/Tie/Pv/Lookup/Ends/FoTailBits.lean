-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailBits.lean.
The smallness test's three claims on the planes of its lookup's counts, written out by hand.

The byte-level routine linBits9 (OnBytes/Model/Tail.lean) does not call Forest.planeClaims. It makes
the claim of the leaves' sumcheck with nothing kept and adds three claims, each a form and one run
on a virtual row of the matrix BZ. This file cuts a run of linBits9 that returns into its steps,
and says what each of the three claims is worth.

* bzRun tl row coef w: a run over all columns of a virtual row of BZ. runK: what it is worth without
  its factor: the sum over the columns of weight times entry.
* linBits9_cut: a run that returns is: the record is there; pscRow on the leaves' sumcheck; three
  calls of t2Lin; the mark that the three claims are added.
* natE_val: a natural number as a field element, read in a ring.
* bits9_claim: in the world (Fork.worldOf) of every state later than the one behind pscRow, the
  three claims (form and run) are worth claimLeaves, claimBits and countK of
  OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean, in this order and with these signs.
  Under: the smallness test's shape is the record's (tl.f9 = g.shape) and is lawful (FoNums.ok);
  the call of pscRow on the record's leaves returns, from a state F that is Sized; the record holds
  the end values endsOf (HeardIs) with a state F0, and F is later than F0.
  The letters bit0, bit1, pin stand under premises too: planesK at zb0 of bit0 is the sum of the run
  on row 0; planesK at zb1 of bit1 is the sum of the run on row 1; countK of pin is the sum of the
  run on row 2 less the number of keys that are not padding. So the third equation says no more
  than that the byte-level constant and factor read as these numbers in the ring.
  It also says that pscRow leaves the context and the next free slot as they were, and leads to a
  later state that is Sized.
  That the columns' sums of the lookup's cells are such letters is not shown here.

Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoClaimsMeet
import OnBytes.Tie.Pv.Lookup.Forest.FoEndsTwins
import OnBytes.Model.Tail
import OnBytes.Model.TreesLaws

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie Cb.Fo.PlaneClaims
open Cb.Fo

/-- A run over all columns of a virtual row of BZ. -/
def bzRun (tl : HTailF2) (row : ℕ) (coef : E) (w : Array E) : Run2 :=
  { tree := tl.ix.BZ, row := row, first := 0, coef := coef, w := w, n := tl.bzColumns }

/-- The weights of the third claim: 2 to the plane's number. -/
def pinW (tl : HTailF2) : Array E := (Array.range tl.bzColumns).map fun u => ofNat (2 ^ (u % 32))

/-- A run of linBits9 that returns, step by step. -/
theorem linBits9_cut (tl tl' : HTailF2) (F G : Fork) (c c' : Ctx)
    (h : tl.linBits9 F c = .ok ((tl', G), c')) :
    ∃ (g : Heard) (row : Aff) (p' : Psc) (F1 F2 F3 F4 : Fork) (c1 c2 c3 c4 : Ctx),
      tl.heard = some g ∧
      pscRow g.leaves oneE {} F c = .ok (((row, p'), F1), c1) ∧
      t2Lin row #[bzRun tl 0 (mulE g.leaves.eps g.leavesA)
        (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] F1 c1 = .ok (((), F2), c2) ∧
      t2Lin (Aff.slot g.sBit) #[bzRun tl 1 (subE zeroE oneE)
        (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] F2 c2 = .ok (((), F3), c3) ∧
      t2Lin (Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))))
        #[bzRun tl 2 oneE (pinW tl)] F3 c3 = .ok (((), F4), c4) ∧
      Forest.planesAdded g F4 c4 = .ok (((), G), c') ∧
      tl' = { tl with bitFactor9 := mulE g.leaves.eps g.leavesA } := by
  unfold HTailF2.linBits9 at h
  obtain ⟨g, A1, a1, r1, k1⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨g', s1, e1⟩ := (get_ok _ F c _).1 r1
  have x1 : g = g' := congrArg (fun x : (Heard × Fork) × Ctx => x.1.1) e1
  have x2 : A1 = F := congrArg (fun x : (Heard × Fork) × Ctx => x.1.2) e1
  have x3 : a1 = c := congrArg (fun x : (Heard × Fork) × Ctx => x.2) e1
  rw [← x1] at s1
  rw [x2, x3] at k1
  obtain ⟨⟨row, p'⟩, F1, c1, r2, k2⟩ := (bind_ok _ _ F c _).1 k1
  obtain ⟨_, F2, c2, r3, k3⟩ := (bind_ok _ _ F1 c1 _).1 k2
  obtain ⟨_, F3, c3, r4, k4⟩ := (bind_ok _ _ F2 c2 _).1 k3
  obtain ⟨_, F4, c4, r5, k5⟩ := (bind_ok _ _ F3 c3 _).1 k4
  obtain ⟨_, F5, c5, r6, k6⟩ := (bind_ok _ _ F4 c4 _).1 k5
  have e6 := (pure_ok _ F5 c5 _).1 k6
  have y1 : tl' = _ := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.1.1) e6
  have y2 : G = F5 := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.1.2) e6
  have y3 : c' = c5 := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.2) e6
  rw [← y2, ← y3] at r6
  exact ⟨g, row, p', F1, F2, F3, F4, c1, c2, c3, c4, s1, r2, r3, r4, r5, r6, y1⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A natural number as a field element, read. -/
theorem natE_val (n : ℕ) : ρ.val (ofNat n) = (n : K) := by
  unfold ofNat fOfNat
  have hp : pW.toNat = 18446744069414584321 := by decide
  have hlt : n % pW.toNat < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by rw [hp]; norm_num)) (by
    rw [hp]; norm_num)
  rw [ofF_val, toNat_word _ hlt, hp]
  conv_rhs => rw [← Nat.div_add_mod n 18446744069414584321]
  rw [Nat.cast_add, Nat.cast_mul, prime_zero ρ, zero_mul, zero_add]

/-- What a run over a virtual row of BZ is worth, without its factor. -/
def runK (W : World K) (tl : HTailF2) (row : ℕ) (w : ℕ → K) : K :=
  runSum (fun i => w i * W.entry tl.ix.BZ row i) tl.bzColumns 0

theorem runSum_congr (f g : ℕ → K) : ∀ (n i : ℕ), (∀ j, f j = g j) → runSum f n i = runSum g n i
  | 0, _, _ => rfl
  | n + 1, i, h => by
    simp only [runSum]
    rw [h i, runSum_congr f g n (i + 1) h]

theorem bzRun_value (W : World K) (tl : HTailF2) (row : ℕ) (coef : E) (w : Array E) :
    Run2.value ρ W (bzRun tl row coef w) =
      ρ.val coef * runK W tl row fun i => (rdL ρ w).getD i 0 := by
  unfold Run2.value bzRun runK
  simp only
  congr 1
  refine runSum_congr _ _ _ _ fun j => ?_
  rw [rdL_getD, Nat.zero_add]

/-- The three claims, each a form and a run, are worth the flat list's three, in its order and with
its signs. F0: the state with which the record holds the end values. F1: the state behind pscRow. -/
theorem bits9_claim (tl : HTailF2) (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (F0 F F1 : Fork)
    (c c1 : Ctx) (row : Aff) (p' : Psc) (hs : tl.f9 = g.shape)
    (h : pscRow g.leaves oneE {} F c = .ok (((row, p'), F1), c1))
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
end Fo
