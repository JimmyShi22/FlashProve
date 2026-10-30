-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerRun.lean.
The layers' sub-proof: its lookup's claims inside the one equation, from `Forest.objects` to
`Layer.claimsPlanes`.

The statement is on three runs in a row, with the records P and o as letters:
`Forest.objects o.H.fo`, the layers' own claims `layerMid P o` (FoLookLayerMid), and
`Layer.claimsPlanes o.v o.H.fo`, each from the state and the context that the one before left.

Main names:
  `grows_three`: a stretch that grows by values, a stretch that adds a list of claims, a stretch
    that grows by values: the total in one equation.
  `layer_look_total`: there is a function A, chosen before all states, contexts, rings, readings,
    rounds and worlds, such that: the total behind `Layer.claimsPlanes` is the total before
    `Forest.objects`, plus the rows of the record of end values under the powers of theta from the
    number of claims before on, plus the claims of the list A (..) (..), plus `Fo.claimLeaves`,
    `Fo.claimBits` and the counts' sum at the columns' sums, under the powers that follow.
  The arguments of A: the values shown under the end slots of the first token sumcheck, in the state
  before `Layer.claimsPlanes`, and the arrays' numbers of columns. The arguments of the lookup's
  members: the shape, lm, the lookup's first slot, the rounds heard by the lookup's routine, and the
  reading ν of the places.

Under: the three runs return; the first state has one coefficient for each slot and its arrays have
their sizes; the lookup's record holds the flat function's end values (`HeardIs`) in an earlier
state; the shape is lawful (`FoNums.ok`); tB0, tB1 and tP are what `Env.tabAt` gives at the names
b-bits-0, b-bits-1, b-pin; the world is `Fork.worldOf` of a state later than the last run's end
state, with ν's values at the mask's places as the mask row, and its entries meet the law of the
reads (`ReadsLaw`) at these three tables.

Limit: identities at the one element theta of the state. Which claims stand in A's list is not
said. A is chosen behind the records P and o, so it can hang on them: that o holds nothing that was
drawn with or after theta is not said here. The other limits of `Fixed` (FoFixed) hold of A too.
That the values shown under the end slots, the reading ν, or the world's entries of virtual rows do
not hang on theta is not said here. Some entries meet the law of the reads if the three tables lie
one behind the other (`readsLaw_some`, FoReads); that the layers' three tables do is not said here.
That a run of the layers' whole check holds these three runs in a row is not said here. The layers
add no claim on the keys: see FoStartClaim.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookLayerMid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun Cb.Fo

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- Values, then a list of claims, then values. -/
theorem grows_three {F F1 Fp G : Fork} {W : World K} {a b : List K} {A : List Cl}
    (h1 : GrowsBy ρ F F1 W a) (h2 : Added F1 Fp A) (h3 : GrowsBy ρ Fp G W b) :
    G.total ρ W = F.total ρ W + powSum (ρ.val F.theta) F.nClaim a +
      clsValue ρ W (ρ.val F.theta) (F.nClaim + a.length) A +
      powSum (ρ.val F.theta) (F.nClaim + a.length + A.length) b := by
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, _, _⟩ := h3
  rw [b1, h2.total, a1, h2.theta, a3, h2.nClaim, a2]

end

/-- **The layers' lookup inside the one equation.** -/
theorem layer_look_total (P : Layer.Pub) (o : Layer.Own) :
    ∃ A : Array E → (ℕ → ℕ) → List Cl,
      ∀ (Fb F1 Fp G : Fork) (cb d1 cp c' : Ctx),
        Forest.objects o.H.fo Fb cb = .ok (((), F1), d1) →
        layerMid P o F1 d1 = .ok (((), Fp), cp) →
        Layer.claimsPlanes o.v o.H.fo Fp cp = .ok (((), G), c') →
        Fb.LS.size = Fb.ns → Sized Fb →
        Later Fb G ∧ Sized G ∧ G.LS.size = G.ns ∧
        ∀ (K : Type) [CommRing K] (ρ : Reading K) (jLK : ℕ) (rsK : Rounds K) (F0 : Fork),
          HeardIs ρ o.H.fo F0 (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK) → Later F0 Fb →
          FoNums.ok o.H.fo.shape = true →
          ∀ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 → o.v.tabAt "b-bits-1" = some tB1 →
            o.v.tabAt "b-pin" = some tP →
          ∀ H, Later G H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
            ReadsLaw o.H.fo.shape o.v.y.h.lmb (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb0
              (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb1 ν entry o.v.iU3 o.v.K3 tB0 tB1 tP →
            G.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
              Fb.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
                powSum (ρ.val Fb.theta) Fb.nClaim
                  ((endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).rows.map (rowRes ν)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val Fb.theta)
                  (Fb.nClaim + ((endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).rows.map
                    (rowRes ν)).length)
                  (A (shownArr Fp o.H.tV.sEnd (nShown P o)) (colsOf Fb)) +
                powSum (ρ.val Fb.theta)
                  (Fb.nClaim + ((endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).rows.map
                    (rowRes ν)).length +
                    (A (shownArr Fp o.H.tV.sEnd (nShown P o)) (colsOf Fb)).length)
                  [claimLeaves o.H.fo.shape o.v.y.h.lmb jLK rsK ν
                      (colsK o.H.fo.shape o.v.y.h.lmb
                        (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb0 ν),
                    claimBits o.H.fo.shape o.v.y.h.lmb jLK rsK ν
                      (colsK o.H.fo.shape o.v.y.h.lmb
                        (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb1 ν),
                    Pin.countK o.H.fo.shape o.v.y.h.lmb (Pin.pinColK o.v.y.h.lmb ν)] := by
  obtain ⟨A, hA⟩ := layerMid_added P o
  obtain ⟨_, _, HO⟩ : Fixed (Forest.objects o.H.fo) := by fixed
  refine ⟨A, fun Fb F1 Fp G cb d1 cp c' hO hM hP hs sb => ?_⟩
  obtain ⟨lO, s1⟩ := Keeps.objects _ _ _ _ _ _ hO sb
  have aO := objects_added hO hs
  obtain ⟨aA, _, lM, sp⟩ := hA F1 Fp d1 cp hM aO.sized s1
  rw [(HO _ _ _ _ _ hO hs).2.2] at aA
  obtain ⟨lG, sG⟩ := Keeps.of hP sp (keeps_Model_Layer_claimsPlanes _ _)
  obtain ⟨_, LP, HP⟩ : Fixed (Layer.claimsPlanes o.v o.H.fo) := by fixed
  refine ⟨(lO.trans lM).trans lG, sG, (HP _ _ _ _ _ hP aA.sized).2.1.sized,
    fun K _ ρ jLK rsK F0 hI h0 hok tB0 tB1 tP e0 e1 eP H hH ν entry Lw => ?_⟩
  obtain ⟨_, _, _, g1⟩ := objects_grows ρ o.H.fo o.v.y.h.lmb jLK rsK F0 Fb F1 cb d1 hO hI hs sb
  obtain ⟨t0, t1, tp, f0, f1, fp, _, _, _, g3⟩ := layer_planes ρ o.v o.H.fo jLK rsK F0 Fp G cp c' hP
    hI ((h0.trans lO).trans lM) hok aA.sized sp
  obtain rfl : t0 = tB0 := Option.some.inj (f0.symm.trans e0)
  obtain rfl : t1 = tB1 := Option.some.inj (f1.symm.trans e1)
  obtain rfl : tp = tP := Option.some.inj (fp.symm.trans eP)
  exact grows_three ρ (g1 H ((((h0.trans lO).trans lM).trans lG).trans hH) ν entry) aA
    (g3 H hH ν entry Lw)

end Fo
