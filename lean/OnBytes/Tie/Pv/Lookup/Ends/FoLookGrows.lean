-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookGrows.lean.
The lookup's claims inside a sub-proof's one equation, stretch by stretch.

A sub-proof adds its claims up into one equation, claim number c under the c-th power of one drawn
element theta. The routines that add the lookup's claims stand among the sub-proof's own. This file
states, for each of them by itself, by how much the total grows: by a sum of values under the powers
of theta. In `objects_grows` and `planeLins_reads`, and on the right side of `joinLin_keys`, neither
a state of the sub-proof nor theta stands among the values' arguments. In `joinLin_grows` and
`planeLins_grows` the caller's forms are still valued in the world of a later state H.

Main names:
  `GrowsBy ρ F G W vals`: from F to G the total, in the world W, has grown by the sum of theta^i
    times the i-th value of vals, i counted from F's number of claims; the number of claims has
    grown by their number; theta is kept. `GrowsBy.trans`, `grows_forms`.
  `still_adds`, `still_keeps`: a routine that turns neither state nor context adds no claim and
    keeps what lies under the filled slots.
  `objects_grows`: `Forest.objects`: the rows of the record of end values, each as its form less its
    target.
  `joinLin_grows`: the form of `Forest.join`, added as a claim: `Fo.claimJoin` at the values of the
    caller's key forms. `joinLin_keys`: under `KeysAt`, at the extensions of the key vectors.
  `planeLins_grows`: `Forest.planeLins`: `Fo.claimLeaves`, `Fo.claimBits` and the counts' sum at the
    values of the caller's forms.
  `fold_ret`, `planeClaims_ret`: in a run that returns, the caller's routines have returned at every
    column of the planes' matrix.
  `planeLins_reads`: where the caller's routines give entries of the vector of reads (`ReadsAt`) and
    the world meets the law of the reads (`ReadsLaw`): at the columns' sums `colsK` and `pinColK`.

Under: the lookup's record holds the flat function's end values (`HeardIs`); the shape is lawful
(`FoNums.ok`); the state's arrays have their sizes, and it has one coefficient for each slot; the
run returns; the world is that of a state H later than the run's end state (in `objects_grows` and
`joinLin_grows`: later than the state F0 with which the record holds the end values). In
`planeLins_grows` and `planeLins_reads` the state before the run is later than F0. In
`joinLin_grows` there are as many key forms as NC. In `planeLins_grows`, `fold_ret` and
`planeClaims_ret` the caller's routines turn neither state nor context.

Limit: identities at the one element theta of the state. Whether the world's entries of virtual
rows, or the readings ν, hang on theta is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailLook
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsLook
import OnBytes.Tie.Pv.Lookup.Forest.FoClaimsMeet
import OnBytes.Tie.Pv.Lookup.Ends.FoKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun Cb.Fo

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- From F to G the total has grown by the values of vals under the powers of theta. -/
def GrowsBy (F G : Fork) (W : World K) (vals : List K) : Prop :=
  G.total ρ W = F.total ρ W + powSum (ρ.val F.theta) F.nClaim vals ∧
    G.nClaim = F.nClaim + vals.length ∧ G.theta = F.theta

theorem GrowsBy.trans {F G H : Fork} {W : World K} {a b : List K} (h1 : GrowsBy ρ F G W a)
    (h2 : GrowsBy ρ G H W b) : GrowsBy ρ F H W (a ++ b) := by
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  refine ⟨?_, by rw [b2, a2, List.length_append]; omega, b3.trans a3⟩
  rw [b1, a1, a3, a2, powSum_append]
  ring

/-- Forms that have been added as claims. -/
theorem grows_forms {F G : Fork} {l : List Aff} (h : Added F G (l.map fun f => (f, #[])))
    (W : World K) : GrowsBy ρ F G W (l.map fun a => a.value ρ W) :=
  ⟨by rw [h.total, clsValue_forms, claimsValue_powSum],
    by rw [h.nClaim, List.length_map, List.length_map], h.theta⟩

end

/-- A routine that turns neither state nor context adds no claim. -/
theorem still_adds {x : SubM Aff} (hx : PlaneClaims.Quiet x) : Quiet x := by
  intro F c a G c' hr hs
  obtain ⟨e, _⟩ := hx F c _ hr
  obtain rfl : G = F := e
  exact ⟨trivial, [], rfl, Added.refl hs⟩

/-- It keeps what lies under the filled slots. -/
theorem still_keeps {x : SubM Aff} (hx : PlaneClaims.Quiet x) : Keeps x := by
  intro F c a G c' hr hS
  obtain ⟨e, _⟩ := hx F c _ hr
  obtain rfl : G = F := e
  exact ⟨Later.refl _, hS⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **`Forest.objects`.** -/
theorem objects_grows (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (F0 F G : Fork) (c c' : Ctx)
    (hO : Forest.objects g F c = .ok (((), G), c'))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (hs : F.LS.size = F.ns) (hF : Sized F) :
    Later F G ∧ Sized G ∧ G.LS.size = G.ns ∧
      ∀ H, Later F0 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
        GrowsBy ρ F G (H.worldOf ρ (fun j => ν (.mask j)) entry)
          ((endsOf g.shape lm jLK rsK).rows.map (rowRes ν)) := by
  obtain ⟨k, z⟩ := Keeps.objects g F c () G c' hO hF
  have a := objects_added hO hs
  refine ⟨k, z, a.sized, fun H hH ν entry => ?_⟩
  have e := grows_forms ρ a (H.worldOf ρ (fun j => ν (.mask j)) entry)
  rwa [PlaneClaims.rows_claim ρ g lm jLK rsK F0 hI H hH ν entry] at e

/-- **The form of `Forest.join`, added as a claim.** -/
theorem joinLin_grows (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (F0 F G : Fork) (KF : Array Aff)
    (hL : (F.paid g.owedJoin).lin (joinForm g KF) = some G)
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (hok : FoNums.ok g.shape = true)
    (hK : KF.size = g.shape.NC) (hs : F.LS.size = F.ns) :
    G.LS.size = G.ns ∧
      ∀ H, Later F0 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
        GrowsBy ρ F G (H.worldOf ρ (fun j => ν (.mask j)) entry)
          [claimJoin g.shape lm jLK rsK ν fun q => (KF.getD q (Aff.ofConst zeroE)).value ρ
            (H.worldOf ρ (fun j => ν (.mask j)) entry)] := by
  have a1 := added_paid hs g.owedJoin
  have a2 := added_lin a1.sized hL
  have a : Added F G ([joinForm g KF].map fun f => (f, #[])) := by
    have := a1.trans a2
    rwa [List.nil_append] at this
  refine ⟨a.sized, fun H hH ν entry => ?_⟩
  have e := grows_forms ρ a (H.worldOf ρ (fun j => ν (.mask j)) entry)
  have hcE : g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      AffK.val ((endsOf g.shape lm jLK rsK).cEndF, (endsOf g.shape lm jLK rsK).cEndC) ν := by
    rw [(hI.cEnd H hH).2 (fun j => ν (.mask j)) entry,
      evalL_muOf (PlaneClaims.onMasks_keyTop g.shape lm jLK rsK) ν]
    show _ = evalL ν (scale (-1) (endsOf g.shape lm jLK rsK).cEndInc) + _
    rw [evalL_scale]
    ring
  have hJ := join_claim ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) g KF hok hK lm jLK rsK ν
    hI.theta hI.alpha (fun k _ => by
      rw [rdL_getD, show rdL ρ g.e = _ from hI.e]) hI.zy hcE
  rwa [List.map_singleton, hJ] at e

/-- Under `KeysAt`: at the extensions of the calls' key vectors. -/
theorem joinLin_keys (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (ν : Pl → K) (W : World K)
    (KF : Array Aff) (Kv : ℕ → ℕ → K) (zk : ℕ → List K) (hK : KeysAt ρ W g.shape.NC KF Kv zk) :
    claimJoin g.shape lm jLK rsK ν (fun q => (KF.getD q (Aff.ofConst zeroE)).value ρ W) =
      claimJoin g.shape lm jLK rsK ν fun q => extL (Kv q) (zk q) :=
  claimJoin_congr _ _ _ _ _ _ _ fun q hq => hK q hq

/-- **`Forest.planeLins`.** -/
theorem planeLins_grows (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) (hb : ∀ e col, PlaneClaims.Quiet (bit e col))
    (hp : ∀ col, PlaneClaims.Quiet (pin col)) (F0 F G : Fork) (c c' : Ctx)
    (h : Forest.planeLins g lm bit pin F c = .ok (((), G), c'))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hs : F.LS.size = F.ns) (hF : Sized F) :
    Later F G ∧ Sized G ∧ G.LS.size = G.ns ∧
      ∀ H, Later G H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
        GrowsBy ρ F G (H.worldOf ρ (fun j => ν (.mask j)) entry)
          [claimLeaves g.shape lm jLK rsK ν fun col =>
              (PlaneClaims.got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
            claimBits g.shape lm jLK rsK ν fun col =>
              (PlaneClaims.got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
            Pin.countK g.shape lm fun col =>
              (PlaneClaims.got (pin col) F c).value ρ
                (H.worldOf ρ (fun j => ν (.mask j)) entry)] := by
  obtain ⟨pl, Fq, cq, hp1, _, ad⟩ := planeLins_added (fun e col => still_adds (hb e col))
    (fun col => still_adds (hp col)) h hs
  obtain ⟨k, z⟩ := Keeps.planeLins g lm bit pin (fun e col => still_keeps (hb e col))
    (fun col => still_keeps (hp col)) F c () G c' h hF
  have hq : Later Fq G := by
    unfold Forest.planeLins at h
    obtain ⟨pl', F11, c11, s1, s2⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨e1', e2'⟩ := Prod.mk.inj (Except.ok.inj (hp1.symm.trans s1))
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1'
    obtain ⟨_, zq⟩ := Keeps.planeClaims _ _ _ _ (fun e col => still_keeps (hb e col))
      (fun col => still_keeps (hp col)) _ _ _ _ _ s1 hF
    obtain ⟨u, F12, c12, s3, s4⟩ := (bind_ok _ _ _ _ _).1 s2
    obtain ⟨m1, y1⟩ := Keeps.arrayForM (fun a => Keeps.lin a) pl _ _ _ _ _ s3 zq
    obtain ⟨m2, _⟩ := Keeps.planesAdded _ _ _ _ _ _ s4 y1
    exact m1.trans m2
  obtain ⟨_, _, _, _, hpl⟩ :=
    PlaneClaims.planes_claim ρ g lm jLK rsK bit pin hb hp F0 F Fq c cq pl hp1 hI h0 hok hF
  refine ⟨k, z, ad.sized, fun H hH ν entry => ?_⟩
  have e := grows_forms ρ ad (H.worldOf ρ (fun j => ν (.mask j)) entry)
  rwa [hpl H (hq.trans hH) ν entry] at e

end

/-- In a fold over routines that turn nothing, if it returns, each routine has returned. -/
theorem fold_ret (x : ℕ → SubM Aff) (hx : ∀ col, PlaneClaims.Quiet (x col))
    (step : Aff → ℕ → Aff → Aff) :
    ∀ (l : List ℕ) (s : Aff) (F : Fork) (c : Ctx) (r : (Aff × Fork) × Ctx),
    (l.foldlM (fun f col => x col >>= fun a => pure (step f col a)) s) F c = .ok r →
    ∀ col ∈ l, ∃ r', x col F c = .ok r'
  | [], _, _, _, _, _, _, hc => absurd hc List.not_mem_nil
  | a :: l, s, Fk, c, r, h, col, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok _ s a l Fk c r).1 h
    obtain ⟨b, G, c2, h3, h4⟩ := (bind_ok _ _ Fk c _).1 h1
    obtain ⟨e1, e2⟩ := hx a Fk c _ h3
    have e4 := (pure_ok _ G c2 _).1 h4
    simp only [Prod.mk.injEq] at e4
    obtain ⟨⟨_, eF⟩, ec⟩ := e4
    obtain rfl : G = Fk := e1
    obtain rfl : c2 = c := e2
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨_, h3⟩
    · rw [eF, ec] at h2
      exact fold_ret x hx step l s₁ _ _ r h2 col hc'

/-- In a run of `Forest.planeClaims` that returns, the caller's routines have returned at every
column of the planes' matrix. -/
theorem planeClaims_ret (g : Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, PlaneClaims.Quiet (bit e col)) (hp : ∀ col, PlaneClaims.Quiet (pin col))
    (F G : Fork) (c c' : Ctx) (rows : Array Aff)
    (h : planeClaims g lm bit pin F c = .ok ((rows, G), c')) (col : ℕ)
    (hc : col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm)) :
    (∃ r, bit 0 col F c = .ok r) ∧ (∃ r, bit 1 col F c = .ok r) ∧ ∃ r, pin col F c = .ok r := by
  unfold planeClaims at h
  obtain ⟨_, F1, c1, h1, k1⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨_, e1⟩ := (must_ok _ F c _).1 h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨⟨_, hF1⟩, hc1⟩ := e1
  rw [hF1, hc1] at k1
  obtain ⟨at0, F2, c2, h2, k2⟩ := (bind_ok _ _ F c _).1 k1
  have e2 := PlaneClaims.planesAt_ok g lm 0 bit (hb 0) F c _ h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨_, hF2⟩, hc2⟩ := e2
  rw [hF2, hc2] at k2
  obtain ⟨at1, F3, c3, h3, k3⟩ := (bind_ok _ _ F c _).1 k2
  have e3 := PlaneClaims.planesAt_ok g lm 1 bit (hb 1) F c _ h3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨⟨_, hF3⟩, hc3⟩ := e3
  rw [hF3, hc3] at k3
  obtain ⟨cnt, F4, c4, h4, _⟩ := (bind_ok _ _ F c _).1 k3
  exact ⟨fold_ret (bit 0) (hb 0) _ _ _ F c _ h2 col (List.mem_range.mpr hc),
    fold_ret (bit 1) (hb 1) _ _ _ F c _ h3 col (List.mem_range.mpr hc),
    fold_ret pin hp (fun f _ a => f + a) _ _ F c _ h4 col (List.mem_range.mpr hc)⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **`Forest.planeLins` under the law of the reads.** -/
theorem planeLins_reads (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) (F0 F G : Fork) (c c' : Ctx) {iU3 K3 tB0 tB1 tP : ℕ}
    (R : ReadsAt bit pin iU3 K3 tB0 tB1 tP F c)
    (h : Forest.planeLins g lm bit pin F c = .ok (((), G), c'))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hs : F.LS.size = F.ns) (hF : Sized F) :
    Later F G ∧ Sized G ∧ G.LS.size = G.ns ∧
      ∀ H, Later G H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
        ReadsLaw g.shape lm (endsOf g.shape lm jLK rsK).zb0 (endsOf g.shape lm jLK rsK).zb1 ν entry
          iU3 K3 tB0 tB1 tP →
        GrowsBy ρ F G (H.worldOf ρ (fun j => ν (.mask j)) entry)
          [claimLeaves g.shape lm jLK rsK ν (colsK g.shape lm (endsOf g.shape lm jLK rsK).zb0 ν),
            claimBits g.shape lm jLK rsK ν (colsK g.shape lm (endsOf g.shape lm jLK rsK).zb1 ν),
            Pin.countK g.shape lm (Pin.pinColK lm ν)] := by
  have hp : ∀ col, PlaneClaims.Quiet (pin col) := fun col => (R.pin col).1
  obtain ⟨k, z, s, hg⟩ :=
    planeLins_grows ρ g lm jLK rsK bit pin R.bitQ hp F0 F G c c' h hI h0 hok hs hF
  refine ⟨k, z, s, fun H hH ν entry Lw => ?_⟩
  obtain ⟨pl, Fq, cq, hp1, _, _⟩ := planeLins_added (fun e col => still_adds (R.bitQ e col))
    (fun col => still_adds (hp col)) h hs
  have hcol := fun col hc => cols_of_reads ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) R
    (h := g.shape) (lm := lm) (ν := ν) Lw col hc
  have hret := planeClaims_ret g lm bit pin R.bitQ hp F Fq c cq pl hp1
  have e := hg H hH ν entry
  unfold claimLeaves claimBits at e ⊢
  rwa [PlaneClaims.planesK_congr g.shape lm _ _ _ fun col hc => (hcol col hc).1 (hret col hc).1,
    PlaneClaims.planesK_congr g.shape lm _ _ _ fun col hc => (hcol col hc).2.1 (hret col hc).2.1,
    PlaneClaims.countK_congr g.shape lm _ _ fun col hc => (hcol col hc).2.2 (hret col hc).2.2] at e

end
end Fo
