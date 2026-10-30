-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadPolicyForms.lean: the four claims of the acceptance policy, each form by name.

The routine claimPolicy (OnBytes/Model/Head.lean) adds four claims to the state of the output head's
sub-proof. To say "four forms that lead from the state before to the state after" does not name the
forms: adding a claim adds a multiple of its form to one gathered equation, so other lists of forms
lead to the same state. A hypothesis "the claims hold" has to speak of the forms that the routine
builds. This file names them.

Each form is described by the verifier's own expression: the readers that the routine calls, each
returning its form from a state and a context that it leaves, and the way in which the routine puts
these forms together (Pol1 to Pol4). The readers take one number from the state, the number of
columns of the array that stores the reads.

Main definitions: Pol1, Pol2, Pol3, Pol4, polLoop; ClaimsPolicy (the four claims hold in a world).
Main theorems: claimPolicy_list (the routine adds four forms with these descriptions, each read from
a state that has kept the numbers of columns); pol1_value to pol4_value (what any form with a
description is worth in a world with true tables); policy_of_claims (if the routine succeeds and the
four claims hold, the library's two sums are 0 and the extensions of its two identities are 0);
claims_of_policy (the other way round: so the hypothesis ClaimsPolicy can be met).

What is not claimed. That the claims hold is a hypothesis: it is what the batching of all claims is
meant to give. Nothing is said about when a world is true. The proofs of the values use the tools of
Johnson/Road/HeadPolicy.lean. The program does not import this file.
-/
import Johnson.Road.HeadPolicy
import Johnson.Road.HeadWalk

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)
open Inst.Model (NormPar)
open HeadSizes (Sizes)
open Inst.Model.Head (hidC hidB hidU hidK hidZ hidS)

/-! ## The four forms -/

/-- a is the form of the first claim, read from the state F and the context C: over the counted
positions, c + C b + u less theta times their number. -/
def Pol1 (R : Model.Head.Run) (F : Fork) (C : Ctx) (a : Aff) : Prop :=
  ∃ g0 g1 g2, Ok (Model.Head.gapAt R "rhoC" 0 (Model.ofNat R.cov.hRC)) F C g0 F C ∧
    Ok (Model.Head.gapAt R "rhoC" 1 (Model.ofNat R.cov.hRC)) F C g1 F C ∧
    Ok (Model.Head.gapAt R "rhoC" 2 (Model.ofNat R.cov.hRC)) F C g2 F C ∧
    a = g0 + g1.scale (Model.ofNat R.h.clipC) + g2 -
      Aff.ofConst (Model.scaleNat (Model.ofNat R.cov.hRC) R.h.theta)

/-- The form of the second claim: over the counted positions, b + z less cap, or less 0 if no
position is counted. -/
def Pol2 (R : Model.Head.Run) (F : Fork) (C : Ctx) (a : Aff) : Prop :=
  ∃ g1 g4, Ok (Model.Head.gapAt R "rhoC" 1 (Model.ofNat R.cov.hRC)) F C g1 F C ∧
    Ok (Model.Head.gapAt R "rhoC" 4 (Model.ofNat R.cov.hRC)) F C g4 F C ∧
    a = g1 + g4 - Aff.ofConst (Model.ofNat (if R.cov.hRC != 0 then R.h.cap else 0))

/-- The form of the third claim: c + k less C, under the weights of the counted positions at the
point of the margins' call. -/
def Pol3 (R : Model.Head.Run) (F : Fork) (C : Ctx) (a : Aff) : Prop :=
  ∃ p0 p3, Ok (Model.Head.gapAt R "phiC" 0 (Model.Head.ercOf R)) F C p0 F C ∧
    Ok (Model.Head.gapAt R "phiC" 3 (Model.Head.ercOf R)) F C p3 F C ∧
    a = p0 + p3 - Aff.ofConst (Model.scaleNat (Model.Head.ercOf R) R.h.clipC)

/-- The two loops of the routine over the table that begins at te: to the form a0 they add the cells
of the looked-up values, three limbs at radix 256, block by block. -/
def polLoop (R : Model.Head.Run) (te : ℕ) (a0 : Aff) : SubM Aff :=
  forIn [:Model.exc] a0 fun l r =>
    (forIn [:R.L.JV / R.h.S2] r fun xh r2 =>
      Model.Head.U3at R te ((R.L.oE + l * R.L.JV) / R.h.S2 + xh) >>= fun c =>
        (pure PUnit.unit : SubM PUnit) >>= fun _ =>
          pure (ForInStep.yield (r2.addMul c (Model.ofNat (256 ^ l))))) >>= fun r3 =>
      (pure PUnit.unit : SubM PUnit) >>= fun _ => pure (ForInStep.yield r3)

/-- The form of the fourth claim: zs and the position's looked-up values less 2^F, under the same
weights: what the routine's two loops over the table "hf@phiZ" return. -/
def Pol4 (R : Model.Head.Run) (F : Fork) (C : Ctx) (a : Aff) : Prop :=
  ∃ te p5, Starts R "hf@phiZ" te ∧
    Ok (Model.Head.gapAt R "phiC" 5 (Model.Head.ercOf R)) F C p5 F C ∧
    Ok (polLoop R te (p5 + Aff.ofConst (subE
      (mulE (Model.scaleNat (Model.Head.ercOf R) Model.Head.offE) (Model.ofNat R.L.JV))
      (Model.scaleNat (Model.Head.ercOf R) ((R.L.JV - R.h.V + 1) * 2 ^ R.h.famF))))) F C a F C

/-! ## The routine, step by step -/

/-- A step that leaves state and context, and what follows it. -/
theorem step_read {α β : Type} {m : SubM α} (hm : Walk.Leaves m) {f : α → SubM β} {F G : Fork}
    {C D : Ctx} {b : β} (h : Ok (m >>= f) F C b G D) :
    ∃ a, Ok m F C a F C ∧ Ok (f a) F C b G D := by
  rw [ok_bind] at h
  obtain ⟨a, F1, C1, h1, h2⟩ := h
  obtain ⟨e1, e2⟩ := hm F C a F1 C1 h1
  rw [e1, e2] at h1 h2
  exact ⟨a, h1, h2⟩

/-- A claim that is added, and what follows it. -/
theorem step_lin {β : Type} {f : Aff} {k : Unit → SubM β} {F G : Fork} {C D : Ctx} {b : β}
    (h : Ok (SubM.lin f >>= k) F C b G D) : ∃ F1, F.lin f = some F1 ∧ Ok (k ()) F1 C b G D := by
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h2⟩ := h
  rw [ok_lin] at h1
  rw [h1.2] at h2
  exact ⟨F1, h1.1, h2⟩

/-- The two loops leave state and context. -/
theorem leaves_polLoop (R : Model.Head.Run) (te : ℕ) (a0 : Aff) : Walk.Leaves (polLoop R te a0) :=
  Walk.leaves_forIn_range _ _ fun l _ => Walk.leaves_bind
    (Walk.leaves_forIn_range _ _ fun xh r2 =>
      Walk.leaves_bind
        (Walk.leaves_U3at R te ((R.L.oE + l * R.L.JV) / R.h.S2 + xh)) fun c =>
          Walk.leaves_bind (Walk.leaves_pure PUnit.unit) fun _ =>
            Walk.leaves_pure (ForInStep.yield (r2.addMul c (Model.ofNat (256 ^ l)))))
    fun r3 => Walk.leaves_bind (Walk.leaves_pure PUnit.unit) fun _ =>
      Walk.leaves_pure (ForInStep.yield r3)

/-- The routine adds four claims. Their forms have the four descriptions, the first at the state
from which the routine starts, the others at states that have kept the numbers of columns. -/
theorem claimPolicy_list {R : Model.Head.Run} {F G : Fork} {C D : Ctx} {u : Unit}
    (hs : F.LS.size = F.ns) (h : Ok (Model.Head.claimPolicy R) F C u G D) :
    D = C ∧ ∃ a1 a2 a3 a4 F1 F2 F3, Pol1 R F C a1 ∧ Walk.Kept F F1 ∧ Pol2 R F1 C a2 ∧
      Walk.Kept F F2 ∧ Pol3 R F2 C a3 ∧ Walk.Kept F F3 ∧ Pol4 R F3 C a4 ∧
      F.lins [a1, a2, a3, a4] = some G := by
  unfold Model.Head.claimPolicy at h
  dsimp only at h
  obtain ⟨g0, h1, h⟩ := step_read (Walk.leaves_gapAt _ _ _ _) h
  obtain ⟨g1, h2, h⟩ := step_read (Walk.leaves_gapAt _ _ _ _) h
  obtain ⟨g2, h3, h⟩ := step_read (Walk.leaves_gapAt _ _ _ _) h
  obtain ⟨Fa, ha, h⟩ := step_lin h
  obtain ⟨sa, ca⟩ := lin_cols hs ha
  obtain ⟨g1b, h4, h⟩ := step_read (Walk.leaves_gapAt _ _ _ _) h
  obtain ⟨g4, h5, h⟩ := step_read (Walk.leaves_gapAt _ _ _ _) h
  obtain ⟨Fb, hb, h⟩ := step_lin h
  obtain ⟨sb, cb⟩ := lin_cols sa hb
  obtain ⟨p0, h6, h⟩ := step_read (Walk.leaves_gapAt _ _ _ _) h
  obtain ⟨p3, h7, h⟩ := step_read (Walk.leaves_gapAt _ _ _ _) h
  obtain ⟨Fc, hc, h⟩ := step_lin h
  obtain ⟨sc, cc⟩ := lin_cols sb hc
  obtain ⟨te, h8, h⟩ := step_read (Walk.leaves_tabAt _ _) h
  obtain ⟨p5, h9, h⟩ := step_read (Walk.leaves_gapAt _ _ _ _) h
  obtain ⟨a4, h10, h⟩ := step_read (leaves_polLoop R te _) h
  rw [ok_lin] at h
  have P1 : Pol1 R F C _ := ⟨g0, g1, g2, h1, h2, h3, rfl⟩
  have P2 : Pol2 R Fa C _ := ⟨g1b, g4, h4, h5, rfl⟩
  have P3 : Pol3 R Fb C _ := ⟨p0, p3, h6, h7, rfl⟩
  have P4 : Pol4 R Fc C a4 := ⟨te, p5, (ok_tabAt h8).2.2, h9, h10⟩
  exact ⟨h.2, _, _, _, a4, Fa, Fb, Fc, P1, ⟨sa, ca⟩, P2, ⟨sb, fun t => (cb t).trans (ca t)⟩, P3,
    ⟨sc, fun t => (cc t).trans ((cb t).trans (ca t))⟩, P4,
    lins_cons_some ha (lins_cons_some hb (lins_cons_some hc (lins_one h.1)))⟩

/-! ## What the forms are worth -/

section Values

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- The sum of the weights of the counted positions is the extension, at the point u of the margins'
call, of the indicator of these positions. -/
theorem erc_value {R : Model.Head.Run} {z : Sizes} (Z : Laid R z) {u : ℕ → K}
    {y : Inst.Model.Head.Req} (Y : ReqFits R z y)
    (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH) (U : PosFit ρ R "HD0" u) :
    ρ.val (Model.Head.ercOf R) =
      Blocks.ext R.h.lt (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) u := by
  obtain ⟨q, hq, hqs, hqu⟩ := id U
  rw [hqH] at hq
  obtain rfl := Option.some.inj hq
  have hE : ρ.val (Model.Head.ercOf R) =
      Blocks.ext R.h.lt (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) u := by
    have e : Model.Head.ercOf R =
      (Model.Head.costWeights R.cov (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH)).2.1 := rfl
    rw [e, costSum_value ρ R _ (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) hqs (Y.rhoCK Z)]
    exact ext_point _ hqu
  exact hE

/-- A form with the first description is worth the library's first sum. -/
theorem pol1_value (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} {F : Fork} {C : Ctx}
    {a : Aff} {t : Inst.Model.Head.Cells K} {y : Inst.Model.Head.Req} (hXL : R.h.XL = 5)
    (hNB : HeadSizes.NB z y = R.cov.hRC) (hpC : y.pol.C = R.h.clipC)
    (hpT : y.pol.theta = R.h.theta)
    (hRho : SumAt W R (colsOf F R.iU3) "hr@rhoC" z.T
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (P : Pol1 R F C a) : a.value ρ W = HeadSizes.sB2 z t y := by
  obtain ⟨g0, g1, g2, h1, h2, h3, rfl⟩ := P
  have hR : ρ.val (Model.ofNat R.cov.hRC) =
      ∑ j ∈ range z.T, ((HeadSizes.rhoC z y j : ℤ) : K) := by
    rw [hρ.ofNat, ← hNB, sum_rhoC]
  obtain ⟨_, _, v0'⟩ := gap_sums hρ (i := 0) (o := 0) (n := 5)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl rfl hRho hR h1
  obtain ⟨_, _, v1'⟩ := gap_sums hρ (i := 1) (o := 5) (n := 1)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl rfl hRho hR h2
  obtain ⟨_, _, v2'⟩ := gap_sums hρ (i := 2) (o := 6) (n := 5)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl rfl hRho hR h3
  have v0 : g0.value ρ W = ∑ j ∈ range z.T, ((HeadSizes.rhoC z y j : ℤ) : K) * hidC t j := v0'
  have v1 : g1.value ρ W = ∑ j ∈ range z.T, ((HeadSizes.rhoC z y j : ℤ) : K) * hidB t j := v1'
  have v2 : g2.value ρ W = ∑ j ∈ range z.T, ((HeadSizes.rhoC z y j : ℤ) : K) * hidU t j := v2'
  rw [Aff.value_sub, Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_ofConst, v0, v1,
    v2, hρ.scaleNat, hρ.ofNat, hρ.ofNat]
  show _ = ∑ i ∈ range z.T, ((HeadSizes.rhoC z y i : ℤ) : K) * (hidC t i +
      (y.pol.C : K) * hidB t i + hidU t i) -
    (y.pol.theta : K) * (HeadSizes.NB z y : K)
  rw [hpC, hpT, hNB, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun j _ => by ring

/-- A form with the second description is worth the library's second sum. -/
theorem pol2_value (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} {F : Fork} {C : Ctx}
    {a : Aff} {t : Inst.Model.Head.Cells K} {y : Inst.Model.Head.Req} (hXL : R.h.XL = 5)
    (hNB : HeadSizes.NB z y = R.cov.hRC) (hpK : y.pol.cap = R.h.cap)
    (hRho : SumAt W R (colsOf F R.iU3) "hr@rhoC" z.T
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (P : Pol2 R F C a) : a.value ρ W = HeadSizes.sB3 z t y := by
  obtain ⟨g1b, g4, h4, h5, rfl⟩ := P
  have hR : ρ.val (Model.ofNat R.cov.hRC) =
      ∑ j ∈ range z.T, ((HeadSizes.rhoC z y j : ℤ) : K) := by
    rw [hρ.ofNat, ← hNB, sum_rhoC]
  obtain ⟨_, _, v3'⟩ := gap_sums hρ (i := 1) (o := 5) (n := 1)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl rfl hRho hR h4
  obtain ⟨_, _, v4'⟩ := gap_sums hρ (i := 4) (o := 16) (n := 2)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl rfl hRho hR h5
  have v3 : g1b.value ρ W = ∑ j ∈ range z.T, ((HeadSizes.rhoC z y j : ℤ) : K) * hidB t j := v3'
  have v4 : g4.value ρ W = ∑ j ∈ range z.T, ((HeadSizes.rhoC z y j : ℤ) : K) * hidZ t j := v4'
  rw [Aff.value_sub, Aff.value_add, Aff.value_ofConst, v3, v4, hρ.ofNat]
  show _ = ∑ i ∈ range z.T, ((HeadSizes.rhoC z y i : ℤ) : K) * (hidB t i + hidZ t i) -
    (if 0 < HeadSizes.NB z y then (y.pol.cap : K) else 0)
  rw [hNB, hpK, ← sum_add_distrib]
  congr 1
  · exact sum_congr rfl fun j _ => by ring
  · by_cases h0 : R.cov.hRC = 0
    · simp [h0]
    · have hp : 0 < R.cov.hRC := Nat.pos_of_ne_zero h0
      simp [h0, hp]

/-- A form with the third description is worth the extension, at u, of the library's identity on c
and k. -/
theorem pol3_value (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z) {F : Fork}
    {C : Ctx} {a : Aff} {u : ℕ → K} {t : Inst.Model.Head.Cells K} {y : Inst.Model.Head.Req}
    (Y : ReqFits R z y) (hXL : R.h.XL = 5)
    (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH) (U : PosFit ρ R "HD0" u)
    (hpC : y.pol.C = R.h.clipC)
    (hPhi : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (P : Pol3 R F C a) :
    a.value ρ W = Blocks.ext R.h.lt (fun i => HeadSizes.dB4 z t y i) u := by
  obtain ⟨p0, p3, h6, h7, rfl⟩ := P
  have hE := erc_value Z Y hqH U
  obtain ⟨_, _, v5'⟩ := gap_cellsK hρ (i := 0) (o := 0) (n := 5)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl rfl hPhi hE h6
  obtain ⟨_, _, v6'⟩ := gap_cellsK hρ (i := 3) (o := 11) (n := 5)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl rfl hPhi hE h7
  have v5 : p0.value ρ W =
      Blocks.ext R.h.lt (fun j => ((HeadSizes.rhoC z y j : ℤ) : K) * hidC t j) u := v5'
  have v6 : p3.value ρ W =
      Blocks.ext R.h.lt (fun j => ((HeadSizes.rhoC z y j : ℤ) : K) * hidK t j) u := v6'
  rw [Aff.value_sub, Aff.value_add, Aff.value_ofConst, v5, v6, hρ.scaleNat, hE]
  have e : (fun i => HeadSizes.dB4 z t y i) = fun i =>
      ((HeadSizes.rhoC z y i : ℤ) : K) * hidC t i + ((HeadSizes.rhoC z y i : ℤ) : K) * hidK t i -
        (R.h.clipC : K) * ((HeadSizes.rhoC z y i : ℤ) : K) := by
    funext i
    show ((HeadSizes.rhoC z y i : ℤ) : K) * (hidC t i + hidK t i - (y.pol.C : K)) = _
    rw [hpC]
    ring
  rw [e, Blocks.ext_sub, Blocks.ext_add, Blocks.ext_smul]

/-- A form with the fourth description is worth the extension, at u, of the library's identity on zs
and the looked-up values. -/
theorem pol4_value (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z) {F : Fork}
    {C : Ctx} {a4 : Aff} {u : ℕ → K} {t : Inst.Model.Head.Cells K} {y : Inst.Model.Head.Req}
    (Y : ReqFits R z y) (hXL : R.h.XL = 5) (hF : R.h.famF = 24)
    (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH) (U : PosFit ρ R "HD0" u)
    (hPhi : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (hZ : FlatAt W R (colsOf F R.iU3) "hf@phiZ" R.h.ls R.h.lt u
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hf φ i))
    (P : Pol4 R F C a4) :
    a4.value ρ W = Blocks.ext R.h.lt (fun i => HeadSizes.dZ z t y i) u := by
  obtain ⟨te, p5, hst, h9, h10⟩ := P
  unfold polLoop at h10
  have hE := erc_value Z Y hqH U
  obtain ⟨_, _, v7'⟩ := gap_cellsK hρ (i := 5) (o := 18) (n := 3)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl rfl hPhi hE h9
  obtain ⟨_, _, hval, hv⟩ := loop_value ρ W Model.exc _
    (fun l => ∑ xh ∈ range (R.L.JV / R.h.S2), (256 : K) ^ l *
      rdW W R.iU3 (colsOf F R.iU3) (te + ((R.L.oE + l * R.L.JV) / R.h.S2 + xh)))
    (fun l => ∀ xh, xh < R.L.JV / R.h.S2 → Valid R te ((R.L.oE + l * R.L.JV) / R.h.S2 + xh))
    (by
      intro l s r' F11 C11 _ hr
      try dsimp only at hr
      rw [ok_bind] at hr
      obtain ⟨s1, F12, C12, h11, h12⟩ := hr
      obtain ⟨i1, i2, i3, i4⟩ := loop_value ρ W (R.L.JV / R.h.S2) _
        (fun xh => (256 : K) ^ l *
          rdW W R.iU3 (colsOf F R.iU3) (te + ((R.L.oE + l * R.L.JV) / R.h.S2 + xh)))
        (fun xh => Valid R te ((R.L.oE + l * R.L.JV) / R.h.S2 + xh))
        (by
          intro xh s2 r2 F13 C13 _ hq'
          try dsimp only at hq'
          rw [ok_bind] at hq'
          obtain ⟨c, F14, C14, h13, h14⟩ := hq'
          obtain ⟨j1, j2, j3, j4⟩ := U3at_value ρ W h13
          rw [ok_bind] at h14
          obtain ⟨_, F15, C15, h15, h16⟩ := h14
          rw [ok_pure] at h15 h16
          obtain ⟨_, j5, j6⟩ := h15
          obtain ⟨j7, j8, j9⟩ := h16
          refine ⟨j8.trans (j5.trans j1), j9.trans (j6.trans j2), j3, _, j7, ?_⟩
          rw [Aff.value_addMul, j4, hρ.ofNat, Nat.cast_pow, Nat.cast_ofNat])
        h11
      try dsimp only at h12
      rw [ok_bind] at h12
      obtain ⟨_, F16, C16, h17, h18⟩ := h12
      rw [ok_pure] at h17 h18
      obtain ⟨_, k1, k2⟩ := h17
      obtain ⟨k3, k4, k5⟩ := h18
      exact ⟨k4.trans (k1.trans i1), k5.trans (k2.trans i2), i3, _, k3, i4⟩)
    h10
  have v7 : p5.value ρ W =
      Blocks.ext R.h.lt (fun j => ((HeadSizes.rhoC z y j : ℤ) : K) * hidS t j) u := v7'
  have hS : R.h.S2 = 2 ^ R.h.ls := rfl
  have hpos : 0 < 2 ^ R.h.ls := by positivity
  obtain ⟨qv, hqv⟩ := Z.SV
  have hN : R.L.JV / R.h.S2 = qv := by
    rw [Z.JV, hS, hqv, Nat.mul_div_cancel_left _ hpos]
  have hV : qv * 2 ^ R.h.ls = z.V := by rw [hqv, Nat.mul_comm]
  have s1 : ∀ l, l < 3 → ∑ xh ∈ range (R.L.JV / R.h.S2), (256 : K) ^ l *
        rdW W R.iU3 (colsOf F R.iU3) (te + ((R.L.oE + l * R.L.JV) / R.h.S2 + xh)) =
      (256 : K) ^ l * ∑ x ∈ range z.V, Blocks.ext R.h.lt
        (fun i => ((HeadSizes.rhoC z y i : ℤ) : K) *
          t.hf (4 * z.d + 3 * z.V + z.V * l + x) i) u := by
    intro l hl
    rw [← mul_sum, hN, flat_blocks hZ hst
      (by
        rw [Z.oE, Z.JV]
        exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 4) (Dvd.dvd.mul_left Z.SV 3))
          (Dvd.dvd.mul_left Z.SV l))
      (fun xh hx => hval l hl xh (by rw [hN]; exact hx)), hV]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    rw [Z.oE, Z.JV, Nat.mul_comm l z.V]
  have s2 : ∑ l ∈ range Model.exc, ∑ xh ∈ range (R.L.JV / R.h.S2), (256 : K) ^ l *
        rdW W R.iU3 (colsOf F R.iU3) (te + ((R.L.oE + l * R.L.JV) / R.h.S2 + xh)) =
      ∑ l ∈ range 3, (256 : K) ^ l * ∑ x ∈ range z.V, Blocks.ext R.h.lt
        (fun i => ((HeadSizes.rhoC z y i : ℤ) : K) *
          t.hf (4 * z.d + 3 * z.V + z.V * l + x) i) u :=
    sum_congr rfl fun l hl => s1 l (mem_range.mp hl)
  have s3 : ρ.val (subE (mulE (Model.scaleNat (Model.Head.ercOf R) Model.Head.offE)
        (Model.ofNat R.L.JV))
        (Model.scaleNat (Model.Head.ercOf R) ((R.L.JV - R.h.V + 1) * 2 ^ R.h.famF))) =
      8421505 * Blocks.ext R.h.lt (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) u * (z.V : K) -
        2 ^ 24 * Blocks.ext R.h.lt (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) u := by
    rw [ρ.sub, ρ.mul, hρ.scaleNat, hρ.scaleNat, hρ.ofNat, hE, offE_value, Z.JV, Z.V, hF,
      Nat.sub_self, Nat.zero_add, Nat.one_mul, Nat.cast_pow, Nat.cast_ofNat]
  have e : Blocks.ext R.h.lt (fun i => HeadSizes.dZ z t y i) u =
      Blocks.ext R.h.lt (fun i => ((HeadSizes.rhoC z y i : ℤ) : K) * hidS t i) u +
        ((z.V : K) * 8421505 - 2 ^ 24) *
          Blocks.ext R.h.lt (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) u +
        ∑ l ∈ range 3, (256 : K) ^ l * ∑ v ∈ range z.V, Blocks.ext R.h.lt
          (fun i => ((HeadSizes.rhoC z y i : ℤ) : K) *
            t.hf (4 * z.d + 3 * z.V + z.V * l + v) i) u :=
    ext_dZ R.h.lt u z.V (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) (fun i => hidS t i)
      (fun l v i => t.hf (4 * z.d + 3 * z.V + z.V * l + v) i) 8421505 (2 ^ 24)
  rw [hv, Aff.value_add, Aff.value_ofConst, v7, s3, s2, e]
  ring

/-! ## The claims hold -/

/-- The four claims of the acceptance policy hold in W. F: a state. The forms are named through the
routine: any form with one of the four descriptions, read from a state in which every array has as
many columns as in F. That asks more than the run's own four forms. In a world with true tables all
forms with one description have one value (pol1_value to pol4_value); that they are one form is not
shown here. -/
def ClaimsPolicy (ρ : Reading K) (W : World K) (R : Model.Head.Run) (F : Fork) : Prop :=
  (∀ F' C' a, Walk.Kept F F' → Pol1 R F' C' a → a.value ρ W = 0) ∧
  (∀ F' C' a, Walk.Kept F F' → Pol2 R F' C' a → a.value ρ W = 0) ∧
  (∀ F' C' a, Walk.Kept F F' → Pol3 R F' C' a → a.value ρ W = 0) ∧
  ∀ F' C' a, Walk.Kept F F' → Pol4 R F' C' a → a.value ρ W = 0

/-- If the routine succeeds from a state Fp that has kept the numbers of columns of F, and the four
claims hold in a world with true tables, the library's two sums over the counted positions are 0,
and so are the extensions, at the point u, of its two identities at a position. -/
theorem policy_of_claims (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F Fp Gp : Fork} {Cp Dp : Ctx} {w : Unit} {u : ℕ → K} {t : Inst.Model.Head.Cells K}
    {y : Inst.Model.Head.Req} (Y : ReqFits R z y) (hXL : R.h.XL = 5) (hF : R.h.famF = 24)
    (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH) (U : PosFit ρ R "HD0" u)
    (hNB : HeadSizes.NB z y = R.cov.hRC) (hpC : y.pol.C = R.h.clipC)
    (hpT : y.pol.theta = R.h.theta) (hpK : y.pol.cap = R.h.cap)
    (hRho : SumAt W R (colsOf F R.iU3) "hr@rhoC" z.T
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (hPhi : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (hZ : FlatAt W R (colsOf F R.iU3) "hf@phiZ" R.h.ls R.h.lt u
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hf φ i))
    (k : Walk.Kept F Fp) (h : Ok (Model.Head.claimPolicy R) Fp Cp w Gp Dp)
    (c : ClaimsPolicy ρ W R F) :
    HeadSizes.sB2 z t y = 0 ∧ HeadSizes.sB3 z t y = 0 ∧
      Blocks.ext R.h.lt (fun i => HeadSizes.dB4 z t y i) u = 0 ∧
      Blocks.ext R.h.lt (fun i => HeadSizes.dZ z t y i) u = 0 := by
  obtain ⟨_, a1, a2, a3, a4, F1, F2, F3, P1, k1, P2, k2, P3, k3, P4, _⟩ := claimPolicy_list k.1 h
  obtain ⟨c1, c2, c3, c4⟩ := c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← pol1_value hρ hXL hNB hpC hpT (by rw [k.2 R.iU3]; exact hRho) P1]
    exact c1 Fp Cp a1 k P1
  · rw [← pol2_value hρ hXL hNB hpK (by rw [(k.trans k1).2 R.iU3]; exact hRho) P2]
    exact c2 F1 Cp a2 (k.trans k1) P2
  · rw [← pol3_value hρ Z Y hXL hqH U hpC (by rw [(k.trans k2).2 R.iU3]; exact hPhi) P3]
    exact c3 F2 Cp a3 (k.trans k2) P3
  · rw [← pol4_value hρ Z Y hXL hF hqH U (by rw [(k.trans k3).2 R.iU3]; exact hPhi)
      (by rw [(k.trans k3).2 R.iU3]; exact hZ) P4]
    exact c4 F3 Cp a4 (k.trans k3) P4

/-- The other way round, so that the hypothesis ClaimsPolicy can be met: in a world with true tables
in which the library's two sums are 0 and the extensions of its two identities are 0 at u, the four
claims hold. -/
theorem claims_of_policy (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F : Fork} {u : ℕ → K} {t : Inst.Model.Head.Cells K} {y : Inst.Model.Head.Req}
    (Y : ReqFits R z y) (hXL : R.h.XL = 5) (hF : R.h.famF = 24)
    (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH) (U : PosFit ρ R "HD0" u)
    (hNB : HeadSizes.NB z y = R.cov.hRC) (hpC : y.pol.C = R.h.clipC)
    (hpT : y.pol.theta = R.h.theta) (hpK : y.pol.cap = R.h.cap)
    (hRho : SumAt W R (colsOf F R.iU3) "hr@rhoC" z.T
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (hPhi : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (hZ : FlatAt W R (colsOf F R.iU3) "hf@phiZ" R.h.ls R.h.lt u
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hf φ i))
    (z1 : HeadSizes.sB2 z t y = 0) (z2 : HeadSizes.sB3 z t y = 0)
    (z3 : Blocks.ext R.h.lt (fun i => HeadSizes.dB4 z t y i) u = 0)
    (z4 : Blocks.ext R.h.lt (fun i => HeadSizes.dZ z t y i) u = 0) : ClaimsPolicy ρ W R F := by
  refine ⟨fun F' C' a k P => ?_, fun F' C' a k P => ?_, fun F' C' a k P => ?_,
    fun F' C' a k P => ?_⟩
  · rw [pol1_value hρ hXL hNB hpC hpT (by rw [k.2 R.iU3]; exact hRho) P]
    exact z1
  · rw [pol2_value hρ hXL hNB hpK (by rw [k.2 R.iU3]; exact hRho) P]
    exact z2
  · rw [pol3_value hρ Z Y hXL hqH U hpC (by rw [k.2 R.iU3]; exact hPhi) P]
    exact z3
  · rw [pol4_value hρ Z Y hXL hF hqH U (by rw [k.2 R.iU3]; exact hPhi)
      (by rw [k.2 R.iU3]; exact hZ) P]
    exact z4

/-- policy_of_claims at the library's sizes, in the library's own names. -/
theorem policy_of_claims_ref (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F Fp Gp : Fork} {Cp Dp : Ctx} {w : Unit} {u : ℕ → K} {t : Inst.Model.Head.Cells K}
    {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y) (hXL : R.h.XL = 5)
    (hF : R.h.famF = 24) (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH)
    (U : PosFit ρ R "HD0" u) (hNB : y.NB = R.cov.hRC) (hpC : y.pol.C = R.h.clipC)
    (hpT : y.pol.theta = R.h.theta) (hpK : y.pol.cap = R.h.cap)
    (hRho : SumAt W R (colsOf F R.iU3) "hr@rhoC" Inst.Model.Head.nT
      (fun φ i => ((y.rhoC i : ℤ) : K) * t.hr φ i))
    (hPhi : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u
      (fun φ i => ((y.rhoC i : ℤ) : K) * t.hr φ i))
    (hZ : FlatAt W R (colsOf F R.iU3) "hf@phiZ" R.h.ls R.h.lt u
      (fun φ i => ((y.rhoC i : ℤ) : K) * t.hf φ i))
    (k : Walk.Kept F Fp) (h : Ok (Model.Head.claimPolicy R) Fp Cp w Gp Dp)
    (c : ClaimsPolicy ρ W R F) :
    Inst.Model.Head.sB2 t y = 0 ∧ Inst.Model.Head.sB3 t y = 0 ∧
      Blocks.ext R.h.lt (fun i => Inst.Model.Head.dB4 t y i) u = 0 ∧
      Blocks.ext R.h.lt (fun i => Inst.Model.Head.dZ t y i) u = 0 :=
  policy_of_claims hρ Z Y hXL hF hqH U hNB hpC hpT hpK hRho hPhi hZ k h c

end Values

#print axioms claimPolicy_list
#print axioms pol1_value
#print axioms pol2_value
#print axioms pol3_value
#print axioms pol4_value
#print axioms policy_of_claims
#print axioms claims_of_policy
#print axioms policy_of_claims_ref

end OnBytes.Road.Hd
