-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/AttCaps.lean: the two caps that the law on an attention sub-proof's rounds asks of
its numbers, from the yes of the verifier's public part.

"Verify.linkRounds X link moment" (OnBytes/Model/VerifySubproofs.lean) plans the rounds of a link's
sub-proof. Its arm for attention is "Attention.rounds a moment" at a member a of X.A.
OnBytes/Params/Fit/FitSubAtt.lean shows that these rounds keep a property of the entries under two
caps (AttentionCap, SmallCap: OnBytes/Params/Fit/FitSub.lean): on 2 lgk + 2 lt + 4, and on the
columns of the smallness test's matrices. This file draws both caps from the yes of
"Verify.publicOf".

Where the numbers come from. A member a of X.A is what Attention.plan returns at the configuration
that Attention.fill makes, but for the field tl of its seam, whose matrices are kept
("Fo.Pub.public_A", OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean). The plan's own numbers lt and lgk
are the configuration's; fill sets lt := P.h.lt and lgk := clog2 P.h.Gk, P the parameter file as
scanned; the layers' layout has tested lt ≤ 16 and H + Gk ≤ 64
(OnBytes/Model/Fit/LayoutCaps.lean).
The seam's tl is what HTailF2.shape returns, which is shapeF by definition, passed on by routines
that keep the matrices ("Fo.BatRows.planA_rows0", "seamPlan_keeps",
OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean); shapeF has tested the number of matrices and each one's
columns (OnBytes/Model/Fit/ShapeFCaps.lean). Of the seam's tl at a only the matrices and tau are
known to be the plan's; the lookup's sizes in it (f9) are not, and no law here or in
OnBytes/Params/Fit/FitSubAtt.lean asks a bound on them.

Main theorems.
 - fill_nums, shape_cf, hid_cf, plan_own: the numbers along that road.
 - att_nums: a.own.lt ≤ 16 and a.own.lgk ≤ 6. att_zero_cap: AttentionCap a.own.
 - seamShape_F: the tl of what Seam.shape returns is a value of shapeF, at arguments that are
   written out but for the record of the owner's array.
 - **att_small_cap**: SmallCap (smallSize a.seam.tl).

Limits. The caps alone: that the rounds keep the entries small under them is
OnBytes/Model/Fit/AttKeeps.lean. Nothing on the other two arms of linkRounds. The program does not
import this file.


-/
import OnBytes.Model.Fit.LayoutCaps
import OnBytes.Model.Fit.ShapeFCaps
import OnBytes.Params.Fit.FitSub
import OnBytes.Slice.ProgCodes
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Fit

open Fo.BatRows (bindE_ok)
open OnBytes.Params (AttentionCap SmallCap)

/-! ## The plan's own numbers -/

/-- What fill sets. -/
theorem fill_nums {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {lines : List Attention.Line}
    {g : Nat} {cf : Attention.Cfg} (e : Attention.fill P y s lines g = .ok cf) :
    cf.lt = P.h.lt ∧ cf.lgk = clog2 P.h.Gk := by
  unfold Attention.fill at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact ⟨rfl, rfl⟩

/-- The shape holds the configuration from which it was made. -/
theorem shape_cf {cf : Attention.Cfg} {S : Attention.Shape} (h : Attention.shape cf = .ok S) :
    S.cf = cf := by
  unfold Attention.shape at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  cases h
  rfl

/-- The same behind the lookup's numbers. -/
theorem hid_cf {lid : Nat} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (h : Attention.shapeHid lid cf = .ok (S, fs)) : S.cf = cf := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  cases h
  show A.cf = cf
  exact shape_cf hA

/-- The plan's own lt and lgk are the configuration's. -/
theorem plan_own {st : Settings} {i : Attention.In} {cf : Attention.Cfg} {P : Attention.Plan}
    (e : Attention.plan st i cf = .ok P) : P.own.lt = cf.lt ∧ P.own.lgk = cf.lgk := by
  unfold Attention.plan at e
  dsimp only at e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨⟨S, fs⟩, hS, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  have hc := hid_cf hS
  exact ⟨congrArg Attention.Cfg.lt hc, congrArg Attention.Cfg.lgk hc⟩

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- **The two numbers of an attention plan of the public part.** -/
theorem att_nums (hX : Verify.publicOf pol KL lay = .ok X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : a.own.lt ≤ 16 ∧ a.own.lgk ≤ 6 := by
  obtain ⟨sc, lines, cf, a0, _, _, hf, hp, ea, _, _⟩ := Fo.Pub.public_A hX g a hg
  have C := polLayout_caps (Fo.Pub.publicOf_cut pol KL lay X hX).1
  obtain ⟨f1, f2⟩ := fill_nums hf
  obtain ⟨p1, p2⟩ := plan_own hp
  have e1 : a.own = a0.own := (congrArg Attention.Plan.own ea).trans rfl
  have hlt : X.P.h.lt ≤ 16 := C.lt
  have hGk : X.P.h.Gk ≤ 2 ^ 6 := by
    have h64 : X.P.h.H + X.P.h.Gk ≤ 64 := C.heads
    omega
  rw [e1, p1, p2, f1, f2]
  exact ⟨hlt, OnBytes.Slice.ceilLog2_le _ 6 hGk⟩

/-- The premise of "keeps_attentionRounds" on 2 lgk + 2 lt + 4. -/
theorem att_zero_cap (hX : Verify.publicOf pol KL lay = .ok X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : AttentionCap a.own := by
  obtain ⟨h1, h2⟩ := att_nums hX hg
  exact ⟨by omega⟩

/-! ## The smallness test's matrices -/

/-- The tl of what Seam.shape returns is a value of shapeF. -/
theorem seamShape_F {g : Settings} {m : Array TMat} {tau col0F ktO aO : Nat} {s : Attention.Seam}
    (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s) :
    ∃ (f : Array T2Foreign),
      ({ tau := g.tau, lidb := g.lidb } : HTailF2).shapeF
        (m.map fun M => if M.kind == 1 then { M with foreign := some 0, ttOff := 0 } else M)
        (Array.replicate
          (m.map fun M => if M.kind == 1 then { M with foreign := some 0, ttOff := 0 } else M).size
          none) f #[false, false, true, false] tau = .ok s.tl := by
  unfold Attention.Seam.shape at e
  dsimp only at e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨tl, ht, e⟩ := bindE_ok e
  cases e
  exact ⟨_, ht⟩

/-- **The cap on the columns of the smallness test's matrices.** -/
theorem att_small_cap (hX : Verify.publicOf pol KL lay = .ok X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : SmallCap (smallSize a.seam.tl) := by
  obtain ⟨sc, lines, cf, a0, _, _, _, hp, _, hm, _⟩ := Fo.Pub.public_A hX g a hg
  obtain ⟨seam0, h0, h1, _⟩ := Fo.BatRows.planA_rows0 _ _ _ _ hp
  obtain ⟨k1, _⟩ := Fo.BatRows.seamPlan_keeps _ _ _ _ _ h1
  obtain ⟨f, hF⟩ := seamShape_F h0
  have hc := small_cap hF
  have e : a.seam.tl.foldColumns = seam0.tl.foldColumns := by
    unfold HTailF2.foldColumns
    rw [hm, k1]
  refine ⟨?_⟩
  show a.seam.tl.foldColumns * 276 ≤ 2 ^ 45
  rw [e]
  exact hc

end OnBytes.Model.Fit

#print axioms OnBytes.Model.Fit.plan_own
#print axioms OnBytes.Model.Fit.att_nums
#print axioms OnBytes.Model.Fit.att_zero_cap
#print axioms OnBytes.Model.Fit.seamShape_F
#print axioms OnBytes.Model.Fit.att_small_cap
