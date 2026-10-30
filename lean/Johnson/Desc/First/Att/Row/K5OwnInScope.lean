-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5OwnInScope.lean: CONDITIONAL (THAT publicOf RETURNS IS A PREMISE):
THE ELEVEN NUMBERS OF KIND K5's OWN ROUNDS AT EACH OF
THE TWELVE ATTENTION
PLANS OF THE PUBLIC DATA, AT ALL PUBLIC FILES IN THE GOALS' SCOPE, ARE THE WRITTEN ONES: OFF THE
MAKER's
TEXT: NO TWIN OF A PLAN, NO PIN, NOTHING UNDER THE HEAD. A join of laws that lie; nothing is
evaluated.
  `own_ext`: two values with the same twelve fields are one.
  **`own_in_scope`** (hS : InScope Pb) (hR : readFiles Pb = .ok pp) (hX : publicOf Pb.pol Pb.KL lay
  =
    .ok X) (hg : g < 12) (ha : X.A[g]? = some a) : `a.own = { ownW with rows := a.own.rows }`
    (`ownW`, K5OwnW.lean).
    By: `Meaning.own_of_public` (eleven of own's fields are the shape's) · `Meaning.scope_plans`,
    `Meaning.Att.hid_in_scope` (the shape is what shapeHid returns at a configuration with the
    reference numbers and the usual call list) · `L5.attSized_hid` (the shape's sizes) ·
    `K5Law.place_of_hid`, `counts_place` (two plane messages; two score units) · `npOf_of_four`
    (K5PiecesFour.lean: each unit has 20 pieces) · arithmetic.
Limits. Nothing on own's field rows. Nothing on soundness. On hiding nothing.
WHAT IT GIVES: the eleven written numbers at each plan. Of K5's row's eight binders (`k5_row_own`,
K5RowOwn.lean) this file pays none: h₁ and h₂ fall in K5OwnScope.lean, from this law and two
decisions of Lean's kernel (K5OwnRounds.lean, K5OwnPlanOk.lean).
WHAT IT DOES NOT: h₄ (the walk at each plan) · hm · hZ, hG: shown at no public files by Lean's
kernel.

-/
import Johnson.Desc.First.Att.Row.K5PiecesFour
import Johnson.Desc.First.Att.Row.K5OwnW
import Johnson.Desc.First.Att.Claims.PlaceOf
import Johnson.Desc.First.Att.K05Record
import Johnson.Goal.Meaning.AttForInScope
import Johnson.Goal.Meaning.PlanOwnRow
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Road.Lane5AttHid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Road.L5 (attSized_hid four_of_hid)

/-- Two values of the own rounds' numbers with the same twelve fields are one. -/
theorem own_ext {x y : Params.AttentionRounds} (h1 : x.lt = y.lt) (h2 : x.lgk = y.lgk)
    (h3 : x.pairs = y.pairs) (h4 : x.Lam = y.Lam) (h5 : x.planeMessages = y.planeMessages)
    (h6 : x.score = y.score) (h7 : x.e = y.e) (h8 : x.valueM = y.valueM)
    (h9 : x.valueD = y.valueD) (h10 : x.attained = y.attained) (h11 : x.bits = y.bits)
    (h12 : x.rows = y.rows) : x = y := by
  cases x
  cases y
  simp_all

/-- **IN SCOPE: THE OWN ROUNDS' ELEVEN NUMBERS ARE THE WRITTEN ONES.** -/
theorem own_in_scope {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hX : publicOf Pb.pol Pb.KL lay = .ok X) {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ha : X.A[g]? = some a) : a.own = { ownW with rows := a.own.rows } := by
  obtain ⟨-, -, -, hA⟩ := Meaning.scope_plans hS hR hX
  obtain ⟨a', ha', eS⟩ := hA g hg
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  obtain ⟨cf, hh, hc, -, h12, h8, U⟩ := Meaning.Att.hid_in_scope hS hR hX hg
  rw [← eS] at hh
  have Sz := attSized_hid hh hc h12 h8
  obtain ⟨k1, k2⟩ := VerifiableInference.Desc.First.Att.P.counts_place (K5Law.place_of_hid hh U)
  obtain ⟨n1, n2⟩ := npOf_of_four (four_of_hid hh U)
  have O := Meaning.own_of_public hX ha'
  have hn : 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) = 20 := by
    rw [hc.ll, hc.H, hc.lgk]
    norm_num
  have z1 := Sz.lgk
  have z2 := Sz.lnT
  have z3 := Sz.lB
  have z4 := Sz.ldh
  have z5 := Sz.lt
  have p1 : a'.S.NP = 20 := by
    show a'.S.Lam * a'.S.HA = 20
    rw [Sz.Lam, Sz.HA]
  have q1 : a'.S.nvKF .fm = 17 := by
    show a'.S.cf.lgk + 2 * a'.S.lnT - 1 + a'.S.cf.ldh = 17
    omega
  have q2 : a'.S.nvKF .fd = 14 := by
    show a'.S.cf.lgk + a'.S.lnT + a'.S.cf.ldh = 14
    omega
  have q3 : a'.S.nvE = 13 := by
    show a'.S.cf.lgk + a'.S.cf.lt = 13
    omega
  have q4 : a'.S.nvVM = 16 := by
    show a'.S.cf.lgk + 2 * a'.S.lnT - 1 + a'.S.cf.lB = 16
    omega
  have q5 : a'.S.nvVD = 13 := by
    show a'.S.cf.lgk + a'.S.lnT + a'.S.cf.lB = 13
    omega
  have q6 : a'.S.nvF = 20 := by
    show a'.S.cf.lt + a'.S.cf.lgk + a'.S.cf.ldh = 20
    omega
  have q7 : a'.S.nvH = 17 := by
    show a'.S.cf.lt + a'.S.cf.lgk + 4 = 17
    omega
  have ks : (Attention.Counts.of a'.S).score.toList = [(17, 20), (14, 20)] := by
    rw [k2, n1, n2, hn, q1, q2]
  exact own_ext (O.lt.trans z5) (O.lgk.trans z1) (O.pairs.trans p1) (O.Lam.trans Sz.Lam)
    (O.planeMessages.trans k1) (O.score.trans ks) (O.e.trans q3) (O.valueM.trans q4)
    (O.valueD.trans q5) (O.attained.trans q6) (O.bits.trans q7) rfl

end H2K5.Row

#print axioms H2K5.Row.own_ext
#print axioms H2K5.Row.own_in_scope
