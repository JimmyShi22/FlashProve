-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OpenClaim.lean: CONDITIONAL.

What is here. One weight claim: the honest side's table, made of its placeholder claim and closed
over the coordinates within a head under the rotation factor (`openOf`, `Sides.weights`, `at2`:
Johnson/Desc/K4/Honest/Sides.lean), is the library's vector of the verifier's claim (`wvClaim`,
Johnson/Road/FormsKeysWv.lean).

  `closeCd`, `weights_eq`   one claim's table, closed; `Sides.weights` is that, claim by claim
  `two_facs`, `three_facs`   a claim's factors at a unit of two or three groups
  `claim_two`, `claim_three`, `claim_last`   the three shapes
  `open_claim`   **the table is the vector**

Limits. At the reading `Reading.gl`. The matrix is any function of row and column to the program's
words, read word by word (`wmOf`). Premises: the layout is what the verifier's own function
`wsLayOf` (OnBytes/Model/Weights.lean) returns for a model with routed experts; the two claims stand
in the relation `ClaimPair` (OpenWalk.lean); the honest function `openOf` returns on the placeholder
claim; the number from which it counts the layers is that of the group's first layer. In a unit with
a group "e" the column lies below two to the bits of an index of "kk"; in another the row is 0.
Nothing on a commitment, a slot or a world.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenShapes
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE maddE)
open OnBytes.Model (Reading WsLay WsUnit WsGrp WsFac WsClaim WsShape wsLayOf eqTab)
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Road (UnitOK sumSel wgtOf wvClaim hasE wkOf selOf claim_inv unit_found
  groups_found groupsOf namesOf unitOK_of_layout map_two map_three mapM_cons_some hasE_two hasE_last
  hasE_three wkOf_three sumSel_two sumSel_last sumSel_three)
open OnBytes.Road.K4.C (gl_foldl_maddE range_sum)
open OnBytes.Desc.First.K4.Honest

/-- **One claim's table, closed**: where the unit has the group "cd", that group is closed under the
verifier's rotation factor at the weights et on the tokens. -/
def closeCd (ce : ClaimEnv) (et lfc : Array E) (o : Open) : Array E :=
  if o.cd == 0 then o.tab
  else
    (Array.range o.kk).map fun k2 =>
      (List.range o.cd).foldl
        (fun s c => maddE s ((ce.ropeFactor et lfc o.lam).getD c zeroE)
          (o.tab.getD (c * o.kk + k2) zeroE)) zeroE

theorem weights_eq (S : OnBytes.Desc.First.K4.Honest.Sides) (et : Array E) :
    S.weights et = S.opens.map (closeCd S.ce et S.lfc) := rfl

/-- A claim's factors at a unit of two groups. -/
theorem two_facs {fac : WsGrp → Option WsFac} {g1 g2 : WsGrp} {f : List WsFac}
    (h : [g1, g2].mapM fac = some f) :
    ∃ X1 X2, fac g1 = some X1 ∧ fac g2 = some X2 ∧ f = [X1, X2] := by
  obtain ⟨X1, r1, h1, hr1, rfl⟩ := mapM_cons_some h
  obtain ⟨X2, r2, h2, hr2, rfl⟩ := mapM_cons_some hr1
  have e : r2 = [] := by simpa using hr2.symm
  subst e
  exact ⟨X1, X2, h1, h2, rfl⟩

/-- At a unit of three groups. -/
theorem three_facs {fac : WsGrp → Option WsFac} {g1 g2 g3 : WsGrp} {f : List WsFac}
    (h : [g1, g2, g3].mapM fac = some f) :
    ∃ X1 X2 X3, fac g1 = some X1 ∧ fac g2 = some X2 ∧ fac g3 = some X3 ∧ f = [X1, X2, X3] := by
  obtain ⟨X1, r1, h1, hr1, rfl⟩ := mapM_cons_some h
  obtain ⟨X2, X3, h2, h3, rfl⟩ := two_facs hr1
  exact ⟨X1, X2, X3, h1, h2, h3, rfl⟩

variable {lay : WsLay} {w : ℕ → ℕ → F} {g0 : ℕ} {x0 x : WsClaim} {o : Open} {u : WsUnit}
  (ce : ClaimEnv) (et lfc : Array E)

/-- **The groups kk, x.** The two claims have one factor on "x". -/
theorem claim_two {g1 g2 : WsGrp} (hg : u.g = [g1, g2]) (n1 : g1.name = "kk")
    (n2 : g2.name = "x") (hu0 : lay.U[x0.ui]? = some u) (U : UnitOK lay.lk u)
    (ho : openOf lay w g0 x0 = some o) {Y1 X1 X2 : WsFac} (hf0 : x0.f = [Y1, X2])
    (hf : x.f = [X1, X2]) (yv : ℕ) :
    Reading.gl.val (at2 (closeCd ce et lfc o) o.kk 0 yv) =
      sumSel Reading.gl (selOf u.g (0 * 2 ^ wkOf u.g + yv)) (x.f.zip u.g) (wgtOf u (wmOf w)) := by
  have hcd := (open_two hg n1 n2 hu0 ho).2.2
  unfold closeCd
  rw [hcd, if_pos (beq_self_eq_true 0), tab_two hg n1 n2 hu0 U ho hf0 yv, Nat.zero_mul,
    Nat.zero_add, hf]
  conv_rhs => rw [hg]
  exact (sumSel_two Reading.gl n1 n2 X1 X2 _ yv).symm

/-- **The groups kk, e, x.** The two claims have one factor on "x". -/
theorem claim_three {g1 g2 g3 : WsGrp} (hg : u.g = [g1, g2, g3]) (n1 : g1.name = "kk")
    (n2 : g2.name = "e") (n3 : g3.name = "x") (hu0 : lay.U[x0.ui]? = some u)
    (U : UnitOK lay.lk u) (ho : openOf lay w g0 x0 = some o) {Y1 Y2 X1 X2 X3 : WsFac}
    (hf0 : x0.f = [Y1, Y2, X3]) (hf : x.f = [X1, X2, X3]) (hi : ℕ) {yv : ℕ}
    (hy : yv < 2 ^ wkOf u.g) :
    Reading.gl.val (at2 (closeCd ce et lfc o) o.kk hi yv) =
      sumSel Reading.gl (selOf u.g (hi * 2 ^ wkOf u.g + yv)) (x.f.zip u.g)
        (wgtOf u (wmOf w)) := by
  have hcd := (open_three hg n1 n2 n3 hu0 ho).2.2
  have hwk : OnBytes.ceilLog2 g1.R = wkOf u.g := by
    rw [hg]
    exact (wkOf_three n1).symm
  unfold closeCd
  rw [hcd, if_pos (beq_self_eq_true 0), tab_three hg n1 n2 n3 hu0 U ho hf0 hi yv, hf]
  have e := sumSel_three Reading.gl n1 n2 n3 X1 X2 X3 (wgtOf u (wmOf w)) hwk hi hy
  rw [← hg] at e
  rw [show ([X1, X2, X3] : List WsFac).zip u.g = [(X1, g1), (X2, g2), (X3, g3)] by rw [hg]; rfl]
  exact e.symm

/-- **The groups hd, cd, kk.** The two claims have one factor on "hd"; the verifier's factor on "cd"
is written out: kap. -/
theorem claim_last {g1 g2 g3 : WsGrp} (hg : u.g = [g1, g2, g3]) (n1 : g1.name = "hd")
    (n2 : g2.name = "cd") (n3 : g3.name = "kk") (c2 : g2.cls = 'A')
    (hu0 : lay.U[x0.ui]? = some u) (U : UnitOK lay.lk u) (ho : openOf lay w g0 x0 = some o)
    {Y2 Y3 X1 X3 : WsFac} (hf0 : x0.f = [X1, Y2, Y3])
    (hf : x.f = [X1, { AV := ce.ropeFactor et lfc o.lam }, X3]) (yv : ℕ) :
    Reading.gl.val (at2 (closeCd ce et lfc o) o.kk 0 yv) =
      sumSel Reading.gl (selOf u.g (0 * 2 ^ wkOf u.g + yv)) (x.f.zip u.g) (wgtOf u (wmOf w)) := by
  obtain ⟨ht, hk, hcd, _⟩ := open_last hg n1 n2 n3 hu0 ho
  have e := sumSel_last Reading.gl n1 n2 n3 X1 { AV := ce.ropeFactor et lfc o.lam } X3
    (wgtOf u (wmOf w)) yv
  rw [← hg] at e
  rw [Nat.zero_mul, Nat.zero_add, hf]
  conv_rhs => rw [show ([X1, { AV := ce.ropeFactor et lfc o.lam }, X3] : List WsFac).zip u.g =
    [(X1, g1), ({ AV := ce.ropeFactor et lfc o.lam }, g2), (X3, g3)] by rw [hg]; rfl]
  rw [e]
  have hfa : ∀ b,
      OnBytes.Road.facAt Reading.gl ({ AV := ce.ropeFactor et lfc o.lam } : WsFac) g2 b =
      Reading.gl.val ((ce.ropeFactor et lfc o.lam).getD b zeroE) := by
    intro b
    unfold OnBytes.Road.facAt
    rw [c2, if_neg (by decide)]
  unfold at2
  rw [hk]
  by_cases hy : yv < g3.R
  · rw [if_pos hy, if_pos hy, Nat.zero_mul, Nat.zero_add]
    unfold closeCd
    rw [hcd, hk]
    by_cases h0 : g2.R = 0
    · rw [h0, if_pos (beq_self_eq_true 0), getD_beyond _ (by
        rw [fbFree_size hu0 ht]
        have es : (stridesOf u ["cd", "kk"]).2 = g3.R * g2.R := by
          simp [stridesOf, hg, n1, n2, n3]
        rw [es, h0, Nat.mul_zero]
        exact Nat.zero_le _), Reading.gl.zero]
      simp
    · rw [if_neg (by simpa using h0), getD_range_map _ _ _ hy, gl_foldl_maddE, Reading.gl.zero,
        zero_add, range_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun b hb => ?_
      have e2 := tab_last hg n1 n2 n3 hu0 U ho hf0 (Finset.mem_range.mp hb) hy
      rw [hk] at e2
      rw [e2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hfa]
      ring
  · rw [if_neg hy, if_neg hy]
    exact Reading.gl.zero

/-- **THE TABLE IS THE VECTOR**, one claim. c0: the environment of the honest side's placeholder
claim x0; rs, rt: the verifier's challenges and end point, at which x is made. -/
theorem open_claim {c0 : ClaimEnv} {rs rt lfc : Array E} {x0 x : WsClaim} {s : WsShape} {lk : ℕ}
    (hl : wsLayOf s true lk = .ok c0.wsLay)
    (P : ClaimPair c0 { c0 with rs := rs, rt := rt } lfc x0 x) {w : ℕ → ℕ → F} {o : Open}
    (ho : openOf c0.wsLay w (c0.v.g * c0.v.y.Lam) x0 = some o) {u : WsUnit}
    (hu : c0.wsLay.U[x.ui]? = some u) (hi yv : ℕ)
    (hc : (hasE u.g = true ∧ yv < 2 ^ wkOf u.g) ∨ (hasE u.g = false ∧ hi = 0)) :
    Reading.gl.val (at2 (closeCd c0 (eqTab rt) lfc o) o.kk hi yv) =
      wvClaim Reading.gl c0.wsLay (wmOf w) x (hi * 2 ^ wkOf u.g + yv) := by
  obtain ⟨X, lam, fac0, fac, hX, h0, h1, hfac, hcd⟩ := P
  obtain ⟨u0, a1, a2, a3⟩ := claim_inv h0
  obtain ⟨u1, b1, b2, b3⟩ := claim_inv h1
  have b1' : c0.wsLay.unitOf X (c0.v.lay lam) = some x.ui := b1
  have b2' : c0.wsLay.U[x.ui]? = some u1 := b2
  obtain rfl : u1 = u := Option.some.inj (b2'.symm.trans hu)
  have eui : x0.ui = x.ui := Option.some.inj (a1.symm.trans b1')
  rw [eui] at a2
  obtain rfl : u0 = u1 := Option.some.inj (a2.symm.trans hu)
  have hu0 : c0.wsLay.U[x0.ui]? = some u0 := by rw [eui]; exact hu
  obtain ⟨U', a, _, oo, eU, _, el⟩ := unit_found hl b1' hu
  have U : UnitOK c0.wsLay.lk u0 := by
    rw [(unitOK_of_layout hl).1]
    exact U'
  have hgr := groups_found hl b1' hu hX
  unfold wvClaim
  rw [hu]
  unfold groupsOf at hgr
  by_cases hX0 : X = 0
  · -- hd, cd, kk
    rw [if_pos hX0] at hgr
    obtain ⟨g1, g2, g3, hg, e1, e2, e3⟩ := map_three hgr
    have n1 : g1.name = "hd" := congrArg Prod.fst e1
    have n2 : g2.name = "cd" := congrArg Prod.fst e2
    have n3 : g3.name = "kk" := congrArg Prod.fst e3
    have c2 : g2.cls = 'A' := congrArg Prod.snd e2
    rw [hg] at a3 b3
    obtain ⟨Y1, Y2, Y3, p1, _, _, hf0⟩ := three_facs a3
    obtain ⟨X1, X2, X3, q1, q2, _, hf⟩ := three_facs b3
    have e11 : Y1 = X1 := by
      have := hfac g1 (by rw [n1, hX0]; decide) (by rw [n1]; decide) (by rw [n1]; decide)
        (by rw [n1]; decide)
      rw [p1, q1] at this
      exact Option.some.inj this
    have hlam : o.lam = lam := by
      rw [(open_last hg n1 n2 n3 hu0 ho).2.2.2, eU]
      show a.l - _ = _
      rw [el]
      show c0.v.g * c0.v.y.Lam + lam - c0.v.g * c0.v.y.Lam = lam
      omega
    have e22 : X2 = { AV := c0.ropeFactor (eqTab rt) lfc o.lam } := by
      have := hcd hX0 g2 n2
      rw [q2] at this
      rw [hlam]
      exact Option.some.inj this
    have hE : hasE u0.g = false := by
      rw [hg]
      exact hasE_last n1 n2 n3
    rcases hc with ⟨k, _⟩ | ⟨_, rfl⟩
    · rw [hE] at k
      cases k
    · rw [e11] at hf0
      rw [e22] at hf
      exact claim_last c0 (eqTab rt) lfc hg n1 n2 n3 c2 hu0 U ho hf0 hf yv
  · rw [if_neg hX0] at hgr
    by_cases hX7 : X = 7 ∨ X = 8 ∨ X = 10
    · -- kk, e, x
      rw [if_pos hX7] at hgr
      obtain ⟨g1, g2, g3, hg, e1, e2, e3⟩ := map_three hgr
      have n1 : g1.name = "kk" := congrArg Prod.fst e1
      have n2 : g2.name = "e" := congrArg Prod.fst e2
      have n3 : g3.name = "x" := congrArg Prod.fst e3
      rw [hg] at a3 b3
      obtain ⟨Y1, Y2, Y3, _, _, p3, hf0⟩ := three_facs a3
      obtain ⟨X1, X2, X3, _, _, q3, hf⟩ := three_facs b3
      have e33 : Y3 = X3 := by
        have := hfac g3 (by
            rw [n3]
            unfold namesOf groupsOf
            rw [if_neg hX0, if_pos hX7]
            decide) (by rw [n3]; decide) (by rw [n3]; decide) (by rw [n3]; decide)
        rw [p3, q3] at this
        exact Option.some.inj this
      have hE : hasE u0.g = true := by
        rw [hg]
        exact hasE_three n1 n2 n3
      rcases hc with ⟨_, hy⟩ | ⟨k, _⟩
      · rw [e33] at hf0
        exact claim_three c0 (eqTab rt) lfc hg n1 n2 n3 hu0 U ho hf0 hf hi hy
      · rw [hE] at k
        cases k
    · -- kk, x
      rw [if_neg hX7] at hgr
      obtain ⟨g1, g2, hg, e1, e2⟩ := map_two hgr
      have n1 : g1.name = "kk" := congrArg Prod.fst e1
      have n2 : g2.name = "x" := congrArg Prod.fst e2
      rw [hg] at a3 b3
      obtain ⟨Y1, Y2, _, p2, hf0⟩ := two_facs a3
      obtain ⟨X1, X2, _, q2, hf⟩ := two_facs b3
      have e22 : Y2 = X2 := by
        have := hfac g2 (by
            rw [n2]
            unfold namesOf groupsOf
            rw [if_neg hX0, if_neg hX7]
            decide) (by rw [n2]; decide) (by rw [n2]; decide) (by rw [n2]; decide)
        rw [p2, q2] at this
        exact Option.some.inj this
      have hE : hasE u0.g = false := by
        rw [hg]
        exact hasE_two n1 n2
      rcases hc with ⟨k, _⟩ | ⟨_, rfl⟩
      · rw [hE] at k
        cases k
      · rw [e22] at hf0
        exact claim_two c0 (eqTab rt) lfc hg n1 n2 hu0 U ho hf0 hf yv

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.weights_eq
#print axioms ProofFile.Honest.K4.two_facs
#print axioms ProofFile.Honest.K4.three_facs
#print axioms ProofFile.Honest.K4.claim_two
#print axioms ProofFile.Honest.K4.claim_three
#print axioms ProofFile.Honest.K4.claim_last
#print axioms ProofFile.Honest.K4.open_claim
