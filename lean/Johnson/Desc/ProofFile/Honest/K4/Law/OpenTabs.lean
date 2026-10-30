-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OpenTabs.lean: CONDITIONAL.

What is here. The tables of the weights that the batched sumcheck's honest job holds (`StackData.F`,
Johnson/Desc/K4/Honest/Stack.lean) are the library's vectors of the verifier's weight claims
(`wvOf`, Johnson/Road/FormsKeysWv.lean), claim by claim.

  `sides_open`   what the honest side's shared data hold of the claims
  `mapM_member`   a member of a list that a function which may refuse has made
  `opens_at`   claim number a: its placeholder, its table, the relation to the verifier's claim
  `opens_are`   **the tables are the vectors**
  `pair_ui`   the two claims of a pair name one unit
  `opens_kk`, `opens_beyond`   the number of columns; a row from the extent of "e" on is 0

Limits. At the reading `Reading.gl`. The matrix is the one that the honest input holds, read word by
word (`wmOf`): nothing ties it to a commitment. Premises: the function that makes the job's data
returns; the verifier's list of claims is what its function returns AT THE HONEST SIDE's OWN
ENVIRONMENT, with any challenges and the end point of the sampled values laid in: that this is the
list of a hearing is not said here (Law/W/MergedAt.lean has it); the layout of the weights is what
the verifier's own function `wsLayOf` (OnBytes/Model/Weights.lean) returns for a model with routed
experts. The place in a vector is row times two to the bits of an index of the claim's group "kk",
plus column: that these bits are a panel's is not said here. In a unit with a group "e" the column
lies below two to these bits; in another the row is 0 and the column is any number. OpenTrial.lean
tries the equation by evaluation at the small plan. Nothing on a slot or a world.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenClaim
import Johnson.Desc.ProofFile.Honest.K4.Law.StackPass
import Johnson.Road.K4.C.CornerKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Reading WsLay WsUnit WsGrp WsFac WsClaim WsShape wsLayOf eqTab)
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Road (wvOf wvOf_at wvClaim hasE wkOf rel_get claim_inv groups_found groupsOf map_two
  map_three hasE_two hasE_last)
open OnBytes.Desc.First.K4.Honest

/-- **What the honest side's shared data hold of the claims**: the placeholder claims, their tables,
the equality table of the coordinates within a head, the environment's group and layout. -/
theorem sides_open {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}
    (h : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) :
    ∃ cl0 AH, S.ce.weightClaims S.TS = some cl0 ∧ S.ce.headWeights = some (AH, S.lfc) ∧
      cl0.toArray.mapM (openOf Q.P.wsLay w.w (Q.g * Q.P.y.Lam)) = some S.opens ∧
      S.ce.wsLay = Q.P.wsLay ∧ S.ce.v.g = Q.g ∧ S.ce.v.y = Q.P.y := by
  unfold OnBytes.Desc.First.K4.Honest.Sides.of at h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨TS, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Z, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨cls, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨AH, lfc⟩, hw, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨opens, ho, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨gl, gr⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ends, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  exact ⟨cls, AH, hc, hw, ho, rfl, OnBytes.Road.K4.C.envOf_g hv, OnBytes.Road.K4.C.envOf_y hv⟩

/-- A member of a list that a function which may refuse has made. -/
theorem mapM_member {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ (a : ℕ) (x : α), l[a]? = some x → ∃ y, r[a]? = some y ∧ f x = some y
  | [], _, _, _, _, hx => by simp at hx
  | z :: l, r, h, a, x, hx => by
    obtain ⟨y, ys, hy, hys, rfl⟩ := OnBytes.Road.mapM_cons_some h
    cases a with
    | zero =>
      obtain rfl : z = x := by simpa using hx
      exact ⟨y, rfl, hy⟩
    | succ a =>
      obtain ⟨y', h1, h2⟩ := mapM_member f l ys hys a x (by simpa using hx)
      exact ⟨y', by simpa using h1, h2⟩

variable {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}

/-- **Claim number a**: its placeholder x0 and table o on the honest side; the relation of x0 to the
verifier's claim; the job's table number a is o's table with "cd" summed out (`closeCd`). -/
theorem opens_at (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {a : ℕ} {x : WsClaim} (hx : cl[a]? = some x) :
    ∃ x0 o, ClaimPair SD.S.ce { SD.S.ce with rs := rs, rt := p.rt } SD.S.lfc x0 x ∧
      openOf SD.S.ce.wsLay w.w (SD.S.ce.v.g * SD.S.ce.v.y.Lam) x0 = some o ∧
      SD.S.ce.wsLay = Q.P.wsLay ∧ SD.S.kkOf a = o.kk ∧
      SD.F.getD a #[] = closeCd SD.S.ce (eqTab p.rt) SD.S.lfc o := by
  obtain ⟨S, hS, hD⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨eS, _, eF, _⟩ := stackDataOn_open hD
  subst eS
  obtain ⟨cl0, AH, h0, hw, ho, e1, e2, e3⟩ := sides_open hS
  have W := claims_walk SD.S.ce rs p.rt SD.S.TS h0 hcl hw
  rcases rel_get W a with ⟨_, k⟩ | ⟨x0, x', k0, k1, P⟩
  · rw [hx] at k
    cases k
  · obtain rfl : x' = x := Option.some.inj (k1.symm.trans hx)
    have ho' : cl0.mapM (openOf Q.P.wsLay w.w (Q.g * Q.P.y.Lam)) = some SD.S.opens.toList := by
      rw [List.mapM_toArray] at ho
      obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp ho
      rw [hr, ← e]
    obtain ⟨o, q1, q2⟩ := mapM_member _ cl0 _ ho' a x0 k0
    have q1' : SD.S.opens[a]? = some o := by rw [← Array.getElem?_toList]; exact q1
    refine ⟨x0, o, P, by rw [e1, e2, e3]; exact q2, e1, ?_, ?_⟩
    · unfold OnBytes.Desc.First.K4.Honest.Sides.kkOf
      rw [Array.getD_eq_getD_getElem?, q1']
      rfl
    · rw [eF, weights_eq, Array.getD_eq_getD_getElem?, Array.getElem?_map, q1']
      rfl

/-- **THE HONEST TABLES ARE THE LIBRARY's VECTORS OF THE WEIGHT CLAIMS.** CONDITIONAL: on every
hypothesis named. cl: the verifier's list of claims, at the challenges rs at which its function
returns and at the end point of the sampled values. hi: a row; yv: a column. -/
theorem opens_are (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) :
    ∀ (a : ℕ) (x : WsClaim) (u : WsUnit), cl[a]? = some x → Q.P.wsLay.U[x.ui]? = some u →
      ∀ hi yv : ℕ, (hasE u.g = true ∧ yv < 2 ^ wkOf u.g) ∨ (hasE u.g = false ∧ hi = 0) →
      Reading.gl.val (at2 (SD.F.getD a #[]) (SD.S.kkOf a) hi yv) =
        wvOf Reading.gl Q.P.wsLay (wmOf w.w) cl a (hi * 2 ^ wkOf u.g + yv) := by
  intro a x u hx hu hi yv hc
  obtain ⟨x0, o, P, ho, e1, ek, eF⟩ := opens_at h hcl hx
  rw [wvOf_at Reading.gl _ _ hx, ek, eF, ← e1]
  exact open_claim (by rw [e1]; exact hl) P ho (by rw [e1]; exact hu) hi yv hc

/-- The two claims of a pair name one unit. -/
theorem pair_ui {c0 : ClaimEnv} {rs rt lfc : Array E} {x0 x : WsClaim}
    (P : ClaimPair c0 { c0 with rs := rs, rt := rt } lfc x0 x) : x0.ui = x.ui := by
  obtain ⟨X, lam, fac0, fac, _, h0, h1, _, _⟩ := P
  obtain ⟨_, a1, _, _⟩ := claim_inv h0
  obtain ⟨_, b1, _, _⟩ := claim_inv h1
  have b1' : c0.wsLay.unitOf X (c0.v.lay lam) = some x.ui := b1
  exact Option.some.inj (a1.symm.trans b1')

/-- **The honest side's number of columns of claim number a** is the extent of the group "kk" of the
claim's unit. -/
theorem opens_kk (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl) :
    ∀ (a : ℕ) (x : WsClaim) (u : WsUnit), cl[a]? = some x → Q.P.wsLay.U[x.ui]? = some u →
      SD.S.kkOf a = ((u.g.find? fun g => g.name == "kk").map (·.R)).getD 0 := by
  intro a x u hx hu
  obtain ⟨x0, o, P, ho, e1, ek, _⟩ := opens_at h hcl hx
  rw [ek]
  exact (openOf_parts (by rw [pair_ui P, e1]; exact hu) ho).2.1

/-- **From the extent of the group "e" on, a row of the honest table is 0.** -/
theorem opens_beyond (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) :
    ∀ (a : ℕ) (x : WsClaim) (u : WsUnit), cl[a]? = some x → Q.P.wsLay.U[x.ui]? = some u →
      hasE u.g = true → ∀ hi yv : ℕ, ((u.g.find? fun g => g.name == "e").map (·.R)).getD 0 ≤ hi →
      at2 (SD.F.getD a #[]) (SD.S.kkOf a) hi yv = zeroE := by
  intro a x u hx hu hE hi yv hh
  obtain ⟨x0, o, P, ho, e1, ek, eF⟩ := opens_at h hcl hx
  have hu0 : SD.S.ce.wsLay.U[x0.ui]? = some u := by rw [pair_ui P, e1]; exact hu
  obtain ⟨X, lam, fac0, fac, hX, h0, _, _, _⟩ := P
  obtain ⟨u0, a1, a2, _⟩ := claim_inv h0
  obtain rfl : u0 = u := Option.some.inj (a2.symm.trans hu0)
  have hgr := groups_found (by rw [e1]; exact hl) a1 a2 hX
  unfold groupsOf at hgr
  by_cases hX0 : X = 0
  · rw [if_pos hX0] at hgr
    obtain ⟨g1, g2, g3, hg, k1, k2, k3⟩ := map_three hgr
    rw [hg, hasE_last (congrArg Prod.fst k1) (congrArg Prod.fst k2) (congrArg Prod.fst k3)] at hE
    cases hE
  · rw [if_neg hX0] at hgr
    by_cases hX7 : X = 7 ∨ X = 8 ∨ X = 10
    · rw [if_pos hX7] at hgr
      obtain ⟨g1, g2, g3, hg, k1, k2, k3⟩ := map_three hgr
      have n1 : g1.name = "kk" := congrArg Prod.fst k1
      have n2 : g2.name = "e" := congrArg Prod.fst k2
      have n3 : g3.name = "x" := congrArg Prod.fst k3
      obtain ⟨ht, hk, hcd⟩ := open_three hg n1 n2 n3 hu0 ho
      have hh' : g2.R ≤ hi := by
        rw [hg] at hh
        simpa [n1, n2] using hh
      rw [ek, eF]
      unfold closeCd at2
      rw [hcd, if_pos (beq_self_eq_true 0), hk]
      by_cases hy : yv < g1.R
      · rw [if_pos hy]
        refine getD_beyond _ ?_
        rw [fbFree_size hu0 ht]
        have es : (stridesOf u0 ["e", "kk"]).2 = g1.R * g2.R := by
          simp [stridesOf, hg, n1, n2]
        rw [es]
        have : g1.R * g2.R ≤ hi * g1.R := by
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_right _ hh'
        omega
      · rw [if_neg hy]
    · rw [if_neg hX7] at hgr
      obtain ⟨g1, g2, hg, k1, k2⟩ := map_two hgr
      rw [hg, hasE_two (congrArg Prod.fst k1) (congrArg Prod.fst k2)] at hE
      cases hE

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sides_open
#print axioms ProofFile.Honest.K4.mapM_member
#print axioms ProofFile.Honest.K4.opens_at
#print axioms ProofFile.Honest.K4.opens_are
#print axioms ProofFile.Honest.K4.pair_ui
#print axioms ProofFile.Honest.K4.opens_kk
#print axioms ProofFile.Honest.K4.opens_beyond
