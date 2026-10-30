-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OpenSides.lean: CONDITIONAL.

What is here. OpenTabs.lean's law at any token point: the tables of the weights that the honest
side's shared data give at the equality table of a point rt (`Sides.weights`,
Johnson/Desc/K4/Honest/Sides.lean) are the library's vectors of the verifier's weight claims made at
that point (`wvOf`, Johnson/Road/FormsKeysWv.lean), claim by claim. OpenTabs.lean has it at the
second token sumcheck's end point, of the batched sumcheck's data; here rt is a letter, so that it
can be a token's corner.

  `weights_at`   claim number a: its placeholder, its table, the relation to the verifier's claim
  `weights_are`   **the tables are the vectors**
  `weights_kk`   the number of columns

Limits. At the reading `Reading.gl`. The matrix is the one that the honest input holds, read word by
word (`wmOf`): nothing ties it to a commitment. Premises: the function that makes the shared data
returns; the verifier's function for the claims, run at the honest side's own environment with
challenges rs and the point rt laid in, returns; the layout of the weights is what the verifier's
`wsLayOf` returns for a model with routed experts. The place in a vector is row times two to the
bits of an index of the claim's group "kk", plus column. In a unit with a group "e" the column lies
below two to these bits; in another the row is 0. Nothing on a slot or a world.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Reading WsUnit WsClaim WsShape wsLayOf eqTab)
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Road (wvOf wvOf_at hasE wkOf rel_get)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}

/-- **Claim number a**: its placeholder x0 and table o on the honest side; the relation of x0 to the
verifier's claim; the table at rt is o's, closed. -/
theorem weights_at (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) {rs rt : Array E}
    {cl : List WsClaim}
    (hcl : ({ S.ce with rs := rs, rt := rt } : ClaimEnv).weightClaims S.TS = some cl)
    {a : ℕ} {x : WsClaim} (hx : cl[a]? = some x) :
    ∃ x0 o, ClaimPair S.ce { S.ce with rs := rs, rt := rt } S.lfc x0 x ∧
      openOf S.ce.wsLay w.w (S.ce.v.g * S.ce.v.y.Lam) x0 = some o ∧
      S.ce.wsLay = Q.P.wsLay ∧ S.kkOf a = o.kk ∧
      (S.weights (eqTab rt)).getD a #[] = closeCd S.ce (eqTab rt) S.lfc o := by
  obtain ⟨cl0, AH, h0, hw, ho, e1, e2, e3⟩ := sides_open hS
  have W := claims_walk S.ce rs rt S.TS h0 hcl hw
  rcases rel_get W a with ⟨_, k⟩ | ⟨x0, x', k0, k1, P⟩
  · rw [hx] at k
    cases k
  · obtain rfl : x' = x := Option.some.inj (k1.symm.trans hx)
    have ho' : cl0.mapM (openOf Q.P.wsLay w.w (Q.g * Q.P.y.Lam)) = some S.opens.toList := by
      rw [List.mapM_toArray] at ho
      obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp ho
      rw [hr, ← e]
    obtain ⟨o, q1, q2⟩ := mapM_member _ cl0 _ ho' a x0 k0
    have q1' : S.opens[a]? = some o := by rw [← Array.getElem?_toList]; exact q1
    refine ⟨x0, o, P, by rw [e1, e2, e3]; exact q2, e1, ?_, ?_⟩
    · unfold OnBytes.Desc.First.K4.Honest.Sides.kkOf
      rw [Array.getD_eq_getD_getElem?, q1']
      rfl
    · rw [weights_eq, Array.getD_eq_getD_getElem?, Array.getElem?_map, q1']
      rfl

/-- **THE HONEST TABLES AT A POINT ARE THE LIBRARY's VECTORS OF THE WEIGHT CLAIMS MADE THERE.**
CONDITIONAL: on every hypothesis named. hi: a row; yv: a column. -/
theorem weights_are (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) {rs rt : Array E}
    {cl : List WsClaim}
    (hcl : ({ S.ce with rs := rs, rt := rt } : ClaimEnv).weightClaims S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) :
    ∀ (a : ℕ) (x : WsClaim) (u : WsUnit), cl[a]? = some x → Q.P.wsLay.U[x.ui]? = some u →
      ∀ hi yv : ℕ, (hasE u.g = true ∧ yv < 2 ^ wkOf u.g) ∨ (hasE u.g = false ∧ hi = 0) →
      Reading.gl.val (at2 ((S.weights (eqTab rt)).getD a #[]) (S.kkOf a) hi yv) =
        wvOf Reading.gl Q.P.wsLay (wmOf w.w) cl a (hi * 2 ^ wkOf u.g + yv) := by
  intro a x u hx hu hi yv hc
  obtain ⟨x0, o, P, ho, e1, ek, eF⟩ := weights_at hS hcl hx
  rw [wvOf_at Reading.gl _ _ hx, ek, eF, ← e1]
  exact open_claim (by rw [e1]; exact hl) P ho (by rw [e1]; exact hu) hi yv hc

/-- **The honest side's number of columns of claim number a** is the extent of the group "kk" of the
claim's unit. -/
theorem weights_kk (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) {rs rt : Array E}
    {cl : List WsClaim}
    (hcl : ({ S.ce with rs := rs, rt := rt } : ClaimEnv).weightClaims S.TS = some cl) :
    ∀ (a : ℕ) (x : WsClaim) (u : WsUnit), cl[a]? = some x → Q.P.wsLay.U[x.ui]? = some u →
      S.kkOf a = ((u.g.find? fun g => g.name == "kk").map (·.R)).getD 0 := by
  intro a x u hx hu
  obtain ⟨x0, o, P, ho, e1, ek, _⟩ := weights_at hS hcl hx
  rw [ek]
  exact (openOf_parts (by rw [pair_ui P, e1]; exact hu) ho).2.1

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.weights_at
#print axioms ProofFile.Honest.K4.weights_are
#print axioms ProofFile.Honest.K4.weights_kk
