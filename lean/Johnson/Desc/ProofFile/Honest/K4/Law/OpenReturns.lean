-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OpenReturns.lean: CONDITIONAL. Statements with their proofs.

What is here: WHEN THE HONEST SIDE's TABLE OF ONE WEIGHT CLAIM IS MADE (`openOf`,
Johnson/Desc/K4/Honest/Sides.lean; `fbFree`, Johnson/Desc/K4/Honest/Units.lean), in the feed-forward
layers' own rounds (the sub-protocol K4). `fbFree_returns`: at a claim that passes the verifier's
own test on a claim's sizes, at a unit with the library's `UnitOK`, and at a list of open names each
of which is a group's and none of which stands twice. `openOf_returns`: so `openOf`, where besides
every group of the unit bears one of its five names. `opens_return`: AT EVERY MEMBER OF THE
VERIFIER's LIST OF THE PANELS' WEIGHT CLAIMS, where the layout is what the verifier's `wsLayOf`
returns for a model with routed experts, the heads' weights return, and each member passes that
test. That is the hypothesis h6 of `sides_of_plan` (Johnson/Road/K4/C/SidesOf.lean), but for the
test on the sizes.
How. Of `fbFree`'s six tests two are the verifier's test's own; two hold by the way the list of open
names is made; the two on the rows' weights and numbers are sizes of outer products
(`rwOf_size`, `rnOf_size`, Law/UnitsRows.lean) against `UnitOK.rows`. Each member of the list is a
claim on the unit of a kind up to 11 (`claims_walk`, Law/OpenWalk.lean), whose groups' names the
library has (`claim_inv`, `groups_found`, `unit_found`, Johnson/Road/).

Not shown here. That the list is made, that the heads' weights return, that a member passes the test
on its sizes: hypotheses. A RETURN ALONE: nothing on what an entry of the table is worth (that:
Law/UnitsSel.lean, Law/OpenClaim.lean). Nothing on soundness, on completeness or on any other
property. No property is claimed.

  `shape_parts`   what the verifier's test's accept says
  `fbFree_returns`, `openOf_returns`   one claim
  `names_five`   the names of the groups of a kind up to 11 are among the five
  `opens_return`   **every member of the list**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenShapes
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE oneE)
open OnBytes.Model (WsLay WsUnit WsGrp WsFac WsClaim WsShape wsClaimShape wsLayOf wsDigits)
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Road (GrpOK UnitOK groupsOf claim_inv groups_found unit_found)
open OnBytes.Desc.First.K4.Honest

variable {lay : WsLay} {w : ℕ → ℕ → F} {g0 : ℕ} {c : WsClaim} {u : WsUnit}

/-- What the accept of the verifier's test on a claim's sizes says. -/
theorem shape_parts (hu : lay.U[c.ui]? = some u) (hs : (wsClaimShape lay c).isOk = true) :
    c.f.length = u.g.length ∧ ∀ y ∈ c.f.zip u.g, y.1.fits y.2 = true := by
  unfold wsClaimShape at hs
  rw [hu] at hs
  dsimp only at hs
  split at hs
  · rename_i hc
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
    exact hc
  · cases hs

/-- CONDITIONAL on every hypothesis named. **`fbFree` RETURNS.** -/
theorem fbFree_returns {free : List String} (hu : lay.U[c.ui]? = some u)
    (hs : (wsClaimShape lay c).isOk = true) (U : UnitOK lay.lk u)
    (hfree : free.all (fun n => u.g.any fun g => g.name == n) = true)
    (hnd : free.eraseDups.length = free.length) : (fbFree lay w c free).isSome = true := by
  obtain ⟨hlen, hfit⟩ := shape_parts hu hs
  have hok : RowsOK (stridesOf u free).1 (c.f.zip u.g) := fun y hy =>
    ⟨U.grp y.2 (List.of_mem_zip hy).2, fun _ => hfit y hy⟩
  have hleft : ((c.f.zip u.g).map (·.2.left)) = u.g.map (·.left) := map_snd_zip' hlen (·.left)
  have h4 : (rowWeights u (c.f.zip u.g) (stridesOf u free).1).size = u.rows := by
    rw [rowWeights_eq, rwOf_size _ hok, hleft, List.size_toArray, OnBytes.Road.wsDigits_length,
      ← U.rows]
  have h5 : (rowNumbers u (c.f.zip u.g) (stridesOf u free).1).size = u.rows := by
    rw [rowNumbers_eq', rnOf_size, hleft, Array.size_replicate, ← U.rows]
  have h6 : ((c.f.zip u.g).all fun y =>
      (strideOf (stridesOf u free).1 y.2).isSome || y.1.fits y.2) = true :=
    List.all_eq_true.2 fun y hy => by rw [hfit y hy, Bool.or_true]
  unfold fbFree
  rw [hu]
  dsimp only
  rw [if_neg (by simp [hlen, hfree, hnd, h4, h5, h6])]
  rfl

/-- CONDITIONAL on every hypothesis named. **`openOf` RETURNS.** -/
theorem openOf_returns (hu : lay.U[c.ui]? = some u) (hs : (wsClaimShape lay c).isOk = true)
    (U : UnitOK lay.lk u)
    (hn : u.g.all (fun G => ["hd", "x", "cd", "e", "kk"].contains G.name) = true) :
    (openOf lay w g0 c).isSome = true := by
  have hfree : (["cd", "e", "kk"].filter fun n => u.g.any fun G => G.name == n).all
      (fun n => u.g.any fun g => g.name == n) = true :=
    List.all_eq_true.2 fun n h => (List.mem_filter.1 h).2
  have hnd : (["cd", "e", "kk"].filter fun n => u.g.any fun G => G.name == n).eraseDups.length =
      (["cd", "e", "kk"].filter fun n => u.g.any fun G => G.name == n).length := by
    cases h1 : (u.g.any fun G => G.name == "cd") <;> cases h2 : (u.g.any fun G => G.name == "e") <;>
      cases h3 : (u.g.any fun G => G.name == "kk") <;> simp [List.filter, h1, h2, h3] <;> decide
  obtain ⟨tab, ht⟩ := Option.isSome_iff_exists.mp (fbFree_returns (w := w) hu hs U hfree hnd)
  unfold openOf
  rw [hu]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, hn, Bool.not_true,
    Bool.false_eq_true, if_false, ht]
  rfl

/-- The names of the groups of a unit of a kind up to 11 are among the five. -/
theorem names_five (X : ℕ) :
    (groupsOf X).all (fun y => ["hd", "x", "cd", "e", "kk"].contains y.1) = true := by
  unfold groupsOf
  split
  · decide
  · split <;> decide

/-- CONDITIONAL on every hypothesis named. **`openOf` RETURNS AT EVERY MEMBER OF THE LIST OF THE
PANELS' WEIGHT CLAIMS.** -/
theorem opens_return {c0 : ClaimEnv} {s : WsShape} {lk : ℕ} {TS : List ℕ} {cls : List WsClaim}
    {AH lfc : Array E} (hws : wsLayOf s true lk = .ok c0.wsLay)
    (hc : c0.weightClaims TS = some cls) (hw : c0.headWeights = some (AH, lfc))
    (hs : ∀ x ∈ cls, (wsClaimShape c0.wsLay x).isOk = true) :
    ∀ x ∈ cls, (openOf c0.wsLay w g0 x).isSome = true := by
  intro x hx
  have W := claims_walk c0 c0.rs c0.rt TS hc hc hw
  have hex : ∀ (l l' : List WsClaim),
      List.Forall₂ (ClaimPair c0 { c0 with rs := c0.rs, rt := c0.rt } lfc) l l' → ∀ a ∈ l,
      ∃ b, ClaimPair c0 { c0 with rs := c0.rs, rt := c0.rt } lfc a b := by
    intro l l' h
    induction h with
    | nil => intro a ha; cases ha
    | cons hab _ ih =>
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact ⟨_, hab⟩
      · exact ih a ha'
  obtain ⟨_, X, lam, fac0, _, hX, h0, _⟩ := hex _ _ W x hx
  obtain ⟨u, h1, h2, _⟩ := claim_inv h0
  have hlk : c0.wsLay.lk = lk := (OnBytes.Road.unitOK_of_layout hws).1
  have U : UnitOK c0.wsLay.lk u := by
    rw [hlk]
    exact (unit_found hws h1 h2).1
  have hg := groups_found hws h1 h2 hX
  have hn : u.g.all (fun G => ["hd", "x", "cd", "e", "kk"].contains G.name) = true := by
    have h5 := names_five X
    rw [← hg, List.all_map] at h5
    exact h5
  exact openOf_returns h2 (hs x hx) U hn

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.shape_parts
#print axioms ProofFile.Honest.K4.fbFree_returns
#print axioms ProofFile.Honest.K4.openOf_returns
#print axioms ProofFile.Honest.K4.names_five
#print axioms ProofFile.Honest.K4.opens_return
