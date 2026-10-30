-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CoveredJoin.lean: three small laws on how the verifier program reads a request, for the
statement that the rounds of a proof file's first chain do not hang on the request
(`PlannedFirstFree`, OnBytes/Flat/LinksDry.lean).



That statement speaks of any two requests that `Head.coveredOf` takes and at which
`Verify.linksOf` returns (OnBytes/Model/HeadLayout.lean, VerifyLinks.lean). To apply it at two
instances one has to know that the two functions return there, and that what they return has the
sizes that the layers' sub-proofs read.

Main theorems:
  `coveredOf_ok`     `Head.coveredOf` returns where the request has T + 2 words, the reply and all
                    tokens are below V, and r < e ≤ T.
  `coveredOf_lawful`, `coveredOf_lawful_at`   what it returns has T tokens, each below V; at the
                    public part X of a plan: `X.layers.y.T` tokens, each below `X.layers.V`.
  `publicOf_V`       `X.layers.V = X.P.h.V` at what `Verify.publicOf` returns.
  `listLinksH_returns`   the loop that lists the links returns where the program's first test on the
                    plans passes.
  `linksOf_alike`    if `Verify.linksOf X` returns at one request's covered positions, it returns
                    at every other's.
That `Head.stFromCall` takes the words of an instance: `stFromCall_wordsOf`
(Johnson/Flat/InstanceLaws.lean). The converse of `listLinksH_returns`: `listLinksH_sizes`
(OnBytes/TieK/LinksAll.lean).

Limits: nothing on a dry run and nothing on `PlannedFirstFree` itself. For proofs only; no module of
the program imports this file.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.Model.VerifyDerives
import OnBytes.TieK.LinksAll

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Params

/-! ## The request is read -/

theorem needed_ok {b : Bool} {n : String} (h : b = true) : Head.needed b n = .ok () := by
  unfold Head.needed
  rw [if_pos h]

theorem needed_inv {b : Bool} {n : String} {u : Unit} (h : Head.needed b n = .ok u) : b = true := by
  unfold Head.needed at h
  split at h
  · assumption
  · cases h

/-- **`Head.coveredOf` returns** where the reply and all tokens are below V and r < e ≤ T. -/
theorem coveredOf_ok (so : Head.StOwn) (T V : Nat) (hy : so.y < V) (hs : so.req.size = T + 2)
    (ht : ∀ v ∈ (so.req.extract 0 T).map (·.toNat), v < V)
    (h1 : (so.req.getD T 0).toNat < (so.req.getD (T + 1) 0).toNat)
    (h2 : (so.req.getD (T + 1) 0).toNat ≤ T) : ∃ cov, Head.coveredOf so T V = .ok cov := by
  unfold Head.coveredOf
  rw [needed_ok (by simpa using hy), needed_ok (by simpa using hs)]
  show ∃ cov, (Head.needed _ _ >>= fun _ => _) = _
  rw [needed_ok (Array.all_eq_true_iff_forall_mem.2 fun v hv => decide_eq_true (ht v hv))]
  show ∃ cov, (Head.needed _ _ >>= fun _ => _) = _
  rw [needed_ok (by
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, ge_iff_le,
      gt_iff_lt, Nat.not_le, Nat.not_lt]
    exact ⟨h1, h2⟩)]
  exact ⟨_, rfl⟩

/-- **What `Head.coveredOf` returns is lawful**: T tokens, each below V. -/
theorem coveredOf_lawful {so : Head.StOwn} {T V : Nat} {cov : Head.Covered}
    (h : Head.coveredOf so T V = .ok cov) : cov.tokv.size = T ∧ ∀ v ∈ cov.tokv, v < V := by
  unfold Head.coveredOf at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, hs, h⟩ := exc_bind h
  obtain ⟨_, ht, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  have hs' : so.req.size = T + 2 := by simpa using needed_inv hs
  refine ⟨by simp [hs'], ?_⟩
  exact fun v hv => of_decide_eq_true (Array.all_eq_true_iff_forall_mem.1 (needed_inv ht) v hv)

/-! ## The links are listed at every request, or at none -/

/-- A loop whose body never refuses does not refuse. -/
theorem forIn_returns {α β ε : Type} (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b, ∃ s, f a b = .ok s) : ∀ (l : List α) (b : β), ∃ r, forIn l b f = .ok r
  | [], b => ⟨b, rfl⟩
  | a :: l, b => by
    obtain ⟨s, hs⟩ := hf a b
    rw [List.forIn_cons, hs]
    cases s with
    | done b' => exact ⟨b', rfl⟩
    | yield b' => exact forIn_returns f hf l b'

/-- **The loop returns** where the program's first test on the plans passes. -/
theorem listLinksH_returns {NGr : Nat} {p4 : Bool} {G A : Array Stages.SubPlanH}
    (H : Stages.SubPlanH) (hG : G.size = NGr) (hA : p4 = true → A.size = NGr) :
    ∃ ls, Stages.listLinksH NGr p4 G A H = .ok ls := by
  have hc : (G.size != NGr || (p4 && A.size != NGr)) = false := by
    cases p4 with
    | false => simp [hG]
    | true => simp [hG, hA rfl]
  have key : ∀ f : Stages.SubPlanH × Nat → Array Stages.LinkH →
      Except String (ForInStep (Array Stages.LinkH)), (∀ a b, ∃ s, f a b = .ok s) →
      ∃ ls, (do
        pure PUnit.unit
        let r ← forIn G.toList.zipIdx #[] f
        pure (r.push (H.link "H" (1 + NGr) 2 0 true))) = Except.ok ls := by
    intro f hf
    obtain ⟨r, hr⟩ := forIn_returns f hf G.toList.zipIdx #[]
    exact ⟨r.push (H.link "H" (1 + NGr) 2 0 true), by
      show (forIn G.toList.zipIdx #[] f >>= fun r => _) = _
      rw [hr]
      rfl⟩
  unfold Stages.listLinksH
  simp only [hc, Bool.false_eq_true, if_false]
  apply key
  intro x r
  split
  · split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **`Verify.linksOf` returns at every request, or at none.** -/
theorem linksOf_alike (X : Verify.Public) (cov cov' : Head.Covered) {ls : Array Stages.LinkH}
    (h : Verify.linksOf X cov = .ok ls) : ∃ ls', Verify.linksOf X cov' = .ok ls' := by
  obtain ⟨hG, hA⟩ := TieK.linksOf_sizes h
  unfold Verify.linksOf
  exact listLinksH_returns _ (by rw [Array.size_mapIdx]; exact hG)
    (fun h4 => by rw [Array.size_map]; exact hA h4)

/-! ## At the public part of a plan -/

theorem pubOf_V {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : L.V = V ∧ L.y = y := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  exact ⟨rfl, rfl⟩

/-- The number of entries of the vocabulary in what the layers' sub-proofs read is the parameter
file's. -/
theorem publicOf_V {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : X.layers.V = X.P.h.V := by
  unfold Verify.publicOf at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals first
    | (cases h; exact (pubOf_V (by assumption)).1)
    | cases h

/-- **What `Head.coveredOf` returns at a plan's numbers is lawful at the letters that the layers'
sub-proofs read**: as many tokens as the layout has positions, each below the vocabulary's size. -/
theorem coveredOf_lawful_at {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (hX : Verify.publicOf pol KL layout = .ok X) {so : Head.StOwn} {cov : Head.Covered}
    (h : Head.coveredOf so X.T X.P.h.V = .ok cov) :
    cov.tokv.size = X.layers.y.T ∧ ∀ v ∈ cov.tokv, v < X.layers.V := by
  rw [publicOf_V hX]
  exact coveredOf_lawful h

end OnBytes.Flat
