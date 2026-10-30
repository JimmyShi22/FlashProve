-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameFold.lean:
FACTS ALONG THE FOLD, AT THE PROOF FILE's OWN FIRST CHAIN, IN THE GOALS' SCOPE: WHAT
THE VERIFIER's STATE HOLDS BEHIND A LINK's FIRST SUB-PROTOCOL, with the frame's "opened" joined
behind it.

  fold_last         a fold's yes over the first k + 1 sub-protocols ends in an accepting step of
                    number k
  opened_at_fold    behind number 14 l + 2 the state is what the row's own "opened" has handed out
  att_tl_at_fold    AT AN ATTENTION LINK: the carried state of the approximate range proof (tl?) is
                    the planned attention entry's seam's, with two marks of the order of steps laid
                    back
  lay_tl_at_fold    at a layers' link: it is the planned layers' entry's

Limits. Which planned entry: the one at X.g, X the link's own element of the planner's list of
links: that X.g is (l - 1) / 2 or l / 2 is not said here. The first state is a letter. No soundness
statement.

-/
import Johnson.P1L20R.FrameSits
import Johnson.IMR.FrameYes
import Johnson.Top.H0.Walk.Reach
import Johnson.Top.H0.Walk.FrameSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn foldBlocks foldBlocks_cons)
open VerifiableInference.Desc.First (S ModelPart)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- A fold's yes over the first k + 1 sub-protocols ends in an accepting step of number k. -/
theorem fold_last {ft k : ℕ} {bs : List (Block S Cl)} {b : Block S Cl} (hb : bs[k]? = some b)
    {s₀ : S} {R : List Fmt.RoundView} {C : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (bs.take (k + 1)) s₀ R C = .ok out) :
    ∃ t rs cols n, b.step ft t rs cols = .ok (out.1, n) := by
  rw [List.take_add_one, hb] at h
  obtain ⟨t, r, c, _, h2⟩ := fold_split ft _ _ _ _ _ _ h
  obtain ⟨s', n, _, hs, h3⟩ := foldBlocks_cons ft b [] t r c _ h2
  unfold foldBlocks at h3
  injection h3 with h3
  rw [← h3]
  exact ⟨t, _, _, n, hs⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Behind a link's first sub-protocol the state is what the row's own "opened" has handed out.**
-/
theorem opened_at_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {ft : ℕ}
    {s₀ : S} {R : List Fmt.RoundView} {C : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take (14 * l + 3)) s₀ R C = .ok out) :
    ∃ fs f m, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ m.failed = none ∧ f.opened m = .ok out.1 ∧ out.1.failed = none := by
  obtain ⟨_, _, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨_, _, _, _, b, b', _, _, _, _, _, _, _, ib, _, _, _, hj, _⟩ := hh l hl
  obtain ⟨t, rs, cols, n, hs⟩ := fold_last (k := 14 * l + 2) ib h
  obtain ⟨fs, f, m, h1, h2, _, h4, h5, h6, _⟩ := hj.step hs
  exact ⟨fs, f, m, h1, h2, h4, h5, h6⟩

/-- The kind in the link's planned entry, by the link's sort. -/
theorem kind_of_sort (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {X : OnBytes.Model.Stages.LinkH} (hX : Z.p.built.links[l]? = some X) :
    ProofFile.subOf X.kind = IM.subAt l := by
  have h2 := IM.subs_scope hS hR O l hl
  unfold ProofFile.subsOf at h2
  rw [List.getElem?_map, Array.getElem?_toList, hX] at h2
  exact Option.some.inj h2

/-- **At an attention link.** -/
theorem att_tl_at_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (ha : IM.subAt l = ModelPart.attention) {ft : ℕ} {s₀ : S} {R : List Fmt.RoundView} {C : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take (14 * l + 3)) s₀ R C = .ok out) :
    ∃ X p, Z.p.built.links[l]? = some X ∧ X.kind = 1 ∧ Z.p.X.A[X.g]? = some p ∧
      out.1.tl? = some { p.seam.tl with funClosed := false, foldDrawn := 0 } := by
  obtain ⟨fs, f, m, hfs, hf, _, ho, _⟩ := opened_at_fold hS hR O hl h
  rcases Johnson.Desc.First.Walk.Seat.framesOf_arms hfs hf with
    ⟨X, hX, hk, _⟩ | ⟨_, X, _, _, hX, hk, _⟩ | ⟨_, X, p, Q, hX, hk, hp, eQ, _, e1, _⟩ |
    ⟨_, X, _, _, hX, hk, _⟩
  · have e := kind_of_sort hS hR O hl hX
    rw [hk, ha] at e
    exact absurd e (by decide)
  · subst_vars
    have e := kind_of_sort hS hR O hl hX
    rw [hk, ha] at e
    exact absurd e (by decide)
  · subst eQ
    rw [e1] at ho
    exact ⟨X, p, hX, hk, hp, Johnson.Desc.First.Walk.Law.openAtt_tl ho⟩
  · have e := kind_of_sort hS hR O hl hX
    rw [hk, ha] at e
    exact absurd e (by decide)

/-- **At a layers' link.** -/
theorem lay_tl_at_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (ha : IM.subAt l = ModelPart.layers) {ft : ℕ} {s₀ : S} {R : List Fmt.RoundView} {C : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take (14 * l + 3)) s₀ R C = .ok out) :
    ∃ X hp, Z.p.built.links[l]? = some X ∧ X.kind = 0 ∧ Z.p.X.G[X.g]? = some hp ∧
      out.1.tl? = some hp.tl := by
  obtain ⟨fs, f, m, hfs, hf, _, ho, _⟩ := opened_at_fold hS hR O hl h
  rcases Johnson.Desc.First.Walk.Seat.framesOf_arms hfs hf with
    ⟨X, hX, hk, _⟩ | ⟨h0, X, hp, Q, hX, hk, hg, eQ, _, e1, _⟩ | ⟨_, X, _, _, hX, hk, _⟩ |
    ⟨_, X, hp, Q, hX, hk, hg, eQ, _, e1, _⟩
  · have e := kind_of_sort hS hR O hl hX
    rw [hk, ha] at e
    exact absurd e (by decide)
  · subst h0
    subst eQ
    rw [e1] at ho
    exact ⟨X, hp, hX, hk, hg, Johnson.Desc.First.Walk.Law.openLayZero_tl ho⟩
  · have e := kind_of_sort hS hR O hl hX
    rw [hk, ha] at e
    exact absurd e (by decide)
  · subst eQ
    rw [e1] at ho
    exact ⟨X, hp, hX, hk, hg, Johnson.Desc.First.Walk.Law.openLay_tl ho⟩

end

end P1L20

#print axioms P1L20.opened_at_fold
#print axioms P1L20.att_tl_at_fold
#print axioms P1L20.lay_tl_at_fold
