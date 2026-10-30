-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/KeepsTailsLinks.lean: behind the routine of every link of the list that the
verifier makes, on a view, no message is open; so none is open at the link's end.

Statements and proofs, from OnBytes/Tie/Pv/Keeps/KeepsTails.lean, along the lines of
OnBytes/Tie/Pv/Keeps/KeepsLinks.lean, which shows of the same lists that every link's routine keeps.
Main names:
  `layersPlan_ends`, `attentionPlan_ends`, `headPlan_ends`: the three plans' routines are
    `EndsClean`.
  `AllEnd ls`: every link's routine is.
  `linksOf_ends`: so for the list that Verify.linksOf makes. `zipped_ends`: and for the list that
    the stage request runs (the built links, each with the routine of linksOf).
  `linkStep_clean`: in one call of runLinkH whose link's routine is `EndsClean`: no message is open
    behind the routine, nor at the end of the call.
Limits: one direction: from a success. Nothing on the context behind a link's first call.
-/
import OnBytes.Tie.Pv.Keeps.KeepsTails

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Cut

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5

theorem layersPlan_ends (X : Verify.Public) (tokv : Array Nat) (g : Nat) (hp : Layer.HPlan2) :
    EndsClean (Verify.layersPlanOf X tokv g hp).run :=
  EndsClean.map some (layer_ends _ hp g)

theorem attentionPlan_ends (A : Attention.Plan) : EndsClean (Verify.attentionPlanOf A).run :=
  (attention_ends A).andThen fun _ => LeavesCh.pure _

theorem headPlan_ends (X : Verify.Public) (cov : Head.Covered) :
    EndsClean (Verify.headPlanOf X cov).run :=
  EndsClean.map some (head_ends _ _ _ _ _ _ _)

/-- Every link's routine leaves no message open. -/
def AllEnd (ls : Array LinkH) : Prop := ∀ l ∈ ls, EndsClean l.run

theorem AllEnd.push {ls : Array LinkH} (h : AllEnd ls) {l : LinkH} (hl : EndsClean l.run) :
    AllEnd (ls.push l) := by
  intro x hx
  rcases Array.mem_push.1 hx with h1 | rfl
  · exact h x h1
  · exact hl

theorem ends_link (s : SubPlanH) (name : String) (gid kind g : Nat) (fv : Bool)
    (h : EndsClean s.run) : EndsClean (s.link name gid kind g fv).run := h

/-- listLinksH takes every link's routine from one of the plans that it is given. -/
theorem listLinksH_ends {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {ls : Array LinkH} (hG : ∀ s ∈ G, EndsClean s.run) (hA : ∀ a ∈ A, EndsClean a.run)
    (hH : EndsClean H.run) (h : listLinksH NGr p4 G A H = .ok ls) : AllEnd ls := by
  unfold listLinksH at h
  by_cases hc : (G.size != NGr || (p4 && A.size != NGr)) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    obtain ⟨_, -, h⟩ := L5.bind_ok h
    obtain ⟨r, hr, h⟩ := L5.bind_ok h
    cases h
    refine AllEnd.push ?_ (ends_link _ _ _ _ _ _ hH)
    refine L5.forIn_inv AllEnd _ _ _ _ (fun _ hx => absurd hx (Array.not_mem_empty _)) ?_ hr
    rintro ⟨s0, g⟩ hx b s hb hs
    have hs0 : EndsClean s0.run := hG s0 (Array.mem_toList_iff.1 (mem_zipIdx_fst _ _ _ hx))
    dsimp only at hs
    split at hs
    · split at hs
      · rename_i a ha
        cases hs
        exact (hb.push (ends_link _ _ _ _ _ _ hs0)).push
          (ends_link _ _ _ _ _ _ (hA a (Array.mem_of_getElem? ha)))
      · cases hs
        exact hb.push (ends_link _ _ _ _ _ _ hs0)
    · cases hs
      exact hb.push (ends_link _ _ _ _ _ _ hs0)

/-- Every link of the list that linksOf makes. -/
theorem linksOf_ends {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (h : Verify.linksOf X cov = .ok ls) : AllEnd ls := by
  unfold Verify.linksOf at h
  refine listLinksH_ends ?_ ?_ (headPlan_ends X cov) h
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hs
    rw [Array.getElem_mapIdx]
    exact layersPlan_ends _ _ _ _
  · intro a ha
    obtain ⟨A, -, rfl⟩ := Array.mem_map.1 ha
    exact attentionPlan_ends A

/-- The list that the stage request runs. -/
theorem zipped_ends {ls : Array LinkH} (h : AllEnd ls) (built : Array LinkH) :
    AllEnd (built.zipWith (fun b l => { b with run := l.run }) ls) := by
  intro Z hZ
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hZ
  have hi' : i < ls.size := by
    rw [Array.size_zipWith] at hi
    omega
  rw [Array.getElem_zipWith]
  exact h (ls[i]'hi') (Array.getElem_mem hi')

/-- One call of runLinkH: behind the link's routine, and at the call's end, no message is open. -/
theorem linkStep_clean {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx}
    {l : Nat} {X : LinkH} (hX : EndsClean X.run) {check : ChainCheck} {out : Proof.LinksResult}
    {c : Ctx} {r : ChainCheck × Proof.LinksResult} {c' : Ctx} {chk : ChainCheck}
    {o : Option WsForkOut} {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2) :
    PscRun.Clean c2 ∧ PscRun.Clean c' := by
  have k2 : PscRun.Clean c2 :=
    ⟨S.v2, hX ({ check := chk, link := l, arrayOf := X.arrayOf, list := X.Tp }, X.Fp, c1) o
      (C', F', c2) S.run S.v1⟩
  exact ⟨k2, Open.LinkStepClean S k2⟩

end OnBytes.Tie.Pv.Keeps.Cut

#print axioms OnBytes.Tie.Pv.Keeps.Cut.linksOf_ends
#print axioms OnBytes.Tie.Pv.Keeps.Cut.zipped_ends
#print axioms OnBytes.Tie.Pv.Keeps.Cut.linkStep_clean
