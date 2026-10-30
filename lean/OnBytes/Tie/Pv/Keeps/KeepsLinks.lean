-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsLinks.lean: from the routines of the sub-proofs
(OnBytes/Tie/Pv/Keeps/KeepsModel.lean) to the block that walks all links of a request's chain, and
to the first chain's whole block.
 1. runLinkH, runLinksFrom, runLinksH, if each link's routine keeps. A link's routine is a field of
    the record LinkH, so this is a hypothesis on the record.
 2. The three plans' routines keep (layers, attention, the head).
 3. Every link of the list that Verify.linksOf makes has one of these three routines; so has every
    link of the list that the stage request runs (the built links, each with the routine of
    linksOf).
 4. So the block of that stage keeps, with no hypothesis but that linksOf has returned the list.
-/
import OnBytes.Tie.Pv.Keeps.KeepsModel
import OnBytes.Model.VerifyStages

namespace OnBytes.L5

open OnBytes OnBytes.Model OnBytes.Model.Stages

/-! ## The walk over the links, if each link's routine keeps -/

instance keepsM_runLinkH (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (l : Nat)
    (X : LinkH) (check : ChainCheck) (out : Proof.LinksResult) [KeepsM X.run] :
    KeepsM (runLinkH links p wsLay l X check out) := by
  unfold runLinkH; keepsM

theorem keepsM_runLinksFrom (links : Array LinkH) (p : Params.First) (wsLay : WsLay) :
    ∀ (rest : List LinkH), (∀ X ∈ rest, KeepsM X.run) → ∀ (l : Nat) (check : ChainCheck)
      (out : Proof.LinksResult), KeepsM (runLinksFrom links p wsLay rest l check out)
  | [], _, l, check, out => by unfold runLinksFrom; keepsM
  | X :: rest, h, l, check, out => by
    haveI := h X List.mem_cons_self
    haveI := keepsM_runLinksFrom links p wsLay rest fun Y hY => h Y (List.mem_cons_of_mem _ hY)
    unfold runLinksFrom; keepsM

/-- Every link's routine keeps. -/
def AllKeep (ls : Array LinkH) : Prop := ∀ l ∈ ls, KeepsM l.run

theorem keepsM_runLinksH (links : Array LinkH) (p : Params.First) (wsLay : WsLay)
    (h : AllKeep links) : KeepsM (runLinksH links p wsLay) := by
  haveI := keepsM_runLinksFrom links p wsLay links.toList fun X hX => h X (Array.mem_toList_iff.1 hX)
  unfold runLinksH; keepsM

/-! ## The three plans' routines -/

instance keepsM_layersPlan (X : Verify.Public) (tokv : Array Nat) (g : Nat) (hp : Layer.HPlan2) :
    KeepsM (Verify.layersPlanOf X tokv g hp).run := by
  unfold Verify.layersPlanOf; keepsM

instance keepsM_attentionPlan (A : Attention.Plan) : KeepsM (Verify.attentionPlanOf A).run := by
  unfold Verify.attentionPlanOf; keepsM

instance keepsM_headPlan (X : Verify.Public) (cov : Head.Covered) :
    KeepsM (Verify.headPlanOf X cov).run := by
  unfold Verify.headPlanOf; keepsM

/-! ## The list of links -/

/-- What a step of a loop hands on. -/
def stepVal {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

/-- A property that every step of a loop keeps holds at the loop's end. For a loop that may
refuse. -/
theorem forIn_inv {ε α β : Type} (P : β → Prop) (f : α → β → Except ε (ForInStep β)) :
    ∀ (l : List α) (init r : β), P init →
      (∀ a ∈ l, ∀ b s, P b → f a b = .ok s → P (stepVal s)) → forIn l init f = .ok r → P r
  | [], init, r, h0, _, h => by
    rw [List.forIn_nil] at h
    cases h
    exact h0
  | a :: l, init, r, h0, hf, h => by
    rw [List.forIn_cons] at h
    cases e : f a init with
    | error x => rw [e] at h; cases h
    | ok s =>
      rw [e] at h
      have hs := hf a List.mem_cons_self init s h0 e
      cases s with
      | done b => cases h; exact hs
      | yield b =>
        exact forIn_inv P f l b r hs (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) h

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mem_zipIdx_fst {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat),
    x ∈ l.zipIdx k → x.1 ∈ l
  | [], _, _, h => by cases h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zipIdx_fst l (k + 1) x h)

theorem AllKeep.push {ls : Array LinkH} (h : AllKeep ls) {l : LinkH} (hl : KeepsM l.run) :
    AllKeep (ls.push l) := by
  intro x hx
  rcases Array.mem_push.1 hx with h1 | rfl
  · exact h x h1
  · exact hl

theorem keepsM_link (s : SubPlanH) (name : String) (gid kind g : Nat) (fv : Bool)
    (h : KeepsM s.run) : KeepsM (s.link name gid kind g fv).run := h

/-- listLinksH takes every link's routine from one of the plans that it is given. -/
theorem listLinksH_keep {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {ls : Array LinkH} (hG : ∀ s ∈ G, KeepsM s.run) (hA : ∀ a ∈ A, KeepsM a.run)
    (hH : KeepsM H.run) (h : listLinksH NGr p4 G A H = .ok ls) : AllKeep ls := by
  unfold listLinksH at h
  by_cases hc : (G.size != NGr || (p4 && A.size != NGr)) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨r, hr, h⟩ := bind_ok h
    cases h
    refine AllKeep.push ?_ (keepsM_link _ _ _ _ _ _ hH)
    refine forIn_inv AllKeep _ _ _ _ (fun _ hx => absurd hx (Array.not_mem_empty _)) ?_ hr
    rintro ⟨s0, g⟩ hx b s hb hs
    have hs0 : KeepsM s0.run := hG s0 (Array.mem_toList_iff.1 (mem_zipIdx_fst _ _ _ hx))
    dsimp only at hs
    split at hs
    · split at hs
      · rename_i a ha
        cases hs
        exact (hb.push (keepsM_link _ _ _ _ _ _ hs0)).push
          (keepsM_link _ _ _ _ _ _ (hA a (Array.mem_of_getElem? ha)))
      · cases hs
        exact hb.push (keepsM_link _ _ _ _ _ _ hs0)
    · cases hs
      exact hb.push (keepsM_link _ _ _ _ _ _ hs0)

/-- **Every link of the list that linksOf makes has a routine that keeps.** -/
theorem linksOf_keep {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (h : Verify.linksOf X cov = .ok ls) : AllKeep ls := by
  unfold Verify.linksOf at h
  refine listLinksH_keep ?_ ?_ inferInstance h
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hs
    rw [Array.getElem_mapIdx]
    infer_instance
  · intro a ha
    obtain ⟨A, -, rfl⟩ := Array.mem_map.1 ha
    infer_instance

/-- The list that the stage request runs: the built links, each with the routine of linksOf. -/
theorem zipped_keep {ls : Array LinkH} (h : AllKeep ls) (built : Array LinkH) :
    AllKeep (built.zipWith (fun b l => { b with run := l.run }) ls) := by
  intro Z hZ
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hZ
  have hi' : i < ls.size := by
    rw [Array.size_zipWith] at hi
    omega
  rw [Array.getElem_zipWith]
  exact h (ls[i]'hi') (Array.getElem_mem hi')

/-- **The block that walks all links of a request's chain keeps**: the flag dry stays, and a mark
stays a mark. No hypothesis but that linksOf has returned the list. -/
theorem keeps_links {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (h : Verify.linksOf X cov = .ok ls) (built : Array LinkH) (p : Params.First) (wsLay : WsLay) :
    Keeps (runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) p wsLay) :=
  @KeepsM.keeps _ _ (keepsM_runLinksH _ p wsLay (zipped_keep (linksOf_keep h) built))

#print axioms keepsM_runLinkH
#print axioms keepsM_runLinksFrom
#print axioms keepsM_runLinksH
#print axioms keepsM_layersPlan
#print axioms keepsM_attentionPlan
#print axioms keepsM_headPlan
#print axioms listLinksH_keep
#print axioms linksOf_keep
#print axioms zipped_keep
#print axioms keeps_links

end OnBytes.L5
