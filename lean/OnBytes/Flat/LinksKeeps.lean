-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksKeeps.lean: the block of the links of a proof's first chain leaves the two flags
of a run as they are.

The block is `Stages.runLinksH links p wsLay` (OnBytes/Model/StagesLinks.lean). The program passes
it the links as built, each with the check that knows the request:
`built.zipWith (fun b l => { b with run := l.run }) links`, where `Verify.linksOf X cov` has
returned `links` (OnBytes/Model/VerifyStages.lean, OnBytes/Model/VerifyLinks.lean). A run has two
flags: whether it is dry, and whether intermediate values are kept. `Blk.Keeps b`
(OnBytes/Iop/DrySizes.lean) says that b leaves both as they are.

 1. `keeps_runLinkH`, `keeps_runLinksFrom`, `keeps_runLinksH`: the block keeps the flags if every
    link's check does.
 2. `layers_run`, `attention_run`, `head_run`: the checks that the three kinds of plan give to their
    links do, at every request. `linksOf_runs`: so every link of `Verify.linksOf` does.
 3. `links_keep`: the program's block keeps the flags, at all public values, all requests and all
    links as built.

Main theorem: `links_keep`.

Not claimed: anything on what the block decides, or on what its dry run returns. For proofs only; no
module of the program imports this file.


-/
import OnBytes.Flat.LinksKeepsBank

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Stages

/-! ## The block, from its links -/

/-- One link keeps the flags, if its check does. -/
theorem keeps_runLinkH (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (l : Nat)
    (X : LinkH) (check : ChainCheck) (out : Proof.LinksResult) (hX : Over.K X.run) :
    Over.K (runLinkH links p wsLay l X check out) := by
  unfold runLinkH
  keeps

/-- The links that are still to come keep the flags, if their checks do. -/
theorem keeps_runLinksFrom (links : Array LinkH) (p : Params.First) (wsLay : WsLay)
    (rest : List LinkH) (h : ∀ X ∈ rest, Over.K X.run) (l : Nat) (check : ChainCheck)
    (out : Proof.LinksResult) : Over.K (runLinksFrom links p wsLay rest l check out) := by
  induction rest generalizing l check out with
  | nil =>
    unfold runLinksFrom
    exact k_pure _
  | cons X rest ih =>
    unfold runLinksFrom
    refine k_bind (keeps_runLinkH links p wsLay l X check out (h X (by simp))) fun r => ?_
    exact ih (fun Y hY => h Y (by simp [hY])) _ _ _

/-- The block of the links keeps the flags, if the links' checks do. -/
theorem keeps_runLinksH (links : Array LinkH) (p : Params.First) (wsLay : WsLay)
    (h : ∀ X ∈ links.toList, Over.K X.run) : Blk.Keeps (runLinksH links p wsLay) := by
  have h' := keeps_runLinksFrom links p wsLay links.toList h
  show Over.K (runLinksH links p wsLay)
  unfold runLinksH
  keeps

/-! ## The checks that the plans give to their links -/

theorem layers_run (X : Verify.Public) (tokv : Array Nat) (g : Nat) (hp : Layer.HPlan2) :
    Over.K (Verify.layersPlanOf X tokv g hp).run := by
  show Over.K (some <$> Layer.runForkHidG2 { X.layers with tokv := tokv } hp g)
  keeps

theorem attention_run (A : Attention.Plan) : Over.K (Verify.attentionPlanOf A).run := by
  show Over.K (do
    Attention.run A
    pure none : LinkM (Option WsForkOut))
  keeps

theorem head_run (X : Verify.Public) (cov : Head.Covered) :
    Over.K (Verify.headPlanOf X cov).run := by
  show Over.K (some <$> Head.runForkHidH2 X.hS X.HLy (Verify.borderOf X.y) X.H X.owner cov
    X.layers.wsLay)
  keeps

/-! ## The list of the links -/

/-- A step of a computation that can refuse. -/
private theorem ok_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e =>
    have h' : (Except.error e : Except ε β) = .ok b := h
    cases h'
  | ok a => exact ⟨a, rfl, h⟩

/-- What holds at a loop's start and is kept by every turn holds at its end. -/
private theorem forIn_keeps {ε α β : Type} (P : β → Prop)
    {f : α → β → Except ε (ForInStep β)} :
    ∀ (l : List α) (init r : β),
      (∀ a ∈ l, ∀ s t, P s → f a s = .ok t → P t.value) → P init →
      forIn l init f = .ok r → P r
  | [], init, r, _, h0, h => by
      rw [List.forIn_nil] at h
      cases h
      exact h0
  | a :: l, init, r, hf, h0, h => by
      rw [List.forIn_cons] at h
      obtain ⟨t, h1, h2⟩ := ok_bind h
      have ht := hf a (by simp) init t h0 h1
      cases t with
      | done b =>
        cases h2
        exact ht
      | yield b => exact forIn_keeps P l b r (fun a' ha' => hf a' (by simp [ha'])) ht h2

/-- A member of a numbered list is a member of the list. -/
private theorem fst_mem_zipIdx {α : Type} :
    ∀ (l : List α) (k : Nat) (x : α × Nat), x ∈ l.zipIdx k → x.1 ∈ l
  | [], _, _, h => by cases h
  | a :: l, k, x, h => by
      have h' : x ∈ (a, k) :: l.zipIdx (k + 1) := h
      rcases List.mem_cons.1 h' with rfl | h''
      · simp
      · exact List.mem_cons_of_mem _ (fst_mem_zipIdx l (k + 1) x h'')

private theorem all_push {arr : Array LinkH} {x : LinkH} (h : ∀ X ∈ arr, Over.K X.run)
    (hx : Over.K x.run) : ∀ X ∈ arr.push x, Over.K X.run := by
  intro X hX
  rcases Array.mem_push.1 hX with h1 | rfl
  · exact h X h1
  · exact hx

/-- Every link of the list has the check of one of the plans. -/
theorem listLinksH_runs {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {links : Array LinkH} (h : listLinksH NGr p4 G A H = .ok links)
    (hG : ∀ s ∈ G, Over.K s.run) (hA : ∀ s ∈ A, Over.K s.run) (hH : Over.K H.run) :
    ∀ X ∈ links, Over.K X.run := by
  unfold listLinksH at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨r, h2, h⟩ := ok_bind h
  have hr : ∀ X ∈ r, Over.K X.run := by
    refine forIn_keeps (fun arr : Array LinkH => ∀ X ∈ arr, Over.K X.run) _ _ _ ?_ ?_ h2
    · intro x hx s t hs hf
      obtain ⟨sp, g⟩ := x
      have hsp : Over.K sp.run := hG sp (Array.mem_toList_iff.1 (fst_mem_zipIdx _ _ _ hx))
      dsimp only at hf
      repeat' split at hf
      all_goals
        simp only [bind, Except.bind, pure, Except.pure] at hf
        cases hf
        first
          | exact all_push (all_push hs hsp) (hA _ (Array.mem_of_getElem? ‹_›))
          | exact all_push hs hsp
    · intro X hX
      simp at hX
  cases h
  exact all_push hr hH

/-- Every link of a request's chain has a check that keeps the flags. -/
theorem linksOf_runs {X : Verify.Public} {cov : Head.Covered} {links : Array LinkH}
    (h : Verify.linksOf X cov = .ok links) : ∀ L ∈ links, Over.K L.run := by
  refine listLinksH_runs h ?_ ?_ (head_run X cov)
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := Array.mem_mapIdx.1 hs
    exact layers_run _ _ _ _
  · intro s hs
    obtain ⟨a, _, rfl⟩ := Array.mem_map.1 hs
    exact attention_run a

/-- The links as built, each with the check of the link at its place. -/
private theorem zipWith_runs : ∀ (bs ls : List LinkH), (∀ X ∈ ls, Over.K X.run) →
    ∀ X ∈ List.zipWith (fun (b l : LinkH) => { b with run := l.run }) bs ls, Over.K X.run
  | [], _, _, X, hX => by simp at hX
  | _ :: _, [], _, X, hX => by simp at hX
  | b :: bs, l :: ls, h, X, hX => by
      rw [List.zipWith_cons_cons] at hX
      rcases List.mem_cons.1 hX with rfl | h'
      · exact h l (by simp)
      · exact zipWith_runs bs ls (fun Y hY => h Y (by simp [hY])) X h'

/-- **The block of the links that the program passes on leaves the two flags of a run as they
are**: at all public values, all requests, and all links as built. -/
theorem links_keep {X : Verify.Public} {cov : Head.Covered} {links : Array LinkH}
    (h : Verify.linksOf X cov = .ok links) (built : Array LinkH) (p : Params.First)
    (wsLay : WsLay) :
    Blk.Keeps (runLinksH (built.zipWith (fun b l => { b with run := l.run }) links) p wsLay) := by
  apply keeps_runLinksH
  rw [Array.toList_zipWith]
  exact zipWith_runs _ _ fun Y hY => linksOf_runs h Y (Array.mem_toList_iff.1 hY)

end OnBytes.Flat
