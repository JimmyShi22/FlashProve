-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainYes.lean: FROM THE BLOCKS' decide TO A ONE-CHAIN FILE's DECISION ON A VIEW.
General in the description, its blocks and the view; no protocol is named. Statements and proofs.

  runEnd_ok, run_iff   what a yes of a one-chain file's decision (OneChainFileDescription.runEnd, OneChainFileDescription.run,
                  Johnson/Desc/Link/OneChainFileDescription.lean) is made of: equivalences
  colsFor_served, colsFor_app   what is served can be looked up, with the wanted keys, positions and
                  widths; two lists in a row
  fold_of_walks   THE FOLD's YES FROM THE BLOCKS' YESES: roundsFit ONCE, at the blocks' declared
                  rounds in a row; the columns ONCE, looked up by key along groupsOf's list in a
                  row; each block's decide at its declared groups read by key (Walks)
  walks_append    two stretches of blocks in a row
  run_of_walks    so the decision's yes

By: Block.step_ok, foldBlocks_cons_ok, chainAt_ok, bind_eq_ok, need_eq_ok
(Johnson/Desc/RunLaws.lean);
roundsFit_append, roundsFit_length, groupsOf_app (Johnson/Top/H0/StepLaws/StepLaws.lean);
regroup_colsFor (Johnson/Desc/Plain/OneYes.lean).

Limits. Walks, Served and every other premise are premises: no block's yes is shown here. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ChainDefs
import Johnson.Desc.RunLaws
import Johnson.Desc.Link.OneChainFileDescription
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc
open VerifiableInference.Desc.Plain.One (readG colsFor regroup_colsFor)

/-! ## The decision -/

/-- **What a yes of a one-chain file's decision is made of.** -/
theorem runEnd_ok {Xi : Type} (F : OneChainFileDescription Xi) (x : Xi) (v : Fmt.View) (e : F.S) :
    F.runEnd x v = .ok e ↔ F.planWord = none ∧ F.okStart x = true ∧ viewWordsBelowPrime v = true ∧
      chainAt "the chain" 0 F.chain.blocksInOrder (F.start x) v = .ok e ∧ F.fin x e = true := by
  unfold OneChainFileDescription.runEnd
  cases hw : F.planWord with
  | some w =>
    constructor
    · intro h
      exact (error_ne_ok h).elim
    · rintro ⟨h, -⟩
      cases h
  | none =>
    constructor
    · intro h
      obtain ⟨_, -, h⟩ := bind_eq_ok h
      obtain ⟨_, h1, h⟩ := bind_eq_ok h
      obtain ⟨_, h2, h⟩ := bind_eq_ok h
      obtain ⟨e', h3, h⟩ := bind_eq_ok h
      obtain ⟨_, h4, h⟩ := bind_eq_ok h
      obtain rfl : e' = e := Except.ok.inj h
      exact ⟨rfl, need_eq_ok h1, need_eq_ok h2, h3, need_eq_ok h4⟩
    · rintro ⟨-, h1, h2, h3, h4⟩
      simp only [h1, h2, h3, h4, need, bind, Except.bind, pure, Except.pure, if_true]

theorem run_iff {Xi : Type} (F : OneChainFileDescription Xi) (x : Xi) (v : Fmt.View) :
    F.run x v = true ↔ ∃ e, F.planWord = none ∧ F.okStart x = true ∧ viewWordsBelowPrime v = true ∧
      chainAt "the chain" 0 F.chain.blocksInOrder (F.start x) v = .ok e ∧ F.fin x e = true := by
  unfold OneChainFileDescription.run
  constructor
  · intro h
    cases hr : F.runEnd x v with
    | error w =>
      rw [hr] at h
      cases h
    | ok e => exact ⟨e, (runEnd_ok F x v e).1 hr⟩
  · rintro ⟨e, h⟩
    rw [(runEnd_ok F x v e).2 h]
    rfl

/-! ## Columns by key -/

/-- What is served can be looked up, and has the wanted keys, positions and widths. -/
theorem colsFor_served (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ ws : List (ℕ × ℕ × ℕ), Served L ws →
      ∃ cs, colsFor L ws = some cs ∧ (cs.map fun c => (c.1, c.2.1, c.2.2.length)) = ws
  | [], _ => ⟨[], rfl, rfl⟩
  | w :: ws, h => by
    obtain ⟨c, hc, hl⟩ := h w List.mem_cons_self
    obtain ⟨cs, h1, h2⟩ := colsFor_served L ws fun w' hw' => h w' (List.mem_cons_of_mem _ hw')
    refine ⟨(w.1, w.2.1, c) :: cs, ?_, ?_⟩
    · show (match L w.1 w.2.1, colsFor L ws with
        | some c, some cs => some ((w.1, w.2.1, c) :: cs)
        | _, _ => none) = _
      rw [hc, h1]
    · show (w.1, w.2.1, c.length) :: cs.map _ = w :: ws
      rw [hl, h2]

/-- Two lists in a row. -/
theorem colsFor_app (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ (g r : List (ℕ × ℕ × ℕ)) (c₁ c₂ : List OpenedColumn), colsFor L g = some c₁ → colsFor L r = some c₂ →
      colsFor L (g ++ r) = some (c₁ ++ c₂)
  | [], _, _, _, h1, h2 => by
    obtain rfl : [] = _ := Option.some.inj h1
    exact h2
  | w :: g, r, c₁, c₂, h1, h2 => by
    have h1' : (match L w.1 w.2.1, colsFor L g with
      | some c, some cs => some ((w.1, w.2.1, c) :: cs)
      | _, _ => none) = some c₁ := h1
    cases hL : L w.1 w.2.1 with
    | none =>
      rw [hL] at h1'
      cases h1'
    | some c =>
      cases hg : colsFor L g with
      | none =>
        rw [hL, hg] at h1'
        cases h1'
      | some cs =>
        rw [hL, hg] at h1'
        obtain rfl := Option.some.inj h1'
        show (match L w.1 w.2.1, colsFor L (g ++ r) with
          | some c, some cs => some ((w.1, w.2.1, c) :: cs)
          | _, _ => none) = _
        rw [hL, colsFor_app L g r cs c₂ hg h2]
        rfl

/-! ## The fold -/

variable {S Cl : Type}

/-- **THE FOLD's YES FROM THE BLOCKS' YESES.** -/
theorem fold_of_walks (ft : ℕ) (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ (bs : List (Block S Cl)) (s e : S) (rs : List Fmt.RoundView) (cs : List OpenedColumn),
      roundsFit (bs.flatMap (·.rounds)) rs = true →
      Served L ((groupsOf ft (bs.flatMap (·.rounds)) (rs.map (·.drawn))).flatMap id) →
      colsFor L ((groupsOf ft (bs.flatMap (·.rounds)) (rs.map (·.drawn))).flatMap id) = some cs →
      Walks ft L bs s rs e → foldBlocks ft bs s rs cs = .ok (e, [], [])
  | [], s, e, rs, cs, _, _, hc, hw => by
    obtain ⟨rfl, rfl⟩ := hw
    obtain rfl : [] = cs := Option.some.inj hc
    rfl
  | b :: l, s, e, rs, cs, hf, hs, hc, hw => by
    obtain ⟨s', hd, hw'⟩ := hw
    rw [List.flatMap_cons] at hf hs hc
    obtain ⟨f1, f2⟩ := (roundsFit_append _ _ _).1 hf
    rw [groupsOf_app, ← List.map_take, ← List.map_drop, List.flatMap_append] at hs hc
    have hs1 : Served L ((groupsOf ft b.rounds
        ((rs.take b.rounds.length).map (·.drawn))).flatMap id) :=
      fun w hw => hs w (List.mem_append_left _ hw)
    have hs2 : Served L ((groupsOf ft (l.flatMap (·.rounds))
        ((rs.drop b.rounds.length).map (·.drawn))).flatMap id) :=
      fun w hw => hs w (List.mem_append_right _ hw)
    obtain ⟨c₁, k1, m1⟩ := colsFor_served L _ hs1
    obtain ⟨c₂, k2, -⟩ := colsFor_served L _ hs2
    obtain rfl : c₁ ++ c₂ = cs :=
      Option.some.inj ((colsFor_app L _ _ c₁ c₂ k1 k2).symm.trans hc)
    have hlen : c₁.length = ((groupsOf ft b.rounds
        ((rs.take b.rounds.length).map (·.drawn))).flatMap id).length := by
      rw [← m1, List.length_map]
    have hstep : b.step ft s (rs.take b.rounds.length) (c₁ ++ c₂) = .ok (s', c₁.length) :=
      Block.step_ok.2 ⟨f1, by rw [List.take_left' rfl]; exact m1,
        by rw [List.take_left' rfl, regroup_colsFor L _ c₁ k1]; exact hd, hlen⟩
    refine foldBlocks_cons_ok.2 ⟨roundsFit_length _ _ f1, s', c₁.length, hstep, ?_⟩
    rw [List.drop_left' rfl]
    exact fold_of_walks ft L l s' e _ c₂ f2 hs2 k2 hw'

/-- Two stretches of blocks in a row. -/
theorem walks_append (ft : ℕ) (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ (l₁ l₂ : List (Block S Cl)) (s m e : S) (rs : List Fmt.RoundView),
      Walks ft L l₁ s (rs.take (l₁.flatMap (·.rounds)).length) m →
      Walks ft L l₂ m (rs.drop (l₁.flatMap (·.rounds)).length) e → Walks ft L (l₁ ++ l₂) s rs e
  | [], _, _, _, _, _, h1, h2 => by
    obtain ⟨-, rfl⟩ := h1
    exact h2
  | b :: l₁, l₂, s, m, e, rs, h1, h2 => by
    obtain ⟨s', hd, hw⟩ := h1
    rw [List.flatMap_cons, List.length_append] at hd hw h2
    rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)] at hd
    refine ⟨s', hd, walks_append ft L l₁ l₂ s' m e (rs.drop b.rounds.length) ?_ ?_⟩
    · rw [List.drop_take, Nat.add_sub_cancel_left] at hw
      exact hw
    · rw [List.drop_drop]
      exact h2

/-- **So the decision's yes.** -/
theorem run_of_walks {Xi : Type} (F : OneChainFileDescription Xi) (x : Xi) (L : ℕ → ℕ → Option (List UInt64))
    (e : F.S) (v : Fmt.View) (hp : F.planWord = none) (ho : F.okStart x = true)
    (hv : viewWordsBelowPrime v = true) (hf : roundsFit F.roundsDeclaredByBlocks v.rounds = true)
    (hs : Served L ((groupsOf 0 F.roundsDeclaredByBlocks (v.rounds.map (·.drawn))).flatMap id))
    (hc : colsFor L ((groupsOf 0 F.roundsDeclaredByBlocks (v.rounds.map (·.drawn))).flatMap id) = some v.opened)
    (hw : Walks 0 L F.chain.blocksInOrder (F.start x) v.rounds e) (he : F.fin x e = true) :
    F.run x v = true :=
  (run_iff F x v).2 ⟨e, hp, ho, hv,
    chainAt_ok.2 ⟨by simp [Chain.blocksInOrder], fold_of_walks 0 L F.chain.blocksInOrder _ e _ _ hf hs hc hw⟩, he⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.runEnd_ok
#print axioms Johnson.Prover.Link.run_iff
#print axioms Johnson.Prover.Link.colsFor_served
#print axioms Johnson.Prover.Link.colsFor_app
#print axioms Johnson.Prover.Link.fold_of_walks
#print axioms Johnson.Prover.Link.walks_append
#print axioms Johnson.Prover.Link.run_of_walks
