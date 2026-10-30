-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/Gather.lean: SEVERAL BLOCKS OF A FOLD AS ONE BLOCK: where the fold over the
blocks returns a record, the fold over the gathered blocks returns the same record.

The setting. A description's chain is a flat list of blocks, a short verifier each. A proved typed
block of the library may span several of them (a whole preamble; a proximity test of eight blocks).
`Block.andThen` (Johnson/Desc/Block.lean) lays two blocks as one: the rounds and the groups of
opened leaves are cut between them. Soundness of a file goes over to a decision that says yes less
often: so a rule that is had at the gathered blocks serves the description itself, if the fold's yes
gives the gathered fold's yes, with the same record.

What is said.
  `step_andThen`: where p's step returns (s₁, k₁) and q's step, from s₁ and behind the k₁ leaves
    taken, returns (s₂, k₂), the step of `p.andThen name q` at the two stretches in a row returns
    (s₂, k₁ + k₂).
  `Gathers l l'`: l' is l with neighbours laid together, any number of times.
  `gathers_fold`, `gathers_chainAt`: where the fold over l returns, the fold over l' returns the
    same. Beneath: `roundsFit_app`, `groupsOf_app`, `groupsOf_len`, `regroup_app`: the format's
    tests and cuts along two stretches in a row.

Limits. One direction. The refusals' words are not compared. Nothing on any block of the protocol.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PassTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

variable {S Cl : Type}

/-! ## 1 The format's tests and cuts along two stretches in a row -/

theorem roundsFit_len : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), roundsFit ds rs = true →
    rs.length = ds.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: ds, _ :: rs, h => by
    have h' := (Bool.and_eq_true_iff.1 h).2
    exact congrArg (· + 1) (roundsFit_len ds rs h')

theorem roundsFit_app : ∀ (ds₁ ds₂ : List Fmt.DeclaredRound) (rs₁ rs₂ : List Fmt.RoundView),
    roundsFit ds₁ rs₁ = true → roundsFit ds₂ rs₂ = true →
    roundsFit (ds₁ ++ ds₂) (rs₁ ++ rs₂) = true
  | [], _, [], _, _, h => h
  | [], _, _ :: _, _, h, _ => by cases h
  | _ :: _, _, [], _, h, _ => by cases h
  | _ :: ds₁, ds₂, _ :: rs₁, rs₂, h, h₂ => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 h
    exact Bool.and_eq_true_iff.2 ⟨ha, roundsFit_app ds₁ ds₂ rs₁ rs₂ hb h₂⟩

theorem groupsOf_app (ft : ℕ) : ∀ (ds₁ ds₂ : List Fmt.DeclaredRound) (Rs₁ Rs₂ : List Fmt.Drawn),
    Rs₁.length = ds₁.length →
    groupsOf ft (ds₁ ++ ds₂) (Rs₁ ++ Rs₂) = groupsOf ft ds₁ Rs₁ ++ groupsOf ft ds₂ Rs₂
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => by cases h
  | _ :: _, _, [], _, h => by cases h
  | d :: ds₁, ds₂, R :: Rs₁, Rs₂, h => by
    have ih := groupsOf_app ft ds₁ ds₂ Rs₁ Rs₂ (Nat.succ.inj h)
    show _ ++ groupsOf ft (ds₁ ++ ds₂) (Rs₁ ++ Rs₂) = (_ ++ groupsOf ft ds₁ Rs₁) ++ _
    rw [ih]
    simp only [List.append_assoc]

/-- The number of a list of declared rounds' groups. -/
def openingsOf (ds : List Fmt.DeclaredRound) : ℕ :=
  (ds.map fun r => r.stored.length + r.opens.length).sum

theorem foldl_openings : ∀ (ds : List Fmt.DeclaredRound) (n : ℕ),
    ds.foldl (fun n r => n + r.stored.length + r.opens.length) n = n + openingsOf ds
  | [], _ => rfl
  | d :: ds, n => by
    show ds.foldl _ (n + d.stored.length + d.opens.length) = _
    rw [foldl_openings ds]
    show _ = n + ((d.stored.length + d.opens.length) + openingsOf ds)
    omega

theorem openings_eq (b : Block S Cl) : b.openings = openingsOf b.rounds := by
  unfold Block.openings
  rw [foldl_openings, Nat.zero_add]

theorem groupsOf_len (ft : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    Rs.length = ds.length → (groupsOf ft ds Rs).length = openingsOf ds
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: ds, R :: Rs, h => by
    have ih := groupsOf_len ft ds Rs (Nat.succ.inj h)
    show (_ ++ _ ++ groupsOf ft ds Rs).length = (d.stored.length + d.opens.length) + openingsOf ds
    rw [List.length_append, List.length_append, List.length_map, List.length_map, ih]

theorem regroup_len : ∀ (ns : List ℕ) (c : List OpenedColumn), (regroup ns c).length = ns.length
  | [], _ => rfl
  | _ :: ns, c => congrArg (· + 1) (regroup_len ns _)

theorem regroup_app : ∀ (ns ms : List ℕ) (c₁ c₂ : List OpenedColumn), c₁.length = ns.sum →
    regroup (ns ++ ms) (c₁ ++ c₂) = regroup ns c₁ ++ regroup ms c₂
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => by cases h
  | n :: ns, ms, c₁, c₂, h => by
    have hn : n ≤ c₁.length := by
      rw [h, List.sum_cons]
      omega
    have h1 : (c₁ ++ c₂).take n = c₁.take n := List.take_append_of_le_length hn
    have h2 : (c₁ ++ c₂).drop n = c₁.drop n ++ c₂ := List.drop_append_of_le_length hn
    show _ :: regroup (ns ++ ms) ((c₁ ++ c₂).drop n) = (_ :: regroup ns (c₁.drop n)) ++ _
    rw [h1, h2, regroup_app ns ms (c₁.drop n) c₂ (by
      rw [List.length_drop, h, List.sum_cons]
      omega)]
    rfl

theorem flat_len {α : Type} : ∀ G : List (List α), (G.flatMap id).length = (G.map List.length).sum
  | [] => rfl
  | g :: G => by
    show (g ++ G.flatMap id).length = g.length + (G.map List.length).sum
    rw [List.length_append, flat_len G]

/-! ## 2 Two blocks as one -/

/-- **The step of two blocks laid as one.** -/
theorem step_andThen (ft : ℕ) (name : String) (p q : Block S Cl) (s s₁ s₂ : S)
    (R₁ R₂ : List Fmt.RoundView) (c : List OpenedColumn) (k₁ k₂ : ℕ) (h₁ : p.step ft s R₁ c = .ok (s₁, k₁))
    (h₂ : q.step ft s₁ R₂ (c.drop k₁) = .ok (s₂, k₂)) :
    (p.andThen name q).step ft s (R₁ ++ R₂) c = .ok (s₂, k₁ + k₂) := by
  obtain ⟨f₁, e₁, hk₁, d₁⟩ := (step_ok_iff ft p s s₁ R₁ c k₁).1 h₁
  obtain ⟨f₂, e₂, hk₂, d₂⟩ := (step_ok_iff ft q s₁ s₂ R₂ (c.drop k₁) k₂).1 h₂
  have l₁ : R₁.length = p.rounds.length := roundsFit_len _ _ f₁
  have l₂ : R₂.length = q.rounds.length := roundsFit_len _ _ f₂
  have hG : groupsOf ft (p.rounds ++ q.rounds) ((R₁ ++ R₂).map (·.drawn)) =
      groupsOf ft p.rounds (R₁.map (·.drawn)) ++ groupsOf ft q.rounds (R₂.map (·.drawn)) := by
    rw [List.map_append, groupsOf_app ft _ _ _ _ (by rw [List.length_map, l₁])]
  have hT : c.take (k₁ + k₂) = c.take k₁ ++ (c.drop k₁).take k₂ := List.take_add
  have hc₁ : (c.take k₁).length =
      ((groupsOf ft p.rounds (R₁.map (·.drawn))).map List.length).sum := by
    rw [← flat_len, ← e₁, List.length_map]
  refine (step_ok_iff ft (p.andThen name q) s s₂ (R₁ ++ R₂) c (k₁ + k₂)).2 ⟨?_, ?_, ?_, ?_⟩
  · exact roundsFit_app _ _ _ _ f₁ f₂
  · show (c.take (k₁ + k₂)).map _ = (groupsOf ft (p.rounds ++ q.rounds) _).flatMap id
    rw [hG, hT, List.map_append, List.flatMap_append, e₁, e₂]
  · show k₁ + k₂ = ((groupsOf ft (p.rounds ++ q.rounds) _).flatMap id).length
    rw [hG, List.flatMap_append, List.length_append, ← hk₁, ← hk₂]
  · show (p.decide s (((R₁ ++ R₂).map noDigest).take p.rounds.length)
        ((regroup ((groupsOf ft (p.rounds ++ q.rounds) ((R₁ ++ R₂).map (·.drawn))).map (·.length))
          (c.take (k₁ + k₂))).take p.openings)).bind (fun s' =>
      q.decide s' (((R₁ ++ R₂).map noDigest).drop p.rounds.length)
        ((regroup ((groupsOf ft (p.rounds ++ q.rounds) ((R₁ ++ R₂).map (·.drawn))).map (·.length))
          (c.take (k₁ + k₂))).drop p.openings)) = .ok s₂
    have hn : (R₁.map noDigest).length = p.rounds.length := by rw [List.length_map, l₁]
    have ho : (regroup ((groupsOf ft p.rounds (R₁.map (·.drawn))).map (·.length))
        (c.take k₁)).length = p.openings := by
      rw [regroup_len, List.length_map, groupsOf_len ft _ _ (by rw [List.length_map, l₁]),
        openings_eq]
    rw [hG, hT, List.map_append, List.map_append, regroup_app _ _ _ _ hc₁,
      List.take_left' hn, List.drop_left' hn, List.take_left' ho, List.drop_left' ho]
    have d₁' : p.decide s (R₁.map noDigest)
        (regroup ((groupsOf ft p.rounds (R₁.map (·.drawn))).map (·.length)) (c.take k₁)) =
          .ok s₁ := d₁
    have d₂' : q.decide s₁ (R₂.map noDigest)
        (regroup ((groupsOf ft q.rounds (R₂.map (·.drawn))).map (·.length))
          ((c.drop k₁).take k₂)) = .ok s₂ := d₂
    rw [d₁']
    exact d₂'

/-! ## 3 The fold -/

/-- What a fold's return says of its first block. -/
theorem foldBlocks_cons_ok (ft : ℕ) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (b :: l) s rs c = .ok r) :
    ∃ s' k, b.rounds.length ≤ rs.length ∧ b.step ft s (rs.take b.rounds.length) c = .ok (s', k) ∧
      foldBlocks ft l s' (rs.drop b.rounds.length) (c.drop k) = .ok r := by
  by_cases hle : b.rounds.length ≤ rs.length
  · have hlen : (rs.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    cases hs : b.step ft s (rs.take b.rounds.length) c with
    | error e =>
      have e1 := foldBlocks_error ft b l s _ (rs.drop b.rounds.length) c hlen e hs
      rw [List.take_append_drop] at e1
      rw [e1] at h
      cases h
    | ok x =>
      obtain ⟨s1, k⟩ := x
      have e1 := foldBlocks_ok ft b l s _ (rs.drop b.rounds.length) c hlen s1 k hs
      rw [List.take_append_drop] at e1
      rw [e1] at h
      exact ⟨s1, k, hle, rfl, h⟩
  · rw [foldBlocks_short ft b l s rs c hle] at h
    cases h

/-- And back. -/
theorem foldBlocks_of_step (ft : ℕ) (b : Block S Cl) (l : List (Block S Cl)) (s s' : S)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (k : ℕ) (hle : b.rounds.length ≤ rs.length)
    (hs : b.step ft s (rs.take b.rounds.length) c = .ok (s', k)) :
    foldBlocks ft (b :: l) s rs c = foldBlocks ft l s' (rs.drop b.rounds.length) (c.drop k) := by
  have hlen : (rs.take b.rounds.length).length = b.rounds.length := by
    rw [List.length_take]
    omega
  have e1 := foldBlocks_ok ft b l s _ (rs.drop b.rounds.length) c hlen s' k hs
  rw [List.take_append_drop] at e1
  exact e1

/-- **Where the fold over p, q and the rest returns, the fold over the two laid as one, and the
rest, returns the same.** -/
theorem fold_andThen (ft : ℕ) (name : String) (p q : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (p :: q :: l) s rs c = .ok r) :
    foldBlocks ft (p.andThen name q :: l) s rs c = .ok r := by
  obtain ⟨s₁, k₁, le₁, st₁, h'⟩ := foldBlocks_cons_ok ft p (q :: l) s rs c r h
  obtain ⟨s₂, k₂, le₂, st₂, h''⟩ := foldBlocks_cons_ok ft q l s₁ _ _ r h'
  rw [List.length_drop] at le₂
  have hlen : (p.andThen name q).rounds.length = p.rounds.length + q.rounds.length :=
    List.length_append
  have hT : rs.take (p.andThen name q).rounds.length =
      rs.take p.rounds.length ++ (rs.drop p.rounds.length).take q.rounds.length := by
    rw [hlen]
    exact List.take_add
  rw [foldBlocks_of_step ft (p.andThen name q) l s s₂ rs c (k₁ + k₂) (by rw [hlen]; omega)
    (by rw [hT]; exact step_andThen ft name p q s s₁ s₂ _ _ c k₁ k₂ st₁ st₂), hlen]
  rw [List.drop_drop, List.drop_drop] at h''
  exact h''

/-- **l' is l with neighbours laid together.** -/
inductive Gathers : List (Block S Cl) → List (Block S Cl) → Prop
  | nil : Gathers [] []
  | keep (b : Block S Cl) {l l' : List (Block S Cl)} : Gathers l l' → Gathers (b :: l) (b :: l')
  | join (name : String) (p q : Block S Cl) {l l' : List (Block S Cl)} :
      Gathers (p.andThen name q :: l) l' → Gathers (p :: q :: l) l'

/-- **Where the fold over l returns, the fold over l' returns the same.** -/
theorem gathers_fold (ft : ℕ) {l l' : List (Block S Cl)} (g : Gathers l l') :
    ∀ (s : S) (rs : List Fmt.RoundView) (c : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft l s rs c = .ok r → foldBlocks ft l' s rs c = .ok r := by
  induction g with
  | nil => exact fun _ _ _ _ h => h
  | keep b _ ih =>
    intro s rs c r h
    obtain ⟨s', k, le, st, h'⟩ := foldBlocks_cons_ok ft b _ s rs c r h
    rw [foldBlocks_of_step ft b _ s s' rs c k le st]
    exact ih _ _ _ _ h'
  | join name p q _ ih =>
    intro s rs c r h
    exact ih _ _ _ _ (fold_andThen ft name p q _ s rs c r h)

theorem gathers_nonempty {l l' : List (Block S Cl)} (g : Gathers l l') :
    l.isEmpty = false → l'.isEmpty = false := by
  induction g with
  | nil => exact fun h => h
  | keep b _ _ => exact fun _ => rfl
  | join name p q _ ih => exact fun _ => ih rfl

theorem endOk_some (x : Except String (S × List Fmt.RoundView × List OpenedColumn)) (s' : S) :
    endOk x = some s' ↔ x = .ok (s', [], []) := by
  constructor
  · intro h
    match x, h with
    | .ok (s, [], []), h => rw [Option.some.inj h]
  · intro h
    rw [h]
    rfl

/-- **The like for a chain's decision**, whatever the chains' names are. -/
theorem gathers_chainAt (n n' : String) (ft : ℕ) {l l' : List (Block S Cl)} (g : Gathers l l')
    (s s' : S) (v : Fmt.View) (h : (chainAt n ft l s v).toOption = some s') :
    (chainAt n' ft l' s v).toOption = some s' := by
  rw [chainAt_toOption] at h ⊢
  cases hE : l.isEmpty with
  | true =>
    rw [hE, if_pos rfl] at h
    cases h
  | false =>
    rw [hE] at h
    rw [gathers_nonempty g hE]
    simp only [Bool.false_eq_true, if_false] at h ⊢
    exact (endOk_some _ _).2 (gathers_fold ft g _ _ _ _ ((endOk_some _ _).1 h))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.step_andThen
#print axioms VerifiableInference.Desc.Sound.fold_andThen
#print axioms VerifiableInference.Desc.Sound.gathers_fold
#print axioms VerifiableInference.Desc.Sound.gathers_chainAt
