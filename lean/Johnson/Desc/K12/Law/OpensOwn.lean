-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K12.Law.WrittenOfDecl
import Johnson.Desc.First.Driver.PlacesLaw
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.Sound.PaidAtDesc
/-
Johnson/Desc/K12/Law/OpensOwn.lean: ON A FILE's FIRST AND SHARED CHAIN EVERY TREE THAT A ROUND OPENS
IS THE CHAIN's OWN: on the plan's side (each declared source is «.own n») and on the data's side
(each opened tree's number over the file is at least the number of trees that the first chain
sends). GENERAL IN THE DESCRIPTION. WHY IT HOLDS: readers take these two chains' declared rounds at
NO earlier chain (Johnson.G.OfPlan.writtenOf's text: Law/WrittenOfDecl.lean's chains_of_written),
and a source «.taken c p» has no image there (Fmt/Parsed.lean: TreeSource.src): so where the declared
rounds can be written out at all, none is taken; and F.data's yes holds writtenOf's
(data_ok). FOR WHOM: leadsK_of_lift | liftHands (Johnson/Desc/Plain/KeyAlone.lean ·
Sound/SharedRule.lean) ask of a piece on the shared chain: its block is a lifted block · the two
laws of get | set · it opens no tree of an earlier chain. AT lo := D.t₁ that rule's key at the row's
first place holds no tree's string (hi = lo): the chain's own first record and the stored table
alone. THE FACT IS THE DESCRIPTION's, NOT THIS KIND's: it belongs beside
Johnson/Desc/BlockSlotOpens.lean.

BOOK-KEEPING ON THE PLAN AND THE DATA. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  some_of_mapM · own_of_round_nil · own_of_rounds_nil     a tool (its home is beside
      First.mem_of_mapM, which goes the other way); one round; a list.
  own_sources_shared | own_sources_first     Johnson.G.OfPlan.writtenOf file D = .ok R gives it of
      D.2.1 | D.1.
  opens_own₂ · opens_own_stretch     F.data file = .ok D ⇒ ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, F.t₁ ≤ j;
      the same at any stretch of that chain's data, at D.t₁ (= F.t₁: Sound/DataRounds.lean's
      opensShaped).
  held_is_lift · held_get_set | held_set_set     the held block is a lifted block, and the two laws:
      each by rfl.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Maker

/-- Where mapM answers, the function answers at every member. -/
theorem some_of_mapM {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ a ∈ l, ∃ b, f a = some b
  | [], _, _ => fun _ ha => nomatch ha
  | a0 :: l, r, h => by
    obtain ⟨b0, bs, hb0, hbs, _⟩ := First.mapM_cons_some f a0 l r h
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b0, hb0⟩
    · exact some_of_mapM f l bs hbs a ha

/-- At no earlier chain a round that readers can take opens own trees alone. -/
theorem own_of_round_nil {r : Fmt.DeclaredRound} {x : Fmt.Round} (h : r.round [] = some x) :
    ∀ o ∈ r.opens, ∃ n, o.2 = .own n := by
  unfold Fmt.DeclaredRound.round at h
  obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨os, hos, _⟩ := Option.map_eq_some_iff.1 h
  intro o ho
  obtain ⟨y, hy⟩ := some_of_mapM _ _ _ hos o ho
  obtain ⟨s, hs, _⟩ := Option.map_eq_some_iff.1 hy
  cases hsrc : o.2 with
  | own n => exact ⟨n, rfl⟩
  | taken c p =>
    rw [hsrc] at hs
    simp [Fmt.TreeSource.src] at hs

theorem own_of_rounds_nil {ds : List Fmt.DeclaredRound} {xs : List Fmt.Round}
    (h : ds.mapM (·.round []) = some xs) : ∀ r ∈ ds, ∀ o ∈ r.opens, ∃ n, o.2 = .own n := by
  intro r hr
  obtain ⟨x, hx⟩ := some_of_mapM _ _ _ h r hr
  exact own_of_round_nil hx

/-- The shared chain's declared rounds, wherever a file's declared rounds can be written out. -/
theorem own_sources_shared {file : String} {D : Johnson.G.OfPlan.Decl3}
    {R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds}
    (hW : Johnson.G.OfPlan.writtenOf file D = .ok R) :
    ∀ r ∈ D.2.1, ∀ o ∈ r.opens, ∃ n, o.2 = .own n :=
  own_of_rounds_nil (H2K.Pub.chains_of_written hW).2.1

/-- The first chain's. -/
theorem own_sources_first {file : String} {D : Johnson.G.OfPlan.Decl3}
    {R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds}
    (hW : Johnson.G.OfPlan.writtenOf file D = .ok R) :
    ∀ r ∈ D.1, ∀ o ∈ r.opens, ∃ n, o.2 = .own n :=
  own_of_rounds_nil (H2K.Pub.chains_of_written hW).1

/-- A member on the left of a Forall₂ has a fellow on the right. -/
theorem fellow_of_forall₂ {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {m : List β},
    List.Forall₂ R l m → ∀ a ∈ l, ∃ b ∈ m, R a b
  | _, _, .nil => fun _ ha => nomatch ha
  | _, _, .cons h t => fun a ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hr⟩ := fellow_of_forall₂ t a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- The shared chain's data open no tree of the first chain: from F.data's yes alone. -/
theorem opens_own₂ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, F.t₁ ≤ j := by
  obtain ⟨R, hR, _⟩ := data_ok h
  intro d hd j hj
  obtain ⟨r, hr, _, e⟩ := fellow_of_forall₂ (opensOfData Xi F file D h).2.1 d hd
  rw [e] at hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hj
  obtain ⟨n, hn⟩ := own_sources_shared hR r hr x hx
  rw [hn]
  exact Nat.le_add_right _ _

/-- The same at any stretch of that chain's data, at the data's own number. -/
theorem opens_own_stretch {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (a n : ℕ) :
    ∀ d ∈ (D.ds₂.drop a).take n, ∀ j ∈ d.opens, D.t₁ ≤ j := by
  intro d hd
  rw [(opensShaped F file D h).2.1]
  exact opens_own₂ F file D h d (List.mem_of_mem_drop (List.mem_of_mem_take hd))

/-- The held block is a lifted block. -/
theorem held_is_lift {P S Cl : Type} (b : Block S Cl) :
    held (P := P) b = (below b).lift Prod.snd fun t s => (t.1, s) := rfl

theorem held_get_set {P S : Type} (t : P × S) (s : S) : Prod.snd ((t.1, s) : P × S) = s := rfl

theorem held_set_set {P S : Type} (t : P × S) (s s' : S) :
    ((((t.1, s) : P × S).1, s') : P × S) = (t.1, s') := rfl

end H2K.JointK

#print axioms H2K.JointK.own_sources_shared
#print axioms H2K.JointK.opens_own₂
#print axioms H2K.JointK.opens_own_stretch
#print axioms H2K.JointK.held_is_lift
