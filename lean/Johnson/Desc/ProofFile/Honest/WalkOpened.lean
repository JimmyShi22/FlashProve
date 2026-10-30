-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/WalkOpened.lean: a part is handed, beside the rounds shown so far, the
columns opened so far (`Seen.opened`). This file proves, of every `walk` from a state with
`ChainProgress.Inv`, that at each round the field holds `front` and then a prefix of the chain's columns
(which prefix: Honest/K12/LiveField.lean); and it names the three walks of a run of `runC`
(Walk.lean), each by an equation at the terms of `runC` itself.

What follows from these, chain by chain, once they are joined (the join is not in this file): at
every round at which a part is called the field is `some c`, where: in the first chain c is a prefix
of the first view's opened columns; in the shared chain, of the shared view's; in the second chain c
is all of the first view's, then all of the shared view's, then a prefix of that chain's view's.

  1  `of_bind_ok`, `map_ok`, `hear_opened`   two small lemmas, on `Except.bind` and on `Except.map`;
     `Step.hear` leaves the field
  2  `ChainProgress.Inv`   a definition: where the run is still played, the field is `some` of `front`
     followed by the columns of the sub-protocols asked so far
  3  `settle_inv`, `start_inv`, `heard_inv`, `walk_inv`   it holds from a chain's start on
  4  `settle_cols_prefix`, `heard_cols`, `walk_cols_prefix`   the list of columns only grows at its
     end
  5  `walk_at`, `say_opened`   **at every round of a chain: `m.shown` at the walk's state has
     `opened = some (front ++ c)` with `c` a prefix of the chain's columns at its end** (that
     `Step.tell` hands it: Limits)
  6  `runC_views`   what `ready` returns, the three starts and the three walks of a run, each as an
     equation at the terms of `runC`; the chains' columns at their ends are the columns of the run's
     three views

Limits.
  * Not joined here: the split of a chain's steps and challenges at a round, with equally long
    fronts, which `walk_at` asks; that the state at that round is the one that `walk_at` names.
  * Which prefix the field holds at a round (that it is just the columns of the sub-protocols before
    the round's own) is not proved here: `live_field` (Honest/K12/LiveField.lean), under premises.
  * `runC_views` ties r to the run through its three lists of opened columns alone.
  * Nothing is said of `run`, `midAt` and `midSharedAt`: they hand `none`; nor of `play`, which
    keeps its start state's field (`play_opened`, Gap.lean).
  * That `ChainProgress.say` calls `Step.tell` at `z.mid`'s state and that `Step.tell` hands the part
    `Mid.shown` of it is these definitions' text. It is not stated here.
  * That a view's columns are what a verifier reads is the text of `readsOf` and `fillCols`. It is
    not shown here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription OpenedColumn)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X W Y : Type}

/-! ## 1 Small lemmas -/

theorem of_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem map_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

/-- Hearing a challenge leaves the opened columns. -/
theorem hear_opened {s : Step W Y} {x : Told} {d : Fmt.Drawn} {m m' : Mid W Y}
    (h : s.hear x d m = .ok m') : m'.opened = m.opened := by
  cases hm : s.move with
  | none =>
    simp only [Step.hear, hm] at h
    obtain rfl := Except.ok.inj h
    rfl
  | some mv =>
    simp only [Step.hear, hm] at h
    split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      rfl

/-! ## 2 and 3 The field along a chain -/

/-- Where the run is still played, the field holds `front` and then the columns of the sub-protocols
asked so far. -/
def ChainProgress.Inv (front : List OpenedColumn) (z : ChainProgress S Cl W Y) : Prop :=
  ∀ m, z.mid = some m → m.opened = some (front ++ z.cols)

theorem settle_inv (L : Lay) (front : List OpenedColumn) : ∀ (bs : List (Block S Cl))
    (z z' : ChainProgress S Cl W Y), z.Inv front → ChainProgress.settle L bs z = .ok z' → z'.Inv front
  | [], z, z', hz, h => by
    rw [ChainProgress.settle] at h
    obtain rfl := Except.ok.inj h
    exact hz
  | b :: bs, z, z', hz, h => by
    rw [ChainProgress.settle] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hz
    · obtain ⟨cols, -, h⟩ := of_bind_ok h
      refine settle_inv L front bs _ z' ?_ h
      intro m hm
      cases hzm : z.mid with
      | none =>
        simp [hzm] at hm
      | some m₀ =>
        have h0 := hz m₀ hzm
        split at hm
        · rw [hzm] at hm
          obtain rfl : m₀.took cols = m := Option.some.inj hm
          show m₀.opened.map (· ++ cols) = some (front ++ (z.cols ++ cols))
          rw [h0, ← List.append_assoc]
          rfl
        · cases hm

theorem start_inv {L : Lay} {bs : List (Block S Cl)} {m : Option (Mid W Y)} {v : Option S}
    {front : List OpenedColumn} {z : ChainProgress S Cl W Y} (h : ChainProgress.start L bs m v front = .ok z) :
    z.Inv front := by
  refine settle_inv L front bs _ z ?_ h
  intro m' hm
  split at hm
  · cases m with
    | none => cases hm
    | some m₀ =>
      obtain rfl := Option.some.inj hm
      show some front = some (front ++ [])
      rw [List.append_nil]
  · cases hm

theorem heard_inv {L : Lay} {front : List OpenedColumn} {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told}
    {d : Fmt.Drawn} (hz : z.Inv front) (h : z.heard L s x d = .ok z') : z'.Inv front := by
  unfold ChainProgress.heard at h
  obtain ⟨m', hm', h⟩ := of_bind_ok h
  refine settle_inv L front _ _ z' ?_ h
  intro m hm
  have hm2 : m' = some m := hm
  subst hm2
  cases hzm : z.mid with
  | none =>
    rw [hzm] at hm'
    cases hm'
  | some m₀ =>
    rw [hzm] at hm'
    obtain ⟨m₁, h1, e⟩ := map_ok hm'
    obtain rfl := Option.some.inj e
    show m₁.opened = some (front ++ z.cols)
    rw [hear_opened h1]
    exact hz m₀ hzm

theorem walk_inv (L : Lay) (front : List OpenedColumn) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), z.Inv front → walk L ss ds z = .ok z' → z'.Inv front
  | [], [], z, z', hz, h => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    exact hz
  | s :: ss, d :: ds, z, z', hz, h => by
    rw [walk] at h
    obtain ⟨x, -, h⟩ := of_bind_ok h
    obtain ⟨z₁, h1, h⟩ := of_bind_ok h
    exact walk_inv L front ss ds z₁ z' (heard_inv hz h1) h
  | [], _ :: _, _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, _, h => by simp [walk] at h

/-! ## 4 The columns only grow -/

theorem settle_cols_prefix (L : Lay) : ∀ (bs : List (Block S Cl)) (z z' : ChainProgress S Cl W Y),
    ChainProgress.settle L bs z = .ok z' → z.cols <+: z'.cols
  | [], z, z', h => by
    rw [ChainProgress.settle] at h
    obtain rfl := Except.ok.inj h
    exact List.prefix_refl _
  | b :: bs, z, z', h => by
    rw [ChainProgress.settle] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact List.prefix_refl _
    · obtain ⟨cols, -, h⟩ := of_bind_ok h
      exact (List.prefix_append z.cols cols).trans (settle_cols_prefix L bs _ z' h)

theorem heard_cols {L : Lay} {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} {d : Fmt.Drawn}
    (h : z.heard L s x d = .ok z') : z.cols <+: z'.cols := by
  unfold ChainProgress.heard at h
  obtain ⟨m', -, h⟩ := of_bind_ok h
  have c := settle_cols_prefix L _ _ z' h
  exact c

theorem walk_cols_prefix (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' → z.cols <+: z'.cols
  | [], [], z, z', h => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    exact List.prefix_refl _
  | s :: ss, d :: ds, z, z', h => by
    rw [walk] at h
    obtain ⟨x, -, h⟩ := of_bind_ok h
    obtain ⟨z₁, h1, h⟩ := of_bind_ok h
    exact (heard_cols h1).trans (walk_cols_prefix L ss ds z₁ z' h)
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h

/-! ## 5 At every round -/

/-- **Before any round of a chain**: the walk up to that round returns a state at which `ChainProgress.Inv`
holds and whose columns are a prefix of the chain's columns at its end. -/
theorem walk_at (L : Lay) (front : List OpenedColumn) : ∀ (ss₁ : List (Step W Y)) (ds₁ : List Fmt.Drawn)
    (s : Step W Y) (d : Fmt.Drawn) (ss₂ : List (Step W Y)) (ds₂ : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), ss₁.length = ds₁.length → z.Inv front →
    walk L (ss₁ ++ s :: ss₂) (ds₁ ++ d :: ds₂) z = .ok z' →
    ∃ z₁, walk L ss₁ ds₁ z = .ok z₁ ∧ z₁.Inv front ∧ z₁.cols <+: z'.cols
  | [], [], s, d, ss₂, ds₂, z, z', _, hz, h =>
    ⟨z, by rw [walk], hz, walk_cols_prefix L _ _ z z' h⟩
  | a :: ss₁, e :: ds₁, s, d, ss₂, ds₂, z, z', hl, hz, h => by
    have h' : walk L (a :: (ss₁ ++ s :: ss₂)) (e :: (ds₁ ++ d :: ds₂)) z = .ok z' := h
    rw [walk] at h'
    obtain ⟨x, hx, h'⟩ := of_bind_ok h'
    obtain ⟨z₀, h0, h'⟩ := of_bind_ok h'
    obtain ⟨z₁, w1, i1, c1⟩ := walk_at L front ss₁ ds₁ s d ss₂ ds₂ z₀ z'
      (Nat.succ.inj hl) (heard_inv hz h0) h'
    refine ⟨z₁, ?_, i1, c1⟩
    rw [walk, hx]
    show (z.heard L a x e).bind _ = _
    rw [h0]
    exact w1
  | [], _ :: _, _, _, _, _, _, _, hl, _, _ => by cases hl
  | _ :: _, [], _, _, _, _, _, _, hl, _, _ => by cases hl

/-- `ChainProgress.Inv`, read at `m.shown`, which is what `Step.tell` hands the part (by its text,
Frame.lean; no statement here names `Step.tell`). -/
theorem say_opened {front : List OpenedColumn} {z : ChainProgress S Cl W Y} {m : Mid W Y} (hz : z.Inv front)
    (hm : z.mid = some m) : m.shown.opened = some (front ++ z.cols) := hz m hm

/-! ## 6 The three chains of a run -/

/-- **The three walks of a run of `runC`, by name**: what `ready` returns, the three starts and the
three walks AT `runC`'s OWN TERMS, each as an equation; `ChainProgress.Inv` at each start; and the chains'
columns at their ends are the columns of the run's three views. -/
theorem runC_views {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {c : Coins B} {ρ : Draws} {r : RunC F} (h : runC F B H w₀ rc x c ρ = .ok r) :
    ∃ (R : Ready W₀ Rc Xi Ky Tr X₀ X)
      (a₁ z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X) (a₂ z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀)
      (a₃ z₃ : ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X),
      ready F B H w₀ rc x c = .ok R ∧
      ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
        (some (F.start₁ (F.pub x))) [] = .ok a₁ ∧
      walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first a₁ = .ok z₁ ∧
      sealQuiet z₁.laid = true ∧
      ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
        (some (F.start₂ (F.pub x))) [] = .ok a₂ ∧
      walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared a₂ = .ok z₂ ∧
      ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
        (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
        (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols) = .ok a₃ ∧
      walk ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ R.second ρ.second a₃ =
        .ok z₃ ∧
      a₁.Inv [] ∧ a₂.Inv [] ∧ a₃.Inv (z₁.cols ++ z₂.cols) ∧
      r.run.views.1.opened = z₁.cols ∧ r.run.views.2.1.opened = z₂.cols ∧
      r.run.views.2.2.opened = z₃.cols := by
  unfold runC at h
  obtain ⟨R, hR, h⟩ := of_bind_ok h
  obtain ⟨a₁, s1, h⟩ := of_bind_ok h
  obtain ⟨z₁, w1, h⟩ := of_bind_ok h
  split at h
  · cases h
  · rename_i hq
    obtain ⟨a₂, s2, h⟩ := of_bind_ok h
    obtain ⟨z₂, w2, h⟩ := of_bind_ok h
    obtain ⟨a₃, s3, h⟩ := of_bind_ok h
    obtain ⟨z₃, w3, rfl⟩ := map_ok h
    have hq' : sealQuiet z₁.laid = true := by
      cases e : sealQuiet z₁.laid with
      | true => rfl
      | false =>
        rw [e] at hq
        exact absurd rfl hq
    exact ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, s1, w1, hq', s2, w2, s3, w3, start_inv s1, start_inv s2,
      start_inv s3, rfl, rfl, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.of_bind_ok
#print axioms ProofFile.Honest.map_ok
#print axioms ProofFile.Honest.hear_opened
#print axioms ProofFile.Honest.settle_inv
#print axioms ProofFile.Honest.start_inv
#print axioms ProofFile.Honest.heard_inv
#print axioms ProofFile.Honest.walk_inv
#print axioms ProofFile.Honest.settle_cols_prefix
#print axioms ProofFile.Honest.heard_cols
#print axioms ProofFile.Honest.walk_cols_prefix
#print axioms ProofFile.Honest.walk_at
#print axioms ProofFile.Honest.say_opened
#print axioms ProofFile.Honest.runC_views
#print axioms ProofFile.Honest.ChainProgress.Inv
