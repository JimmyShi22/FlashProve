-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/JoinKeeps.lean: A FIELD OF THE CARRIED RECORD THAT EVERY RUN OF A LINK
KEEPS IS KEPT BY THE LINK's TWO MOVES: the duty `MoveKeeps f`
(Johnson/Desc/First/Batch/Law/KeepsField.lean) at the moves of a segment that the driver makes
(`moves₁ L rl`, `moves₂ L`: LinkJoinRuns.lean), FROM ONE DUTY AN ENTRY OF THE ORDER. Theorems:
tools.

Why. KeepsField.lean's `join_keeps` and `join_marks` («a mark stays» at the joining's three pieces)
take `MoveKeeps f` of every move. It pays that duty at the moves of a list of steps. A link's own
first move is the link's gatherer, its second the frame's function behind the batching: these are
reached here.

What is said.
  `claimsInBy_keep`, `afterIn_keep`, `runBehind_keep`: the gatherer, the runs behind the batching
    and the frame's function keep f, if each run does. `moves_keepL`: **`MoveKeeps f` of every move
    of `moves₁ L rl ++ moves₂ L`**, from one duty an entry of the order (`At`) and one an entry of
    the order behind (`AtAfter`).

Limits. Tools. That a run of the protocol keeps a field is its kind's law's to show. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.LinkJoinPay
import Johnson.Desc.First.Batch.Law.KeepsField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks

variable {α β : Type} (f : S → β)

/-- The link's gatherer keeps f, if each run that the order names does. -/
theorem claimsInBy_keep (each : ℕ × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (ℕ × String))
    (hr : ∀ r ∈ runsIn bs order, ∀ n e c e₁, r.2 n e = .ok (c, e₁) → f e₁ = f e) :
    MoveKeeps f (.add (claimsInBy each bs order)) := by
  intro e c e₁ h
  exact gather_keep f (fun _ => []) [] (runsIn bs order) hr ([], e) (c, e₁)
    (fold_gstep each bs order ([], e) (c, e₁) h)

/-- The runs behind the batching keep f, if each does. -/
theorem afterIn_keep (bs : List (Block S Claim)) (order : List (ℕ × String))
    (hq : ∀ o ∈ order, ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
      ∀ e e₁, run e = .ok e₁ → f e₁ = f e) (e e₁ : S) (h : afterIn bs order e = .ok e₁) :
    f e₁ = f e := by
  have hR := afterIn_ran bs order e e₁ h
  clear h
  induction hR with
  | nil e => rfl
  | cons o l run e e' e₁ hl hr _ ih =>
    exact (ih fun o' ho' => hq o' (List.mem_cons_of_mem _ ho')).trans
      (hq o (List.mem_cons_self ..) run hl e e' hr)

/-- The same of the frame's function. -/
theorem runBehind_keep (L : Link S Claim)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → f e₁ = f e) :
    MoveKeeps f (.quiet L.runBehind) :=
  fun e e₁ h => afterIn_keep f L.hear L.orderAfter hq e e₁ (Link.afterIn_of_runBehind h)

/-- **THE DUTY OF A LINK's TWO MOVES, FROM ONE DUTY AN ENTRY.** -/
theorem moves_keepL (L : Link S Claim) (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E))
    (hp : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → f e₁ = f e) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := α) L, MoveKeeps f m.move := by
  intro m hm
  rcases List.mem_append.1 hm with hm | hm
  · obtain rfl := List.mem_singleton.1 hm
    refine claimsInBy_keep f L.each L.hear L.order fun r hr => ?_
    obtain ⟨o, ho, h2⟩ := List.mem_filterMap.1 hr
    cases hl : ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) with
    | none =>
      rw [hl] at h2
      exact nomatch h2
    | some run =>
      rw [hl] at h2
      obtain rfl := Option.some.inj h2
      exact hp o ho run hl
  · obtain rfl := List.mem_singleton.1 hm
    exact runBehind_keep f L hq

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.claimsInBy_keep
#print axioms VerifiableInference.Desc.LinkJoin.afterIn_keep
#print axioms VerifiableInference.Desc.LinkJoin.runBehind_keep
#print axioms VerifiableInference.Desc.LinkJoin.moves_keepL
