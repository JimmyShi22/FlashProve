-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/LeftIsBack.lean: kind K5: THE CONVERSE OF leftP_spec (Johnson/Desc/First/Att/K5LeftAll.lean): whatever record l meets LeftIs g zk h F l
is what leftP g zk h F returns. So LeftIs is leftP's return, an iff.

Main names: optMapM_of (the converse of optMapM_spec) · leftP_of_is · leftP_iff · ptsFrom_of_is.
For whom: a law that holds LeftIs and pointsOf's return as premises, and must meet a seat's reading, which calls leftP.
IS IT EMPTY HERE? No: an iff. LeftIs is shown of nothing here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5LeftAll
import Johnson.Desc.First.Att.RunsK

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts)

theorem optMapM_of {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β),
    List.Forall₂ (fun a b => f a = some b) l bs → l.mapM f = some bs
  | [], _, .nil => rfl
  | a :: l, _, .cons (b := b) (l₂ := bs) h1 h2 => by
    rw [List.mapM_cons, h1, Option.bind_eq_bind, Option.bind_some, optMapM_of f l bs h2]
    rfl

variable {g : Geo} {zk : Array (Array E)} {h : Heard} {F : Fork} {l : Left}

/-- **What meets LeftIs is what leftP returns.** -/
theorem leftP_of_is (a : P.LeftIs g zk h F l) : P.leftP g zk h F = some l := by
  obtain ⟨wl, g3, n1, n2, g5, g6, g7, g8, g9, g10⟩ := a.rest
  unfold P.leftP
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  refine ⟨(), by simp [a.nUnits], l.scores, ?_, wl, g3, (), by rw [n1, n2]; simp, l.division, g5, l.below, g6, l.on, g7,
    l.atIndex, g8, l.key, g9, l.cells, g10, rfl⟩
  rw [Array.mapM_eq_mapM_toList]
  refine Option.map_eq_some_iff.2 ⟨l.scores.toList, optMapM_of _ _ _ (a.scores.imp fun u f hu => ?_), by simp⟩
  obtain ⟨W, w1, w2⟩ := hu
  exact Option.bind_eq_some_iff.2 ⟨W, w1, w2⟩

theorem leftP_iff : P.leftP g zk h F = some l ↔ P.LeftIs g zk h F l := ⟨P.leftP_spec, leftP_of_is⟩

/-- So the kind's road from what was heard returns what pointsOf makes of l. -/
theorem ptsFrom_of_is {p : Pts} (a : P.LeftIs g zk h F l) (hp : P.pointsOf g zk h l = some p) :
    P.ptsFrom g zk h F = some p := by
  unfold P.ptsFrom
  exact Option.bind_eq_some_iff.2 ⟨l, leftP_of_is a, hp⟩

end K5Law

#print axioms K5Law.leftP_of_is
#print axioms K5Law.leftP_iff
#print axioms K5Law.ptsFrom_of_is
