-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQLocal.lean: the protocol that is made from a chain's description has a local verifier,
whatever the decision on the untyped view: it depends on the prover's oracle messages only at the
positions that it reads.

Statements and proofs. Tools on this library's own terms; no text is rendered.
A description is a value of `Fmt.Spec` (Fmt/Rules8.lean). From its rounds' data (`PQ.rds S`,
Run/PlanQTypes.lean: for each round the plan's entry, kind, items, tree sent, trees opened)
Run/PlanQTypes.lean makes an interactive oracle protocol, without proof of work (`Q0`) and with it
(`QT`). Local is `InteractiveOracleProof.IsLocal` (Iop/InteractiveOracleProof.lean): the verifier's answer (`accept`) is the same at
two transcripts with the same verifier's messages and the same plain parts, and at two values of the
external oracles, that agree at the positions read.
Run/PlanQTypes.lean gives the decision an untyped view of a transcript: for each round the items
read and what was drawn; and the columns at the pairs (tree, position) that the drawn positions ask
for. The protocol's "reads" are these same pairs, as positions of the shape.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `rvL_congr`: the rounds' part of the view is a function of plain parts and verifier's messages.
  `Spec.view_congr`: the same verifier's messages, the same plain parts, the same symbols at the
    positions read: the same view.
  `Spec.q0_local`: `(Q0 C ds dec).IsLocal` (Iop/InteractiveOracleProof.lean), for every kit, every list of rounds'
    data, every decision.
  `Spec.qT_local`: the same with proof of work, of `QT C ds dec`.

Limits: this file does not say that the protocol is sound for anything.
Terms: lean/GLOSSARY.md.
-/
import Run.PlanQTypes
import Iop.GrindProofs

set_option autoImplicit false

namespace Run.PQ
open Iop

theorem rvL_congr (C : CK) :
    ∀ (ds : List RD) (τ τ' : Tr (shapeL C ds)),
      τ.rho = τ'.rho → τ.plains = τ'.plains → rvL C ds τ = rvL C ds τ'
  | [], _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), hρ, hp => by
      have e1 : c = c' := congrArg Prod.fst hρ
      have e2 : τ.rho = τ'.rho := congrArg Prod.snd hρ
      have e3 : m.2 = m'.2 := congrArg Prod.fst hp
      have e4 : τ.plains = τ'.plains := congrArg Prod.snd hp
      show (⟨PlainOf.gots d.items m.2, C.dr d.entry d.kind c⟩ : RV) :: rvL C ds τ =
        ⟨PlainOf.gots d.items m'.2, C.dr d.entry d.kind c'⟩ :: rvL C ds τ'
      rw [e1, e3, rvL_congr C ds τ τ' e2 e4]

theorem colAt_congr (C : CK) :
    ∀ (ds : List RD) (τ τ' : Tr (shapeL C ds)) (n x : Nat),
      (∀ p, posAt C ds n x = some p → τ.read p = τ'.read p) → colAt C ds τ n x = colAt C ds τ' n x
  | [], _, _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), n, x, h => by
      unfold colAt
      unfold posAt at h
      by_cases ht : d.tree.isSome = true
      · rw [if_pos ht, if_pos ht]
        rw [if_pos ht] at h
        by_cases hn : n = 0
        · rw [if_pos hn, if_pos hn]
          rw [if_pos hn] at h
          by_cases hx : x < posN d.tree
          · rw [dif_pos hx, dif_pos hx]
            rw [dif_pos hx] at h
            have e : m.1 ⟨x, hx⟩ = m'.1 ⟨x, hx⟩ := h _ rfl
            rw [e]
          · rw [dif_neg hx, dif_neg hx]
        · rw [if_neg hn, if_neg hn]
          rw [if_neg hn] at h
          refine colAt_congr C ds τ τ' (n - 1) x fun p hp => ?_
          exact h (.inr p) (by rw [hp]; rfl)
      · rw [if_neg ht, if_neg ht]
        rw [if_neg ht] at h
        refine colAt_congr C ds τ τ' n x fun p hp => ?_
        exact h (.inr p) (by rw [hp]; rfl)

namespace Spec

def view_congr : Prop :=
  ∀ (C : CK) (ds : List RD) (τ τ' : Tr (shapeL C ds)), τ.rho = τ'.rho → τ.plains = τ'.plains →
    (∀ nx ∈ wanted ds (drawnL C ds τ.rho),
      ∀ p, posAt C ds nx.1 nx.2 = some p → τ.read p = τ'.read p) →
    viewL C ds τ = viewL C ds τ'

def q0_local : Prop :=
  ∀ (Y : Type) (C : CK) (ds : List RD) (dec : Y → View → Bool), (Q0 C ds dec).IsLocal

def qT_local : Prop :=
  ∀ (Y : Type) (C : CK) (ds : List RD) (dec : Y → View → Bool), (QT C ds dec).IsLocal

end Spec

theorem filterMap_congr_mem {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
        filterMap_congr_mem f g l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem view_congr : Spec.view_congr := by
  intro C ds τ τ' hρ hp hr
  unfold viewL
  rw [rvL_congr C ds τ τ' hρ hp, ← hρ]
  congr 1
  refine filterMap_congr_mem _ _ _ fun nx hnx => ?_
  rw [colAt_congr C ds τ τ' nx.1 nx.2 (hr nx hnx)]

theorem q0_local : Spec.q0_local := by
  rintro Y C ds dec x y y' ⟨m0, c0, τ⟩ ⟨m0', c0', τ'⟩ hρ hp _ hr
  have e1 : τ.rho = τ'.rho := congrArg Prod.snd hρ
  have e2 : τ.plains = τ'.plains := congrArg Prod.snd hp
  show dec x (viewL C ds τ) = dec x (viewL C ds τ')
  rw [view_congr C ds τ τ' e1 e2 fun nx hnx p hpos => ?_]
  refine hr (Sum.inr p) ?_
  show (Sum.inr p : OPos (shapeOf C ds)) ∈
    (((wanted ds (drawnL C ds τ.rho)).filterMap fun nx =>
      (posAt C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (shapeOf C ds)))).toFinset
  rw [List.mem_toFinset, List.mem_filterMap]
  exact ⟨nx, hnx, by rw [hpos]; rfl⟩

theorem qT_local : Spec.qT_local := fun Y C ds dec => (q0_local Y C ds dec).grind (gOf C ds)

end Run.PQ
