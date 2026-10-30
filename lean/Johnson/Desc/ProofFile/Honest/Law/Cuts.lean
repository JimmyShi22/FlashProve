-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Cuts.lean: small lemmas for whoever proves the hypotheses of the
rule for `Owed` at a file (Honest/Law/OwedRule.lean). The cut is unique: the hypotheses run over
every cut of a chain's flat list at a sub-protocol; where the description passes its test on the
places (`FileDescription.placesOk`) there is at most one. And what `InsideOf` (Honest/Law/Inside.lean) says
after no round.

  1  `cut_unique`, `places_nodup`, `cut_first`, `cut_shared`, `cut_second`   the cut is unique
  2  `insideOf_zero`   after no round

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Inside
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Pb Xi : Type}

/-! ## 1 The cut is unique -/

theorem cut_unique {α β : Type} (f : α → β) : ∀ (pre pre' : List α) (b : α) (t t' : List α),
    pre ++ b :: t = pre' ++ b :: t' → ((pre ++ b :: t).map f).Nodup → pre = pre' ∧ t = t'
  | [], [], _, _, _, h, _ => ⟨rfl, (List.cons.inj h).2⟩
  | [], c :: pre', b, t, t', h, hn => by
    have h' : b :: t = c :: (pre' ++ b :: t') := h
    obtain ⟨-, e2⟩ := List.cons.inj h'
    have hn' : (f b :: t.map f).Nodup := hn
    have hm : f b ∈ t.map f := by
      rw [e2]
      exact List.mem_map.2 ⟨b, List.mem_append_right _ List.mem_cons_self, rfl⟩
    exact absurd hm (List.nodup_cons.1 hn').1
  | c :: pre, [], b, t, t', h, hn => by
    have h' : c :: (pre ++ b :: t) = b :: t' := h
    obtain ⟨e1, -⟩ := List.cons.inj h'
    subst e1
    have hn' : (f c :: (pre ++ c :: t).map f).Nodup := hn
    have hm : f c ∈ (pre ++ c :: t).map f :=
      List.mem_map.2 ⟨c, List.mem_append_right _ List.mem_cons_self, rfl⟩
    exact absurd hm (List.nodup_cons.1 hn').1
  | c :: pre, c' :: pre', b, t, t', h, hn => by
    have h' : c :: (pre ++ b :: t) = c' :: (pre' ++ b :: t') := h
    obtain ⟨e1, e2⟩ := List.cons.inj h'
    have hn' : (f c :: (pre ++ b :: t).map f).Nodup := hn
    obtain ⟨g1, g2⟩ := cut_unique f pre pre' b t t' e2 (List.nodup_cons.1 hn').2
    exact ⟨by rw [e1, g1], g2⟩

theorem places_nodup {F : FileDescription Xi} (hp : F.placesOk = true) :
    (F.first.blocksInOrder.map (·.place)).Nodup ∧ (F.shared.blocksInOrder.map (·.place)).Nodup ∧
      (F.second.blocksInOrder.map (·.place)).Nodup := by
  have hn := orderOf_nodup hp
  unfold orderOf at hn
  obtain ⟨n12, n3, -⟩ := List.nodup_append.1 hn
  obtain ⟨n1, n2, -⟩ := List.nodup_append.1 n12
  exact ⟨n1, n2, n3⟩

section
variable {F : FileDescription Xi} (hp : F.placesOk = true)
include hp

theorem cut_first {pre pre' t t' : List (Block F.S₁ F.Cl)} {b : Block F.S₁ F.Cl}
    (h : F.first.blocksInOrder = pre ++ b :: t) (h' : F.first.blocksInOrder = pre' ++ b :: t') :
    pre = pre' ∧ t = t' :=
  cut_unique (·.place) pre pre' b t t' (h.symm.trans h') (by rw [← h]; exact (places_nodup hp).1)

theorem cut_shared {pre pre' t t' : List (Block F.S₂ F.Cl)} {b : Block F.S₂ F.Cl}
    (h : F.shared.blocksInOrder = pre ++ b :: t) (h' : F.shared.blocksInOrder = pre' ++ b :: t') :
    pre = pre' ∧ t = t' :=
  cut_unique (·.place) pre pre' b t t' (h.symm.trans h')
    (by rw [← h]; exact (places_nodup hp).2.1)

theorem cut_second {pre pre' t t' : List (Block F.S₃ F.Cl)} {b : Block F.S₃ F.Cl}
    (h : F.second.blocksInOrder = pre ++ b :: t) (h' : F.second.blocksInOrder = pre' ++ b :: t') :
    pre = pre' ∧ t = t' :=
  cut_unique (·.place) pre pre' b t t' (h.symm.trans h')
    (by rw [← h]; exact (places_nodup hp).2.2)

end

/-! ## 2 After no round -/

/-- After no round `InsideOf` says: the condition before the sub-protocol, at some state of the
verifier and at tables of which the available ones are `Env.add` of no round. -/
theorem insideOf_zero {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : Nat} {hs : List (Placed V W Y)}
    {b : Block S Cl} {A : Coins Bk → S → Mid W Y → Env → Prop} {k : Coins Bk} {m : Mid W Y}
    {E : Env} (h : InsideOf φ Bk chain hs b A 0 k m E) : ∃ s E₀, A k s m E₀ ∧ E = E₀.add [] := by
  obtain ⟨s, m₀, E₀, l, ds, y, hA, -, hd, hp, rfl, rfl⟩ := h
  have hds : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => simp [drawsFit] at hd
  subst hds
  have hp' : (Except.ok (([] : List Played), m₀) : Except Refusal (List Played × Mid W Y)) =
      .ok y := hp
  cases hp'
  exact ⟨s, E₀, hA, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.cut_unique
#print axioms ProofFile.Honest.places_nodup
#print axioms ProofFile.Honest.cut_first
#print axioms ProofFile.Honest.cut_shared
#print axioms ProofFile.Honest.cut_second
#print axioms ProofFile.Honest.insideOf_zero
