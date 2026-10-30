-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Fill.lean: the columns that declared rounds read are filled, with
no stored run to fall back on, wherever each stored table that the rounds declare is available at
every position in range, and each tree that they open is available, with the declared widths
(`filled`). The lemma is general in the rounds, the challenges and the look-ups. It gives the clause
on `fillCols` in `Good.plays` (Honest/Side.lean) and in `Passes` (Honest/Law/Thread.lean), from two
conditions on the available tables.

  `fillCols_ok`     if every read has words of the declared width, the columns are filled
  `reads_at_hand`   the reads of declared rounds have such words, if every column, at each position
                    in range, of each stored table that the rounds declare, and each tree that
                    they open, is available with the declared width
  `filled`          the two together

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Fmt.Rules6Laws
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

theorem fillCols_ok : ∀ q : List Read, (∀ r ∈ q, ∃ u, r.words = some u ∧ u.length = r.width) →
    ∃ c, fillCols q [] = .ok c
  | [], _ => ⟨[], rfl⟩
  | r :: rs, h => by
    obtain ⟨u, hu, hl⟩ := h r List.mem_cons_self
    obtain ⟨c, hc⟩ := fillCols_ok rs fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    refine ⟨(r.key, r.pos, u) :: c, ?_⟩
    simp [fillCols, hu, hl, hc, Except.map]

section
variable (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
  (tree : Fmt.TreeSource → Option (Place × Table))

theorem reads_at_hand : ∀ (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    (∀ d ∈ zs, (∀ s ∈ d.stored, ∀ x, x < 2 ^ s.sh.a →
        ∃ u, stored s.item x = some u ∧ u.length = s.sh.W) ∧
      ∀ o ∈ d.opens, ∃ pt, tree o.2 = some pt ∧ pt.2.words = o.1.W) →
    ∀ r ∈ readsOf chain ft stored tree zs ds, ∃ u, r.words = some u ∧ u.length = r.width
  | [], _, _, r, hr => by simp [readsOf] at hr
  | _ :: _, [], _, r, hr => by simp [readsOf] at hr
  | d :: zs, R :: ds, h, r, hr => by
    have hr' : r ∈ (d.stored.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
          (⟨Fmt.storedKey s.item, x, some s.item, none, none, stored s.item x, s.sh.W⟩ : Read)) ++
      (d.opens.flatMap fun o =>
        (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
          (⟨o.1.tree - ft, x, none, some (srcOf chain o.2), (tree o.2).map (·.1),
            (tree o.2).map (·.2.col x), o.1.W⟩ : Read)) ++
      readsOf chain ft stored tree zs ds := hr
    obtain ⟨h1, h2⟩ := h d List.mem_cons_self
    rcases List.mem_append.1 hr' with hr' | hr'
    · rcases List.mem_append.1 hr' with hr' | hr'
      · obtain ⟨s, hs, hx⟩ := List.mem_flatMap.1 hr'
        obtain ⟨x, hx', rfl⟩ := List.mem_map.1 hx
        have hx'' := (Fmt.listOf_mem _ x).1 hx'
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx''
        exact h1 s hs _ (Nat.mod_lt _ (Nat.two_pow_pos _))
      · obtain ⟨o, ho, hx⟩ := List.mem_flatMap.1 hr'
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hx
        obtain ⟨pt, hpt, hw⟩ := h2 o ho
        refine ⟨pt.2.col x, ?_, ?_⟩
        · show (tree o.2).map (·.2.col x) = _
          rw [hpt]
          rfl
        · show (pt.2.col x).length = o.1.W
          rw [← hw]
          exact List.length_ofFn
    · exact reads_at_hand zs ds (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) r hr'

/-- **The columns are filled**, wherever every column, at each position in range, of each stored
table that the rounds declare, and each tree that they open, is available with the declared width.
The challenges do not occur in the hypothesis. -/
theorem filled (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn)
    (h : ∀ d ∈ zs, (∀ s ∈ d.stored, ∀ x, x < 2 ^ s.sh.a →
        ∃ u, stored s.item x = some u ∧ u.length = s.sh.W) ∧
      ∀ o ∈ d.opens, ∃ pt, tree o.2 = some pt ∧ pt.2.words = o.1.W) :
    ∃ c, fillCols (readsOf chain ft stored tree zs ds) [] = .ok c :=
  fillCols_ok _ (reads_at_hand chain ft stored tree zs ds h)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.fillCols_ok
#print axioms ProofFile.Honest.reads_at_hand
#print axioms ProofFile.Honest.filled
