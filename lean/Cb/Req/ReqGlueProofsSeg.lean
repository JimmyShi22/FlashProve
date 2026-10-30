-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqGlueProofsSeg.lean: the proofs of the statements of Cb/Req/ReqGlue.lean on segments and
partitions, from those on families (Cb/Req/ReqGlueProofs.lean).

Nothing is defined here that a statement reads, but `group`, which `mem_glued_keys` and `mem_group`
read.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqGlueProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset

section
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

open Classical in
/-- the families of keys with the table T -/
def group (S : SegSpec X F E) (T : Tab F) : List (Fam X E) :=
  (S.keys.filter fun k => decide (k.2 = T)).map (·.1)

omit [Field F] [Field E] [Algebra F E] in
theorem mem_group (S : SegSpec X F E) (T : Tab F) (f : Fam X E) :
    f ∈ group S T ↔ (f, T) ∈ S.keys := by
  classical
  unfold group
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hk
    have h3 : k.2 = T := of_decide_eq_true h2
    rw [← h3]
    exact h1
  · intro h
    exact List.mem_map.2 ⟨(f, T), List.mem_filter.2 ⟨h, decide_eq_true rfl⟩, rfl⟩

theorem mem_glued_keys (S : SegSpec X F E) (k : Fam X E × Tab F) :
    k ∈ S.glued.keys ↔
    (∃ f, (f, k.2) ∈ S.keys) ∧ k.1 = Fam.glue (algebraMap F E (k.2.t 0)) (group S k.2) := by
  classical
  show k ∈
      (S.keys.map (·.2)).dedup.map (fun T => (Fam.glue (algebraMap F E (T.t 0)) (group S T), T)) ↔
    _
  constructor
  · intro h
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 h
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hT)
    exact ⟨⟨k'.1, hk'⟩, rfl⟩
  · rintro ⟨⟨f, hf⟩, h2⟩
    refine List.mem_map.2 ⟨k.2, List.mem_dedup.2 (List.mem_map.2 ⟨(f, k.2), hf, rfl⟩), ?_⟩
    exact Prod.ext h2.symm rfl

theorem group_wf {S : SegSpec X F E} {Φ : IdxFmt F} (h : S.WF Φ) (T : Tab F) :
    ∀ f ∈ group S T, f.WF Φ :=
  fun f hf => h.2 (f, T) ((mem_group S T f).1 hf)

end

theorem glued_holds_iff : Spec.glued_holds_iff := by
  intro X F E _ _ _ S Φ x W A h
  refine and_congr ?_ ?_
  · show (∀ f ∈ [Fam.glue (0 : E) S.idn], ∀ b < 2 ^ f.v, f.val Φ x W A b = 0) ↔ _
    rw [List.forall_mem_singleton]
    exact glue_zero_iff X F E S.idn Φ x W A h.1
  · constructor
    · intro hg k hk
      have h1 := hg (Fam.glue (algebraMap F E (k.2.t 0)) (group S k.2), k.2)
        ((mem_glued_keys S _).2 ⟨⟨k.1, hk⟩, rfl⟩)
      exact (glue_key_iff X F E (group S k.2) k.2 Φ x W A (group_wf h k.2)).1
        h1 k.1 ((mem_group S k.2 k.1).2 hk)
    · intro hs k hk
      obtain ⟨-, h2⟩ := (mem_glued_keys S k).1 hk
      rw [h2]
      exact (glue_key_iff X F E (group S k.2) k.2 Φ x W A (group_wf h k.2)).2
        fun f hf => hs (f, k.2) ((mem_group S k.2 f).1 hf)

theorem glued_wf : Spec.glued_wf := by
  intro X F E _ _ _ S Φ h
  refine ⟨fun f hf => ?_, fun k hk => ?_⟩
  · obtain rfl := List.mem_singleton.1 hf
    exact glue_wf X F E S.idn 0 Φ h.1
  · obtain ⟨-, h2⟩ := (mem_glued_keys S k).1 hk
    rw [h2]
    exact glue_wf X F E _ _ Φ (group_wf h k.2)

theorem glued_places : Spec.glued_places := by
  intro X F E _ _ _ S Φ h
  ext p
  constructor
  · rintro (⟨f, hf, hp⟩ | ⟨k, hk, hp⟩)
    · obtain rfl := List.mem_singleton.1 hf
      exact Or.inl ((glue_places X F E S.idn 0 Φ h.1 p).1 hp)
    · obtain ⟨-, h2⟩ := (mem_glued_keys S k).1 hk
      rw [h2] at hp
      obtain ⟨f, hf, hp'⟩ := (glue_places X F E _ _ Φ (group_wf h k.2) p).1 hp
      exact Or.inr ⟨(f, k.2), (mem_group S k.2 f).1 hf, hp'⟩
  · rintro (⟨f, hf, hp⟩ | ⟨k, hk, hp⟩)
    · exact Or.inl ⟨_, List.mem_singleton.2 rfl, (glue_places X F E S.idn 0 Φ h.1 p).2 ⟨f, hf, hp⟩⟩
    · exact Or.inr
        ⟨(Fam.glue (algebraMap F E (k.2.t 0)) (group S k.2), k.2),
          (mem_glued_keys S _).2 ⟨⟨k.1, hk⟩, rfl⟩,
          (glue_places X F E _ _ Φ (group_wf h k.2) p).2 ⟨k.1, (mem_group S k.2 k.1).2 hk, hp⟩⟩

theorem glued_counts : Spec.glued_counts := by
  classical
  intro X F E _ _ _ S
  have h1 : S.glued.keys.map (·.2) = (S.keys.map (·.2)).dedup := by
    show ((S.keys.map (·.2)).dedup.map fun T =>
        (Fam.glue (algebraMap F E (T.t 0)) (group S T), T)).map (·.2) = _
    rw [List.map_map]
    exact List.map_id _
  refine ⟨rfl, ?_, fun T => ?_⟩
  · rw [h1]
    exact List.nodup_dedup _
  · rw [h1]
    exact List.mem_dedup

end Cb
