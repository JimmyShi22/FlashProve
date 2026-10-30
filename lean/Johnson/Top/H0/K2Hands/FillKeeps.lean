-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FillKeeps.lean: DriverKeeps.lean's walk, carried from the driver's structure
`Blocks` to the list of sub-protocols from which the proof file's first chain is made
(Johnson/Desc/ProofFile/FillCore.lean: `fill`, `chainC`; Frames1.lean: `chainBy`). General in the
state, in the property P and in the property R of the rounds. A law file; no running text imports
it.

  `keepsRuns_andThen`   two sub-protocols as one: the runs are the two lists in a row.
  `fill_keeps`     `BlocksKeep R P (fill bs z fr)`, from the list's members that stand inside a
                   segment, the batching's makers, the two functions where a segment starts and
                   ends, and the first entry.
  `chainC_ok`      a chain that `chainC` returns is the driver's chain over `fill`.
  `chainBy_front`  a chain that `chainBy` returns has no entry between its first and its segments,
                   and every entry of `frontOf c` that passes its own test on the plan has
                   `KeepsD R P`: asked are the members of `base` that stand inside a segment and
                   pass their own tests on the plan, all of `fr`, and the batching's makers.
Limits. Nothing is asked, and nothing is said, of a member of `base` that stands outside the
segments. Nothing on any one property or kind. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.DriverKeeps
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Blocks ModelPart firstChain)
open Meaning.K2 (frontOf firstChain_noFront)

variable {σ Cl : Type} {R : Fmt.RoundView → Prop} {P : σ → Prop}

theorem keepsRuns_andThen (name : String) {p q : Block σ Cl} (hp : KeepsRuns P p)
    (hq : KeepsRuns P q) : KeepsRuns P (p.andThen name q) :=
  ⟨fun c hc => (List.mem_append.1 hc).elim (hp.1 c) (hq.1 c),
    fun c hc => (List.mem_append.1 hc).elim (hp.2 c) (hq.2 c)⟩

theorem fill_keeps {bs : List (Block σ Cl)} {z : Block σ Cl} {fr : ProofFile.Frames σ Cl}
    (hD : ∀ b ∈ bs, b.place.link ≠ none → b.planOk = true → KeepsD R P b)
    (hR : ∀ b ∈ bs, b.place.link ≠ none → b.place.kind ≠ KindName.K9 →
      b.place.kind ≠ KindName.K10 → KeepsRuns P b)
    (hB : ∀ a mk, fr.batch a = some mk →
      ∀ f : σ → Except String (List Cl × σ), (∀ s y, f s = .ok y → P s → P y.2) → KeepsD R P (mk f))
    (hl : ∀ l s s', fr.lay l s = .ok s' → P s → P s')
    (hc : ∀ l s s', fr.clear l s = .ok s' → P s → P s') (hf : KeepsD R P fr.first) :
    BlocksKeep R P (ProofFile.fill bs z fr) where
  blockD := fun a b ha h => by
    have h' : bs.find? (fun b => b.place == a) = some b := h
    have hp : b.place = a :=
      eq_of_beq (List.find?_some (p := fun b : Block σ Cl => b.place == a) h')
    exact hD b (List.mem_of_find?_eq_some h') (by rw [hp]; exact ha)
  blockR := fun a b ha h9 h10 h => by
    have h' : bs.find? (fun b => b.place == a) = some b := h
    have hp : b.place = a :=
      eq_of_beq (List.find?_some (p := fun b : Block σ Cl => b.place == a) h')
    exact hR b (List.mem_of_find?_eq_some h') (by rw [hp]; exact ha) (by rw [hp]; exact h9)
      (by rw [hp]; exact h10)
  batch := fun a mk ha h f hf hp => by
    have h' : (fr.batch a <|> (bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h
    cases hq : fr.batch a with
    | some m =>
      rw [hq] at h'
      obtain rfl : m = mk := Option.some.inj h'
      exact hB a m hq f hf
    | none =>
      rw [hq] at h'
      have h2 : ((bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h'
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h2
      have hq' : b.place = a :=
        eq_of_beq (List.find?_some (p := fun b : Block σ Cl => b.place == a) hb)
      exact hD b (List.mem_of_find?_eq_some hb) (by rw [hq']; exact ha) hp
  lay := hl
  clear := hc
  first := hf

theorem chainC_ok {bs : List (Block σ Cl)} {links : List ModelPart} {fr : ProofFile.Frames σ Cl}
    {c : Chain σ Cl} (h : ProofFile.chainC bs links fr = .ok c) :
    ∃ z several, firstChain (ProofFile.fill bs.dropLast z fr) links several = some c := by
  unfold ProofFile.chainC at h
  split at h
  · cases h
  · rename_i z _
    dsimp only at h
    split at h
    · cases h
    · rename_i c0 hc
      split at h
      · cases h
      · cases h
        exact ⟨z, _, hc⟩

/-- **The first chain that `chainBy` returns, in front of what stands behind its segments.** -/
theorem chainBy_front {σ : Type} {P : σ → Prop} {Z : ProofFile.Pub} {base : List (Block σ ProofFile.Cl)}
    {fr : List (ProofFile.FrameRole × Block σ ProofFile.Cl)} {road : ProofFile.Gather σ ProofFile.Cl}
    {c : Chain σ ProofFile.Cl} (h : ProofFile.chainBy Z base fr road = .ok c)
    (hD : ∀ b ∈ base, b.place.link ≠ none → b.planOk = true → KeepsD R P b)
    (hR : ∀ b ∈ base, b.place.link ≠ none → b.place.kind ≠ KindName.K9 →
      b.place.kind ≠ KindName.K10 → KeepsRuns P b)
    (hF : ∀ x ∈ fr, KeepsD R P x.2 ∧ KeepsRuns P x.2)
    (hB : ∀ a mk, road.batch a = some mk →
      ∀ f : σ → Except String (List ProofFile.Cl × σ), (∀ s y, f s = .ok y → P s → P y.2) →
        KeepsD R P (mk f)) :
    c.front = [] ∧ ∀ b ∈ frontOf c, b.planOk = true → KeepsD R P b := by
  unfold ProofFile.chainBy at h
  dsimp only at h
  obtain ⟨z, several, hc⟩ := chainC_ok h
  refine ⟨firstChain_noFront hc, firstChain_front (fill_keeps ?_ ?_ hB ?_ ?_ ?_) hc⟩
  · intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 (List.dropLast_subset _ hb)
    split
    · rename_i x hx
      exact fun hl hp => keepsD_andThen _ (hD b₀ hb₀ hl ((Bool.and_eq_true _ _ ▸ hp).1))
        (keepsD_guarded _ _ (hF x (List.mem_of_find?_eq_some hx)).1)
    · exact hD b₀ hb₀
  · intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 (List.dropLast_subset _ hb)
    split
    · rename_i x hx
      exact fun hl h9 h10 => keepsRuns_andThen _ (hR b₀ hb₀ hl h9 h10)
        (keepsRuns_guarded _ _ (hF x (List.mem_of_find?_eq_some hx)).2)
    · exact hR b₀ hb₀
  · intro l s s' hy hs
    dsimp only at hy
    split at hy
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hF x (List.mem_of_find?_eq_some hx)).1 s s' [] [] (fun _ hm => nomatch hm) hy hs
    · cases hy
      exact hs
  · intro l s s' hy hs
    dsimp only at hy
    split at hy
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hF x (List.mem_of_find?_eq_some hx)).1 s s' [] [] (fun _ hm => nomatch hm) hy hs
    · cases hy
      exact hs
  · dsimp only
    split
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact keepsD_under rfl (hF x (List.mem_of_find?_eq_some hx)).1
    · exact keepsD_quiet fun s s' hy hs => by
        cases hy
        exact hs

end VerifiableInference.Desc.Keeps1

#print axioms VerifiableInference.Desc.Keeps1.fill_keeps
#print axioms VerifiableInference.Desc.Keeps1.chainC_ok
#print axioms VerifiableInference.Desc.Keeps1.chainBy_front
