-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SizesStretch.lean: THE LEDGER's SIZES, PULLED BACK OVER THE TEXTS OF THE STRETCH BETWEEN A SEGMENT's OWN KIND's SUB-PROTOCOL AND ITS BATCHING, ONE TEXT AT A
TIME: K1's later moment, K8, the layers' quiet step, the step without a round behind the digits, K11. Theorems on the decisions' texts.

Why. SizesBack.lean (beside this file) has the tool (`SameSizes`, `hideRun_sizes`) and the merge. The clauses of a link's Ok that step back further along «reached» (to 14 l + 6,
28 g + 5, 343) ask the ledger's sizes there. StretchParts.lean's steps (`back_k1_of`, `back_k8_of`, `back_readsL_of`, `back_k11_of`) are general in the relation R that is carried.

What is said.
  `SizesS s s'`: **THE RELATION**: where s' holds a ledger, s holds one, and the two have the same number of slots and the same three lengths. `.refl`, `.trans`.
  `SizesS.pulls`: so: a ledger open and `Sized` at s' ⊢ one open and `Sized` at s.
  `commitOne_sizes` .. `commitStep_sizes`: a commitment's frame marks arrays as received: it turns no length.
  `k1_sizesS`, `k8_sizesS`, `quietLayers_sizesS`, `k11_sizesS`: **the four texts' decisions keep SizesS: NO PREMISE ON THE SIZES.**
  `quietAt_sizesS`: so does the step without a round behind the lookup on the digits.
  `decides_and`: two relations that a decision keeps are kept together: so that ONE walk back carries SizesS beside another relation, at ONE earlier state.

Limits. ON THE DECISIONS ALONE. **K3's OWN HEARING IS NOT HERE**: left to the lookup's files. The attention's and the head's quiet steps at the sending of the reads are not here. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.SizesBack
import Johnson.Desc.First.Link.Law.StretchParts
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headClaimMergeKind)
open L3

/-- **Where s' holds a ledger, s holds one, of the same sizes.** -/
def SizesS (s s' : S) : Prop :=
  ∀ G', s'.fork? = some G' → ∃ G, s.fork? = some G ∧ SameSizes G G'

theorem SizesS.refl (s : S) : SizesS s s := fun G h => ⟨G, h, SameSizes.refl G⟩

theorem SizesS.trans (a b c : S) (h : SizesS a b) (k : SizesS b c) : SizesS a c := by
  intro H hH
  obtain ⟨G, hG, l2⟩ := k H hH
  obtain ⟨F, hF, l1⟩ := h G hG
  exact ⟨F, hF, l1.trans l2⟩

/-- Where the ledger is left as it is. -/
theorem SizesS.of_eq {s s' : S} (h : s'.fork? = s.fork?) : SizesS s s' := fun G hG =>
  ⟨G, h ▸ hG, SameSizes.refl G⟩

/-- **THE SIZES, PULLED BACK.** -/
theorem SizesS.pulls {s s' : S} (h : SizesS s s') (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ G, s.fork? = some G ∧ Sized G := by
  obtain ⟨G', hG', hz⟩ := hB
  obtain ⟨G, hG, k⟩ := h G' hG'
  exact ⟨G, hG, k.back hz⟩

/-- Two relations that a decision keeps are kept together. -/
theorem decides_and {Cl : Type} {R R' : S → S → Prop} {b : Block S Cl} (h : Decides R b)
    (k : Decides R' b) : Decides (fun s s' => R s s' ∧ R' s s') b :=
  fun s rs gs s' hd => ⟨h s rs gs s' hd, k s rs gs s' hd⟩

/-! ## K1's later moment -/

theorem commitOne_sizes (L : LinkCtx) (F F' : Fork) (t : ℕ) (h : commitOne L F t = .ok F') :
    SameSizes F F' := by
  unfold commitOne at h
  dsimp only at h
  split at h <;> split at h <;>
    first
      | (cases h; exact ⟨rfl, rfl, rfl, rfl⟩)
      | cases h

theorem commitFold_sizes (L : LinkCtx) (trees : List ℕ) : ∀ (F F' : Fork),
    trees.foldlM (commitOne L) F = .ok F' → SameSizes F F' := by
  induction trees with
  | nil =>
    intro F F' h
    cases h
    exact SameSizes.refl F
  | cons t l ih =>
    intro F F' h
    rw [List.foldlM_cons] at h
    obtain ⟨G, h1, h2⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
    exact (commitOne_sizes L F G t h1).trans (ih G F' h2)

theorem commitBehind_sizes (L : LinkCtx) (check : ChainCheck) (F : Fork) (trees : List ℕ)
    (y : LinkCtx × Fork) (h : commitBehind L check F trees = .ok y) : SameSizes F y.2 := by
  unfold commitBehind at h
  obtain ⟨G, h1, h2⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  split at h2
  · cases h2
    exact commitFold_sizes L trees F G h1
  · cases h2

theorem commitStep_sizes {W : Type} (send : Send W) (trees : List ℕ) (s s' : St W)
    (rs : List Fmt.RoundView) (h : commitStep send trees s rs = .ok s') : SameSizes s.F s'.F := by
  unfold commitStep at h
  obtain ⟨_, _, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  obtain ⟨⟨check, w⟩, _, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨⟨L', F'⟩, h2, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  cases h
  exact commitBehind_sizes _ _ _ _ _ h2

theorem commitAtS_sizes {Cl : Type} (P : K1.Par) (link moment : ℕ) (arrays : Option (List ℕ)) :
    Decides SizesS (K1.commitAtS (Cl := Cl) P link moment arrays) := by
  intro s rs gs s' h
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl hL hF htl
    obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
    subst h2
    intro G' hG'
    rw [First.fork_putFork _ F _ (by rw [First.fork_putLink]; exact hF)] at hG'
    obtain rfl := Option.some.inj hG'
    refine ⟨F, hF, ?_⟩
    simp only [K1.commitOwn] at h1
    split at h1
    · split at h1
      · cases h1
      · obtain ⟨x, g1, g2⟩ := Keeps.emap_ok h1
        subst g2
        exact commitStep_sizes _ _ _ _ _ g1
    · cases h1
  · cases h

/-- **K1's LATER MOMENT.** -/
theorem k1_sizesS (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Decides SizesS (K1.laterAt (Cl := Unit) q gp link piece moment arrays) :=
  fun s rs gs s' h => commitAtS_sizes _ _ _ _ s rs gs s' h

/-! ## K8, the layers' quiet step, K11, the step behind the digits -/

/-- **K8.** -/
theorem k8_sizesS (p : First.K8.ParW) : Decides SizesS (First.K8.whole p) :=
  fun s rs gs s' h => SizesS.of_eq (First.K8.hear_leaves_fork (Cl := Claim) p.toPar s rs gs s' h)

/-- **THE LAYERS' QUIET STEP.** -/
theorem quietLayers_sizesS (P : K8.ReadsQuiet.PG) : Decides SizesS (K8.ReadsQuiet.layers P) := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  refine SizesS.of_eq ?_
  simp [S.fork?, ha]

/-- **K11.** -/
theorem k11_sizesS (P : HeadMergeP) : Decides SizesS (headClaimMergeKind P) := by
  intro s rs _ s' h G' hG'
  obtain ⟨a, a', ha, ha', ho, ho', hz⟩ :=
    merge_sizes P (show headMergeDecide P s rs = .ok s' from h)
  have e : a'.F = G' := by simpa [S.fork?, ha', ho'] using hG'
  exact ⟨a.F, by simp [S.fork?, ha, ho], e ▸ hz⟩

/-- **THE STEP WITHOUT A ROUND BEHIND THE LOOKUP ON THE DIGITS.** -/
theorem quietAt_sizesS (X : Verify.Public) (i : ℕ) (f : S → Except String S)
    (hf : K3.quietAt X i true = some f) (s t : S) (h : f s = .ok t) : SizesS s t := by
  obtain ⟨F, c, hF, hG, -⟩ := VerifiableInference.OnPublicFiles.quietAt_ledger X i f hf s t h
  intro G' hG'
  obtain rfl := Option.some.inj (hG.symm.trans hG')
  exact ⟨F, hF, rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.SizesS.trans
#print axioms VerifiableInference.Desc.LinkJoin.SizesS.pulls
#print axioms VerifiableInference.Desc.LinkJoin.decides_and
#print axioms VerifiableInference.Desc.LinkJoin.commitStep_sizes
#print axioms VerifiableInference.Desc.LinkJoin.commitAtS_sizes
#print axioms VerifiableInference.Desc.LinkJoin.k1_sizesS
#print axioms VerifiableInference.Desc.LinkJoin.k8_sizesS
#print axioms VerifiableInference.Desc.LinkJoin.quietLayers_sizesS
#print axioms VerifiableInference.Desc.LinkJoin.k11_sizesS
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_sizesS
