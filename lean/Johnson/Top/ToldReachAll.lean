-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/ToldReachAll.lean: TWO ENUMERATIONS THAT COVER THE WHOLE SPACE OF THE HONEST COMMITTER'S
COINS. Definitions, statements and proofs; general.

Why. Johnson/Top/ToldReach.lean shows that every pair out of the committer's two enumerations is
reached by a number. How much that is hangs on the enumerations. Here are two that cover all: every
member of a finite type; every choice of salts as far as the tree over the encoded index reads it.

Main names (namespace `VerifiableInference.OnPublicFiles`).
  `enumAll β`, `enumAll_onto`: the enumeration of a finite type that is not empty, by a numbering of
    it; it is onto (`Enum.ofNum_ok`, Iop/WireOK.lean).
  `saltsOfBits d s f`, `saltsAll d s`: the salts that are s bits at each of the first 2^d places, as
    f says, and no bits beyond; the enumeration of all of these.
  `enumAll_once`, `saltsAll_once`: each lists every one of its values ONCE. `pair_once`: two numbers
    below the product of the lengths with the same two remainders are one. So, with `reach_pair`,
    numbers below the product, pairs of places, and pairs of values stand ONE TO ONE.
  **`saltsAll_covers`**: whatever salts σ have s bits at each of the first 2^d places: some entry
    agrees with σ at all these places.
  **`committerTreeRoot_congr`**: the tree over a word (`committerTreeRoot`, Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean) reads
    the salts at the first 2^depth places alone.

Limits.
- THE ENUMERATIONS ARE PICKED BY CHOICE (`Exists.choose`; beneath it `Fintype.equivFin`): these
  enumerations are witnesses for how far a theorem reaches; they are no algorithm, and no committer
  that runs can be made of them.
- Salts of another length than s at one of these places are not covered. (The verifier refuses an
  opening whose salt has not the length that it asks: Compile/Bcs.lean. That is not used here.)
- In `committerAtFixedCoins` the salts enter the key through the tree alone, and stand besides in what the
  committer keeps: seen at its text, not restated here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ToldReach
import Iop.WireOK

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- A finite type that is not empty has an enumeration that lists each member once. -/
theorem exists_enumAll (β : Type) [Fintype β] [Nonempty β] : ∃ e : Enum β, e.OK :=
  ⟨Enum.ofNum β (Fintype.equivFin β), Enum.ofNum_ok β (Fintype.equivFin β)⟩

/-- All members of a finite type that is not empty: one such enumeration, picked by choice. (So its
length is a name and no number that Lean could set out to compute: at the types meant here it has
more digits than can be written.) -/
def enumAll (β : Type) [Fintype β] [Nonempty β] : Enum β := (exists_enumAll β).choose

theorem enumAll_onto (β : Type) [Fintype β] [Nonempty β] : Function.Surjective (enumAll β).e :=
  (exists_enumAll β).choose_spec.2

/-- It lists each member once. -/
theorem enumAll_once (β : Type) [Fintype β] [Nonempty β] : Function.Injective (enumAll β).e :=
  (exists_enumAll β).choose_spec.1

/-- Salts of s bits at each of the first 2^d places, no bits beyond. -/
def saltsOfBits (d s : ℕ) (f : Fin (2 ^ d) → Fin s → Bool) : ℕ → Bits :=
  fun j => if h : j < 2 ^ d then List.ofFn (f ⟨j, h⟩) else []

/-- All of these. -/
def saltsAll (d s : ℕ) : Enum (ℕ → Bits) where
  n := (enumAll (Fin (2 ^ d) → Fin s → Bool)).n
  e := fun c => saltsOfBits d s ((enumAll (Fin (2 ^ d) → Fin s → Bool)).e c)

/-- It lists each of these once. -/
theorem saltsAll_once (d s : ℕ) : Function.Injective (saltsAll d s).e := by
  intro c c' h
  apply enumAll_once (Fin (2 ^ d) → Fin s → Bool)
  funext j
  have hj : saltsOfBits d s ((enumAll (Fin (2 ^ d) → Fin s → Bool)).e c) j.val =
      saltsOfBits d s ((enumAll (Fin (2 ^ d) → Fin s → Bool)).e c') j.val := congrFun h j.val
  unfold saltsOfBits at hj
  rw [dif_pos j.isLt, dif_pos j.isLt] at hj
  exact List.ofFn_injective hj

/-- **Every choice of salts of the right length is covered, as far as the first 2^d places go.** -/
theorem saltsAll_covers (d s : ℕ) (σ : ℕ → Bits) (hσ : ∀ j, j < 2 ^ d → (σ j).length = s) :
    ∃ c, ∀ j, j < 2 ^ d → (saltsAll d s).e c j = σ j := by
  obtain ⟨c, hc⟩ := enumAll_onto (Fin (2 ^ d) → Fin s → Bool)
    (fun j k => (σ j.val).getD k.val false)
  refine ⟨c, fun j hj => ?_⟩
  show saltsOfBits d s ((enumAll (Fin (2 ^ d) → Fin s → Bool)).e c) j = σ j
  rw [hc]
  unfold saltsOfBits
  rw [dif_pos hj]
  apply List.ext_getElem
  · rw [List.length_ofFn, hσ j hj]
  · intro k h₁ h₂
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ h₂

/-- **Each pair has one number**: two numbers below (p + 1) (q + 1) with the same two remainders are
one. With `reach_pair` (Johnson/Top/ToldReach.lean): the numbers below the product and the pairs of
places stand one to one. -/
theorem pair_once (p q n n' : ℕ) (hn : n < (p + 1) * (q + 1)) (hn' : n' < (p + 1) * (q + 1))
    (h₁ : n % (p + 1) = n' % (p + 1))
    (h₂ : n / (p + 1) % (q + 1) = n' / (p + 1) % (q + 1)) : n = n' := by
  have d : n / (p + 1) < q + 1 := Nat.div_lt_of_lt_mul hn
  have d' : n' / (p + 1) < q + 1 := Nat.div_lt_of_lt_mul hn'
  rw [Nat.mod_eq_of_lt d, Nat.mod_eq_of_lt d'] at h₂
  rw [← Nat.div_add_mod n (p + 1), ← Nat.div_add_mod n' (p + 1), h₁, h₂]

/-- **The tree reads the salts at its leaves' places alone.** -/
theorem committerTreeRoot_congr {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (b₀ : Bd) (y : Fin L.wordLength → L.Symbol)
    (σ σ' : ℕ → Bits) (h : ∀ j, j < 2 ^ W.depth → σ j = σ' j) :
    committerTreeRoot W b₀ y σ = committerTreeRoot W b₀ y σ' := by
  have e : (List.range (2 ^ W.depth)).map (committerLeafInput W b₀ y σ) =
      (List.range (2 ^ W.depth)).map (committerLeafInput W b₀ y σ') :=
    List.map_congr_left fun j hj => by
      unfold committerLeafInput
      rw [h j (List.mem_range.1 hj)]
  unfold committerTreeRoot
  rw [e]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.enumAll_onto
#print axioms VerifiableInference.OnPublicFiles.enumAll_once
#print axioms VerifiableInference.OnPublicFiles.saltsAll_once
#print axioms VerifiableInference.OnPublicFiles.pair_once
#print axioms VerifiableInference.OnPublicFiles.saltsAll_covers
#print axioms VerifiableInference.OnPublicFiles.committerTreeRoot_congr
