-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SameStored.lean: two implementations of typed oracles by one oracle on bit strings
read the same stored symbols under one root off one log in which no two strings have one answer, if
they spell stored leaves and vertices alike.

OnBytes/Slice/SameRead.lean has this for any two readings of a leaf query that agree on strings.
This file has the reading of the library's extractor `Compile.Batch.extEnc`: the stored table's
symbol in a leaf query, whatever the salt; and a handy way to meet the agreement, said on the
implementations' strings.

Main definitions.
 `storedSym`           the stored table's symbol in a leaf query, if it holds one.
 `SameStored m₁ m₂ u`  a vertex query on two digests has one string in both; a leaf query on a
                       stored table's symbol has one string in both, for every salt, also one that
                       no program would write. u matches the two interfaces' symbols.
Main theorems.
 `sameRead_of_stored`  `SameStored` gives `SameRead` at that reading.
 `extLeaf_same`        so the symbol at leaf j of the tree of depth d under a root is the same
                       through m₁ and through m₂, off a log without a clash.
 `extEnc_eq_storedSym` what `extEnc` keeps of the leaf query at a place is `storedSym` of it.
 `extEnc_same`         the strings that `extEnc` reads through both agree place by place, if the two
                       wirings have one depth and fill alike.

Why place by place. The two strings have the types `Fin L₁.wordLength → L₁.Symbol` and `Fin L₂.wordLength → L₂.Symbol`. Where
the two lengths are equal by a hypothesis only, these are two types, and an equation between the
strings cannot be written.

What is not claimed. That any two implementations meet `SameStored` (an instance:
OnBytes/Slice/SameStoredAt.lean). Of leaves of other kinds (a protocol's own symbols, padding)
nothing: the two may see different queries there, or one of them none. Nothing on any protocol,
language, checker or hash function; no probability.

-/
import OnBytes.Slice.SameRead

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch

section
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The stored table's symbol in a leaf query, if it holds one (the library's "symbol of an encoded
index": a body `some (.inl s)`). The salt is not looked at. -/
def storedSym (q : LeafIn L) : Option L.Symbol :=
  match q.body with
  | some (.inl s) => some s
  | _ => none

/-- `storedSym q` is s exactly if q's body is the stored table's symbol s. -/
theorem storedSym_eq_some (q : LeafIn L) (s : L.Symbol) :
    storedSym q = some s ↔ q = ⟨some (.inl s), q.salt⟩ := by
  obtain ⟨b, salt⟩ := q
  unfold storedSym
  constructor
  · intro h
    split at h
    · rename_i s' hb
      have hb' : b = some (.inl s') := hb
      rw [hb', Option.some.inj h]
    · cases h
  · intro h
    have hb : b = some (.inl s) := congrArg Batch.LeafIn.body h
    subst hb
    rfl

/-- What `extEnc` keeps of the leaf query at a place is `storedSym` of it. -/
theorem extEnc_eq_storedSym (W : QueryLayout lam L) (tr : Tc W) (cm : Dig lam) :
    extEnc W tr cm =
      W.B.ext.build fun q => (Batch.extLeaf tr W.depth cm q.val).bind storedSym := by
  unfold Batch.extEnc
  refine congrArg _ (funext fun q => ?_)
  rcases Batch.extLeaf tr W.depth cm q.val with _ | ⟨_ | (s | y), salt⟩ <;> rfl

end

variable {I₁ X₁ I₂ X₂ : Type} {lam K₁ K₂ : ℕ} {L₁ : BatchProtocol I₁ X₁} {L₂ : BatchProtocol I₂ X₂}

/-- **The two implementations spell stored leaves and vertices alike.** A vertex query on two
digests has one string in both. A leaf query on a stored table's symbol has one string in both, for
every symbol and EVERY salt. u matches the symbols of the two interfaces. Said for all numbers of
blocks j₁, j₂; under `OneBlock` there is one of each. -/
structure SameStored (m₁ : OracleCoding (spec lam K₁ L₁) lam) (m₂ : OracleCoding (spec lam K₂ L₂) lam)
    (u : L₁.Symbol ≃ L₂.Symbol) : Prop where
  node : ∀ (a b : Dig lam) j₁ j₂, m₁.code Batch.OracleName.node (List.ofFn a, List.ofFn b) j₁ =
    m₂.code Batch.OracleName.node (List.ofFn a, List.ofFn b) j₂
  stored : ∀ (x : L₁.Symbol) (salt : Bits) j₁ j₂, m₁.code Batch.OracleName.leaf ⟨some (.inl x), salt⟩ j₁ =
    m₂.code Batch.OracleName.leaf ⟨some (.inl (u x)), salt⟩ j₂

section
variable {m₁ : OracleCoding (spec lam K₁ L₁) lam} {m₂ : OracleCoding (spec lam K₂ L₂) lam}

/-- `SameStored` gives `SameRead` at the reading "the stored table's symbol, whatever the salt". -/
theorem sameRead_of_stored {u : L₁.Symbol ≃ L₂.Symbol} (h₁ : OneBlock m₁) (h₂ : OneBlock m₂)
    (h : SameStored m₁ m₂ u) :
    SameRead (fun _ q => (storedSym q).map u) (fun _ q => storedSym q) m₁ m₂ where
  node := fun s a b => by
    rw [inv_iff_code, inv_iff_code]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨⟨0, by rw [h₂.node1]; omega⟩, hk.trans (h.node _ _ _ _)⟩
    · rintro ⟨k, hk⟩
      exact ⟨⟨0, by rw [h₁.node1]; omega⟩, hk.trans (h.node _ _ _ _).symm⟩
  leaf := fun s _ y => by
    constructor
    · rintro ⟨q, k, hk, hy⟩
      obtain ⟨x, hx, hxy⟩ := Option.map_eq_some_iff.1 hy
      obtain ⟨k', hk'⟩ := (inv_iff_code m₁ s Batch.OracleName.leaf q).1 ⟨k, hk⟩
      rw [(storedSym_eq_some q x).1 hx] at hk'
      obtain ⟨k2, hk2⟩ := (inv_iff_code m₂ s Batch.OracleName.leaf ⟨some (.inl (u x)), q.salt⟩).2
        ⟨⟨0, by rw [h₂.leaf1]; omega⟩, hk'.trans (h.stored _ _ _ _)⟩
      exact ⟨_, k2, hk2, by rw [← hxy]; rfl⟩
    · rintro ⟨q, k, hk, hy⟩
      obtain ⟨k', hk'⟩ := (inv_iff_code m₂ s Batch.OracleName.leaf q).1 ⟨k, hk⟩
      rw [(storedSym_eq_some q y).1 hy] at hk'
      have hs := h.stored (u.symm y) q.salt ⟨0, by rw [h₁.leaf1]; omega⟩ k'
      rw [Equiv.apply_symm_apply] at hs
      obtain ⟨k2, hk2⟩ := (inv_iff_code m₁ s Batch.OracleName.leaf ⟨some (.inl (u.symm y)), q.salt⟩).2
        ⟨_, hk'.trans hs.symm⟩
      refine ⟨_, k2, hk2, ?_⟩
      show (some (u.symm y)).map u = some y
      rw [Option.map_some, Equiv.apply_symm_apply]

/-- **Two implementations that spell stored leaves and vertices alike read one symbol.** Off a log
in which no two strings have one answer, the stored table's symbol at leaf j of the tree of depth d
under the digest cm is the same through m₁ and through m₂ (matched by u); where the one finds none,
so does the other. Asked: `OneBlock` of both, `SameStored`, `NoClash`. Nothing says that any two
implementations meet `SameStored`. Of the whole strings built from the symbols: `extEnc_same`. No
probability. -/
theorem extLeaf_same {u : L₁.Symbol ≃ L₂.Symbol} (h₁ : OneBlock m₁) (h₂ : OneBlock m₂)
    (h : SameStored m₁ m₂ u) (σ : Trace (rom lam)) (hσ : NoClash σ) (d j : ℕ) (cm : Dig lam) :
    (Batch.extLeaf (singleTr m₁ σ) d cm j).bind (fun q => (storedSym q).map u) =
      (Batch.extLeaf (singleTr m₂ σ) d cm j).bind storedSym :=
  extLeaf_sameRead h₁ h₂ (sameRead_of_stored h₁ h₂ h) σ hσ d j cm

end

/-- **The strings under one root, through both, agree place by place.** Asked beside
`extLeaf_same`'s hypotheses: the two wirings have one depth; and their fillings (`build`) agree
where their inputs do. That the two strings have one length is neither asked nor said: a place that
one of them alone has is not compared. That any two wirings meet the two hypotheses is not shown
here (an instance: OnBytes/Slice/SameAt.lean). No probability. -/
theorem extEnc_same (W₁ : QueryLayout lam L₁) (W₂ : QueryLayout lam L₂) {m₁ : OracleCoding (spec lam W₁.K L₁) lam}
    {m₂ : OracleCoding (spec lam W₂.K L₂) lam} {u : L₁.Symbol ≃ L₂.Symbol} (h₁ : OneBlock m₁) (h₂ : OneBlock m₂)
    (h : SameStored m₁ m₂ u) (σ : Trace (rom lam)) (hσ : NoClash σ) (cm : Dig lam)
    (hd : W₁.depth = W₂.depth)
    (hb : ∀ (f₁ : Fin L₁.wordLength → Option L₁.Symbol) (f₂ : Fin L₂.wordLength → Option L₂.Symbol),
      (∀ q₁ q₂, q₁.val = q₂.val → (f₁ q₁).map u = f₂ q₂) →
      ∀ q₁ q₂, q₁.val = q₂.val → u (W₁.B.ext.build f₁ q₁) = W₂.B.ext.build f₂ q₂) :
    ∀ (q₁ : Fin L₁.wordLength) (q₂ : Fin L₂.wordLength), q₁.val = q₂.val →
      u (extEnc W₁ (singleTr m₁ σ) cm q₁) = extEnc W₂ (singleTr m₂ σ) cm q₂ := by
  intro q₁ q₂ hq
  rw [extEnc_eq_storedSym, extEnc_eq_storedSym]
  refine hb _ _ (fun p₁ p₂ hp => ?_) q₁ q₂ hq
  have e := extLeaf_same h₁ h₂ h σ hσ W₁.depth p₁.val cm
  rw [hd, hp] at e
  rw [← e, hd, hp]
  cases Batch.extLeaf (singleTr m₁ σ) W₂.depth cm p₂.val <;> rfl

end OnBytes.Slice
