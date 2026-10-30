-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyPinsRide.lean: What rides along PinsStay (Johnson/Desc/Key/KeyLetters.lean): at
two records that give one sample at the seats of l, and one record of the stored table: hasSmp ·
NoColl · FreeAt FORWARD; and the three clauses of onAt that read the reading, in one lemma. (BACK,
for PIN and PINW: rides_pin2_at | rides_pinT2_at, Johnson/Desc/Key/KeyQuiet.lean.) Theorems; no
definition. General in the chain.

Why. A row's proof is to NAME PIN | NoColl | hasSmp | PINW | Member and not to unfold them: Johnson/Desc/Msg.lean turns (enc a relation). THIS FILE OPENS THEM: NoColl by its binders, hasSmp and FreeAt by
unfolding. Msg.lean's turn falls here, on no row that only names them. Johnson/Desc/Key/KeySendRow.lean:71, Johnson/RunOne/KeyRows2225.lean:112 and others unfold hasSmp.

  PinsStay.hasSmp          one value at both records
  PinsStay.noColl | freeAt in front ⟹ behind
  PinsStay.onAt            from onAt in front: the book-keeping behind and the last letter behind give onAt behind, where «unmarked» is True at both and the pinned messages are those of l on both sides

Nothing on soundness.
-/
import Johnson.Desc.Key.KeyLetters
import Johnson.Desc.Key.KeyOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open VerifiableInference.Desc

section
variable {Xi P S Cells M Smp Rec : Type} (F : FileDescription Xi) {G : Reading (P × S) Cells M Smp Rec} {at_ : Where} {l : List Nat} {u v : P × S}

theorem PinsStay.hasSmp (h : PinsStay G at_ l u v) (k : Nat) (hk : k ∈ l) :
    hasSmp G (at_ k).1 (at_ k).2 v = hasSmp G (at_ k).1 (at_ k).2 u := by
  unfold VerifiableInference.Desc.hasSmp
  rw [h.smp k hk]

theorem PinsStay.noColl (h : PinsStay G at_ l u v) (k : Nat) (hk : k ∈ l) (y : Strs)
    (hn : NoColl F G (at_ k).1 (at_ k).2 u y) : NoColl F G (at_ k).1 (at_ k).2 v y :=
  fun o s ho hs => hn o s ho ((h.smp k hk).symm.trans hs)

theorem PinsStay.freeAt (h : PinsStay G at_ l u v) (coll : Strs → Rec → Prop) (y : Strs) (hf : FreeAt G coll u y) : FreeAt G coll v y := by
  obtain ⟨r, h1, h2⟩ := hf
  exact ⟨r, h.recOf.trans h1, h2⟩

/-- **The promise, forward**, but for its book-keeping and its last letter. -/
theorem PinsStay.onAt (h : PinsStay G at_ l u v) (Mg : KMeaning P S (Wit Cells Unit M)) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop)
    (O O' : List KItem) (y : Strs) (hO : pinned O = l) (hO' : pinned O' = l) (hu : Mg.unmarked u)
    (hs : shape u.2 = true → shape' v.2 = true) (hf : shape u.2 = true → free u y → free' v y)
    (hon : onAt F G at_ Mg shape free O u y) : onAt F G at_ Mg shape' free' O' v y := by
  rcases hon with hn | ⟨h1, h2, h3, h4⟩
  · exact absurd hu hn
  · refine Or.inr ⟨hs h1, ?_, hf h1 h3, ?_⟩
    · rw [hO']
      rw [hO] at h2
      refine List.all_eq_true.2 fun k hk => ?_
      rw [h.hasSmp k hk]
      exact List.all_eq_true.1 h2 k hk
    · intro k hk
      rw [hO'] at hk
      exact h.noColl F k hk y (h4 k (by rw [hO]; exact hk))

end

end VerifiableInference.Desc.Key
