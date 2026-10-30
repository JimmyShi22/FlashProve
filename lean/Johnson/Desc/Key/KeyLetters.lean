-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/KeyLetters.lean: THE KEY FILE's TABLES: PREMISES ON THE LETTERS THAT EVERY ROW's LAW MEETS, NAMED ONCE. Definitions, general in the chain, and three small lemmas. No binder of a table turns.
  PinsStay G at_ l u v     at the seats of the messages of l the reading gives ONE SAMPLE at the records u and v, and one record of the stored table. WHO MEETS IT: every block that turns the record while pins are open (a sending: at the ELDER pins; book-keeping: at all). The last chain's
                           files' SamePinsAt (not in this library) is this at l := [0, 2, 4]; SamePins (KeyFrames.lean) is this at every seat.
  LayIdem G                a table laid over itself is itself: G.lay j t m m = m. True at a filling whose «if» has two equal arms; proved at famLay's filling (layIdem_famLay, Johnson/Desc/Key/KeyFillLay.lean); a letter in Msg.lean. WHO MEETS IT: whoever lays one table as a message AND as its pad.
  LaysSeat at_ l w         the witness w holds, for each message k of l, ONE table as message k and as the pad at k's seat. WHO MEETS IT: a map on witnesses at a row that closes a pin.
  msgOf_of_laysSeat        PROVED: then what PIN k pins at w is w.msg k
  reads_of_laysSeat        PROVED: and, under ReadsPinned, what the rows read of k at w is w.msg k
WHERE THE OTHER NAMES STAND: SameLaws (KeyMeaning23.lean: R.same is a congruence for + and ·; sameLaws_of_read: at «ρ x = ρ y») · CellOnly (KeyKeeps23.lean: coll reads of the strings the stored cells alone: so it rides past every sending) · AtOk (KeyRows23At.lean: at_ against the books' offsets;
a member: atOk_member) · PlanOk (KeyAtFkMore.lean: the plan's two maps are inverse at I and V; planOk₁) · ArrOk | ReadsPinned | Placed (KeyTies.lean) · SmReads | SmGroups (on the readings' member: KeyOneReading.lean | KeyLettersAt.lean).
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyTies

set_option autoImplicit false

namespace VerifiableInference.Desc.Key

/-- **At the seats of l the two records give one sample, and one record of the stored table.** -/
structure PinsStay {A Cells M Smp Rec : Type} (G : Reading A Cells M Smp Rec) (at_ : Where) (l : List Nat) (u v : A) : Prop where
  smp : ∀ k ∈ l, G.smp v (at_ k).1 (at_ k).2 = G.smp u (at_ k).1 (at_ k).2
  recOf : G.recOf v = G.recOf u

theorem PinsStay.mono {A Cells M Smp Rec : Type} {G : Reading A Cells M Smp Rec} {at_ : Where} {l l' : List Nat} {u v : A} (h : PinsStay G at_ l u v) (hl : ∀ k ∈ l', k ∈ l) :
    PinsStay G at_ l' u v := ⟨fun k hk => h.smp k (hl k hk), h.recOf⟩

/-- **A table laid over itself is itself.** -/
def LayIdem {A Cells M Smp Rec : Type} (G : Reading A Cells M Smp Rec) : Prop := ∀ j t m, G.lay j t m m = m

/-- **The witness holds one table as message k and as the pad at k's seat.** -/
def LaysSeat {Cells M : Type} (at_ : Where) (l : List Nat) (w : Wit Cells Unit M) : Prop := ∀ k ∈ l, w.pad (at_ k).1 (at_ k).2 = w.msg k

theorem msgOf_of_laysSeat {A Cells M Smp Rec : Type} (G : Reading A Cells M Smp Rec) (at_ : Where) (l : List Nat) (w : Wit Cells Unit M) (ha : ArrOk G at_ l) (hi : LayIdem G)
    (hw : LaysSeat at_ l w) : ∀ k ∈ l, msgOf G w (at_ k).1 (at_ k).2 = w.msg k := fun k hk => by
  unfold msgOf
  rw [ha k hk, hw k hk]
  exact hi _ _ _

theorem reads_of_laysSeat {A Cells M Smp Rec : Type} (G : Reading A Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (l : List Nat) (w : Wit Cells Unit M) (ha : ArrOk G at_ l)
    (hr : ReadsPinned G at_ R l) (hi : LayIdem G) (hw : LaysSeat at_ l w) : ∀ k ∈ l, R.of w k = w.msg k := fun k hk =>
  (hr w k hk).trans (msgOf_of_laysSeat G at_ l w ha hi hw k hk)

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.PinsStay.mono
#print axioms VerifiableInference.Desc.Key.msgOf_of_laysSeat
#print axioms VerifiableInference.Desc.Key.reads_of_laysSeat
