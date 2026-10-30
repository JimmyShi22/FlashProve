-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/CarryOverReply.lean: the code switch: «carry» RIDES OVER THE
SUB-PROTOCOL THAT ENTERS THE HEAD (the reply's block, with the head's own first step in front of
it): the closed sentence carryAtZ (CarryClosed.lean) says the same at the state in front and at the
state behind.
  carry_over_reply   where the item is spent at a place of the sort .head: s, in front, is outside a
                     link and not yet at the head; t, behind, stands in the head's front, unopened;
                     s0 is what the head's own first step K2.headFrontQ tl makes of s, at whatever
                     plan tl of the smallness test it is seated; t has s0's front, book and roots:
                     then carryAtZ Z lay m (z, s) y w' ↔ carryAtZ Z lay m (z, t) y w
  carry_over_reply_stands  the same, with where s and t stand said as standOf s = .between and
                     standOf t = .headFront
HOW. Behind, the way in doorZ hands t itself. In front it runs the head's first step at the blank
plan: CarryReads.lean's doorZ_head (over headFrontQ_tl) says that this costs nothing; carryRow_reads
carries the sentence from s0 to t along the three equations. WHO PAYS THE PREMISES. h0, hfr, hb, hr:
place_front (Kinds/Law/ReplyFront.lean: its
conclusion, to the letter AS REPORTED: NOT READ HERE). h1,
h2: the promise in front and behind (DoorOfPromise.lean's stand_of_promise) with two closed facts on
the written places: First/Borders.lean's standAt says «between» at the head's segment's piece 1 and
«the head's front» at its piece 2 [by reading]. hs: a closed fact on ProofFile.pAtK2.
LIMITS. The sentence reads nothing of the witness, so w and w' are free. Nothing on whether the
sentence holds anywhere. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.CarryReads
import Johnson.Top.H0.K2Caller.DoorOfPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Strs)

/-- **«carry» says the same in front of and behind the sub-protocol that enters the head.** s: the
state in front. t: the state behind. s0: what the head's own first step makes of s. -/
theorem carry_over_reply {P W : Type} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ)
    (hs : (ProofFile.pAtK2 Z m).stands = .head) (z : P) (s t s0 : VerifiableInference.Desc.First.S)
    (tl : OnBytes.Model.HTailF2) (hout : s.inLink = false) (hnh : ∀ a, s.here ≠ .head a)
    (h0 : K2.headFrontQ tl s = .ok s0) (hfr : ∀ p, K2.frontAt p t = K2.frontAt p s0)
    (hb : t.book = s0.book) (hr : t.roots = s0.roots)
    (hth : ∃ a, t.here = .head a ∧ a.opened = false) (y : Strs) (w w' : W) :
    carryAtZ Z lay m (z, s) y w' ↔ carryAtZ Z lay m (z, t) y w := by
  have hdt : doorZ Z m t = some t := by
    obtain ⟨a, ha, ho⟩ := hth
    unfold doorZ
    rw [hs]
    simp only [ha, ho]
    rfl
  have h0' : K2.headFrontQ tl (rest s) = .ok s0 := by rw [rest_out s hout]; exact h0
  rw [carryAtZ_iff, carryAtZ_iff]
  constructor
  · rintro ⟨r, t1, hrow, hd, hok, hc⟩
    obtain ⟨t', hd', hi⟩ := doorZ_head (r := r) (H := r.ok_says hok)
      (K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z)) (smpK2 r (r.ok_says hok)) Z m s s0 hs hnh tl h0'
    obtain rfl : t' = t1 := Option.some.inj (hd'.symm.trans hd)
    exact ⟨r, t, hrow, hdt, hok, (carryRow_reads _ _ _ t s0 y (hfr _) hb hr).2 ((hi y).1 hc)⟩
  · rintro ⟨r, t1, hrow, hd, hok, hc⟩
    obtain rfl : t = t1 := Option.some.inj (hdt.symm.trans hd)
    obtain ⟨t', hd', hi⟩ := doorZ_head (r := r) (H := r.ok_says hok)
      (K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z)) (smpK2 r (r.ok_says hok)) Z m s s0 hs hnh tl h0'
    exact ⟨r, t', hrow, hd', hok, (hi y).2 ((carryRow_reads _ _ _ t s0 y (hfr _) hb hr).1 hc)⟩

/-- The same, with where the two states stand said in the table of joints' own words (the promise's
shapeAt gives both: DoorOfPromise.lean's stand_of_promise). -/
theorem carry_over_reply_stands {P W : Type} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ)
    (hs : (ProofFile.pAtK2 Z m).stands = .head) (z : P) (s t s0 : VerifiableInference.Desc.First.S)
    (tl : OnBytes.Model.HTailF2) (h1 : VerifiableInference.Desc.First.standOf s = .between)
    (h2 : VerifiableInference.Desc.First.standOf t = .headFront)
    (h0 : K2.headFrontQ tl s = .ok s0) (hfr : ∀ p, K2.frontAt p t = K2.frontAt p s0)
    (hb : t.book = s0.book) (hr : t.roots = s0.roots) (y : Strs) (w w' : W) :
    carryAtZ Z lay m (z, s) y w' ↔ carryAtZ Z lay m (z, t) y w := by
  obtain ⟨o1, o2⟩ := out_of_between s h1
  obtain ⟨o3, a, ha⟩ := out_of_headFront t h2
  have ho : a.opened = false := by
    unfold VerifiableInference.Desc.First.S.inLink VerifiableInference.Desc.First.S.fork? at o3
    rw [ha] at o3
    cases hb' : a.opened with
    | false => rfl
    | true => simp [hb'] at o3
  exact carry_over_reply Z lay m hs z s t s0 tl o1 o2 h0 hfr hb hr ⟨a, ha, ho⟩ y w w'

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.carry_over_reply_stands

#print axioms VerifiableInference.Desc.First.K2Caller.carry_over_reply
