-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/HKTHear.lean: two fields of the public record Pub34, and half of a third, from a run
of the layers' whole hearing.

Johnson/Road/Rows/LayerEnds34.lean gathers in a record Pub34 what is public once a layer sub-proof's
own messages have been heard. Three of its fields speak of the second token sumcheck: hT (its record
is there), hKT (the form KT is the equation that its rounds leave, asked for without the summand,
times -1 / eps) and hinv (the reading takes -1 / eps times eps to -1). Its head says of hKT: "by
reading: no theorem of this library concludes it from a run".
OnBytes/Desc/First/K4/HearLaws.lean (`hearTerms_KT`) concludes hT, hKT and the test "coin-zero" from
a run of one stretch, `hearTerms`. Pub34's letter H is what the WHOLE hearing returns. This file
carries the three there.

Main theorems (namespace `Meaning.HKT`).
  `hear_cut`: a run of `hearFl` (OnBytes/Desc/First/K4/Plain.lean) holds a run of `hearNorms` from
      the same ledger and tape, then a run of `hearTerms`, whose value is the field H of what
      `hearFl` returns.
  `hear_KT`: so hT, hKT and "eps's three words are not all 0" hold at that field H.
  `hinv_gl`: hinv in the library's field (`Reading.gl`), from that test AND: eps's words are below
      p.
  `coinZero_not_enough`: the second premise cannot be dropped. The test compares words with 0; the
      element with the words (p, 0, 0) passes it and reads as 0.

Limits. Identities on data: nothing on what KT is worth, on a draw, on soundness. That eps's words
are below p is a premise here; Johnson/Meaning/HKTDrawn.lean gets it from the tape. If the text of
`hear` turns, `hear_cut` is owed anew.
-/
import OnBytes.Desc.First.K4.HearLaws
import Johnson.Road.Rows.LayerEnds34Ref
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.HKT
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own HPlan2)
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (engFl hearFl hear hearTerms hearNorms andThen_some)

theorem bind_some {α β : Type} {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape}
    {r : β × Fork × Tape} (h : (x >>= f) F t = some r) :
    ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some r := andThen_some h

theorem pure_some {α : Type} {a b : α} {F G : Fork} {t u : Tape}
    (h : (pure a : Fl α) F t = some (b, G, u)) : b = a := by
  have h' : Fl.ret a F t = some (b, G, u) := h
  unfold Fl.ret at h'
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  exact h'.1.symm

theorem need_some {α : Type} {x : Option α} {a : α} {F G : Fork} {t u : Tape}
    (h : Fl.need x F t = some (a, G, u)) : G = F ∧ u = t := by
  unfold Fl.need at h
  obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.2.1.symm, e.2.2.symm⟩

/-- A run of the whole hearing, cut behind its first two stretches: the norms' messages are heard
from the ledger and the tape with which the hearing began, then the second token sumcheck; and what
that one returns is the field H of what the hearing returns. -/
theorem hear_cut {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, F', t')) :
    ∃ H0 F1 t1 F2 t2, hearNorms engFl P g fo F t = some (H0, F1, t1) ∧
      hearTerms engFl P H0 F1 t1 = some (o.H, F2, t2) := by
  unfold hearFl hear at h
  obtain ⟨_, Fa, ta, m1, h1⟩ := bind_some h
  clear h
  obtain ⟨_, ea, eb⟩ := Desc.First.K4.must_some m1
  rw [ea, eb] at h1
  obtain ⟨_, Fb, tb, m2, h2⟩ := bind_some h1
  clear h1
  obtain ⟨_, ec, ed⟩ := Desc.First.K4.must_some m2
  rw [ec, ed] at h2
  obtain ⟨iU3, Fc, tc, m3, h3⟩ := bind_some h2
  clear h2
  obtain ⟨ee, ef⟩ := need_some m3
  rw [ee, ef] at h3
  obtain ⟨H0, F1, t1, hN, h⟩ := bind_some h3
  clear h3
  obtain ⟨H, F2, t2, hT, h⟩ := bind_some h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨x, _, _, _, h⟩ := bind_some h
  obtain ⟨tab, laid, nU3⟩ := x
  dsimp only at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨K, _, _, _, h⟩ := bind_some h
  obtain ⟨⟨hd, hd2⟩, _, _, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨claimsP, _, _, _, h⟩ := bind_some h
  refine ⟨H0, F1, t1, F2, t2, hN, ?_⟩
  suffices e : o.H = H by rw [e]; exact hT
  split at h <;>
  · obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    rw [pure_some h]

/-- **hT and hKT of Pub34, and the test coin-zero, at what the whole hearing returns.** -/
theorem hear_KT {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, F', t')) :
    ∃ tT, o.H.tT = some tT ∧
      o.H.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)) ∧
      (!isZeroE tT.p.eps) = true := by
  obtain ⟨_, _, _, _, _, _, hT⟩ := hear_cut h
  exact Desc.First.K4.hearTerms_KT hT

/-- **hinv of Pub34 in the library's field**, from the test coin-zero and: eps has words below p. -/
theorem hinv_gl {eps : E} (ok : okE eps = true) (nz : (!isZeroE eps) = true) :
    Reading.gl.val (negE (invE eps)) * Reading.gl.val eps = -1 := by
  refine Road.Rows.hinv_of Road.gl_numerals ?_ (Road.Rows.gl_inv eps)
  intro h0
  have z : isZeroE eps = true := (Slice.isZeroE_iff eps ok).2 h0
  rw [z] at nz
  cases nz

/-- The premise on the words cannot be dropped: an element with a word equal to the prime passes the
test coin-zero and reads as 0. -/
theorem coinZero_not_enough :
    ∃ eps : E, (!isZeroE eps) = true ∧ Reading.gl.val eps = 0 := by
  refine ⟨OnBytes.ofF pW, by decide, ?_⟩
  show Slice.readE (OnBytes.ofF pW) = 0
  have z : Slice.toF pW = 0 := by
    rw [← Slice.toF_normF]
    have e : normF pW = 0 := by decide
    rw [e]
    have := Slice.readE_zero
    exact congrArg (·.c0) this
  rw [Slice.readE_ofF, z, map_zero]

#print axioms hear_cut
#print axioms hear_KT
#print axioms hinv_gl
#print axioms coinZero_not_enough

end Meaning.HKT
