-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSmp.lean: smpY AND ITS WALK: proofs of the statements that
Johnson/Desc/K14/Law/LedgerSmpOwed.lean lays as
propositions by def. In the
pattern of msgY (Johnson/Desc/K14/Law/LedgerNew.lean), line for line.

THE SIX OF THE WALK:
  smpSeat       sampleL reads of a seat its shape and its number alone
  smpOfPart     smpY stands where (shape, sampled, sampleRows) at the number stand
  smpHands      HandsOn for a test with smpY beside it, where the sending's decision earns it
  smpHandsAt    the like in the form HandsAt, where the sending's piece earns it
  smpOnGu, smpOnGomega   the two proximity tests hand it on
Helpers: sampleL_of_part (sampleL reads of a message its mark and its sample rows alone) · smpY_iff.
NOT HERE: SmpEarnAtOwed · SmpEarnOwed (or its refutation).
(SmpEarnAtOwed is proved in Johnson/Desc/K14/Law/LedgerSmpEarn.lean: smpEarnAt. No theorem of this
tree has the type SmpEarnOwed.)

IS IT EMPTY? The six are implications at all letters. smpHands | smpHandsAt take the earning at the
sending as a premise: whether anybody can meet it is the two statements that are not here.
Nothing on soundness.
-/
import Johnson.Desc.K14.Law.LedgerSmpOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt)
open VerifiableInference.Desc.K12 (P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Coin (onGu_leaves onGomega_leaves)
open Desc.K14.Law.Fence (keepsSmp_k14)

/-- **sampleL reads of a seat its shape and its number alone.** -/
theorem smpSeat : SmpSeatOwed := by
  intro cs m m' x h1 h2
  unfold H2K.Pin.sampleL
  rw [h1, h2]

/-- sampleL reads of a message its mark and its sample rows alone. -/
theorem sampleL_of_part (cs : Codes) (m : H2K.First.Seat1) (x x' : OnBytes.Oracle)
    (e2 : x'.sampled = x.sampled) (e3 : x'.sampleRows = x.sampleRows) :
    H2K.Pin.sampleL cs m x' = H2K.Pin.sampleL cs m x := by
  unfold H2K.Pin.sampleL
  rw [e2, e3]

theorem smpY_iff (cs : Codes) (sh : OracleShape) (o k₀ k : ℕ) (s : St) :
    smpY cs sh o k₀ k s = true ↔
      k ≤ k₀ ∨ ∃ x, s.st.oracles[o]? = some x ∧
        H2K.Pin.ok (H2K.Pin.sampleL cs (seatY sh o) x) = true := by
  unfold smpY
  rw [Bool.or_eq_true, decide_eq_true_iff]
  refine or_congr_right ?_
  cases s.st.oracles[o]? with
  | none => simp
  | some x => simp

/-- **What a reader of a sample reads of a message stands: so does smpY.** -/
theorem smpOfPart : SmpOfPartOwed := by
  intro cs sh o k₀ j k hj d d' e hx
  obtain ⟨x, h1, h2⟩ := ((smpY_iff cs sh o k₀ j d).1 hx).resolve_left (by omega)
  rw [h1, Option.map_some] at e
  obtain ⟨x', hx', ex⟩ := Option.map_eq_some_iff.1 e
  have e2 : x'.sampled = x.sampled := congrArg (·.2.1) ex
  have e3 : x'.sampleRows = x.sampleRows := congrArg (·.2.2) ex
  exact (smpY_iff cs sh o k₀ k d').2
    (Or.inr ⟨x', hx', by rw [sampleL_of_part cs _ x x' e2 e3]; exact h2⟩)

/-- **Earned at the sending (a premise), it is handed on by every later block of the kind.** -/
theorem smpHands : SmpHandsOwed := by
  intro cs Q b1 b2 b3 b4 b5 b6 b7 b8 hbl X hX i₀ n K inFront groups behind _ hblk base _ k _ h6
    hearn
  refine ⟨fun i b hi hb d d' rs gs h hxy => ?_, fun s z hxy => ?_, fun s hxy => ?_⟩
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    refine Bool.and_eq_true_iff.2 ⟨hX.step i b hi hb d d' rs gs h hx, ?_⟩
    by_cases h3 : i + 2 ≤ i₀ + 1
    · exact (smpY_iff _ _ _ _ _ d').2 (Or.inl h3)
    by_cases h4 : i = i₀
    · subst h4
      obtain rfl : sendAt Q n K inFront groups behind = b := Option.some.inj (hblk.symm.trans hb)
      exact hearn d d' rs gs h hx
    · have ks := keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) d d' rs gs h
      obtain ⟨x, h1, _⟩ := ((smpY_iff _ _ _ _ _ d).1 hy).resolve_left (by omega)
      exact smpOfPart _ _ _ _ (i + 1) (i + 2) (by omega) d d'
        (ks.2.2 _ (Array.getElem?_eq_some_iff.1 h1).1) hy
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    exact Bool.and_eq_true_iff.2 ⟨hX.zeta s z hx,
      (smpY_iff _ _ _ _ 8 _).2 (Or.inr (((smpY_iff _ _ _ _ 7 s).1 hy).resolve_left (by omega)))⟩
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    exact Bool.and_eq_true_iff.2 ⟨hX.last s hx,
      (smpY_iff _ _ _ _ 12 s).2 (Or.inr (((smpY_iff _ _ _ _ 11 s).1 hy).resolve_left (by omega)))⟩

/-- **The like at the pieces, inside the promise.** -/
theorem smpHandsAt : SmpHandsAtOwed := by
  intro P₁ Cl Cells Tok Fr cs Q b1 b2 b3 b4 b5 b6 b7 b8 hbl on X hX sh o i₀ b₀ hb₀ _ h6 hon hearn
  refine ⟨fun i b hi hb c hc hr x hx a τ y ha hout => Bool.and_eq_true_iff.2
    ⟨hX.step i b hi hb c hc hr x hx a τ y ha hout, ?_⟩, fun s z h => ?_, fun s h => ?_⟩
  · by_cases h3 : i + 2 ≤ i₀ + 1
    · exact (smpY_iff _ _ _ _ _ _).2 (Or.inl h3)
    by_cases h4 : i = i₀
    · subst h4
      obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
      exact hearn c hc hr x hx a τ y ha hout
    · obtain ⟨rs, gs, hd⟩ := held_yes x c hx a τ y hout
      rw [hc] at hd
      have ks := keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) _ _ rs gs hd
      have hy := hon (i + 1) a ha
      obtain ⟨x0, h1, _⟩ := ((smpY_iff _ _ _ _ _ a.1.2).1 hy).resolve_left (by omega)
      exact smpOfPart _ _ _ _ (i + 1) (i + 2) (by omega) a.1.2 y.1.2
        (ks.2.2 _ (Array.getElem?_eq_some_iff.1 h1).1) hy
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    exact Bool.and_eq_true_iff.2 ⟨hX.zeta s z h1,
      (smpY_iff _ _ _ _ 8 _).2 (Or.inr (((smpY_iff _ _ _ _ 7 s).1 h2).resolve_left (by omega)))⟩
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    exact Bool.and_eq_true_iff.2 ⟨hX.last s h1,
      (smpY_iff _ _ _ _ 12 s).2 (Or.inr (((smpY_iff _ _ _ _ 11 s).1 h2).resolve_left (by omega)))⟩

/-- **The test on G_u hands smpY on**, where the first mask is not that message. -/
theorem smpOnGu : SmpOnGuOwed := by
  intro cs sh o k₀ h9 p he ha d d' rs gs h hm hx
  obtain ⟨x, h1, _⟩ := ((smpY_iff cs sh o k₀ 9 d).1 hx).resolve_left (by omega)
  exact smpOfPart cs sh o k₀ 9 10 h9 d d'
    ((onGu_leaves p he ha d d' rs gs h).2.1 o (Array.getElem?_eq_some_iff.1 h1).1 hm) hx

/-- **The test on G_omega hands smpY on.** -/
theorem smpOnGomega : SmpOnGomegaOwed := by
  intro cs sh o k₀ h9 p he ha d d' rs gs h hx
  obtain ⟨x, h1, _⟩ := ((smpY_iff cs sh o k₀ 10 d).1 hx).resolve_left (by omega)
  exact smpOfPart cs sh o k₀ 10 11 h9 d d'
    ((onGomega_leaves p he ha d d' rs gs h).2.1 o (Array.getElem?_eq_some_iff.1 h1).1) hx

end Desc.K14.Law

#print axioms Desc.K14.Law.smpSeat
#print axioms Desc.K14.Law.smpOfPart
#print axioms Desc.K14.Law.smpHands
#print axioms Desc.K14.Law.smpHandsAt
#print axioms Desc.K14.Law.smpOnGu
#print axioms Desc.K14.Law.smpOnGomega
