-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSmpK.lean: smpK, smpY AT THE THREE MESSAGES: proofs of the four
statements that Johnson/Desc/K14/Law/LedgerSmpKOwed.lean lays as
propositions by def: the forms that XK's letter Y asks.


  smpKEarly      idle at the first three borders
  smpKHandsAt    HandsAt for smpK: earned at the pieces of "send o_u" and "send o_omega" (two
                 premises), kept else
  smpKOnGu, smpKOnGomega   the two proximity tests hand it on
Helpers: smpK_iff · smp_step (a piece of the kind's eight hands smpY on from i + 1 to i + 2, where
i + 1 is not the border behind which it is asked).

IS IT EMPTY? Implications at all letters. smpKHandsAt takes the two earnings as premises: smpEarnAt
(Johnson/Desc/K14/Law/LedgerSmpEarn.lean) is meant to meet them.
Nothing on soundness.
-/
import Johnson.Desc.K14.Law.LedgerSmpKOwed
import Johnson.Desc.K14.Law.LedgerSmp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12 (P12 proximityTestKind guardedProximityTestParts)
open Desc.K14.Law.Fence (keepsSmp_k14)

theorem smpK_iff (cs : Codes) (shU shO shS : OracleShape) (sU k : ℕ) (s : St) :
    smpK cs shU shO shS sU k s = true ↔
      (smpY cs shU 0 2 k s = true ∧ smpY cs shO sU 5 k s = true) ∧
        smpY cs shS (sU + 1) 5 k s = true := by
  unfold smpK
  rw [Bool.and_eq_true, Bool.and_eq_true]

/-- **Idle at the first three borders.** -/
theorem smpKEarly : SmpKEarlyOwed := by
  intro cs shU shO shS sU k s hk
  exact (smpK_iff cs shU shO shS sU k s).2
    ⟨⟨(smpY_iff _ _ _ _ _ _).2 (Or.inl hk), (smpY_iff _ _ _ _ _ _).2 (Or.inl (by omega))⟩,
      (smpY_iff _ _ _ _ _ _).2 (Or.inl (by omega))⟩

/-- A piece of the kind's eight hands smpY on, where it is not the one that earns it. -/
theorem smp_step {P₁ Cl Cells Tok : Type} {Fr : Frame} (cs : Codes) (Q : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (i : ℕ) (b : Block St Unit)
    (hb : [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b) (c : Block St Cl) (hc : DecidesAs c b)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW c)
    (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some y) (sh : OracleShape) (o k₀ : ℕ) (hne : i + 1 ≠ k₀)
    (h : smpY cs sh o k₀ (i + 1) a.1.2 = true) : smpY cs sh o k₀ (i + 2) y.1.2 = true := by
  by_cases h3 : i + 2 ≤ k₀
  · exact (smpY_iff _ _ _ _ _ _).2 (Or.inl h3)
  obtain ⟨rs, gs, hd⟩ := held_yes x c hx a τ y hout
  rw [hc] at hd
  have ks := keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) _ _ rs gs hd
  obtain ⟨x0, h1, _⟩ := ((smpY_iff _ _ _ _ _ a.1.2).1 h).resolve_left (by omega)
  exact smpOfPart _ _ _ _ (i + 1) (i + 2) (by omega) a.1.2 y.1.2
    (ks.2.2 _ (Array.getElem?_eq_some_iff.1 h1).1) h

/-- smpY does not read z_fd. -/
theorem smpY_zeta (cs : Codes) (sh : OracleShape) (o k₀ : ℕ) (h6 : k₀ < 7) (s : St) (z : List E)
    (h : smpY cs sh o k₀ 7 s = true) :
    smpY cs sh o k₀ 8 { s with loc := { s.loc with zFd := z } } = true :=
  (smpY_iff _ _ _ _ 8 _).2 (Or.inr (((smpY_iff _ _ _ _ 7 s).1 h).resolve_left (by omega)))

theorem smpY_last (cs : Codes) (sh : OracleShape) (o k₀ : ℕ) (h6 : k₀ < 11) (s : St)
    (h : smpY cs sh o k₀ 11 s = true) : smpY cs sh o k₀ 12 s = true :=
  (smpY_iff _ _ _ _ 12 s).2 (Or.inr (((smpY_iff _ _ _ _ 11 s).1 h).resolve_left (by omega)))

/-- **HandsAt for smpK.** -/
theorem smpKHandsAt : SmpKHandsAtOwed := by
  intro P₁ Cl Cells Tok Fr cs Q b1 b2 b3 b4 b5 b6 b7 b8 hbl on shU shO shS sU hon hU hO
  refine ⟨fun i b _ hb c hc hr x hx a τ y ha hout => ?_, fun s z h => ?_, fun s h => ?_⟩
  · obtain ⟨⟨kU, kO⟩, kS⟩ := (smpK_iff _ _ _ _ _ _ _).1 (hon (i + 1) a ha)
    refine (smpK_iff _ _ _ _ _ _ _).2 ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h1 : i = 1
      · subst h1
        obtain rfl : b2 = b := Option.some.inj hb
        exact hU c hc hr x hx a τ y ha hout
      · exact smp_step cs Q b1 b2 b3 b4 b5 b6 b7 b8 hbl i b hb c hc x hx a τ y hout _ _ _
          (by omega) kU
    · by_cases h4 : i = 4
      · subst h4
        obtain rfl : b5 = b := Option.some.inj hb
        exact (hO c hc hr x hx a τ y ha hout).1
      · exact smp_step cs Q b1 b2 b3 b4 b5 b6 b7 b8 hbl i b hb c hc x hx a τ y hout _ _ _
          (by omega) kO
    · by_cases h4 : i = 4
      · subst h4
        obtain rfl : b5 = b := Option.some.inj hb
        exact (hO c hc hr x hx a τ y ha hout).2
      · exact smp_step cs Q b1 b2 b3 b4 b5 b6 b7 b8 hbl i b hb c hc x hx a τ y hout _ _ _
          (by omega) kS
  · obtain ⟨⟨kU, kO⟩, kS⟩ := (smpK_iff _ _ _ _ _ _ _).1 h
    exact (smpK_iff _ _ _ _ _ _ _).2 ⟨⟨smpY_zeta _ _ _ _ (by omega) s z kU,
      smpY_zeta _ _ _ _ (by omega) s z kO⟩, smpY_zeta _ _ _ _ (by omega) s z kS⟩
  · obtain ⟨⟨kU, kO⟩, kS⟩ := (smpK_iff _ _ _ _ _ _ _).1 h
    exact (smpK_iff _ _ _ _ _ _ _).2 ⟨⟨smpY_last _ _ _ _ (by omega) s kU,
      smpY_last _ _ _ _ (by omega) s kO⟩, smpY_last _ _ _ _ (by omega) s kS⟩

/-- **The test on G_u hands smpK on.** -/
theorem smpKOnGu : SmpKOnGuOwed := by
  intro cs shU shO shS sU h2 p he ha d d' rs gs h hm hx
  obtain ⟨⟨kU, kO⟩, kS⟩ := (smpK_iff _ _ _ _ _ _ _).1 hx
  have ne : ∀ o : ℕ, o ≠ 1 → d.loc.firstMask ≠ some o := by
    intro o ho e
    rw [hm] at e
    exact ho (Option.some.inj e).symm
  exact (smpK_iff _ _ _ _ _ _ _).2
    ⟨⟨smpOnGu _ _ _ _ (by omega) p he ha d d' rs gs h (ne 0 (by omega)) kU,
      smpOnGu _ _ _ _ (by omega) p he ha d d' rs gs h (ne sU (by omega)) kO⟩,
      smpOnGu _ _ _ _ (by omega) p he ha d d' rs gs h (ne (sU + 1) (by omega)) kS⟩

/-- **The test on G_omega hands smpK on.** -/
theorem smpKOnGomega : SmpKOnGomegaOwed := by
  intro cs shU shO shS sU p he ha d d' rs gs h hx
  obtain ⟨⟨kU, kO⟩, kS⟩ := (smpK_iff _ _ _ _ _ _ _).1 hx
  exact (smpK_iff _ _ _ _ _ _ _).2
    ⟨⟨smpOnGomega _ _ _ _ (by omega) p he ha d d' rs gs h kU,
      smpOnGomega _ _ _ _ (by omega) p he ha d d' rs gs h kO⟩,
      smpOnGomega _ _ _ _ (by omega) p he ha d d' rs gs h kS⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.smpKEarly
#print axioms Desc.K14.Law.smpKHandsAt
#print axioms Desc.K14.Law.smpKOnGu
#print axioms Desc.K14.Law.smpKOnGomega
