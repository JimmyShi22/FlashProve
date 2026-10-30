-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- The proofs of the seven statements of Johnson/Desc/Sound/BordersLastQ.lean.
import Johnson.Desc.Sound.BordersLastQ
import Johnson.Desc.Sound.GlueSecondProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last

theorem lastJoin : LastJoin := by
  intro P S₁ S₂ S₃ Cl Wt C Fr N Mg ML Pm PL Oc l h
  exact spineRule _ Cl Wt ItemL C Fr _ _ _ _ _ l 0 h

theorem lastJoinPlain : LastJoinPlain := by
  intro P S₁ S₂ S₃ Cl Wt C Fr N Mg ML Pm PL Oc l h
  exact spinePlain _ Cl Wt ItemL C Fr _ _ _ _ _ l 0 h

theorem endLast : EndLast := by
  intro i h
  have h' := (openIsList ItemL insL₃ outsL₃ startLast lastPlaces.length i).1 h
  have e : openL insL₃ outsL₃ startLast lastPlaces.length = [] := by decide
  rw [e] at h'
  cases h'

theorem endsLast : EndsLast := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt T Q N Mg ML hlen a b _
  refine Or.inl ?_
  intro i hi
  have hi' : openAfter insQ₃ outsQ₃ (· ∈ startLast) (1 + T.l₃.length) i := hi
  rw [hlen] at hi'
  exact absurd hi' (endLast i)

theorem onZero₃OfEnd₂ : OnZero₃OfEnd₂ := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt start₃ T N Mg ML Pm PL Oc split hlen hStart hSh hPOf b s
    hon hs
  have hmem : PromS.noColl .oOmega ∈ promsAt split (1 + T.l₂.length) := by
    rw [hlen]
    cases split <;> decide
  refine ⟨hon.2, hStart _ _ _ s hs, fun _ => hPOf b (hon.1 _ hmem), hSh b s hon hs, fun h => ?_⟩
  exact absurd h (by decide)

/-- What goes back over the joint, piece by piece. -/
theorem lastBack {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type}
    (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt)
    (hStart : ∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → Mg.unmarked1 (p, s₁))
    (hPOb : ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : Wt),
      (ItemS.pin .oOmega).holdsSh N Mg b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ N Mg T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w)
    (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃') (w : Wt)
    (hs : start₃ b.1.1.1 b.1.1.2 b.1.2 = some s)
    (hr : relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML 0
      (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) w) :
    muQ N Mg T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w ∧
      ∀ i ∈ endS.filter (·.own), i.holdsOwn N Mg b.1.1 b.1.2
        (strsOf (frameAt D all D.key₂ T.ft₂) b.2) w := by
  have hr' : ∀ i, i ∈ startLast → meansQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML i
      (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) w := hr
  refine ⟨hPOb b w (hr' .pinO (by decide)), fun i hi => ?_⟩
  have hi' : i ∈ [ItemS.unmarked1, .pinI, .pinV, .ev, .dot] := hi
  rcases List.mem_cons.1 hi' with rfl | hi'
  · exact hStart _ _ _ s hs
  rcases List.mem_cons.1 hi' with rfl | hi'
  · exact hr' .pinI (by decide)
  rcases List.mem_cons.1 hi' with rfl | hi'
  · exact hr' .pinV (by decide)
  rcases List.mem_cons.1 hi' with rfl | hi'
  · exact hr' .ev (by decide)
  · obtain rfl := List.mem_singleton.1 hi'
    exact hr' .dot (by decide)

theorem relEnd₂OfZero₃ : RelEnd₂OfZero₃ := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt start₃ T N Mg ML Pm PL Oc split hlen hStart hPOb b s w hs hr
  obtain ⟨h1, h2⟩ := lastBack start₃ T N Mg ML hStart hPOb b s w hs hr
  refine ⟨fun i hi => ?_, fun i hi => h2 i ?_⟩
  · have hi' : openAfter (insSh split) (outsSh split) startSh (1 + T.l₂.length) i := hi
    rw [hlen] at hi'
    obtain rfl := (endShared split i).1 hi'
    exact h1
  · have hk : ownAt (1 + T.l₂.length) = endS.filter (·.own) := by
      have h2le : ¬ 1 + T.l₂.length ≤ pointAt := by
        rw [hlen]
        cases split <;> decide
      unfold ownAt
      rw [if_neg h2le]
    have hi' : i ∈ ownAt (1 + T.l₂.length) := hi
    rw [hk] at hi'
    exact hi'

theorem tieLast : TieLast := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt pub start₁ start₂ start₃ T Q N Mg ML Pm PL Oc split
    hlen hStart hSh hPOf hPOb
  exact glueSecond C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt pub start₁ start₂ start₃ T
    { Q with
      on₃ := onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc
      R₃ := relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML } N Mg Pm Oc split hlen
    (onZero₃OfEnd₂ C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt start₃ T N Mg ML Pm PL Oc split hlen hStart hSh
      hPOf)
    (fun b s w _ hs hr => lastBack start₃ T N Mg ML hStart hPOb b s w hs hr)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.lastJoin
#print axioms VerifiableInference.Desc.Sound.lastJoinPlain
#print axioms VerifiableInference.Desc.Sound.endLast
#print axioms VerifiableInference.Desc.Sound.endsLast
#print axioms VerifiableInference.Desc.Sound.onZero₃OfEnd₂
#print axioms VerifiableInference.Desc.Sound.relEnd₂OfZero₃
#print axioms VerifiableInference.Desc.Sound.tieLast
