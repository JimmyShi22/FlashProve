-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstEnd.lean: WHAT THE SHARED TABLE's PROMISE STILL HOLDS AT THE SHARED
CHAIN's LAST BORDER, for the joint with the last chain. Inside the constant's promise at border 12
(Johnson/Desc/K14/Law/SharedConst.lean): the chain's end is there (K14.ended is some), there is no
collision at Omega's tenant, and the tests in the promise's slot accept.

  tested_of_untested   the chain's end's two named clauses (untestedL) give K14's own test at its
                  end (tested): general.
  Sh.ended_of_on  **K14.ended of the last state is some**: by the promise's clause "nothing is
                  left", which stands at border 12.
  Sh.noColl_omega_of_on   **no collision at Omega, and its words shown**: the clause noColl at
                  o_omega stands at border 12 (the pin on Omega is open there).
A CAUTION. K14's tested, the clause "nothing is left" and "K14.ended is some" hold at the shared
chain's FIRST state too (no group, no message yet: true of nothing; by a run at the full size they
are true at borders 0, 1, 11, 12 and false between). By themselves they are no sign that the
proximity tests ran. Here each is concluded from the WHOLE promise at border 12, whose clause shape
12 (Sh.X A 12) stands beside them and fails at the first state (it asks a message at o_omega's
number: Sh.omega_sampled). Spend them with that clause, never alone.
What is not claimed. That the proximity tests ran. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

/-- The end's two named clauses give K14's own test at its end. -/
theorem tested_of_untested (d : St)
    (h : (VerifiableInference.Desc.ChainEnd.untestedL d.st).all (·.2) = true) : tested d = true :=
        by
  simp only [VerifiableInference.Desc.ChainEnd.untestedL, List.all_cons, List.all_nil,
      Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold tested
  rw [Bool.and_eq_true]
  refine ⟨h1, ?_⟩
  rw [Array.all_eq_true_iff_forall_mem] at h2 ⊢
  intro x hx
  have hx' := h2 x hx
  rw [Bool.or_eq_true] at hx' ⊢
  rcases hx' with e | e
  · exact Or.inl e
  · refine Or.inr ?_
    cases hg : x.groups with
    | nil => rw [hg] at e; simp at e
    | cons _ _ => rfl

namespace Sh

variable {Xi P₀ P₁ Cl Cells Tok : Type} {Fr : Frame} (A : ShPlan Xi)
  (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- **K14.ended of the shared chain's last state is some.** -/
theorem ended_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece
    (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l 12 a) : (ended a.1.2).isSome = true := by
  have h : (pm A O).nothingLeft a.1.2 = true := ha.1 .nothingLeft (by decide)
  have ht : tested a.1.2 = true := tested_of_untested a.1.2 h
  unfold ended
  simp only [ht, if_true, Option.isSome_some]

/-- **No collision at Omega, at the last border.** -/
theorem noColl_omega_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List
    (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l 12 a) :
    (PromS.noColl .oOmega).holds (nums A O) (pm A O) a.1.2
      (strsOfAct Fr ((actQ (nums A O) f l 12).2 a)) :=
  ha.1 (.noColl .oOmega) (by decide)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.tested_of_untested
#print axioms Desc.K14.Law.Sh.ended_of_on
#print axioms Desc.K14.Law.Sh.noColl_omega_of_on
