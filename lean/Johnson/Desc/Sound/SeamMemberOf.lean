-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamMemberOf.lean: **MemberFacts (Johnson/Desc/Sound/SeamMembers.lean) AT ONE MEMBER, ASSEMBLED FROM WHAT IS TYPED IN OTHER FILES.** One statement, general in the seat, the arm, the chain and the number of members; its proof is calls. What for: THAT OTHER FILES' LEMMAS FIT
MemberFacts' CLAUSES, SIGN FOR SIGN, is hereby held by Lean.
  **memberFacts_of**   at a record t of the kind, whatever it fixes, a member j of the data, a member x of the list with the entry (s, e0):
      FROM  hseed : the record in front holds the sendings' own invariant at the member's number, at the plan's shape s (K1.SeedIs cs s t.st id ρ y) · Tie cs s · hsmp : the reading smp at x is K1.smpAt at the record's statement and the member's number
            [these three give clauses (4) AND (6) WHOLE: member_of_seedIs · six_at_member, Johnson/Desc/Sound/SeedAtKind.lean]
      AND   h1 : siteL's yes (1) · h2 : sampleL's yes (2) · h3 : the test's radius against e0 (3) · h5 : the plan's mem lays x at the member's number (5) · h7 : the word (7), each at the plan's shape s
      TO    MemberFacts cs G Fr no rad smp mem y a0 Y a D j x e0.
Limits. Every premise is a premise. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamMembers
import Johnson.Desc.Sound.SeedAtKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain)
open H2K.Pub (sgOf)

theorem memberFacts_of (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (no : ℕ → ℕ)
    (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (π : P12) (t : T12)
    (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length) (x : Mem) (s : OracleShape) (e0 : ℕ)
    (hx : x.1.l.get x.2 = (s, e0)) (hT : K1.Tie cs s) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (yv : GE)
    (hseed : K1.SeedIs cs s t.st (D.mems.get j).id ρ yv)
    (hsmp : smp a0 x.1 x.2 =
      K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st (D.mems.get j).id)
    (h1 : ok (siteL cs a (D.mems.get j)) = true)
    (h2 : ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
      ok (sampleL cs (D.mems.get j) o) = true)
    (h3 : rad (sgOf a) < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf cs s))
    (h5 : mem (D.mems.get j).id = some x)
    (h7 : HEq (strOf cs s e0 (layOf (D.mems.get j))
        (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
      (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat Y x.2)) :
    MemberFacts cs G Fr no rad smp mem y a0 Y a D j x e0 := by
  have hs : (D.mems.get j).sh = s := (member_of_seedIs hf default j hseed).1
  refine ⟨h1, h2, ?_, ?_, h5, six_at_member cs smp a0 hf default j x e0 hx hT hseed hsmp, ?_⟩
  · rw [hs]; exact h3
  · rw [hs]; exact hx
  · rw [hs]; exact h7

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.memberFacts_of
