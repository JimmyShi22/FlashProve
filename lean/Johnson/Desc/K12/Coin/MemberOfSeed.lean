-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/MemberOfSeed.lean: A MEMBER's SEVEN CLAUSES (
`MemberFacts`, Johnson/Desc/Sound/SeamMembers.lean) FROM THE SENDINGS' INVARIANT AT THE VERIFIER's
STATE IN FRONT AND
THE TWO «accept»s. General in the IOP as written in Lean, the frame, the place, the numbering, the
number of members. One statement; its proof is calls.
  `memberFacts_of_seed`: `memberFacts_of` (SeamMemberOf.lean) WITH ITS h1 (the site's
    «accept») AND h2 (the sample's «accept») PAID: h1 by `site_long` | `site_mask`
    (ShapesAtSeat.lean) · h2 by `hQ_of_yes` (CoreAtYes.lean), at the out-of-domain (OOD) seed's text
    that `seed_at_member` (SeedAtKind.lean) reads off the invariant. Both spend the
    «accept» of the plain data's tests (gpL); the second also the decision's own.
`memberLeft_of_seed`: `MemberLeft` (MemberAtYes.lean) from the same
premises, WITHOUT THE TWO «accept»s AND THE CODES' EQUATION: for the premise «left» of
`core_behind_QWm`.
WHAT STAYS, at a member j of the plain data and a member x of the list with the entry (s, e0):
K1.Tie cs s · K1.SeedIs cs s t.st ‹the member's number› · the reading's tie to K1.smpAt · on the
shape s: rows of
one kind · the case · one of two facts for the site · (3) the test's radius against e0 · (5) mem
lays x at the member's number · (7) the word.
KIN: `coreFacts_one` (RunOne/Law/K12Facts15C.lean): the like for a group of one member at the
ranges' seat; its road to clause (2) is another (the plain test on the sample accepts at the state
in front, carried by `sampleL_at_record`) · `two_at_member` (SeedTwo.lean): clause (2)
from the invariant with two premises on the codes' lengths, which `hQ_of_yes` has from gpL's
«accept». What it is not. A SHAPE WITH ROWS OF BOTH KINDS IS NOT SERVED (the key file's B and V):
there clause (2) wants every coordinate of the OOD seed's point canonical, which the invariant does
not say. Every premise is a premise. It pays no field of a table. No soundness is claimed. Nothing
on hiding.
-/
import Johnson.Desc.K12.Coin.CoreAtYes
import Johnson.Desc.K12.Coin.MemberAtYes
import Johnson.Desc.Sound.SeamMemberOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain gpL)
open H2K.Pub (sgOf)
open _root_.Desc.K14.Law.Fence (MemberFacts memberFacts_of seed_at_member member_of_seedIs
  six_at_member)

/-- **A member's seven clauses from the sendings' invariant and the two «accept»s.** -/
theorem memberFacts_of_seed (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (no : ℕ → ℕ) (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row : GroupRow)
    (hok : H2K.First.ok (gpL π a row D) = true) (hcs : D.st.codes = cs)
    (j : Fin D.mems.length) (x : Mem) (s : OracleShape) (e0 : ℕ)
    (hx : x.1.l.get x.2 = (s, e0)) (hT : K1.Tie cs s) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ)
    (yv : GE) (hseed : K1.SeedIs cs s t.st (D.mems.get j).id ρ yv)
    (hsmp : smp a0 x.1 x.2 =
      K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st (D.mems.get j).id)
    (h1 : s.answers = 1) (hone : ¬ (0 < s.mainRows ∧ 0 < s.maskRows))
    (hcase : (0 < s.maskRows ∨ s.mainDeg = 3) ∨ (s.maskRows = 0 ∧ s.mainDeg = 1))
    (hsite : (0 < s.mainRows ∧ (s.maskRows = 0 → cs.mask.size ≤ s.maskCode)) ∨
      (0 < s.maskRows ∧ cs.base.size ≤ s.code ∧ (D.mems.get j).tsh.logN ≤ a.Z.a))
    (h3 : rad (sgOf a) < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf cs s))
    (h5 : mem (D.mems.get j).id = some x)
    (h7 : HEq (strOf cs s e0 (layOf (D.mems.get j))
        (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
      (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat Y x.2)) :
    MemberFacts cs G Fr no rad smp mem y a0 Y a D j x e0 := by
  subst hcs
  obtain ⟨hs, hsd⟩ := seed_at_member hf row j hT hseed
  refine memberFacts_of D.st.codes G Fr no rad smp mem y a0 Y π t a rest G0 Ly D hf j x s e0 hx hT ρ
    yv hseed hsmp ?_ ?_ h3 h5 h7
  · rcases hsite with ⟨s1, s2⟩ | ⟨s1, s2, s3⟩
    · exact site_long π a row D hok j (hs ▸ s1) (by rw [hs]; exact s2)
    · exact site_mask π a row D hok j (hs ▸ s1) (by rw [hs]; exact s2) s3
  · exact hQ_of_yes π he hp t tE rs gs h a rest G0 Ly D hf row hok j hsd (by rw [hs]; exact h1)
      (by rw [hs]; exact hone)
      (by rw [hs]; exact hsite.elim (fun q => Or.inl q.1) fun q => Or.inr q.1)
      (by rw [hs]; exact hcase)

/-- **`MemberLeft` (MemberAtYes.lean) from the sendings' invariant: NO «accept» IS SPENT.** So
the premise «left» of `core_behind_QWm` can be shown at whatever the verifier's state fixes: clause
(4) is the entry with `member_of_seedIs` («the member's shape is s») · clause (6) is
`six_at_member` (SeedAtKind.lean), whole · the guarded conjunct is free at rows of one kind. -/
theorem memberLeft_of_seed (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (no : ℕ → ℕ) (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (t : T12) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length) (x : Mem) (s : OracleShape) (e0 : ℕ)
    (hx : x.1.l.get x.2 = (s, e0)) (hT : K1.Tie cs s) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ)
    (yv : GE) (hseed : K1.SeedIs cs s t.st (D.mems.get j).id ρ yv)
    (hsmp : smp a0 x.1 x.2 =
      K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st (D.mems.get j).id)
    (h1 : s.answers = 1) (hone : ¬ (0 < s.mainRows ∧ 0 < s.maskRows))
    (hcase : (0 < s.maskRows ∨ s.mainDeg = 3) ∨ (s.maskRows = 0 ∧ s.mainDeg = 1))
    (hsite : (0 < s.mainRows ∧ (s.maskRows = 0 → cs.mask.size ≤ s.maskCode)) ∨
      (0 < s.maskRows ∧ cs.base.size ≤ s.code ∧ (D.mems.get j).tsh.logN ≤ a.Z.a))
    (h3 : rad (sgOf a) < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf cs s))
    (h5 : mem (D.mems.get j).id = some x)
    (h7 : HEq (strOf cs s e0 (layOf (D.mems.get j))
        (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
      (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat Y x.2)) :
    MemberLeft cs G Fr no rad smp mem y a0 Y a D j x e0 := by
  obtain ⟨hs, _⟩ := member_of_seedIs hf default j hseed
  obtain ⟨o, seed, row0, tt, β, e1, e4, e5, e6, e7, e8⟩ :=
    six_at_member cs smp a0 hf default j x e0 hx hT hseed hsmp
  subst hs
  exact ⟨h1, hcase, hsite, h3, hx, h5,
    ⟨o, seed, row0, tt, β, e1, Or.inl hone, e4, e5, e6, e7, e8⟩, h7⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.memberFacts_of_seed
#print axioms VerifiableInference.Desc.K12.Coin.memberLeft_of_seed
