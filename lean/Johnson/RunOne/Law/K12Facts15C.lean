-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15C.lean: WHAT THE COMPOSITION OF THE PROXIMITY TEST's LAW ASKS (CoreFacts, Johnson/Desc/Sound/SeamFacts.lean), AT THE RANGES' TEST's SEAT, WHERE THE GROUP UNDER TEST HAS ONE MEMBER: assembled from its payers. One statement with its proof: calls alone. GENERAL IN THE SEAT's LETTERS: no numeral of a size is read. IT PAYS NO FIELD OF THE KEY FILE's TABLES.
OBJECT. CoreFacts at rangesParams N, at the radii fun s => r s.st, at the reading of samples smpSt cs oNo stOf, at the one member x of a list.
USER. Whoever pays the law's composition at the key file's first proximity test.
LETTERS. All free. THE PREMISES, BY KIND. On the list of rounds: the test below the Johnson radius accepts the radii r · the seat's test planOk · the first radius against the member's own (hfit). The run: the seat's own yes at s · t is the test's own state that the seat makes of s · the law's conclusion QN at (t, y). The test's state in front: its codes are cs · the group under test has the one member n · message n bears an OOD sample of the shape sh (K1.SeedIs) · K1.Tie · the plain test on that sample accepts (hm) · the shape has main rows. The list's member: x's entry is (sh, e₁) · oNo x = n · stOf a0 = t.st · mem n = some x. AND, NAMED, NOT PAID: hword: the word off the plain strings is the word as sent.

  coreFacts_one: the statement. BY: coreFacts_all (Johnson/Desc/Sound/SeamMembersAll.lean) · the group: codes_fixed (SeamGroup.lean), six_of_yes (K12Facts15G.lean) · one_member (K12MemberCarry.lean) · the member: site_of_tuple (Johnson/Desc/K12/Coin/SiteAtSeats.lean) behind qn_iff (ChecksAt.lean) · sampleL_at_record (Johnson/Desc/Sound/SeedAtRecord.lean) · member_of_seedIs, six_at_member (SeedAtKind.lean).
Limits. That the premises can be met together is not shown. As empty as hword and hseed. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15G
import Johnson.RunOne.Law.K12MemberCarry
import Johnson.Desc.Sound.SeamMembersAll
import Johnson.Desc.Sound.SeamGroup
import Johnson.Desc.Sound.SmpShared
import Johnson.Desc.Sound.SeedAtRecord
import Johnson.Desc.K12.Coin.SiteAtSeats
import Johnson.Desc.K12.Coin.ChecksAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Facts15
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain)
open H2K.Pub (sgOf johOk)
open _root_.Desc.K14.Law.Fence (CoreFacts GroupFacts MemberFacts coreFacts_all codes_fixed member_of_seedIs six_at_member sampleL_at_record)
open Johnson.RunOne.Law.K12MemberCarry (one_member)

variable {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ} {N : H2U.PlaceNums}

/-- **CoreFacts at the ranges' test's seat, where the group under test has one member.** -/
theorem coreFacts_one (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (no : ℕ → ℕ)
    (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ) (oNo : Mem → ℕ) (stOf : A → Statement) (mem : ℕ → Option Mem)
    (y : Fr.E.Str) (a0 : A) (Y : Strs) (t : T12) (x : Mem) (sh : OracleShape) (e₁ n : ℕ)
    (joh : johOk (rangesParams N) r = true)
    (hp : (rangesTest laid back N : Block σ Cl).planOk = true)
    (hfit : ∀ a rest, (rangesParams N).nums.stages = a :: rest →
      r (sgOf a).st < (e₁ + 1) * 2 ^ ((sgOf a).C.a - aOf cs sh))
    {s s' : σ} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (rangesTest laid back N : Block σ Cl).decide s rs gs = .ok s')
    (ht : enterAndAsk laid (rangesParams N) s = .ok t)
    (hq : QN (rangesParams N) (NTuple Fr (rangesParams N) no (fun s => r s.st) rd) (t, y))
    (hcs : t.st.codes = cs)
    (hG : ∀ G0, t.st.groups[t.g]? = some G0 → G0.members.toList = [n])
    (hseed : ∃ ρ v, K1.SeedIs cs sh t.st n ρ v) (hT : K1.Tie cs sh)
    (hm : ∃ o, t.st.oracles[n]? = some o ∧ o.shape = sh ∧
      ∀ m : Seat1, m.sh = sh → m.id = n → H2K.First.ok (sampleL cs m o) = true)
    (hmain : 0 < sh.mainRows) (hmask : sh.maskRows = 0 → cs.mask.size ≤ sh.maskCode)
    (hx : x.1.l.get x.2 = (sh, e₁)) (hoNo : oNo x = n) (hst : stOf a0 = t.st) (hmem : mem n = some x)
    (hword : ∀ a rest G0 Ly D, Fixes (rangesParams N) t a rest G0 Ly D → ∀ j : Fin D.mems.length,
      HEq (strOf cs (D.mems.get j).sh e₁ (layOf (D.mems.get j))
          (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
        (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat Y x.2)) :
    CoreFacts cs G Fr (rangesParams N) no (fun s => r s.st) (smpSt cs oNo stOf) mem (· = x) t y a0 Y := by
  refine coreFacts_all cs G Fr (rangesParams N) no (fun s => r s.st) (smpSt cs oNo stOf) mem y a0 Y (· = x) t ?_
  intro a rest G0 Ly D hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := six_of_yes r joh hp h ht a rest G0 Ly D hf
  have hcD : D.st.codes = cs := (codes_fixed (rangesParams N) t a rest G0 Ly D hf).trans hcs
  obtain ⟨hlen, hid⟩ := one_member hf n (hG G0 hf.2.1)
  obtain ⟨ρ, v, hS⟩ := hseed
  obtain ⟨o, ho, hosh, hmo⟩ := hm
  have hN := (qn_iff (rangesParams N) _ (t, y) hf).1 hq
  refine ⟨⟨hcD, h1, h2, h3, h4, h5, h6⟩, fun _ => x, fun _ => e₁, ?_, ?_, ?_⟩
  · intro i j _
    exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
  · intro z hz
    exact ⟨⟨0, by omega⟩, hz.symm⟩
  · intro j
    have hj := hid j
    have hS' : K1.SeedIs cs sh t.st (D.mems.get j).id ρ v := by rw [hj]; exact hS
    have hsh : (D.mems.get j).sh = sh := (member_of_seedIs hf default j hS').1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hword a rest G0 Ly D hf j⟩
    · exact site_of_tuple no (fun s => r s.st) rd y hf hN cs hcD j o (by rw [hj]; exact ho)
        (Or.inl ⟨by rw [hosh]; exact hmain, by rw [hosh]; exact hmask⟩)
    · exact sampleL_at_record rfl ⟨o, ho, hosh, hmo⟩ hf default j hj
    · rw [hsh]
      exact hfit a rest hf.1
    · rw [hsh]
      exact hx
    · rw [hj]
      exact hmem
    · refine six_at_member cs (smpSt cs oNo stOf) a0 hf default j x e₁ hx hT hS' ?_
      show K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 (stOf a0) (oNo ⟨x.1, x.2⟩) = _
      rw [hst, hj]
      show K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st (oNo x) = _
      rw [hoNo]

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.coreFacts_one
