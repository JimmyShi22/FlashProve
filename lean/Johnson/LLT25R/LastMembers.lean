-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastMembers.lean (each premise and conclusion of the form "∀ a …,
the promise at border 2 → …" stands besides under a letter E of the statement [a
lemma that takes the promise as a named premise, like `tidy_two`, does not]: what holds beside
the promise; at the ledger: the layer on the last chain's own state; of an elder
member five is also told that x's seat is one of the two elder seats; five may also
spend WHICH KIND the member is: an elder message, with its seat by the first chain's last book, or
Omega's copy; that the state's message at the member's number has x's shape; and
the game's own conclusion `NTuple`):
THE FIELD members OF `LastOwed` (what the seam's core asks member by member at the last
chain's own proximity test) FROM WHERE THE GROUP's THREE MEMBERS SIT AND WHAT IS STILL ASKED OF
EACH.
  `ends_carry`: what the last chain's state at border 2 carries of the two earlier chains' ends,
    inside the book-keeping's yes: the group under test is the handed own group with Omega's copy
    behind; an older member has the seat (by the state's own book) and the very message that it had
    at the first chain's end; the copy has Omega's seat at the shared chain's end and the plan's
    shape. (`groupSits_of_ends`, LastSits.lean, is a consequence; its proof is this one's.)
  `memBy_eq`: the closed mem names whoever of mine sits at a number's seat.
  `FiveAt`: what is still asked of one member, at a member x of mine that sits at its number: the
    premises of `memberFacts_of` (Johnson/Desc/Sound/SeamMemberOf.lean) but for the
    entry and mem: the shape's tie; the sendings' invariant on the OOD sample at the state in front;
    the reader smp is the reading off that state; the yes of `siteL`; the yes of `sampleL`; the
    test's radius fits the member's; the word as sent is the table's.
  `members_of_five`: **the field.** FROM: three of mine xI, xW, xO at three seats wI, wW, wO,
    pairwise apart, with the shapes sI, sW and the plan's for Omega; no two of mine have one seat,
    and every one of mine has one of the three; two: `HandedTwo wI wW sI sW`
    of what is handed; om: Omega's seat at the shared chain's end is wO; five: `FiveAt`. The tuple
    xs is written out (place 0: xI; 1: xW; 2: xO): so it is one to one and onto mine; the entry
    holds by the make of the radii; mem by `memBy_eq`.
Limits. two, om and five are premises. `FiveAt` is shown at no state. Nothing on soundness.

-/
import Johnson.LLT25R.LastSits
import Johnson.LLT25R.LastCore
import Johnson.LLT25R.LastSeamEnds
import Johnson.Desc.Sound.SeamMemberOf
import Johnson.ToldDescR.HandedTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open Cb Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Johnson.Pack
open OnBytes.Means H2K.ClaimSays H2K.Pin
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.Third.Law (start₃E_st start₃E_book start₃E_border)
open VerifiableInference.Desc.Book (placed_of_fits)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open _root_.Desc.K14.Law.Fence (MemberFacts memberFacts_of)
open H2K.First (Plain made_of)
open H2K.Pub (sgOf johOk)
open ToldDesc (HandedTwo)
open _root_.Run

/-- **What the last chain's state at border 2 carries of the two earlier chains' ends**: the group
under test is the handed own group with Omega's copy behind; an older member has the seat and the
message that it had; the copy has Omega's seat and the plan's shape. -/
theorem ends_carry (p : P₁₄) (R : List Fmt.DeclaredRound) (f : Handed) (e : SharedOut) (s : S₃)
    (t : T12) (G0 : Group) (t₁ t₂ : ℕ) (hk : shapeAt p R 2 f e s = true)
    (ht : enterOwn s = .ok t) (hG : t.st.groups[t.g]? = some G0) :
    ∃ Gh, f.st.groups[f.own]? = some Gh ∧ G0.members = Gh.members.push s.loc.omega ∧
      (∀ i ∈ Gh.members.toList,
        seatBy (noLast t₁ t₂ s.loc.firstTree) s.book i = seatBy noFirst f.book i ∧
          t.st.oracles[i]? = f.st.oracles[i]?) ∧
      seatBy (noLast t₁ t₂ s.loc.firstTree) s.book s.loc.omega =
        seatBy (noShared t₁) e.book e.omega ∧
      (t.st.oracles[s.loc.omega]?).map (·.shape) = some p.S.omega := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  have hst := start₃E_st _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨hbk, -, hft⟩ := start₃E_book _ _ _ _ _ _ _ _ _ _ _ B.start
  have hbd := start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨hown, hroots⟩ := start_own B.start
  obtain ⟨Gh, G, hGh, hGs, hmem, -, -⟩ := three_members B hst hbd
  obtain ⟨b, y, Gx, dot, L⟩ := B.laid
  have e0 : t.st = s.st ∧ t.g = s.loc.own := by
    obtain rfl : _ = t := Except.ok.inj ht
    exact ⟨rfl, rfl⟩
  obtain rfl : G = G0 := by
    rw [e0.1, e0.2, hGs] at hG
    exact Option.some.inj hG
  have hfirst : s.loc.firstTree = s₀.book.trees.size + 1 := by
    rw [L.loc]
    show s₀.loc.firstTree = _
    rw [hft, hbk, hroots]
  obtain ⟨g, hg⟩ := hbd
  obtain rfl : (⟨g, e⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
  have em : s.loc.omega = s₀.st.oracles.size := by rw [L.loc]
  obtain ⟨q, tr, tO, hq, htr, -, htO, hnum, -⟩ := L.tree
  refine ⟨Gh, by rw [← hst, ← hown]; exact hGh, hmem, fun i c' => ?_, ?_, ?_⟩
  · have hlt : i < s₀.st.oracles.size := by
      have T : Means.Tidy s₀.st := by rw [hst]; exact B.handed.tidy
      exact (T.inOrder.groups _ _ hGh).there i c'
    refine ⟨?_, by rw [e0.1, L.old i hlt, hst]⟩
    rw [← hbk]
    refine seat_older t₁ t₂ s.loc.firstTree s₀.book s.book i (L.oldPlaces i (L.step ▸ hlt))
      (fun q hq => L.oldTrees q.1 (placed_of_fits (hbk ▸ B.handed.fits₁) i q hq))
      (fun q _ hq _ => ?_)
    have := placed_of_fits (hbk ▸ B.handed.fits₁) i q hq
    omega
  · rw [em]
    exact seat_taken t₁ t₂ s.loc.firstTree e.book s.book e.omega s₀.st.oracles.size q
      (s₀.book.trees.size, 0) tr tO hq htr L.place htO hfirst.symm hnum
      (B.handed.tenant q hq).symm
  · obtain ⟨y', hy', hsy⟩ := B.handed.omega
    obtain rfl : y' = y := Option.some.inj (hy'.symm.trans L.there)
    rw [em, e0.1, L.copy, ← hsy]
    rfl

/-- The closed mem names whoever of mine sits there. -/
theorem memBy_eq {P S₁ S₂ : Type} (mine : List Mem)
    (seatAt : ((P × S₁ × S₂) × S₃) → ℕ → Option (ℕ × ℕ))
    (hnd : ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y) (a0 : (P × S₁ × S₂) × S₃) (o : ℕ)
    (x : Mem) (hx : x ∈ mine) (hs : seatAt a0 o = some (seatOf x)) :
    memBy mine seatAt a0 o = some x := by
  unfold memBy
  cases hf : mine.find? fun y => seatAt a0 o == some (seatOf y) with
  | none =>
    have := List.find?_eq_none.1 hf x hx
    rw [hs] at this
    simp at this
  | some y =>
    have hy := List.find?_some hf
    have hym := List.mem_of_find?_eq_some hf
    rw [hs] at hy
    have e : seatOf x = seatOf y := by simpa using hy
    rw [hnd x hx y hym e]

variable {P S₁ S₂ Cells Tok Cl' : Type} {Fr : Frame} (Nn : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
  (Oc : P × S₁ → Strs → Prop) (p : P₁₄) (R : List Fmt.DeclaredRound)
  (hand : P × S₁ → Option Handed) (ended : S₂ → Option SharedOut)
  {Xi : Type} (G : FileDescription Xi)
  (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf p.codes s.l).om i).Smp)
  (mine : List Mem) (π : P12) (no : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ) (t₁ t₂ : ℕ)

/- what holds beside the promise at border 2: a letter -/
variable {E : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Prop}

/-- **What is still asked of one member**, at a member x of mine that sits at its number: the
premises of `memberFacts_of` but for the entry and mem. -/
def FiveAt (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) (t : T12) (st : Fmt.M1.Stage) (D : Plain)
    (j : Fin D.mems.length) (x : Mem) : Prop :=
  K1.Tie p.codes (x.1.l.get x.2).1 ∧
  (∃ ρ yv, K1.SeedIs p.codes (x.1.l.get x.2).1 t.st (D.mems.get j).id ρ yv) ∧
  smp a.1 x.1 x.2 =
    K1.smpAt p.codes (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st (D.mems.get j).id ∧
  ok (siteL p.codes st (D.mems.get j)) = true ∧
  (∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
    ok (sampleL p.codes (D.mems.get j) o) = true) ∧
  r (sgOf st).st < ((x.1.l.get x.2).2 + 1) *
    2 ^ ((sgOf st).C.a - aOf p.codes (x.1.l.get x.2).1) ∧
  HEq (strOf p.codes (x.1.l.get x.2).1 (x.1.l.get x.2).2 (layOf (D.mems.get j))
      (W0 Fr no D.book a.2 (D.mems.get j).t).1 (W0 Fr no D.book a.2 (D.mems.get j).t).2)
    (VerifiableInference.Desc.Sound.wordsOf G p.codes x.1.l x.1.seat (strsOf Fr a.2) x.2)

/-- **THE FIELD members, FROM WHERE THE THREE SIT AND WHAT IS STILL ASKED OF EACH.** -/
theorem members_of_five (wI wW wO : ℕ × ℕ) (sI sW : OracleShape) (xI xW xO : Mem)
    (hnd : ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y)
    (hI : xI ∈ mine ∧ seatOf xI = wI ∧ (xI.1.l.get xI.2).1 = sI)
    (hW : xW ∈ mine ∧ seatOf xW = wW ∧ (xW.1.l.get xW.2).1 = sW)
    (hO : xO ∈ mine ∧ seatOf xO = wO ∧ (xO.1.l.get xO.2).1 = p.S.omega)
    (dIW : wI ≠ wW) (dIO : wI ≠ wO) (dWO : wW ≠ wO)
    (all : ∀ z ∈ mine, seatOf z = wI ∨ seatOf z = wW ∨ seatOf z = wO)
    (two : ∀ a f, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      hand (a.1.1.1, a.1.1.2.1) = some f → HandedTwo wI wW sI sW f)
    (om : ∀ a e, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      ended a.1.1.2.2 = some e → seatBy (noShared t₁) e.book e.omega = some wO)
    (five : ∀ a t, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised p.codes G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      (∃ rs gs s', (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Cl')).decide a.1.2 rs gs = .ok s') →
      ∀ st rest G0 Ly D, Fixes π t st rest G0 Ly D →
      NTuple Fr π no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D →
      ∀ (j : Fin D.mems.length) (x : Mem),
      x ∈ mine → seatLast t₁ t₂ a.1 (D.mems.get j).id = some (seatOf x) →
      (t.st.oracles[(D.mems.get j).id]?).map (·.shape) = some (x.1.l.get x.2).1 →
      ((∃ f, hand (a.1.1.1, a.1.1.2.1) = some f ∧
          seatBy noFirst f.book (D.mems.get j).id = some (seatOf x) ∧
          (seatOf x = wI ∨ seatOf x = wW)) ∨
        ((D.mems.get j).id = a.1.2.loc.omega ∧ seatOf x = wO)) →
      FiveAt p G smp no r a t st D j x) :
    ∀ a t, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised p.codes G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      (∃ rs gs s', (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Cl')).decide a.1.2 rs gs = .ok s') →
      ∀ st rest G0 Ly D, Fixes π t st rest G0 Ly D →
      NTuple Fr π no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D →
      ∃ (xs : Fin D.mems.length → Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z ∈ mine → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length, MemberFacts p.codes G Fr no (fun s => r s.st) smp
          (memBy mine (seatLast t₁ t₂) a.1) a.2 a.1 (strsOf Fr a.2) st D j (xs j) (es j) := by
  intro a t hon hE hP ht hY st rest G0 Ly D hf hN
  obtain ⟨f, e, hf', he', hk⟩ := shapeAt_of_onL Nn Mg Pm Oc p R hand ended hon
  obtain ⟨Gh, hGh, hmem, hold, hom, homs⟩ := ends_carry p R f e a.1.2 t G0 t₁ t₂ hk ht hf.2.1
  obtain ⟨G', i₁, i₂, hG', hl, s1, s2, sh1, sh2⟩ := two a f hon hE hf'
  obtain rfl : G' = Gh := Option.some.inj (hG'.symm.trans hGh)
  have hm := made_of π _ st Ly D (hf.2.2.2 default)
  have hL : Ly = layoutOf t.st G0 :=
    Option.some.inj (hf.2.2.1.symm.trans (layout_eq t.st t.g G0 hf.2.1))
  have hLm : Ly.members.toList = [i₁, i₂, a.1.2.loc.omega] := by
    have : Ly.members = G0.members := by rw [hL]; rfl
    rw [this, hmem, Array.toList_push, hl]
    rfl
  have h3 : D.mems.length = 3 := by
    rw [← hm.size, ← Array.length_toList, hLm]
    rfl
  have hid : ∀ j : Fin D.mems.length, [i₁, i₂, a.1.2.loc.omega][j.val]? = some (D.mems.get j).id :=
      by
    intro j
    rw [← hLm, Array.getElem?_toList]
    exact (hm.mem j).1
  have seat1 : seatLast t₁ t₂ a.1 i₁ = some wI :=
    ((hold i₁ (by rw [hl]; simp)).1).trans s1
  have seat2 : seatLast t₁ t₂ a.1 i₂ = some wW :=
    ((hold i₂ (by rw [hl]; simp)).1).trans s2
  have seat3 : seatLast t₁ t₂ a.1 a.1.2.loc.omega = some wO := hom.trans (om a e hon hE he')
  have shp1 : (t.st.oracles[i₁]?).map (·.shape) = some sI := by
    rw [(hold i₁ (by rw [hl]; simp)).2]; exact sh1
  have shp2 : (t.st.oracles[i₂]?).map (·.shape) = some sW := by
    rw [(hold i₂ (by rw [hl]; simp)).2]; exact sh2
  let xs : Fin D.mems.length → Mem := fun j =>
    if j.val = 0 then xI else if j.val = 1 then xW else xO
  have key : ∀ j : Fin D.mems.length, xs j ∈ mine ∧
      seatLast t₁ t₂ a.1 (D.mems.get j).id = some (seatOf (xs j)) ∧
      (t.st.oracles[(D.mems.get j).id]?).map (·.shape) = some ((xs j).1.l.get (xs j).2).1 ∧
      ((∃ f, hand (a.1.1.1, a.1.1.2.1) = some f ∧
          seatBy noFirst f.book (D.mems.get j).id = some (seatOf (xs j)) ∧
          (seatOf (xs j) = wI ∨ seatOf (xs j) = wW)) ∨
        ((D.mems.get j).id = a.1.2.loc.omega ∧ seatOf (xs j) = wO)) := by
    intro j
    have hj := j.isLt
    have h := hid j
    by_cases e0 : j.val = 0
    · rw [e0] at h
      obtain rfl : i₁ = (D.mems.get j).id := by simpa using h
      have hx : xs j = xI := by simp only [xs, e0, if_true]
      rw [hx]
      exact ⟨hI.1, by rw [hI.2.1]; exact seat1, by rw [hI.2.2]; exact shp1,
        .inl ⟨f, hf', by rw [hI.2.1]; exact s1, .inl hI.2.1⟩⟩
    · by_cases e1 : j.val = 1
      · rw [e1] at h
        obtain rfl : i₂ = (D.mems.get j).id := by simpa using h
        have hx : xs j = xW := by simp only [xs, e1, if_true, Nat.one_ne_zero, if_false]
        rw [hx]
        exact ⟨hW.1, by rw [hW.2.1]; exact seat2, by rw [hW.2.2]; exact shp2,
          .inl ⟨f, hf', by rw [hW.2.1]; exact s2, .inr hW.2.1⟩⟩
      · have e2 : j.val = 2 := by omega
        rw [e2] at h
        have e3 : a.1.2.loc.omega = (D.mems.get j).id := by simpa using h
        have hx : xs j = xO := by simp only [xs, e0, e1, if_false]
        rw [hx]
        exact ⟨hO.1, by rw [hO.2.1, ← e3]; exact seat3, by rw [hO.2.2, ← e3]; exact homs,
          .inr ⟨e3.symm, hO.2.1⟩⟩
  have nIW : xI ≠ xW := fun h => dIW (by rw [← hI.2.1, ← hW.2.1, h])
  have nIO : xI ≠ xO := fun h => dIO (by rw [← hI.2.1, ← hO.2.1, h])
  have nWO : xW ≠ xO := fun h => dWO (by rw [← hW.2.1, ← hO.2.1, h])
  refine ⟨xs, fun j => ((xs j).1.l.get (xs j).2).2, ?_, ?_, fun j => ?_⟩
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    by_cases i0 : i.val = 0 <;> by_cases j0 : j.val = 0 <;> by_cases i1 : i.val = 1 <;>
      by_cases j1 : j.val = 1 <;> simp only [xs, i0, j0, i1, j1, if_true, if_false] at hij <;>
      first
        | omega
        | exact absurd hij nIW
        | exact absurd hij.symm nIW
        | exact absurd hij nIO
        | exact absurd hij.symm nIO
        | exact absurd hij nWO
        | exact absurd hij.symm nWO
  · intro z hz
    rcases all z hz with h | h | h
    · exact ⟨⟨0, by omega⟩, (hnd z hz xI hI.1 (h.trans hI.2.1.symm)).symm⟩
    · exact ⟨⟨1, by omega⟩, (hnd z hz xW hW.1 (h.trans hW.2.1.symm)).symm⟩
    · exact ⟨⟨2, by omega⟩, (hnd z hz xO hO.1 (h.trans hO.2.1.symm)).symm⟩
  · obtain ⟨hxm, hs, hsp, hcase⟩ := key j
    obtain ⟨hT, ⟨ρ, yv, hseed⟩, hsmp, h1, h2, h3', h7⟩ :=
      five a t hon hE hP ht hY st rest G0 Ly D hf hN j (xs j) hxm hs hsp hcase
    exact memberFacts_of p.codes G Fr no (fun s => r s.st) smp (memBy mine (seatLast t₁ t₂) a.1) a.2
      a.1 (strsOf Fr a.2) π t st rest G0 Ly D hf j (xs j) _ _ rfl hT ρ yv hseed hsmp h1 h2 h3'
      (memBy_eq mine (seatLast t₁ t₂) hnd a.1 _ (xs j) hxm hs) h7

end LLT25

#print axioms LLT25.ends_carry
#print axioms LLT25.members_of_five
