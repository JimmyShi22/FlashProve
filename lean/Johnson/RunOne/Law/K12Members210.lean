-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Members210.lean: The key
file's tables, row 2.10 (the proximity test on Omega's group G_omega; the test's second arm): THE
PREMISE «left» OF `back_210M` (K12Back210.lean), SHOWN MEMBER BY MEMBER at the reading of
out-of-domain (OOD) samples smpSt csKey oNo (·.2.st) (Johnson/Desc/Sound/SmpShared.lean). Made of
K12Members29.lean's text at other letters: a mend of the one is a mend of the other.
WHAT IT IS NOT, FIRST. IT MOVES DEBTS, IT ENDS NONE BUT THE BOOKKEEPING: what stays is named below,
and THE WORD (hw2 | hw3: the last clause of `MemberLeft`) IS THE HEAVIEST: it is another file's
to show (word_210L, K12Left2910.lean), and there «the book is in order» and «the place's first
tree is 0» come back. NO EXAMPLE IS SHOWN. It pays no field of the tables. No soundness is claimed.
Nothing on hiding.
  `left_210`: at whatever the verifier's state behind Omega's door fixes: the codes' equation; the
    plain data has two members: number 2 (Omega; the six's member 4) and number 3 (the shared
    split's masks; the six's member 5); `MemberLeft` at each. At any numbering by labels nl.
  `back_210S`: `back_210M` with «left» paid by `left_210`, at the second arm's own numbering:
    that the two fit is held by Lean.
BY: `codes_fixed` (SeamGroup.lean) · `mems_ids`
(Johnson/Desc/K12/Coin/MembersLaid.lean) · `tie_six` (KeyFillSeedAt.lean) ·
`memberLeft_of_seed` (Johnson/Desc/K12/Coin/MemberOfSeed.lean). No «accept» is spent.
WHAT STAYS, EACH A BINDER: of the state in front: its codes are csKey (hcod) · the group's members
are [2, 3] (hgm: a projection of the invariant's test on the state's shape at border 10) · the
sendings' invariant at the two numbers (hs2 | hs3) · the filler's letters: oNo and mem at the two ·
on the two closed shapes: rows of one kind · the case · the site's fact (hO | hSp: Omega's shape has
twelve main rows of degree 3 and no mask row, as the folded row's has: the same case; the split's
masks' one mask row) · the split's masks' tree's depth (hdep) · the fit at the place's first stage
(hf2 | hf3) · the word (hw2 | hw3).
BESIDE THEM: `hO_six` | `hSp_six`: hO | hSp by
the kernel at the six's closed shapes. `word_at_210`: hw2 | hw3 from `word_210L`.
`back_210W`: `back_210S` with these laid in; hcod · «message 3 is sampled, with a sample row» ·
«message 2 is there» drawn out of hs2 | hs3; two thirds of hgrp out of hgm. GONE AGAINST
`back_210S`: hcod · hO · hSp · hw2 · hw3 · hgrp · x0 hx hsmd hss · hlt. NEW: hft · hoff (the seats'
offset is the chain's first own tree's number) · hcnt (one open row) · hF (SeatFits at the two) ·
htS (the book's tree at the member's place stands and has the told shape:
shapeIs_2910 (BookAt2910.lean), off the history) · hd (the frame's depth).
htS hands its payer «the book places the member's message at q» too
(which `back_210W` has off Free₂.placed, and shapeIs_2910 wants). ALSO:
`dep_at_210`: hdep from the book's facts and one comparison on the place's first stage.

-/
import Johnson.RunOne.Law.K12Back210
import Johnson.Desc.K12.Coin.MemberOfSeed
import Johnson.Desc.K12.Coin.MembersLaid
import Johnson.Desc.Sound.SeamGroup
import Johnson.Desc.Sound.SmpShared
import Johnson.RunOne.KeyFillSeedAt
import Johnson.RunOne.Law.K12Left2910

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Members210
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf smpSt Piece held BookOrd)
open _root_.Run (ckP)
open H2K.Pub (johOk)
open Cb Johnson.Pack OnBytes.Maker
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open LPFD.CandLaid
open H2K.Pin (strOf layOf tabP NTuple)
open H2K.Pub (sgOf)
open _root_.Desc.K14.Law.Fence (codes_fixed member_of_seedIs)
open Johnson.RunOne.Law.K12Back210 (i4 i5)

theorem two_apart : (⟨sixS, i4⟩ : Sound.Mem) ≠ ⟨sixS, i5⟩ := fun h =>
  absurd (eq_of_heq (Sigma.mk.inj_iff.1 h).2) (by decide)

/-- **«left» of `back_210M`, member by member.** -/
theorem left_210 {XI : Type} (F : FileDescription XI) (Fr₂ : Frame) (π : P12) (nl : ℕ → ℕ)
    (r : Fmt.M1.Stage → ℕ) (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (x : (P₂ × St₂) × Fr₂.E.Str) (hcod : x.1.2.st.codes = csKey)
    (hgm : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 → G0.members.toList = [2, 3])
    (hs2 : ∃ ρ yv, K1.SeedIs csKey (six.get i4).1 x.1.2.st 2 ρ yv)
    (hs3 : ∃ ρ yv, K1.SeedIs csKey (six.get i5).1 x.1.2.st 3 ρ yv)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hO : ¬ (0 < (six.get i4).1.mainRows ∧ 0 < (six.get i4).1.maskRows) ∧
      ((0 < (six.get i4).1.maskRows ∨ (six.get i4).1.mainDeg = 3) ∨
        ((six.get i4).1.maskRows = 0 ∧ (six.get i4).1.mainDeg = 1)) ∧
      0 < (six.get i4).1.mainRows ∧
      ((six.get i4).1.maskRows = 0 → csKey.mask.size ≤ (six.get i4).1.maskCode))
    (hSp : ¬ (0 < (six.get i5).1.mainRows ∧ 0 < (six.get i5).1.maskRows) ∧
      ((0 < (six.get i5).1.maskRows ∨ (six.get i5).1.mainDeg = 3) ∨
        ((six.get i5).1.maskRows = 0 ∧ (six.get i5).1.mainDeg = 1)) ∧
      0 < (six.get i5).1.maskRows ∧ csKey.base.size ≤ (six.get i5).1.code)
    (hdep : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 → (D.mems.get j).tsh.logN ≤ s.Z.a)
    (hf2 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i4).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i4).1))
    (hf3 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1))
    (hw2 : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 2 →
      HEq (strOf csKey (six.get i4).1 (six.get i4).2 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i4))
    (hw3 : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 →
      HEq (strOf csKey (six.get i5).1 (six.get i5).2 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i5)) :
    ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain),
      Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ),
        Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i5⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₂ (nuOf π nl t) (fun q => r q.st)
            (smpSt csKey oNo fun a : P₂ × St₂ => a.2.st) mem x.2 x.1
            (strsOf Fr₂ x.2) s D j (xs j) (es j) := by
  intro t ht s rest G0 Ly D hf
  have hd := hdep t ht s rest G0 Ly D hf
  have w2 := hw2 t ht s rest G0 Ly D hf
  have w3 := hw3 t ht s rest G0 Ly D hf
  cases ht
  have hm := hgm G0 hf.2.1
  obtain ⟨hlen, hid⟩ := mems_ids π _ s rest G0 Ly D hf
  have h2 : D.mems.length = 2 := by
    rw [hlen]
    simpa using congrArg List.length hm
  have key : ∀ j : Fin D.mems.length, (j.val = 0 ∧ (D.mems.get j).id = 2) ∨
      (j.val = 1 ∧ (D.mems.get j).id = 3) := by
    intro j
    have hj := hid j
    rw [← Array.getElem?_toList, hm] at hj
    have hlt := j.isLt
    have : j.val = 0 ∨ j.val = 1 := by omega
    rcases this with e | e
    · rw [e] at hj
      exact Or.inl ⟨e, (Option.some.inj hj).symm⟩
    · rw [e] at hj
      exact Or.inr ⟨e, (Option.some.inj hj).symm⟩
  refine ⟨(codes_fixed π _ s rest G0 Ly D hf).trans hcod,
    fun j => if j.val = 0 then ⟨sixS, i4⟩ else ⟨sixS, i5⟩,
    fun j => if j.val = 0 then (six.get i4).2 else (six.get i5).2, ?_, ?_, ?_⟩
  · intro j j' e
    dsimp only at e
    have hlt := j.isLt
    have hlt' := j'.isLt
    split_ifs at e with a b b
    · exact Fin.ext (a.trans b.symm)
    · exact absurd e two_apart
    · exact absurd e.symm two_apart
    · exact Fin.ext (by omega)
  · rintro z (rfl | rfl)
    · exact ⟨⟨1, by omega⟩, if_neg Nat.one_ne_zero⟩
    · exact ⟨⟨0, by omega⟩, if_pos rfl⟩
  · intro j
    rcases key j with ⟨e, hj⟩ | ⟨e, hj⟩
    · beta_reduce
      rw [if_pos e, if_pos e]
      obtain ⟨ρ, yv, hs⟩ := hs2
      exact memberLeft_of_seed csKey F Fr₂ π _ _ _ mem x.2 x.1 _ _ s rest G0 Ly D hf j ⟨sixS, i4⟩
        (six.get i4).1 (six.get i4).2 rfl (tie_six i4) ρ yv (by rw [hj]; exact hs)
        (by rw [hj]; show K1.smpAt _ _ _ _ (oNo ⟨sixS, i4⟩) = _; rw [ho2]) (tie_six i4).one hO.1
        hO.2.1 (Or.inl hO.2.2) (hf2 s rest hf.1) (by rw [hj]; exact hmem2) (w2 j hj)
    · have e0 : ¬ j.val = 0 := by omega
      beta_reduce
      rw [if_neg e0, if_neg e0]
      obtain ⟨ρ, yv, hs⟩ := hs3
      exact memberLeft_of_seed csKey F Fr₂ π _ _ _ mem x.2 x.1 _ _ s rest G0 Ly D hf j ⟨sixS, i5⟩
        (six.get i5).1 (six.get i5).2 rfl (tie_six i5) ρ yv (by rw [hj]; exact hs)
        (by rw [hj]; show K1.smpAt _ _ _ _ (oNo ⟨sixS, i5⟩) = _; rw [ho3]) (tie_six i5).one hSp.1
        hSp.2.1 (Or.inr ⟨hSp.2.2.1, hSp.2.2.2, hd j hj⟩) (hf3 s rest hf.1)
        (by rw [hj]; exact hmem3) (w3 j hj)

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan)
  (enc : (Nat → E) → Nat → E) (rad a : Nat) (coll : Strs → Rec → Prop)
  (last₁ : VerifiableInference.Desc.Key.FirstState → Bool) (off₂ : Nat → Nat)

/-- **`back_210M` (K12Back210.lean) WITH «left» PAID BY `left_210`**: that the two fit is hereby
held by Lean. Row 2.10's «law» off the antecedents of the last clause of `Pays`, at the reading
smpSt csKey oNo (·.2.st): of the seam's bundle there stay: the codes · the group's members · the
sendings' invariant at the two · the closed shapes' facts · the depth · the fit · the word. -/
theorem back_210S {Cl W : Type} (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W) (B : Block St₂ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) B)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t ∧
      (Seat.leave x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QO Fr₂ π t₁ t₂ 1 (fun s => r s.st) rdN (t, x.2))
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 10 x)
    (hj : johOk π r = true)
    (hcod : x.1.2.st.codes = csKey)
    (hgm : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 → G0.members.toList = [2, 3])
    (hs2 : ∃ ρ yv, K1.SeedIs csKey (six.get i4).1 x.1.2.st 2 ρ yv)
    (hs3 : ∃ ρ yv, K1.SeedIs csKey (six.get i5).1 x.1.2.st 3 ρ yv)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hO : ¬ (0 < (six.get i4).1.mainRows ∧ 0 < (six.get i4).1.maskRows) ∧
      ((0 < (six.get i4).1.maskRows ∨ (six.get i4).1.mainDeg = 3) ∨
        ((six.get i4).1.maskRows = 0 ∧ (six.get i4).1.mainDeg = 1)) ∧
      0 < (six.get i4).1.mainRows ∧
      ((six.get i4).1.maskRows = 0 → csKey.mask.size ≤ (six.get i4).1.maskCode))
    (hSp : ¬ (0 < (six.get i5).1.mainRows ∧ 0 < (six.get i5).1.maskRows) ∧
      ((0 < (six.get i5).1.maskRows ∨ (six.get i5).1.mainDeg = 3) ∨
        ((six.get i5).1.maskRows = 0 ∧ (six.get i5).1.mainDeg = 1)) ∧
      0 < (six.get i5).1.maskRows ∧ csKey.base.size ≤ (six.get i5).1.code)
    (hdep : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 → (D.mems.get j).tsh.logN ≤ s.Z.a)
    (hf2 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i4).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i4).1))
    (hf3 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1))
    (hw2 : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 2 →
      HEq (strOf csKey (six.get i4).1 (six.get i4).2 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π (nlAt π (numAt t₁ t₂ 1 (.own 0))) t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π (nlAt π (numAt t₁ t₂ 1 (.own 0))) t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i4))
    (hw3 : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 →
      HEq (strOf csKey (six.get i5).1 (six.get i5).2 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π (nlAt π (numAt t₁ t₂ 1 (.own 0))) t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π (nlAt π (numAt t₁ t₂ 1 (.own 0))) t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i5))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      (smpSt csKey oNo fun a : P₂ × St₂ => a.2.st) x.1 sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 3 ∨ o = 2) ∧ 3 ∈ G0.members.toList ∧ 0 + 1 ≤ G0.rows.size)
    (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[3]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hlt : ∀ o, orc₂ ((baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr
      (atSix 4).1 (atSix 4).2) = some o → o < x.1.2.st.oracles.size)
    (hbase : (atSix 4).1 < p.base) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
      KItem.pin 4 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [5] tbl w) :=
  K12Back210.back_210M F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ π t₁ t₂ r rdN _ mem
    rd hrd p B hb hal hp x y τ hout hq hon hj
    (left_210 F Fr₂ π _ r oNo mem x hcod hgm hs2 hs3 ho2 ho3 hmem3 hmem2 hO hSp hdep hf2 hf3 hw2
      hw3)
    hi hlog told hsm hsh hmem3 hmem2 hK hgrp x0 hx hsmd hss hSm hlt hbase

/-! ## The closed shapes' facts · the word · what the invariant holds -/

/-- Omega's shape at the six: rows of one kind · the case · the site's fact. By the kernel. -/
theorem hO_six : ¬ (0 < (six.get i4).1.mainRows ∧ 0 < (six.get i4).1.maskRows) ∧
      ((0 < (six.get i4).1.maskRows ∨ (six.get i4).1.mainDeg = 3) ∨
        ((six.get i4).1.maskRows = 0 ∧ (six.get i4).1.mainDeg = 1)) ∧
      0 < (six.get i4).1.mainRows ∧
      ((six.get i4).1.maskRows = 0 → csKey.mask.size ≤ (six.get i4).1.maskCode) := by
  decide +kernel

/-- The shared split's masks' shape at the six. By the kernel. -/
theorem hSp_six : ¬ (0 < (six.get i5).1.mainRows ∧ 0 < (six.get i5).1.maskRows) ∧
      ((0 < (six.get i5).1.maskRows ∨ (six.get i5).1.mainDeg = 3) ∨
        ((six.get i5).1.maskRows = 0 ∧ (six.get i5).1.mainDeg = 1)) ∧
      0 < (six.get i5).1.maskRows ∧ csKey.base.size ≤ (six.get i5).1.code := by
  decide +kernel

/-- **The word at a member of G_omega**: `left_210`'s hw2 | hw3 from `word_210L` (K12Left2910.lean):
the member's shape is the six's by the sendings' invariant (`member_of_seedIs`). -/
theorem word_at_210 {XI : Type} (F : FileDescription XI) (Fr₂ : Frame) (π : P12) (lo : ℕ) (off₂ : ℕ → ℕ)
    (hoff : ∀ q, off₂ q = lo + q) (hft : π.nums.firstTree = 0) (x : (P₂ × St₂) × Fr₂.E.Str)
    (hB : BookOrd 0 x.1.2.book) (i : Fin six.length) (sh : OracleShape) (e0 : ℕ)
    (hx : six.get i = (sh, e0)) (o : ℕ) (q : ℕ × ℕ) (hq : x.1.2.book.place[o]? = some q)
    (hat : atSix i.val = (off₂ q.1, q.2))
    (hs : ∃ ρ yv, K1.SeedIs csKey sh x.1.2.st o ρ yv)
    (hF : Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (htold : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∃ T, x.1.2.book.trees[q.1]? = some T ∧ ShapeIs T.shape u)
    (hd : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∀ e ∈ Fr₂.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ u.logLength) :
    ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = o →
      HEq (strOf csKey sh e0 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π (nlAt π lo) t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π (nlAt π lo) t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i) := by
  intro t ht s rest G0 Ly D hf j hj
  cases ht
  obtain ⟨ρ, yv, hs⟩ := hs
  have hsh := (member_of_seedIs hf default j (by rw [hj]; exact hs)).1
  subst hsh
  exact K12Left2910.word_210L F Fr₂ π lo off₂ hoff _ rfl hft hB hf j i q (by rw [hj]; exact hq) hat
    x.2 e0 hx hF hS htold hd

/-- **`left_210`'s hdep, from the same facts on the book as the word, and ONE COMPARISON ON THE
PLACE's FIRST STAGE**: the member's tree's depth is the told tree's log-length
(`seatIs_210L`; `SeatIs.log`), that is the code's depth (hlog). What stays: hZ: «the
code's depth is at most the first stage's mask code's»: closed numbers at the made place. Made of
K12Members29.lean's `dep_at_29` at Omega's doors. -/
theorem dep_at_210 {XI : Type} (F : FileDescription XI) (π : P12) (lo : ℕ) (off₂ : ℕ → ℕ)
    (hoff : ∀ q, off₂ q = lo + q) (hft : π.nums.firstTree = 0) (d : St₂)
    (hB : BookOrd 0 d.book) (i : Fin six.length) (o : ℕ)
    (q : ℕ × ℕ) (hq : d.book.place[o]? = some q) (hat : atSix i.val = (off₂ q.1, q.2))
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hlog : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      u.logLength = aOf csKey (six.get i).1)
    (htold : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∃ T, d.book.trees[q.1]? = some T ∧ ShapeIs T.shape u)
    (hZ : ∀ s rest, π.nums.stages = s :: rest → aOf csKey (six.get i).1 ≤ s.Z.a) :
    ∀ t, Seat.enter (·.gOmega) (fun _ => none) d = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = o → (D.mems.get j).tsh.logN ≤ s.Z.a := by
  intro t ht s rest G0 Ly D hf j hj
  cases ht
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 told
  have S := K12Left2910.seatIs_210L π lo off₂ hoff _ rfl hft hB hf j i.val q (by rw [hj]; exact hq)
    hat u (htold u hu)
  rw [S.log, hlog u hu]
  exact hZ s rest hf.1

/-- **`back_210S` with the word had by `word_210L`, the closed shapes' facts by the kernel, and
what the sendings' invariant itself holds drawn out of it** (the state's codes · «message 3 is
sampled and has a sample row» · «message 2 is there»). THE PRICE THAT HAD MOVED COMES BACK:
firstTree = 0, and the book's order (out of the invariant's test on the state's shape). -/
theorem back_210W {Cl W : Type} (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W) (B : Block St₂ Cl) (hb : p.b = held B)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) B)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t ∧
      (Seat.leave x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QO Fr₂ π t₁ t₂ 1 (fun s => r s.st) rdN (t, x.2))
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 10 x)
    (hj : johOk π r = true) (hft : π.nums.firstTree = 0)
    (hoff : ∀ q, off₂ q = numAt t₁ t₂ 1 (.own 0) + q)
    (hgm : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 → G0.members.toList = [2, 3])
    (hcnt : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 → 0 + 1 ≤ G0.rows.size)
    (hs2 : ∃ ρ yv, K1.SeedIs csKey (six.get i4).1 x.1.2.st 2 ρ yv)
    (hs3 : ∃ ρ yv, K1.SeedIs csKey (six.get i5).1 x.1.2.st 3 ρ yv)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hdep : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 → (D.mems.get j).tsh.logN ≤ s.Z.a)
    (hf2 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i4).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i4).1))
    (hf3 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1))
    (hF : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (htS : ∀ (i : Fin six.length) (o : ℕ), (i = i5 ∧ o = 3) ∨ (i = i4 ∧ o = 2) → ∀ q : ℕ × ℕ,
      x.1.2.book.place[o]? = some q → atSix i.val = (off₂ q.1, q.2) →
      ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∃ T, x.1.2.book.trees[q.1]? = some T ∧ ShapeIs T.shape u)
    (hd : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ u,
      F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∀ e ∈ Fr₂.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ u.logLength)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      (smpSt csKey oNo fun a : P₂ × St₂ => a.2.st) x.1 sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hbase : (atSix 4).1 < p.base) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
      KItem.pin 4 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [5] tbl w) := by
  obtain ⟨hshape, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  have hB : BookOrd 0 x.1.2.book := (bookStep_of_shape₂ S a 10 x.1.2 hshape).2
  obtain ⟨o4, q4, e4, hq4, hat4⟩ := hfree.placed 4 (by decide)
  obtain rfl : 2 = o4 := Option.some.inj e4
  obtain ⟨o5, q5, e5, hq5, hat5⟩ := hfree.placed 5 (by decide)
  obtain rfl : 3 = o5 := Option.some.inj e5
  obtain ⟨_, _, hcod, z2, _, _, _, hz2, _⟩ := id hs2
  obtain ⟨_, _, _, x0, _, _, _, hx, _, hsmd, hrows, _⟩ := id hs3
  exact back_210S F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ π t₁ t₂ r rdN oNo mem rd
    hrd p B hb hal hp x y τ hout hq hon hj hcod hgm hs2 hs3 ho2 ho3 hO_six hSp_six hdep hf2 hf3
    (word_at_210 F Fr₂ π _ off₂ hoff hft x hB i4 _ _ rfl 2 q4 hq4 hat4 hs2 (hF i4 (Or.inr rfl))
      (hsh i4 (Or.inr rfl)) (htS i4 2 (Or.inr ⟨rfl, rfl⟩) q4 hq4 hat4) (hd i4 (Or.inr rfl)))
    (word_at_210 F Fr₂ π _ off₂ hoff hft x hB i5 _ _ rfl 3 q5 hq5 hat5 hs3 (hF i5 (Or.inl rfl))
      (hsh i5 (Or.inl rfl)) (htS i5 3 (Or.inl ⟨rfl, rfl⟩) q5 hq5 hat5) (hd i5 (Or.inl rfl)))
    hi hlog told hsm hsh hmem3 hmem2 hK
    (fun G0 hG => ⟨fun o ho => by
        rw [hgm G0 hG] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        exact ho.symm, by rw [hgm G0 hG]; decide, hcnt G0 hG⟩)
    x0 hx hsmd (by rw [hrows]; exact Nat.one_ne_zero) hSm
    (fun o ho => by
      have earr : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr (atSix 4).1
          (atSix 4).2 = 4 := hfree.arr 4 (by decide)
      rw [earr] at ho
      have e2 : o = 2 := by simpa [orc₂] using ho.symm
      subst e2
      exact (Array.getElem?_eq_some_iff.1 hz2).1)
    hbase

end Johnson.RunOne.Law.K12Members210

#print axioms Johnson.RunOne.Law.K12Members210.left_210
#print axioms Johnson.RunOne.Law.K12Members210.back_210S
#print axioms Johnson.RunOne.Law.K12Members210.hO_six
#print axioms Johnson.RunOne.Law.K12Members210.hSp_six
#print axioms Johnson.RunOne.Law.K12Members210.word_at_210
#print axioms Johnson.RunOne.Law.K12Members210.back_210W
#print axioms Johnson.RunOne.Law.K12Members210.dep_at_210
