-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Members29.lean: The key
file's tables, row 2.9 (the proximity test on the folded row's group G_u): THE PREMISE «left» OF
`back_29M` (K12Back29.lean), SHOWN MEMBER BY MEMBER at the reading of out-of-domain (OOD) samples
smpSt csKey oNo (·.2.st) (Johnson/Desc/Sound/SmpShared.lean). One statement; its proof is calls and
a count to two. WHAT IT IS NOT, FIRST. IT MOVES DEBTS, IT ENDS NONE BUT THE BOOKKEEPING: what stays
is named below, and THE WORD (hw0 | hw3: `MemberLeft`'s last clause) IS THE HEAVIEST: it is another
file's to
show (word_29, K12Left2910.lean),
and there «the book is in order» and «the place's first tree is 0» come back. It pays no
field of the tables. No soundness is claimed. Nothing on hiding.
  `left_29`: at whatever the verifier's state behind U's door fixes: the codes' equation; the
  plain
    data has two members: number 0 (U; the six's member 3) and number 3 (the shared split's masks;
    the six's member 5); `MemberLeft` at each.
  `back_29S`: `back_29M` with «left» paid by `left_29`: that the two fit is held by Lean.
BESIDE THEM: `hU_six` · `hSp_six` (the closed shapes' facts, by the kernel) ·
`word_at_29` (hw0 | hw3
from `word_29`) · `sm_of_seed` (hsm at smpSt from K1.SeedIs). ALSO:
`dep_at_29` (hdep from the book's facts and one comparison on the place's first stage).
BY: `codes_fixed` (SeamGroup.lean) · `mems_ids`
(Johnson/Desc/K12/Coin/MembersLaid.lean) · `tie_six` (KeyFillSeedAt.lean) ·
`memberLeft_of_seed` (Johnson/Desc/K12/Coin/MemberOfSeed.lean; over `member_of_seedIs` |
`six_at_member`). No «accept» is spent.
WHAT STAYS, EACH A BINDER: of the state in front: its codes are csKey (hcod) · the group's members
are [0, 3] (hgm: a projection of the promise's test on the state's shape) · the sendings' invariant
at the two numbers (hs0 | hs3) · the filler's letters: oNo and mem at the two (rfl at a filler's
terms) · on the two
closed shapes: rows of one kind · the case · the site's fact (hU | hSp) · the split's masks' tree's
depth (hdep) · the fit at the place's first stage (hf0 | hf3) · the word (hw0 | hw3).

-/
import Johnson.RunOne.Law.K12Back29
import Johnson.Desc.K12.Coin.MemberOfSeed
import Johnson.Desc.K12.Coin.MembersLaid
import Johnson.Desc.Sound.SeamGroup
import Johnson.Desc.Sound.SmpShared
import Johnson.RunOne.KeyFillSeedAt
import Johnson.RunOne.KeyFillChains
import Johnson.RunOne.Law.K12Left2910

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Members29
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
open Johnson.RunOne.Law.K12Law29Core (i3 i5)

theorem two_apart : (⟨sixS, i3⟩ : Sound.Mem) ≠ ⟨sixS, i5⟩ := fun h =>
  absurd (eq_of_heq (Sigma.mk.inj_iff.1 h).2) (by decide)

/-- **«left» of `back_29M`, member by member.** -/
theorem left_29 {XI : Type} (F : FileDescription XI) (Fr₂ : Frame) (π : P12) (nl : ℕ → ℕ)
    (r : Fmt.M1.Stage → ℕ) (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (x : (P₂ × St₂) × Fr₂.E.Str) (hcod : x.1.2.st.codes = csKey)
    (hgm : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 → G0.members.toList = [0, 3])
    (hs0 : ∃ ρ yv, K1.SeedIs csKey (six.get i3).1 x.1.2.st 0 ρ yv)
    (hs3 : ∃ ρ yv, K1.SeedIs csKey (six.get i5).1 x.1.2.st 3 ρ yv)
    (ho0 : oNo ⟨sixS, i3⟩ = 0) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hU : ¬ (0 < (six.get i3).1.mainRows ∧ 0 < (six.get i3).1.maskRows) ∧
      ((0 < (six.get i3).1.maskRows ∨ (six.get i3).1.mainDeg = 3) ∨
        ((six.get i3).1.maskRows = 0 ∧ (six.get i3).1.mainDeg = 1)) ∧
      0 < (six.get i3).1.mainRows ∧
      ((six.get i3).1.maskRows = 0 → csKey.mask.size ≤ (six.get i3).1.maskCode))
    (hSp : ¬ (0 < (six.get i5).1.mainRows ∧ 0 < (six.get i5).1.maskRows) ∧
      ((0 < (six.get i5).1.maskRows ∨ (six.get i5).1.mainDeg = 3) ∨
        ((six.get i5).1.maskRows = 0 ∧ (six.get i5).1.mainDeg = 1)) ∧
      0 < (six.get i5).1.maskRows ∧ csKey.base.size ≤ (six.get i5).1.code)
    (hdep : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 → (D.mems.get j).tsh.logN ≤ s.Z.a)
    (hf0 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i3).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i3).1))
    (hf3 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1))
    (hw0 : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 0 →
      HEq (strOf csKey (six.get i3).1 (six.get i3).2 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i3))
    (hw3 : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 →
      HEq (strOf csKey (six.get i5).1 (six.get i5).2 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i5)) :
    ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain),
      Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ),
        Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₂ (nuOf π nl t) (fun q => r q.st)
            (smpSt csKey oNo fun a : P₂ × St₂ => a.2.st) mem x.2 x.1
            (strsOf Fr₂ x.2) s D j (xs j) (es j) := by
  intro t ht s rest G0 Ly D hf
  have hd := hdep t ht s rest G0 Ly D hf
  have w0 := hw0 t ht s rest G0 Ly D hf
  have w3 := hw3 t ht s rest G0 Ly D hf
  cases ht
  have hm := hgm G0 hf.2.1
  obtain ⟨hlen, hid⟩ := mems_ids π _ s rest G0 Ly D hf
  have h2 : D.mems.length = 2 := by
    rw [hlen]
    simpa using congrArg List.length hm
  have key : ∀ j : Fin D.mems.length, (j.val = 0 ∧ (D.mems.get j).id = 0) ∨
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
    fun j => if j.val = 0 then ⟨sixS, i3⟩ else ⟨sixS, i5⟩,
    fun j => if j.val = 0 then (six.get i3).2 else (six.get i5).2, ?_, ?_, ?_⟩
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
    · exact ⟨⟨0, by omega⟩, if_pos rfl⟩
    · exact ⟨⟨1, by omega⟩, if_neg Nat.one_ne_zero⟩
  · intro j
    rcases key j with ⟨e, hj⟩ | ⟨e, hj⟩
    · beta_reduce
      rw [if_pos e, if_pos e]
      obtain ⟨ρ, yv, hs⟩ := hs0
      exact memberLeft_of_seed csKey F Fr₂ π _ _ _ mem x.2 x.1 _ _ s rest G0 Ly D hf j ⟨sixS, i3⟩
        (six.get i3).1 (six.get i3).2 rfl (tie_six i3) ρ yv (by rw [hj]; exact hs)
        (by rw [hj]; show K1.smpAt _ _ _ _ (oNo ⟨sixS, i3⟩) = _; rw [ho0]) (tie_six i3).one hU.1
        hU.2.1 (Or.inl hU.2.2) (hf0 s rest hf.1) (by rw [hj]; exact hmem0) (w0 j hj)
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

/-- **`back_29M` (K12Back29.lean) WITH «left» PAID BY `left_29`**: that the two fit is hereby
held by Lean. Row 2.9's «law» off the antecedents of `Pays`' last clause, at the reading smpSt csKey
oNo (·.2.st): of the seam's bundle there stay: the codes · the group's members · the sendings'
invariant at the two ·
the closed shapes' facts · the depth · the fit · the word. -/
theorem back_29S {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W) (B : Block St₂ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) B)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t ∧
      (Seat.leave x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₂ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 9 x)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hcod : x.1.2.st.codes = csKey)
    (hgm : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 → G0.members.toList = [0, 3])
    (hs0 : ∃ ρ yv, K1.SeedIs csKey (six.get i3).1 x.1.2.st 0 ρ yv)
    (hs3 : ∃ ρ yv, K1.SeedIs csKey (six.get i5).1 x.1.2.st 3 ρ yv)
    (ho0 : oNo ⟨sixS, i3⟩ = 0) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hU : ¬ (0 < (six.get i3).1.mainRows ∧ 0 < (six.get i3).1.maskRows) ∧
      ((0 < (six.get i3).1.maskRows ∨ (six.get i3).1.mainDeg = 3) ∨
        ((six.get i3).1.maskRows = 0 ∧ (six.get i3).1.mainDeg = 1)) ∧
      0 < (six.get i3).1.mainRows ∧
      ((six.get i3).1.maskRows = 0 → csKey.mask.size ≤ (six.get i3).1.maskCode))
    (hSp : ¬ (0 < (six.get i5).1.mainRows ∧ 0 < (six.get i5).1.maskRows) ∧
      ((0 < (six.get i5).1.maskRows ∨ (six.get i5).1.mainDeg = 3) ∨
        ((six.get i5).1.maskRows = 0 ∧ (six.get i5).1.mainDeg = 1)) ∧
      0 < (six.get i5).1.maskRows ∧ csKey.base.size ≤ (six.get i5).1.code)
    (hdep : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 → (D.mems.get j).tsh.logN ≤ s.Z.a)
    (hf0 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i3).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i3).1))
    (hf3 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1))
    (hw0 : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 0 →
      HEq (strOf csKey (six.get i3).1 (six.get i3).2 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i3))
    (hw3 : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = 3 →
      HEq (strOf csKey (six.get i5).1 (six.get i5).2 (layOf (D.mems.get j))
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i5))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
      (smpSt csKey oNo fun a : P₂ × St₂ => a.2.st) x.1 sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 0 ∨ o = 3) ∧ 0 ∈ G0.members.toList ∧
        S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0) (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hlt : ∀ o, orc₂ ((baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr
      (atSix 5).1 (atSix 5).2) = some o →
      o < x.1.2.st.oracles.size ∧ x.1.2.loc.firstMask ≠ some o)
    (hbase : (atSix 5).1 < p.base) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
      KItem.pin 5 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [3] tbl w) :=
  K12Back29.back_29M F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ π nl r rdN _ mem rd
    hrd p B hb hal x y τ hout hq hon hj hp
    (left_29 F Fr₂ π nl r oNo mem x hcod hgm hs0 hs3 ho0 ho3 hmem0 hmem3 hU hSp hdep hf0 hf3 hw0
      hw3)
    hi hlog told hsm hsh hmem0 hmem3 hK hgrp h1 h2 x0 hx hsmd hss hSm hlt hbase

/-! ## The closed shapes · the word · the OOD seeds' tie: each from what lies -/

/-- **`left_29`'s hU, paid**: closed facts on U's shape and the key file's codes, by the kernel.
(Its like at Omega and at the split's masks: `hO_six` | `hSp_six`,
K12Members210.lean.) -/
theorem hU_six : ¬ (0 < (six.get i3).1.mainRows ∧ 0 < (six.get i3).1.maskRows) ∧
    ((0 < (six.get i3).1.maskRows ∨ (six.get i3).1.mainDeg = 3) ∨
      ((six.get i3).1.maskRows = 0 ∧ (six.get i3).1.mainDeg = 1)) ∧
    0 < (six.get i3).1.mainRows ∧
    ((six.get i3).1.maskRows = 0 → csKey.mask.size ≤ (six.get i3).1.maskCode) := by
  decide +kernel

/-- **`left_29`'s hSp, paid.** ONE STATEMENT with `hSp_six` (K12Members210.lean), at
this file's own i5: that file stands over row 2.10's laws, outside this one's cone. -/
theorem hSp_six : ¬ (0 < (six.get i5).1.mainRows ∧ 0 < (six.get i5).1.maskRows) ∧
    ((0 < (six.get i5).1.maskRows ∨ (six.get i5).1.mainDeg = 3) ∨
      ((six.get i5).1.maskRows = 0 ∧ (six.get i5).1.mainDeg = 1)) ∧
    0 < (six.get i5).1.maskRows ∧ csKey.base.size ≤ (six.get i5).1.code := by
  decide +kernel

/-- **`left_29`'s hw0 | hw3, general in the member, from `word_29`**
(K12Left2910.lean)
and `member_of_seedIs` («the member's shape is the list of rounds'»). After
`word_at_210`. HERE THE PRICE THAT `back_29M` HAD SHED COMES BACK: «the first tree is 0» ·
«the book is in
order» · «a first mask is handed in». -/
theorem word_at_29 {XI : Type} (F : FileDescription XI) (Fr₂ : Frame) (π : P12) (lo : ℕ) (off₂ : ℕ → ℕ)
    (hoff : ∀ q, off₂ q = lo + q) (hft : π.nums.firstTree = 0) (x : (P₂ × St₂) × Fr₂.E.Str)
    (hmk : x.1.2.loc.firstMask.isSome = true) (hB : BookOrd 0 x.1.2.book) (i : Fin six.length)
    (sh : OracleShape) (e0 : ℕ) (hx : six.get i = (sh, e0)) (o : ℕ) (q : ℕ × ℕ)
    (hq : x.1.2.book.place[o]? = some q) (hat : atSix i.val = (off₂ q.1, q.2))
    (hs : ∃ ρ yv, K1.SeedIs csKey sh x.1.2.st o ρ yv)
    (hF : Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (htold : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∃ T, x.1.2.book.trees[q.1]? = some T ∧ ShapeIs T.shape u)
    (hd : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∀ e ∈ Fr₂.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ u.logLength) :
    ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
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
  exact K12Left2910.word_29 F Fr₂ π lo off₂ hoff _ hmk hft hB hf j i q (by rw [hj]; exact hq) hat
    x.2 e0 hx hF hS htold hd

/-- **`left_29`'s hdep, from the same facts on the book as the word, and ONE COMPARISON ON THE
PLACE's FIRST STAGE**: the member's tree's depth is the told tree's log-length
(`seatIs_29`; `SeatIs.log`), that is the code's depth (hlog). What stays: hZ: «the
code's depth is at most
the
first stage's mask code's»: closed numbers at the made place. -/
theorem dep_at_29 {XI : Type} (F : FileDescription XI) (π : P12) (lo : ℕ) (off₂ : ℕ → ℕ)
    (hoff : ∀ q, off₂ q = lo + q) (hft : π.nums.firstTree = 0) (d : St₂)
    (hmk : d.loc.firstMask.isSome = true) (hB : BookOrd 0 d.book) (i : Fin six.length) (o : ℕ)
    (q : ℕ × ℕ) (hq : d.book.place[o]? = some q) (hat : atSix i.val = (off₂ q.1, q.2))
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hlog : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      u.logLength = aOf csKey (six.get i).1)
    (htold : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∃ T, d.book.trees[q.1]? = some T ∧ ShapeIs T.shape u)
    (hZ : ∀ s rest, π.nums.stages = s :: rest → aOf csKey (six.get i).1 ≤ s.Z.a) :
    ∀ t, Seat.enter (·.gU) (·.firstMask) d = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = o → (D.mems.get j).tsh.logN ≤ s.Z.a := by
  intro t ht s rest G0 Ly D hf j hj
  cases ht
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 told
  have S := K12Left2910.seatIs_29 π lo off₂ hoff _ hmk hft hB hf j i.val q (by rw [hj]; exact hq)
    hat u (htold u hu)
  rw [S.log, hlog u hu]
  exact hZ s rest hf.1

/-- **The OOD seeds' tie of the tables' files' bridge (hsm), AT THE READING smpSt, from the
sendings' invariant**: ONE FACT IN THE FORMS OF K1's FILES AND OF THE TABLES' FILES, shown once:
where K1.SeedIs holds at the member's number, what smpSt reads there is K1.smpAt's value
(`K1.smpAt_of`), and `seedIsS_iff₂_hi` (KeyFillChains.lean) says the rest. orc₁ is a
free letter: at a message of the shared chain's own (¬ numSix i < 3) src₂ never reads it. -/
theorem sm_of_seed (orc₁ : ℕ → Option ℕ) (oNo : Sound.Mem → ℕ) (i : Fin six.length)
    (hi : ¬ numSix i < 3) (o : ℕ) (ho : orc₂ (numSix i) = some o) (hN : oNo ⟨sixS, i⟩ = o)
    (x : P₂ × St₂) (hs : ∃ ρ yv, K1.SeedIs csKey (six.get i).1 x.2.st o ρ yv) :
    ∀ σ : (OmAt csKey six i).Smp,
      (smpSt csKey oNo fun a : P₂ × St₂ => a.2.st) x sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x ρ σ.2 := by
  obtain ⟨ρ, yv, h⟩ := hs
  obtain ⟨z, e1, e2, e3⟩ :=
    K1.smpAt_of csKey (six.get i).1 (six.get i).2 x.2.st o ρ yv (tie_six i) h
  intro σ hσ
  have e : K1.smpAt csKey (six.get i).1 (six.get i).2 x.2.st (oNo ⟨sixS, i⟩) = some σ := hσ
  rw [hN, e1] at e
  obtain rfl : z = σ := Option.some.inj e
  exact ⟨ρ, e2, (seedIsS_iff₂_hi csKey six numSix orc₁ i hi x ρ z.2).2 ⟨o, ho, yv, h, e3⟩⟩

end Johnson.RunOne.Law.K12Members29

#print axioms Johnson.RunOne.Law.K12Members29.left_29
#print axioms Johnson.RunOne.Law.K12Members29.back_29S
#print axioms Johnson.RunOne.Law.K12Members29.hU_six
#print axioms Johnson.RunOne.Law.K12Members29.hSp_six
#print axioms Johnson.RunOne.Law.K12Members29.word_at_29
#print axioms Johnson.RunOne.Law.K12Members29.sm_of_seed
#print axioms Johnson.RunOne.Law.K12Members29.dep_at_29
