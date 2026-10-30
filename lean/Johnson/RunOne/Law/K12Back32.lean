-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Back32.lean: The key file's
tables, row 3.2 (the proximity test on the last chain's own group): THE LAST JOIN OF THE WAY BACK: OFF
THE VERY ANTECEDENTS THAT `Pays` HANDS ITS PAYER (K12AtField.lean: its last clause): the promise in front
· the sub-protocol's piece puts out y at x · the game's conclusion at the seat's two doors. Statements;
each proof is a few calls. The like of `back_29` | `back_210`.
WHAT IT IS NOT, FIRST. NO EXAMPLE: that the premises can hold together is shown nowhere. THE PROMISE
BEHIND (on₃ … 3 y: that clause's first half) IS NOT TOUCHED: it is fwd_32_name (K12FwdName.lean). WITHOUT IT
`Pays` IS NOT HAD, WHATEVER THIS FILE GIVES. It pays no field of the tables. No soundness is claimed.
Nothing on hiding.
  `law_32_of_pays`: `law_32_coreF`'s conclusion (K12Law32Core.lean); QW is made of the piece's
    «accept» (`qw_of_yes`, Johnson/Desc/K12/Coin/GameOut.lean). (KeyRide23.lean's own
    `back_32` keeps that name.)
  `step_32`: the open items behind the row are the table's own at border 3 (by evaluation).
  `back_32_L`: L₃ … 3 y → L₃ … 2 x: THE SECOND HALF OF Pays' LAST CLAUSE, TO THE LETTER, at
    n := 2: over KeyRide23.lean's `back_32` and `ride_32` (no item rides but "unmarked").
BESIDE THEM: `law_32_of_paysM` · `back_32_LM`: the same two with «left» member by member
(`MemberLeft`; over `law_32_coreM`). ALSO: `law_32_of_paysM₂` · `back_32_LM₂`: over `MemberLeft₂`.
OWNERS: hb · hal: other files' (halC_32, Johnson/RunOne/Law/K12AlikeC.lean, concludes
VerifiableInference.Desc.K12.Coin.Alike, which this file asks; the elder hal_32 another constant,
H2K.JointK.Alike; hal_32: Johnson/RunOne/Law/K12Alike.lean) · told · hlog · LayIdem: other files'.
EVERY BINDER, ITS OWNER AND ITS STATE: in a text of this project that is not in this repository.

-/
import Johnson.RunOne.Law.K12Law32Core
import Johnson.Desc.K12.Coin.GameOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Back32
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf Piece held)
open Cb Johnson.Pack OnBytes.Maker
open _root_.Run (ckP)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.KeyRide23 (ins32)
open LPFD.CandLaid
open H2K.Pin (tabP NTuple)
open H2K.Pub (johOk)
open Johnson.RunOne.Law.K12TupleOfCore Johnson.RunOne.Law.K12Law32Core

/-- The row, typed by hand: that it steps as the table's own third row does is `step_32`; that the
table's row has these lists is `KeyRide23.row32`. -/
def rowK32 : KRow := { ins := ins32, lays := [0, 2, 4], whose := "K12's house (H2)" }

/-- Behind the row the open items are the table's own at border 3. -/
theorem step_32 : stepOpen (open₃ 2) rowK32 = open₃ 3 := by decide

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₃ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan) (a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **Row 3.2's «law», off the antecedents of `Pays`' last clause.** -/
theorem law_32_of_pays {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₃ (P₃ × St₃) Cl W) (B : Block St₃ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) B)
    (x y : (P₃ × St₃) × Fr₃.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enterOwn x.1.2 = .ok t ∧
      (Seat.leaveOwn x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t tE rs gs, Seat.enterOwn x.1.2 = .ok t →
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE →
      CoreLeft csKey F Fr₃ π (nuOf π nl t) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩) t x.2 x.1 (strsOf Fr₃ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) y.1
          (strsOf Fr₃ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) x.1
          (strsOf Fr₃ x.2) (layAt atSix [0, 2, 4] tbl w) := by
  obtain ⟨t, t', e1, ⟨e2, _⟩, e3⟩ := hq
  exact law_32_coreF F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ π nl r rdN smp mem rd
    hrd x y (qw_of_yes π nl r rdN _ _ p B hb hal x y τ hout ⟨t, t', e1, e2, e3⟩) hj hp hon left hi hlog told hsm
    hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI

/-- **The second half of `Pays`' last clause at row 3.2.** -/
theorem back_32_L {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₃ (P₃ × St₃) Cl W) (B : Block St₃ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) B)
    (x y : (P₃ × St₃) × Fr₃.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enterOwn x.1.2 = .ok t ∧
      (Seat.leaveOwn x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t tE rs gs, Seat.enterOwn x.1.2 = .ok t →
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE →
      CoreLeft csKey F Fr₃ π (nuOf π nl t) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩) t x.2 x.1 (strsOf Fr₃ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0)
    (hL : L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) 3 y) :
    L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) 2 x := by
  obtain ⟨tbl, hlaw⟩ := law_32_of_pays F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ π nl r
    rdN smp mem rd hrd p B hb hal x y τ hout hq hj hp hon left hi hlog told hsm
    hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI
  obtain ⟨w, hw⟩ := hL
  exact ⟨layAt atSix [0, 2, 4] tbl w, KeyRide23.back_32 F _ atSix S K₁ _ rowK32 rfl rfl tbl x.1 y.1
    (strsOf Fr₃ x.2) (strsOf Fr₃ y.2) w (hlaw rowK32 w rfl) (by rw [step_32]; exact hw)⟩

/-- **The same with «left» member by member**. -/
theorem law_32_of_paysM {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₃ (P₃ × St₃) Cl W) (B : Block St₃ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) B)
    (x y : (P₃ × St₃) × Fr₃.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enterOwn x.1.2 = .ok t ∧
      (Seat.leaveOwn x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1 (strsOf Fr₃ x.2) s D
            j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) y.1
          (strsOf Fr₃ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) x.1
          (strsOf Fr₃ x.2) (layAt atSix [0, 2, 4] tbl w) := by
  obtain ⟨t, t', e1, ⟨e2, _⟩, e3⟩ := hq
  exact law_32_coreM F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ π nl r rdN smp mem rd
    hrd x y (qw_of_yes π nl r rdN _ _ p B hb hal x y τ hout ⟨t, t', e1, e2, e3⟩) hj hp hon left hi hlog told hsm
    hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI

/-- **The second half of `Pays`' last clause at row 3.2, «left» member by member**. -/
theorem back_32_LM {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₃ (P₃ × St₃) Cl W) (B : Block St₃ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) B)
    (x y : (P₃ × St₃) × Fr₃.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enterOwn x.1.2 = .ok t ∧
      (Seat.leaveOwn x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1 (strsOf Fr₃ x.2) s D
            j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0)
    (hL : L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) 3 y) :
    L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) 2 x := by
  obtain ⟨tbl, hlaw⟩ := law_32_of_paysM F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ π nl r
    rdN smp mem rd hrd p B hb hal x y τ hout hq hj hp hon left hi hlog told hsm
    hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI
  obtain ⟨w, hw⟩ := hL
  exact ⟨layAt atSix [0, 2, 4] tbl w, KeyRide23.back_32 F _ atSix S K₁ _ rowK32 rfl rfl tbl x.1 y.1
    (strsOf Fr₃ x.2) (strsOf Fr₃ y.2) w (hlaw rowK32 w rfl) (by rw [step_32]; exact hw)⟩

/-- **The same over the parted remainder `MemberLeft₂`**. -/
theorem law_32_of_paysM₂ {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₃ (P₃ × St₃) Cl W) (B : Block St₃ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) B)
    (x y : (P₃ × St₃) × Fr₃.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enterOwn x.1.2 = .ok t ∧
      (Seat.leaveOwn x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft₂ csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1 (strsOf Fr₃ x.2) s D
            j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) y.1
          (strsOf Fr₃ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) x.1
          (strsOf Fr₃ x.2) (layAt atSix [0, 2, 4] tbl w) := by
  obtain ⟨t, t', e1, ⟨e2, _⟩, e3⟩ := hq
  exact law_32_coreM₂ F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ π nl r rdN smp mem rd
    hrd x y (qw_of_yes π nl r rdN _ _ p B hb hal x y τ hout ⟨t, t', e1, e2, e3⟩) hj hp hon left hi hlog told hsm
    hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI

/-- **The second half of `Pays`' last clause at row 3.2, over `MemberLeft₂`**. -/
theorem back_32_LM₂ {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₃ (P₃ × St₃) Cl W) (B : Block St₃ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) B)
    (x y : (P₃ × St₃) × Fr₃.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enterOwn x.1.2 = .ok t ∧
      (Seat.leaveOwn x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft₂ csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1 (strsOf Fr₃ x.2) s D
            j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0)
    (hL : L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) 3 y) :
    L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) 2 x := by
  obtain ⟨tbl, hlaw⟩ := law_32_of_paysM₂ F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ π nl r
    rdN smp mem rd hrd p B hb hal x y τ hout hq hj hp hon left hi hlog told hsm
    hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI
  obtain ⟨w, hw⟩ := hL
  exact ⟨layAt atSix [0, 2, 4] tbl w, KeyRide23.back_32 F _ atSix S K₁ _ rowK32 rfl rfl tbl x.1 y.1
    (strsOf Fr₃ x.2) (strsOf Fr₃ y.2) w (hlaw rowK32 w rfl) (by rw [step_32]; exact hw)⟩

end Johnson.RunOne.Law.K12Back32

#print axioms Johnson.RunOne.Law.K12Back32.step_32
#print axioms Johnson.RunOne.Law.K12Back32.law_32_of_pays
#print axioms Johnson.RunOne.Law.K12Back32.back_32_L
#print axioms Johnson.RunOne.Law.K12Back32.law_32_of_paysM
#print axioms Johnson.RunOne.Law.K12Back32.back_32_LM
#print axioms Johnson.RunOne.Law.K12Back32.law_32_of_paysM₂
#print axioms Johnson.RunOne.Law.K12Back32.back_32_LM₂
