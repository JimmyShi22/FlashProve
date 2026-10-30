-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Pays32.lean: The key file's tables, row 3.2 (the proximity
test on the last chain's own group; the test's first arm): THE JOIN: what the door
`keepsAt_k12₃` | `keepsAt_own` asks of whoever pays the row (`Pays`, Johnson/RunOne/Law/K12AtField.lean),
from the test's law with nothing promised, at a numbering by labels (`pays_gameV`, K12PaysGameV.lean,
over `k12_gameV`), the «law» of the way back (`law_32_of_pays`, K12Back32.lean) and
the rider (`back_32`, KeyRide23.lean). Statements and proofs: rows of calls. The like of
`pays_of_law` at row 2.10 (K12PaysOfLaw210.lean).
What it is not, first.
  (0) NO EXAMPLE IS SHOWN: that the premises hold together at any state or list of rounds is not said.
  (1) A JOIN: it pays no debt on the verifier's state and none on the list of rounds: each is a binder;
    those that name the state stand under «∀ a τ b, on 2 a → the piece puts out b at a →», gathered in
    one structure (`Debts32`): so that a payer can spend the piece's accepting run.
  (2) THE INVARIANT BEHIND (on 3) IS A PREMISE (fwd), in the form of `fwd_32_name` (K12FwdName.lean), which asks
    the history (Hist₃) beside the promise: so «on» IS A LETTER, with one tie (hin : on 2 a → on₃ … 2 a):
    the caller fills on k := On₃ k ∧ (k = 2 → the history), as at rows 2.9 | 2.10.
  (3) That the row's look-up at 2 gives a stretch dB :: dt with nothing put behind is the caller's.
  (4) It fills no field of the tables. No soundness is claimed. Nothing on hiding.
Main names.
  `i2_32_of_law`: the last clause of `Pays` at the row, the «law» a letter. NOTHING RIDES: no premise on
    what stays across the test but the strings at the three open pins.
  `pays_32_of_law`: `Pays`, the «law» a letter.
  `Debts32`: what `law_32_of_pays` asks of a state in front.
  `pays_32`: `Pays`, the «law» paid by `law_32_of_pays`.
  `Debts32M` · `pays_32M`: «left» member by member (`MemberLeft`).
  `Debts32M₂` · `pays_32M₂`: over the parted remainder `MemberLeft₂`.

-/
import Johnson.RunOne.Law.K12Back32
import Johnson.RunOne.Law.K12AtField
import Johnson.RunOne.Law.K12PaysGameV
import Johnson.Desc.Key.KeyKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Pays32
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf Piece held pieceOf Rest)
open VerifiableInference.Desc.Plain (piece_decides_at)
open Cb Johnson.Pack OnBytes.Maker
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.KeyRide23 (ins32)
open LPFD.CandLaid
open H2K.Pin (tabP NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)
open Johnson.RunOne.Law.K12AtField (Pays)
open Johnson.RunOne.Law.K12TupleOfCore Johnson.RunOne.Law.K12Law32Core
open Johnson.RunOne.Law.K12Back32 (rowK32 step_32 law_32_of_pays law_32_of_paysM law_32_of_paysM₂)

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₃ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan) (a₀ : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **The last clause of `Pays` at row 3.2, from the «law» of the way back.** -/
theorem i2_32_of_law {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₃ × St₃) × Fr₃.E.Str → Prop)
    (Bb : Block St₃ Cl)
    (fwd : ∀ a c rs gs, on 2 a → (held Bb : Block (P₃ × St₃) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₃ 2) (strsOf Fr₃ a.2) (strsOf Fr₃ c.2) → on 3 c)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₃ 2), (atSix k).1 < base)
    (ds : List RDT) (back : List Fmt.RoundView) (x' : Rest (ckP .two) Fr₃ (P₃ × St₃) W ds)
    (hlaw : ∀ a τ b, on 2 a →
      (pieceOf (held Bb) base ds back x').ior.red.out a τ = some b →
      (∃ t t', Seat.enterOwn a.1.2 = .ok t ∧
        (Seat.leaveOwn a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, a.2)) →
      ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
        (∀ i ∈ rw.outs ++ rw.ctx,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
            (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) b.1
            (strsOf Fr₃ b.2) w) →
        ∀ i ∈ rw.ins,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
            (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) a.1
            (strsOf Fr₃ a.2) (layAt atSix [0, 2, 4] tbl w))
    :
    ∀ a τ b, on 2 a → (pieceOf (held Bb) base ds back x').ior.red.out a τ = some b →
      (∃ t t', Seat.enterOwn a.1.2 = .ok t ∧
        (Seat.leaveOwn a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, a.2)) →
      on (2 + 1) b ∧
        (L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) (2 + 1) b →
        L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) 2 a) := by
  intro a τ b ha hout hq
  have hSt := strsStay_of_out F Fr₃ atSix (pieceOf (held Bb) base ds back x') (open₃ 2) hpins a b τ
    hout
  refine ⟨fwd a b _ _ ha (piece_decides_at _ a τ b hout) hSt, ?_⟩
  rintro ⟨w, hw⟩
  obtain ⟨tbl, law⟩ := hlaw a τ b ha hout hq
  exact ⟨layAt atSix [0, 2, 4] tbl w, KeyRide23.back_32 F _ atSix S K₁ _ rowK32 rfl rfl tbl a.1 b.1
    (strsOf Fr₃ a.2) (strsOf Fr₃ b.2) w (law rowK32 w rfl) (by rw [step_32]; exact hw)⟩

/-- **`Pays` at row 3.2, from the «law» of the way back.** -/
theorem pays_32_of_law {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₃ × St₃) × Fr₃.E.Str → Prop)
    (Bb : Block St₃ Cl)
    (fwd : ∀ a c rs gs, on 2 a → (held Bb : Block (P₃ × St₃) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₃ 2) (strsOf Fr₃ a.2) (strsOf Fr₃ c.2) → on 3 c)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₃ 2), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₃ (P₃ × St₃) W (dB :: dt))
    (hlaw : ∀ a τ b, on 2 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      (∃ t t', Seat.enterOwn a.1.2 = .ok t ∧
        (Seat.leaveOwn a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, a.2)) →
      ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
        (∀ i ∈ rw.outs ++ rw.ctx,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
            (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) b.1
            (strsOf Fr₃ b.2) w) →
        ∀ i ∈ rw.ins,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
            (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) a.1
            (strsOf Fr₃ a.2) (layAt atSix [0, 2, 4] tbl w))
    (num : Fmt.TreeSource → ℕ)
    (hA : AtPlace Fr₃ π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt))
    (hj : johOk π r = true) (hb1 : batOneOk π = true) (hpl : LabelsPub π num nl base)
    (hle : Err.le ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (dB :: dt))) x'.err) :
    Pays Fr₃ π (fun s t => Seat.enterOwn s = .ok t) (fun s t s' => Seat.leaveOwn s t = .ok s')
      (held Bb : Block (P₃ × St₃) Cl) on
      (L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab)) 2 base (dB :: dt) [] x' :=
  K12PaysGameV.pays_gameV π _ _ _ on _ 2 num nl Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rdN base
    dB dt _ (errJ π r dt) x' r hA (fun _ => rfl) hj hb1 (Nat.le_refl _) hpl hle
    (i2_32_of_law F Fr₃ decT recOf orc₁ tab S K₁ π nl r rdN on Bb fwd base hpins (dB :: dt) [] x'
      hlaw)

/-- **What `law_32_of_pays` asks of a state in front of the test** (its binders that name the state). -/
structure Debts32 (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem) (oI : ℕ) (x : (P₃ × St₃) × Fr₃.E.Str) : Prop where
  left : ∀ t tE rs gs, Seat.enterOwn x.1.2 = .ok t →
    (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE →
    CoreLeft csKey F Fr₃ π (nuOf π nl t) (fun s => r s.st) smp mem
      (fun z => z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩) t x.2 x.1 (strsOf Fr₃ x.2)
  seeds : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
    smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
      (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
      seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2
  shown : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
    Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i
  numV : K₁.num x.1.2.loc.w = some 2
  apartI : oI ≠ nOwn x.1.2
  memV : mem x.1.2.loc.w = some ⟨sixS, i2⟩
  memO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩
  kinds : Means.OpenKinds x.1.2.st
  sampledI : ∃ xI : OnBytes.Oracle, x.1.2.st.oracles[oI]? = some xI ∧ xI.sampled = true ∧
    xI.sampleRows.size ≠ 0

/-- **`Pays` at row 3.2.** -/
theorem pays_32 {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₃ × St₃) × Fr₃.E.Str → Prop)
    (Bb : Block St₃ Cl)
    (fwd : ∀ a c rs gs, on 2 a → (held Bb : Block (P₃ × St₃) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₃ 2) (strsOf Fr₃ a.2) (strsOf Fr₃ c.2) → on 3 c)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₃ 2), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₃ (P₃ × St₃) W (dB :: dt))
    (hin : ∀ a, on 2 a →
      on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a₀ idx coll src off₂ off₃ t₁ 2 a)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hmI : mem oI = some ⟨sixS, i0⟩) (ha : a₀ ≠ 0)
    (hdebt : ∀ a τ b, on 2 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      Debts32 F Fr₃ orc₁ K₁ π nl r smp mem oI a)
    (num : Fmt.TreeSource → ℕ)
    (hA : AtPlace Fr₃ π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt))
    (hj : johOk π r = true) (hb1 : batOneOk π = true) (hpl : LabelsPub π num nl base)
    (hle : Err.le ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (dB :: dt))) x'.err) :
    Pays Fr₃ π (fun s t => Seat.enterOwn s = .ok t) (fun s t s' => Seat.leaveOwn s t = .ok s')
      (held Bb : Block (P₃ × St₃) Cl) on
      (L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab)) 2 base (dB :: dt) [] x' :=
  pays_32_of_law F Fr₃ decT recOf orc₁ tab S K₁ π nl r rdN on Bb fwd base hpins dB dt x'
    (fun a τ b ha2 hout hq => by
      have D := hdebt a τ b ha2 hout
      obtain ⟨xI, hxI, hsI, hzI⟩ := D.sampledI
      exact law_32_of_pays F Fr₃ decT recOf orc₁ tab S K₁ a₀ idx coll src off₂ off₃ t₁ π nl r rdN smp
        mem rd hrd (pieceOf (held Bb) base (dB :: dt) [] x') Bb rfl hal a b τ hout hq hj hp
        (hin a ha2) D.left hi hlog told D.seeds D.shown oI hidx hoI hnI D.numV D.apartI hmI D.memV
        D.memO D.kinds ha xI hxI hsI hzI)
    num hA hj hb1 hpl hle

/-- **The same with «left» member by member.** -/
structure Debts32M (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem) (oI : ℕ) (x : (P₃ × St₃) × Fr₃.E.Str) : Prop where
  left : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
    D.st.codes = csKey ∧
    ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
      (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
      ∀ j : Fin D.mems.length,
        MemberLeft csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1 (strsOf Fr₃ x.2) s D j
          (xs j) (es j)
  seeds : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
    smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
      (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
      seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2
  shown : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
    Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i
  numV : K₁.num x.1.2.loc.w = some 2
  apartI : oI ≠ nOwn x.1.2
  memV : mem x.1.2.loc.w = some ⟨sixS, i2⟩
  memO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩
  kinds : Means.OpenKinds x.1.2.st
  sampledI : ∃ xI : OnBytes.Oracle, x.1.2.st.oracles[oI]? = some xI ∧ xI.sampled = true ∧
    xI.sampleRows.size ≠ 0

/-- **`Pays` at row 3.2, «left» member by member.** -/
theorem pays_32M {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₃ × St₃) × Fr₃.E.Str → Prop)
    (Bb : Block St₃ Cl)
    (fwd : ∀ a c rs gs, on 2 a → (held Bb : Block (P₃ × St₃) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₃ 2) (strsOf Fr₃ a.2) (strsOf Fr₃ c.2) → on 3 c)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₃ 2), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₃ (P₃ × St₃) W (dB :: dt))
    (hin : ∀ a, on 2 a →
      on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a₀ idx coll src off₂ off₃ t₁ 2 a)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hmI : mem oI = some ⟨sixS, i0⟩) (ha : a₀ ≠ 0)
    (hdebt : ∀ a τ b, on 2 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      Debts32M F Fr₃ orc₁ K₁ π nl r smp mem oI a)
    (num : Fmt.TreeSource → ℕ)
    (hA : AtPlace Fr₃ π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt))
    (hj : johOk π r = true) (hb1 : batOneOk π = true) (hpl : LabelsPub π num nl base)
    (hle : Err.le ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (dB :: dt))) x'.err) :
    Pays Fr₃ π (fun s t => Seat.enterOwn s = .ok t) (fun s t s' => Seat.leaveOwn s t = .ok s')
      (held Bb : Block (P₃ × St₃) Cl) on
      (L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab)) 2 base (dB :: dt) [] x' :=
  pays_32_of_law F Fr₃ decT recOf orc₁ tab S K₁ π nl r rdN on Bb fwd base hpins dB dt x'
    (fun a τ b ha2 hout hq => by
      have D := hdebt a τ b ha2 hout
      obtain ⟨xI, hxI, hsI, hzI⟩ := D.sampledI
      exact law_32_of_paysM F Fr₃ decT recOf orc₁ tab S K₁ a₀ idx coll src off₂ off₃ t₁ π nl r rdN smp
        mem rd hrd (pieceOf (held Bb) base (dB :: dt) [] x') Bb rfl hal a b τ hout hq hj hp
        (hin a ha2) D.left hi hlog told D.seeds D.shown oI hidx hoI hnI D.numV D.apartI hmI D.memV
        D.memO D.kinds ha xI hxI hsI hzI)
    num hA hj hb1 hpl hle

/-- **The same over the parted remainder `MemberLeft₂`.** «left» does not stand under the test's own
acceptance, as `Debts32`'s does: no premise has grown: MemberLeft₂ is free of every acceptance by its make,
and the whole structure is asked under the piece's accepting run. -/
structure Debts32M₂ (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem) (oI : ℕ) (x : (P₃ × St₃) × Fr₃.E.Str) : Prop where
  left : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
    D.st.codes = csKey ∧
    ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
      (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
      ∀ j : Fin D.mems.length,
        MemberLeft₂ csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1 (strsOf Fr₃ x.2) s D j
          (xs j) (es j)
  seeds : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
    smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
      (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
      seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2
  shown : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
    Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i
  numV : K₁.num x.1.2.loc.w = some 2
  apartI : oI ≠ nOwn x.1.2
  memV : mem x.1.2.loc.w = some ⟨sixS, i2⟩
  memO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩
  kinds : Means.OpenKinds x.1.2.st
  sampledI : ∃ xI : OnBytes.Oracle, x.1.2.st.oracles[oI]? = some xI ∧ xI.sampled = true ∧
    xI.sampleRows.size ≠ 0

/-- **`Pays` at row 3.2, over `MemberLeft₂`.** -/
theorem pays_32M₂ {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₃ × St₃) × Fr₃.E.Str → Prop)
    (Bb : Block St₃ Cl)
    (fwd : ∀ a c rs gs, on 2 a → (held Bb : Block (P₃ × St₃) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₃ 2) (strsOf Fr₃ a.2) (strsOf Fr₃ c.2) → on 3 c)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₃ 2), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₃ (P₃ × St₃) W (dB :: dt))
    (hin : ∀ a, on 2 a →
      on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a₀ idx coll src off₂ off₃ t₁ 2 a)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hmI : mem oI = some ⟨sixS, i0⟩) (ha : a₀ ≠ 0)
    (hdebt : ∀ a τ b, on 2 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      Debts32M₂ F Fr₃ orc₁ K₁ π nl r smp mem oI a)
    (num : Fmt.TreeSource → ℕ)
    (hA : AtPlace Fr₃ π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt))
    (hj : johOk π r = true) (hb1 : batOneOk π = true) (hpl : LabelsPub π num nl base)
    (hle : Err.le ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (dB :: dt))) x'.err) :
    Pays Fr₃ π (fun s t => Seat.enterOwn s = .ok t) (fun s t s' => Seat.leaveOwn s t = .ok s')
      (held Bb : Block (P₃ × St₃) Cl) on
      (L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab)) 2 base (dB :: dt) [] x' :=
  pays_32_of_law F Fr₃ decT recOf orc₁ tab S K₁ π nl r rdN on Bb fwd base hpins dB dt x'
    (fun a τ b ha2 hout hq => by
      have D := hdebt a τ b ha2 hout
      obtain ⟨xI, hxI, hsI, hzI⟩ := D.sampledI
      exact law_32_of_paysM₂ F Fr₃ decT recOf orc₁ tab S K₁ a₀ idx coll src off₂ off₃ t₁ π nl r rdN smp
        mem rd hrd (pieceOf (held Bb) base (dB :: dt) [] x') Bb rfl hal a b τ hout hq hj hp
        (hin a ha2) D.left hi hlog told D.seeds D.shown oI hidx hoI hnI D.numV D.apartI hmI D.memV
        D.memO D.kinds ha xI hxI hsI hzI)
    num hA hj hb1 hpl hle

end Johnson.RunOne.Law.K12Pays32

#print axioms Johnson.RunOne.Law.K12Pays32.i2_32_of_law
#print axioms Johnson.RunOne.Law.K12Pays32.pays_32_of_law
#print axioms Johnson.RunOne.Law.K12Pays32.pays_32
#print axioms Johnson.RunOne.Law.K12Pays32.pays_32M
#print axioms Johnson.RunOne.Law.K12Pays32.pays_32M₂
