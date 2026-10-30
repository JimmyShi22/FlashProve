-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillSeed2At.lean: Johnson/RunOne/KeyFillSeed2.lean's TIE ON THE OOD SAMPLE AT THE KEY FILE's SIX MEMBERS, FOR THE SHARED CHAIN's OWN THREE MESSAGES (the tables' numbers 3 | 4 | 5), AND IN SCOPE. Calls, and rewritings by get3 | get4 | get5.
  tie_six₂_hi            tieS_at₂_hi at csKey · six · numSix · atSix: its premises inj · apart · Tie · «the main rows' code is as long as the tree» are paid by seat_inj_six · shapesApart_six · tie_six · LPFD.mains_six. LEFT: hlog (what F tells of the seat's tree has the length of the member's code)
  lt3 | lt4 | lt5 · get3 | get4 | get5   the members 3 | 4 | 5 of the six, written out: by decide · by rfl
  tie3_six | tie4_six | tie5_six   that at the members 3 | 4 | 5, every number written out: shape shU | shO | shSp · radius 8342420 | 3138896 | 6130 · seat (6, 0) | (7, 0) | (8, 0) · the statement's message 0 | 2 | 3
  fits_six_scope         IN SCOPE: FitsAt at each of the six members at the key file's IOP as written in Lean (Fk X N P): fitsAt_of_noFault at the six «no fault at the seat» of seven_at | six_at
  seatFits_one_scope     IN SCOPE: so SeatFits of the list of that one member alone, at its seat: at each of the six
  tie3_scope | tie4_scope | tie5_scope   IN SCOPE, at F := Fk X N P and the reading (baseAt X decT recOf).h₂, over a frame's oracles (str := Sound.strsOf Fr₂): hlog paid by Johnson.RunOne.Law.KeyAt2932.seats_six_scope.
                         THE FORM IS THAT OF THE PREMISES tieS | tie4 | tie5 OF Johnson/RunOne/KeyRows2225At.lean's keeps₂_send2_at | keeps₂_send5_at, without their premise on the number of messages (not needed), at P₁.codes := csKey · shapeAt P₁ k := the member's shape · radP k := the member's radius · fOf y k := symsW ∘ wordOf ∘ strsOf
BUILT ON: beside the library and the tables' files it imports Johnson/RunOne/Law/KeyAt2932Scope.lean and, beneath that, KeyTenInScope · KeySevenInScope · KeySeatScope23 · KeyScopeNums23.
OBJECT: the tables' reading (baseAt X decT recOf).h₂; the sending kind's Sealed · USER: none yet (meant: the calls of rows 2.2 | 2.5; seatFits_one_scope: the proximity test's kind's files' clause on the word at rows 2.9 | 2.10 | 3.2) · LETTERS: decT · recOf · orc₁ · F · str; in scope: X N P · Fr₂ · the scope's.
NOT SAID: that Sealed holds at any state and oracles (it is what the sending kind's law send_goodIn concludes off the bad set): THESE ARE IMPLICATIONS; NO EXAMPLE IS SHOWN · that the sendings of rows 2.2 | 2.5 have just these codes, shapes, radii and this reader: the caller's four ties · THE RADIUS HAS THE WEIGHT: the user's condPort P₁ radP stands at the same radP as its Sealed: condPort at 8342420 | 3138896 · 6130 is not shown here (meets_six has meetsB at just these three pairs) · that scope's premises can be met together. One size. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillSeed2
import Johnson.Top.Fire.Code.RowsEightSix
import Johnson.RunOne.Law.KeyAt2932Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces madeAt sourceOf)
open VerifiableInference.Desc.K1 (Sealed)
open Cb OnBytes.Maker OnBytes.Slice
open Johnson.Pack hiding shU shO
open Johnson.Top.H (csKey shU shO shSp)
open Johnson.G.OfPlan (Made)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.KeyLetters (seven_at six_at)
open Johnson.RunOne.Law.KeyAt2932 (seats_six_scope)
open LPFD (baseAt)

section
variable {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs)

/-- **The tie at the six**, for a member whose number is 3 or more: what is left is hlog. -/
theorem tie_six₂_hi (i : Fin six.length) (hi : ¬ numSix i < 3) (o₀ : ℕ) (ho : orc₂ (numSix i) = some o₀)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (s : OnBytes.OracleShape) (e : ℕ) (hl : six.get i = (s, e)) (a : P₂ × St₂) (y : Y')
    (h : Sealed csKey s e (symsW csKey s e (wordOf F (str y) (atSix (numSix i)).1 (atSix (numSix i)).2)) a.2.st o₀) :
    hasSmp (baseK csKey six numSix atSix decT recOf orc₁).h₂ (atSix (numSix i)).1 (atSix (numSix i)).2 a = true ∧
      NoColl F (baseK csKey six numSix atSix decT recOf orc₁).h₂ (atSix (numSix i)).1 (atSix (numSix i)).2 a (str y) :=
  tieS_at₂_hi csKey six numSix atSix decT recOf orc₁ F str seat_inj_six shapesApart_six i hi o₀ ho (tie_six i) hlog (LPFD.mains_six i) s e hl a y h

theorem lt3 : 3 < six.length := by decide
theorem lt4 : 4 < six.length := by decide
theorem lt5 : 5 < six.length := by decide
/-- The members 3 | 4 | 5 of the six, written out. -/
theorem get3 : six.get ⟨3, lt3⟩ = (shU, 8342420) := rfl
theorem get4 : six.get ⟨4, lt4⟩ = (shO, 3138896) := rfl
theorem get5 : six.get ⟨5, lt5⟩ = (shSp, 6130) := rfl

/-- The tables' number 3: the shape shU at the radius 8342420, the seat (6, 0), the shared chain's statement's message 0. -/
theorem tie3_six (hlog : ∀ o, F.oracleAt 6 = some o → o.logLength = aOf csKey shU) (a : P₂ × St₂) (y : Y')
    (h : Sealed csKey shU 8342420 (symsW csKey shU 8342420 (wordOf F (str y) 6 0)) a.2.st 0) :
    hasSmp (baseK csKey six numSix atSix decT recOf orc₁).h₂ (atSix 3).1 (atSix 3).2 a = true ∧
      NoColl F (baseK csKey six numSix atSix decT recOf orc₁).h₂ (atSix 3).1 (atSix 3).2 a (str y) := by
  refine tie_six₂_hi decT recOf orc₁ F str ⟨3, lt3⟩ (by show ¬ (3 : ℕ) < 3; omega) 0 rfl ?_ shU 8342420 get3 a y h
  intro o ho
  rw [get3]
  exact hlog o ho

/-- The tables' number 4: the shape shO at the radius 3138896, the seat (7, 0), the statement's message 2. -/
theorem tie4_six (hlog : ∀ o, F.oracleAt 7 = some o → o.logLength = aOf csKey shO) (a : P₂ × St₂) (y : Y')
    (h : Sealed csKey shO 3138896 (symsW csKey shO 3138896 (wordOf F (str y) 7 0)) a.2.st 2) :
    hasSmp (baseK csKey six numSix atSix decT recOf orc₁).h₂ (atSix 4).1 (atSix 4).2 a = true ∧
      NoColl F (baseK csKey six numSix atSix decT recOf orc₁).h₂ (atSix 4).1 (atSix 4).2 a (str y) := by
  refine tie_six₂_hi decT recOf orc₁ F str ⟨4, lt4⟩ (by show ¬ (4 : ℕ) < 3; omega) 2 rfl ?_ shO 3138896 get4 a y h
  intro o ho
  rw [get4]
  exact hlog o ho

/-- The tables' number 5: the shape shSp at the radius 6130, the seat (8, 0), the statement's message 3. -/
theorem tie5_six (hlog : ∀ o, F.oracleAt 8 = some o → o.logLength = aOf csKey shSp) (a : P₂ × St₂) (y : Y')
    (h : Sealed csKey shSp 6130 (symsW csKey shSp 6130 (wordOf F (str y) 8 0)) a.2.st 3) :
    hasSmp (baseK csKey six numSix atSix decT recOf orc₁).h₂ (atSix 5).1 (atSix 5).2 a = true ∧
      NoColl F (baseK csKey six numSix atSix decT recOf orc₁).h₂ (atSix 5).1 (atSix 5).2 a (str y) := by
  refine tie_six₂_hi decT recOf orc₁ F str ⟨5, lt5⟩ (by show ¬ (5 : ℕ) < 3; omega) 3 rfl ?_ shSp 6130 get5 a y h
  intro o ho
  rw [get5]
  exact hlog o ho

end

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **IN SCOPE: each of the six members' seats fits** at the key file's IOP as written in Lean. -/
theorem fits_six_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull) :
    ∀ i : Fin six.length, FitsAt csKey six (seatAt six numSix atSix) (Fk X N P) i := by
  have hD : (Fk X N P).data "key file" = .ok Johnson.G.writtenKFull := by rw [hD₀, hDK]
  obtain ⟨h0, h1, h2⟩ := (seven_at hZ hP hm hX hp hw hD).1 "" "" ""
  obtain ⟨h3, h4, h5⟩ := (six_at hZ hP hm hX hp hw hD).1 "" "" ""
  intro i
  match i with
  | ⟨0, _⟩ => exact fitsAt_of_noFault csKey six (seatAt six numSix atSix) (Fk X N P) _ "" h0
  | ⟨1, _⟩ => exact fitsAt_of_noFault csKey six (seatAt six numSix atSix) (Fk X N P) _ "" h1
  | ⟨2, _⟩ => exact fitsAt_of_noFault csKey six (seatAt six numSix atSix) (Fk X N P) _ "" h2
  | ⟨3, _⟩ => exact fitsAt_of_noFault csKey six (seatAt six numSix atSix) (Fk X N P) _ "" h3
  | ⟨4, _⟩ => exact fitsAt_of_noFault csKey six (seatAt six numSix atSix) (Fk X N P) _ "" h4
  | ⟨5, _⟩ => exact fitsAt_of_noFault csKey six (seatAt six numSix atSix) (Fk X N P) _ "" h5
  | ⟨n + 6, hn⟩ =>
    exact absurd hn (by
      show ¬ n + 6 < 6
      omega)

/-- **IN SCOPE: the list of one member alone fits at that member's seat**, at each of the six. -/
theorem seatFits_one_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    (i : Fin six.length) : Sound.SeatFits (Fk X N P) csKey [six.get i] (fun _ => seatAt six numSix atSix i) :=
  (seatFits_iff csKey [six.get i] (fun _ => seatAt six numSix atSix i) (Fk X N P)).2 fun j => by
    obtain ⟨v, hv⟩ := j
    obtain rfl : v = 0 := Nat.lt_one_iff.1 hv
    exact fits_six_scope hZ hP hm hX hp hw DK hD₀ hDK i

variable {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (Fr₂ : Sound.Frame)

/-- **IN SCOPE, the form of row 2.2's premise tieS.** -/
theorem tie3_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull) :
    ∀ x' : (P₂ × St₂) × Fr₂.E.Str,
      Sealed csKey shU 8342420 (symsW csKey shU 8342420 (wordOf (Fk X N P) (Sound.strsOf Fr₂ x'.2) 6 0)) x'.1.2.st 0 →
      hasSmp (baseAt X decT recOf).h₂ (atSix 3).1 (atSix 3).2 x'.1 = true ∧ NoColl (Fk X N P) (baseAt X decT recOf).h₂ (atSix 3).1 (atSix 3).2 x'.1 (Sound.strsOf Fr₂ x'.2) :=
  fun x' h => by
    have H := (seats_six_scope hZ hP hm hX hp hw DK hD₀ hDK ⟨3, lt3⟩).2
    rw [get3] at H
    exact tie3_six decT recOf _ (Fk X N P) (Sound.strsOf Fr₂) (fun o ho => H o ho) x'.1 x'.2 h

/-- **IN SCOPE, the form of row 2.5's premise tie4.** -/
theorem tie4_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull) :
    ∀ x' : (P₂ × St₂) × Fr₂.E.Str,
      Sealed csKey shO 3138896 (symsW csKey shO 3138896 (wordOf (Fk X N P) (Sound.strsOf Fr₂ x'.2) 7 0)) x'.1.2.st 2 →
      hasSmp (baseAt X decT recOf).h₂ (atSix 4).1 (atSix 4).2 x'.1 = true ∧ NoColl (Fk X N P) (baseAt X decT recOf).h₂ (atSix 4).1 (atSix 4).2 x'.1 (Sound.strsOf Fr₂ x'.2) :=
  fun x' h => by
    have H := (seats_six_scope hZ hP hm hX hp hw DK hD₀ hDK ⟨4, lt4⟩).2
    rw [get4] at H
    exact tie4_six decT recOf _ (Fk X N P) (Sound.strsOf Fr₂) (fun o ho => H o ho) x'.1 x'.2 h

/-- **IN SCOPE, the form of row 2.5's premise tie5.** -/
theorem tie5_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull) :
    ∀ x' : (P₂ × St₂) × Fr₂.E.Str,
      Sealed csKey shSp 6130 (symsW csKey shSp 6130 (wordOf (Fk X N P) (Sound.strsOf Fr₂ x'.2) 8 0)) x'.1.2.st 3 →
      hasSmp (baseAt X decT recOf).h₂ (atSix 5).1 (atSix 5).2 x'.1 = true ∧ NoColl (Fk X N P) (baseAt X decT recOf).h₂ (atSix 5).1 (atSix 5).2 x'.1 (Sound.strsOf Fr₂ x'.2) :=
  fun x' h => by
    have H := (seats_six_scope hZ hP hm hX hp hw DK hD₀ hDK ⟨5, lt5⟩).2
    rw [get5] at H
    exact tie5_six decT recOf _ (Fk X N P) (Sound.strsOf Fr₂) (fun o ho => H o ho) x'.1 x'.2 h

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.tie_six₂_hi
#print axioms Johnson.RunOne.KeyRows23.lt3
#print axioms Johnson.RunOne.KeyRows23.lt4
#print axioms Johnson.RunOne.KeyRows23.lt5
#print axioms Johnson.RunOne.KeyRows23.get3
#print axioms Johnson.RunOne.KeyRows23.get4
#print axioms Johnson.RunOne.KeyRows23.get5
#print axioms Johnson.RunOne.KeyRows23.tie3_six
#print axioms Johnson.RunOne.KeyRows23.tie4_six
#print axioms Johnson.RunOne.KeyRows23.tie5_six
#print axioms Johnson.RunOne.KeyRows23.fits_six_scope
#print axioms Johnson.RunOne.KeyRows23.seatFits_one_scope
#print axioms Johnson.RunOne.KeyRows23.tie3_scope
#print axioms Johnson.RunOne.KeyRows23.tie4_scope
#print axioms Johnson.RunOne.KeyRows23.tie5_scope
