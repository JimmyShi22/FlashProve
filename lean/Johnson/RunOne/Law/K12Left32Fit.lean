-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Left32Fit.lean: The key file's
tables, row 3.2: THAT TWO FILES FIT, HELD BY LEAN: `shapeIs_32` (BookAt32.lean: at the seats
0 · 2 · 4 the last chain's book's tree whose number through the file is the seat's stands and has the
shape that the IOP as written in Lean tells of it; in scope, off the history) IS the premise htold of
`word_32S` (K12Left32.lean: clause (7) of `MemberLeft` at a member), at F := Fk X N P ·
off₂ := off₂N · off₃ := off₃N · t₁ := 6. Two statements; each proof is one call.
  `htold_32_scope`: word_32S's htold, to the letter, from shapeIs_32's premises, the door and hat.
  `word_32_scope`: word_32S with htold so paid and AtOk · off₃ 6 = 7 paid by
    `atOk_six` (KeyAtOff.lean) and by rfl.
What it is not. NO EXAMPLE: empty where no state is reached. WITH shapeIs_32 COMES ITS PREMISE hw :
(Fk X N P).wantedOk = true: a test that stands beside planOk, not in it: BookAt32.lean's premise at the key file:
who shows it in scope is not known here. The other premises of word_32S stand as
binders: the mask · BookOrdW 6 1 t.book and the count of its trees · the book's place of the message ·
the entry · SeatFits at the member · ShownAt · the frame's depth. It pays no field of the tables. No
soundness is claimed. Nothing on hiding.

-/
import Johnson.RunOne.Law.K12Left32
import Johnson.RunOne.Law.BookAt32

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Left32Fit
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (FirstState Xi)
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf)
open Johnson.Top.H (csKey)
open Johnson.RunOne.KeyRows23 (Fk St₂ St₃ atSix numSix seatAt)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.G (writtenKFull)
open LPFD (Hist₃)
open LPFD.CandLaid (sixS)
open H2K.First (BookOrdW)
open H2K.Pin (strOf layOf)

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
variable {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made}

/-- **word_32S's htold, in scope, off the history.** -/
theorem htold_32_scope (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z)
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = writtenKFull) (hN : rangesNumbers m = .ok N)
    (D : WholeD) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) (t : T12)
    (ht : Seat.enterOwn a.2 = .ok t) (i : Fin six.length) (hk : i.val ∈ [0, 2, 4]) (q : ℕ × ℕ)
    (hat : atSix i.val = (LPFD.off₃N q.1, q.2)) :
    ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i).1 = some o →
      ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o := by
  cases ht
  exact BookAt32.shapeIs_32 hZ hP hm hX hp hw DK hD₀ hDK hN D a h i.val hk q.1
    (congrArg Prod.fst hat)

/-- **Clause (7) at a member of row 3.2, the tree's shape paid in scope.** «scope» in the name says: htold is
paid in scope; NOT: nothing is left: the mask · the book's order and count · the place · the entry ·
SeatFits · ShownAt · the depth stand as binders. -/
theorem word_32_scope (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z)
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = writtenKFull) (hN : rangesNumbers m = .ok N)
    (Dh : WholeD) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) Dh 2 a) (t : T12)
    (ht : Seat.enterOwn a.2 = .ok t) (Fr₃ : Frame) (π : P12) (hmask : t.mask.isSome = true)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : GroupLayout)
    (D : H2K.First.Plain) (hf : Fixes π t s rest G0 Ly D) (hB : BookOrdW 6 1 t.book)
    (hsz : t.book.trees.size = 6 + 1) (j : Fin D.mems.length) (i : Fin six.length)
    (hk : i.val ∈ [0, 2, 4]) (q : ℕ × ℕ) (hq : t.book.place[(D.mems.get j).id]? = some q)
    (hat : atSix i.val = (LPFD.off₃N q.1, q.2)) (y : Fr₃.E.Str) (e0 : ℕ)
    (hx : six.get i = ((D.mems.get j).sh, e0))
    (hF : Sound.SeatFits (Fk X N P) csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hS : Sound.ShownAt (Fk X N P) csKey six (seatAt six numSix atSix) (strsOf Fr₃ y) i)
    (hd : ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i).1 = some o →
      ∀ e ∈ Fr₃.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ o.logLength) :
    HEq (strOf csKey (D.mems.get j).sh e0 (layOf (D.mems.get j))
        (W0 Fr₃ (nuOf π (nlKW 6) t) D.book y (D.mems.get j).t).1
        (W0 Fr₃ (nuOf π (nlKW 6) t) D.book y (D.mems.get j).t).2)
      (Sound.wordsOf (Fk X N P) csKey (⟨sixS, i⟩ : Sound.Mem).1.l (⟨sixS, i⟩ : Sound.Mem).1.seat
        (strsOf Fr₃ y) (⟨sixS, i⟩ : Sound.Mem).2) :=
  K12Left32.word_32S (Fk X N P) Fr₃ π 6 LPFD.off₂N LPFD.off₃N LPFD.atOk_six rfl t hmask s rest G0 Ly D
    hf hB hsz j i hk q hq hat y e0 hx hF hS
    (htold_32_scope hZ hP hm hX hp hw DK hD₀ hDK hN Dh a h t ht i hk q hat) hd

end Johnson.RunOne.Law.K12Left32Fit

#print axioms Johnson.RunOne.Law.K12Left32Fit.htold_32_scope
#print axioms Johnson.RunOne.Law.K12Left32Fit.word_32_scope
