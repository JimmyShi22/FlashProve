-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HFOfDoor.lean: **THE PREMISE hF OF `hCar_ren` | `hCar_lay`
(HCarRen.lean, HCarLay.lean: at every row, way in, front and frame: the front carries `rows`, and
`FrontFitsAt`), TO THE LETTER, FROM FACTS ON THE STATE s' AT THE BORDER BEHIND THE CLOSING**, with
rows := (rdBK s').1.rows, the names `namesOf … no` and mW b := mWRaw … (strsOf F b.2) tree skip aF.
The join of `frontFitsAt_of` (FrontFitsOf.lean) with `DoorReads`
(Johnson/Top/H0/Walk/FrameCarryFenceEnds.lean): what the way in lets in has the border's state's
book and number of roots, and its front carries the border's state's frame's rows. Theorems. No
other file turns.

  `shownAt_congr`, `mWRaw_congr`: «every leaf is shown» and the fresh mask's raw word read of the
    strings the columns of the seat's tree alone.
  `hF_of_door`: **hF**, from: DoorReads at every answer of the way in · `frontFitsAt_of`'s premises
    with the layout, the sizes, the three tests on the book and PlanAt AT s' ITSELF · ShownAt at the
    strings IN FRONT of the closing · the members' seats' trees and the fresh mask's tree stay ·
    FOUR FACTS ON THE FRONT (hFr): the book behind the sending is there · the front's statement has
    the written shape at each member's number · it has 2 ^ h mask rows at the fresh mask · the kept
    members' main rows add up to rows.keptRows.
SO K2Caller/KeptSeatOf.lean's CAVEAT («the three tests are asked at the state that the way in lets
in; the table's facts speak of the state at the border») IS MET: the tests read the book and the
number of roots alone, and DoorReads keeps both.
IS THE FRESH MASK's TREE AMONG THE STRINGS IN FRONT? By the text
(Johnson/Desc/First/Close/Closing.lean): `closing`'s letter mask is «the fresh mask's message, as
the link's first message has left it»; the closing refuses where there is none («K10.mask») and
takes no column: so the message is sent before the closing's border. That its tree stays (hyF) is a
premise.
Limits. EVERY PREMISE STANDS; NONE IS SHOWN AT A REACHED STATE. The four facts on the front are on
the switch's front's maker's text: not treated. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.FrontFitsOf
import Johnson.Top.H0.Walk.FrameCarryFenceEnds
import Johnson.Desc.First.Close.Law.AtBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (ShownAt Frame strsOf)
open VerifiableInference.Desc.First.K2Caller (SeatFitAt doorZ)
open VerifiableInference.Desc.First.Close (groupLayK namesOf posOf ShapesAre AgreesWith layAt sizesM
  sizesZ rdBK)
open _root_.Tw.K2 (switchNotices)

theorem shownAt_congr {Xi : Type} (G : FileDescription Xi) (cs : Codes) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) {y y' : Strs} (i : Fin l.length)
    (h : ∀ x, y.col (seat i).1 x = y'.col (seat i).1 x) (hs : ShownAt G cs l seat y' i) :
    ShownAt G cs l seat y i := by
  intro x hx
  have e : wordOf G y (seat i).1 (seat i).2 x = wordOf G y' (seat i).1 (seat i).2 x := by
    unfold wordOf
    rw [h x]
  rw [e]
  exact hs x hx

theorem mWRaw_congr (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
    (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
    (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
    (kp : {i // mem i} → Prop) [DecidablePred kp] {y y' : Strs} (tree skip aF : ℕ)
    (h : ∀ x, y.col tree x = y'.col tree x) :
    mWRaw cs l mem s e oM oZ hM hZ kp y tree skip aF =
      mWRaw cs l mem s e oM oZ hM hZ kp y' tree skip aF := by
  unfold mWRaw
  simp only [h]

/-- **hF, FROM FACTS ON THE STATE AT THE BORDER.** -/
theorem hF_of_door (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    (no : Fin lo.length → ℕ) {Xi : Type} (G : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ)
    {F : Frame} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ) (a : First.S × F.E.Str) (s' : First.S)
    (y : Strs) (tree skip aF : ℕ)
    (hD : ∀ t, doorZ Z m s' = some t →
      _root_.Johnson.Desc.First.Walk.Tied.DoorReads (ProofFile.pAtK2 Z m) s' t)
    (hgood : (groupLayK cs lo s e kb hM hZ).Good) {T : Statement} {Gr : Group}
    (H : ShapesAre T Gr lo kb no) (hLm : s'.live.frame.rows.layout.members = Gr.members)
    (hLk : s'.live.frame.rows.layout.kept = Gr.kept)
    (hA : AgreesWith lo kb s'.live.frame.rows.layout) (hm : s'.live.frame.rows.masks = 2)
    (hγ : s'.live.frame.rows.gamma.length = s.h + s.g)
    (hk : s'.live.frame.rows.layout.k = s.h + s.g) (hh : s'.live.frame.rows.layout.h = s.h)
    (hord : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → ∀ i : Fin lo.length, memMain lo i →
      kb i = true → (keptNosOf lo kb)[r.kept.idxOf i.val]? = some (posOf lo i))
    (hS : ∀ b : {i // memMain lo i}, SeatFitAt G cs lo seat b.1)
    (hSh : ∀ b : {i // memMain lo i}, ShownAt G cs lo seat (strsOf F a.2) b.1)
    (hy : ∀ i x, y.col (seat i).1 x = (strsOf F a.2).col (seat i).1 x)
    (hyF : ∀ x, y.col tree x = (strsOf F a.2).col tree x)
    (Lp : VerifiableInference.Desc.K12.Door.Laid)
    (hP : ∀ b : {i // memMain lo i}, PlanAt G s' Lp
      (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) y (no b.1) (seat b.1) (aOf cs (lo.get b.1).1))
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook
      (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree s' = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats Lp s' = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits s' = true)
    (hpos : 2 ^ s.C.a ≤ 2 ^ (ProofFile.pAtK2 Z m).logN)
    (hfo : s'.live.frame.rows.fresh < s'.book.place.size) (tpF tnF : ℕ)
    (hfL : Lp.places[s'.live.frame.rows.fresh]? = some (tpF, tnF)) (shF0 : TreeShape)
    (hfs : Lp.shapes[tpF]? = some shF0) (hfa : shF0.logN = aF)
    (hforc : ∀ x, x < 2 ^ s.C.a →
      First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y tpF (x % 2 ^ aF) = y.col tree (x % 2 ^ aF))
    (hfskip : shF0.mainWidth + (shF0.maskSymbols.extract 0 tnF).foldl (· + ·) 0 = skip)
    (hFr : ∀ t fx', doorZ Z m s' = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' →
      (∃ B, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx'.st t.book t.roots
        (switchNotices fx'.T fx'.others) = some B) ∧
      (∀ b : {i // memMain lo i}, ∃ xo, (First.K2.skelOf fx').oracles[no b.1]? = some xo ∧
        xo.shape = (lo.get b.1).1) ∧
      (∃ xoF, (First.K2.skelOf fx').oracles[s'.live.frame.rows.fresh]? = some xoF ∧
        xoF.shape.maskRows = 2 ^ s.h) ∧
      keptCount s'.live.frame.rows.layout
        (fun w => ((First.K2.skelOf fx').oracles.getD
          (s'.live.frame.rows.layout.members.getD w 0) default).shape.mainRows)
        (List.range s'.live.frame.rows.layout.members.size) = s'.live.frame.rows.keptRows) :
    ∀ r t fx' W₀, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → doorZ Z m s' = some t →
      First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' → First.K2.frameAt fx' = some W₀ →
      fx'.f.rows = (rdBK s').1.rows ∧
      FrontFitsAt cs lo (memMain lo) s e
        (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
        hM hZ (fun a => kb a.1 = true) r.kept G
        seat y (ProofFile.pAtK2 Z m) t (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) (fun b => no b.1)
        (fun b => posOf lo b.1)
        (mWRaw cs lo (memMain lo) s e (fun i => layAt (sizesM lo kb) i.val)
          (fun i => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 = true) (strsOf F a.2) tree
          skip aF)
        (namesOf cs lo s e kb hM hZ no) fx' W₀ := by
  intro r t fx' W₀ h1 h2 h3 h4
  have D := hD t h2
  have er : fx'.f.rows = s'.live.frame.rows := D.rows fx' h3
  refine ⟨er, ?_⟩
  obtain ⟨⟨B, hB⟩, hsh, ⟨xoF, hfx, hfr⟩, hkc⟩ := hFr t fx' h2 h3
  rw [← mWRaw_congr cs lo (memMain lo) s e _ _ hM hZ _ tree skip aF hyF]
  exact frontFitsAt_of cs lo s e kb hM hZ no r.kept G seat y (ProofFile.pAtK2 Z m) t _ fx' W₀ hgood H
    (by rw [er]; exact hLm) (by rw [er]; exact hLk) (by rw [er]; exact hA) (by rw [er]; exact hm)
    (by rw [er]; exact hγ) (by rw [er]; exact hk) (by rw [er]; exact hh) h4 (hord r h1) hsh hS
    (fun b => shownAt_congr G cs lo seat b.1 (hy b.1) (hSh b)) Lp
    (fun b => ⟨by rw [D.book]; exact (hP b).is.1, (hP b).is.2⟩)
    (by
      unfold VerifiableInference.Desc.K12.Door.atFirstBook at hIn ⊢
      rw [D.book, D.roots]
      exact hIn)
    (by
      unfold VerifiableInference.Desc.K12.Door.atFirstSeats at hSe ⊢
      rw [D.book]
      exact hSe)
    (by
      unfold VerifiableInference.Desc.K12.Door.atFirstFits at hFi ⊢
      rw [D.book]
      exact hFi)
    B hB hpos tree skip aF (by rw [er, D.book]; exact hfo) tpF tnF (by rw [er]; exact hfL) shF0 hfs
    xoF (by rw [er]; exact hfx) hfr hfa hforc hfskip (by rw [er]; exact hkc)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shownAt_congr
#print axioms VerifiableInference.Desc.LinkJoin.mWRaw_congr
#print axioms VerifiableInference.Desc.LinkJoin.hF_of_door
