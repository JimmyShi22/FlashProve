-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HFOfEnd.lean: **THE PREMISE hF OF `hCar_ren`
  (HCarRen.lean), TO THE
LETTER, FROM WHAT IS KNOWN IN FRONT OF K10's CLOSING AND WHAT THE CLOSING HAS WRITTEN**:
`hF_of_door` (HFOfDoor.lean) with its premises at the border behind carried back over the closing:
the state behind is a'.1 = wrK a.1 f' S' and the trees below the base stay (`K10EndS`'s own
clauses). By
`tests_behind`, `wrK_book` (EndReads.lean), `doorReads_door` (FrontStEnds.lean),
`planAt_below`, `orcY_below` (OrcBelow.lean). A theorem. It changes no other file.

  `hF_of_end`: **hF at s' := a'.1, y := strsOf F a'.2, rows := (rdBK a'.1).1.rows, N := namesOf …
    no, the fresh mask's word mWRaw … (strsOf F a.2) tree skip aF**, from:
    IN FRONT (at a.1 and the strings a.2): the three tests on the book · planPubB at every member ·
      the fresh mask's number is
      below the book's places · ShownAt at every member;
    ON THE PLAN: the plan's list has the member's seat at its number, and (tree, tnF) at the fresh
      mask's · these trees are below the first chain's number of trees and below the base · the
      fresh mask's tree's shape · SeatFitAt · the sentence on lo, kb, r.kept · 2 ^ C.a ≤ 2 ^ logN;
    ON WHAT THE CLOSING HAS WRITTEN (a'.1.live.frame.rows): its layout has Gr's members and flags ·
      AgreesWith · the four sizes;
    AND: Good · ShapesAre · the proof file's rounds have data · hFr (four facts on the front) · hH.
ONE PREMISE: hH («where the switch stands at the head,
the state does not stand at the head's link»). at_head_behind_24 shows
that behind the closing of link 24 the state DOES stand at the
head: so an outright form hangs on which switch stands at the head. hH IS ASKED AT THE STATE
BEHIND, UNDER «THE WAY IN ANSWERS»: the form that hH_of_stand | hH_behind_K10 end in.
Limits. EVERY PREMISE STANDS; NONE IS SHOWN AT A REACHED STATE HERE. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HFOfDoor
import Johnson.Desc.First.Link.Law.EndReads
import Johnson.Desc.First.Link.Law.FrontStEnds
import Johnson.Desc.First.Link.Law.OrcBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker Cb Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound (ShownAt Frame strsOf)
open VerifiableInference.Desc.First.K2Caller (SeatFitAt doorZ)
open VerifiableInference.Desc.First.Close (groupLayK namesOf posOf ShapesAre AgreesWith layAt sizesM
  sizesZ rdBK wrK)
open _root_.Tw.K2 (switchNotices)

/-- **hF, FROM WHAT IS KNOWN IN FRONT OF THE CLOSING AND WHAT IT HAS WRITTEN.** -/
theorem hF_of_end (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    (no : Fin lo.length → ℕ) {Xi : Type} (G : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ)
    {F : Frame} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ) (D : WholeD)
    (hW : ProofFile.wholeAt Z = some D) (a a' : First.S × F.E.Str) (f' : ReqFrame) (S' : Statement)
    (ew : a'.1 = wrK a.1 f' S') (base : ℕ)
    (hst : ∀ j x, j < base → (strsOf F a'.2).col j x = (strsOf F a.2).col j x)
    (hH : ∀ t, doorZ Z m a'.1 = some t → (ProofFile.pAtK2 Z m).stands = .head →
      ∀ b, a'.1.here ≠ .head b)
    (hgood : (groupLayK cs lo s e kb hM hZ).Good) {T : Statement} {Gr : Group}
    (H : ShapesAre T Gr lo kb no) (hLm : a'.1.live.frame.rows.layout.members = Gr.members)
    (hLk : a'.1.live.frame.rows.layout.kept = Gr.kept)
    (hA : AgreesWith lo kb a'.1.live.frame.rows.layout) (hm : a'.1.live.frame.rows.masks = 2)
    (hγ : a'.1.live.frame.rows.gamma.length = s.h + s.g)
    (hk : a'.1.live.frame.rows.layout.k = s.h + s.g) (hh : a'.1.live.frame.rows.layout.h = s.h)
    (hord : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → ∀ i : Fin lo.length, memMain lo i →
      kb i = true → (keptNosOf lo kb)[r.kept.idxOf i.val]? = some (posOf lo i))
    (hS : ∀ b : {i // memMain lo i}, SeatFitAt G cs lo seat b.1)
    (hSh : ∀ b : {i // memMain lo i}, ShownAt G cs lo seat (strsOf F a.2) b.1)
    (Lp : VerifiableInference.Desc.K12.Door.Laid)
    (hPB : ∀ b : {i // memMain lo i},
      planPubB G a.1 Lp (no b.1) (seat b.1) (aOf cs (lo.get b.1).1) = true)
    (hPl : ∀ b : {i // memMain lo i}, Lp.places[no b.1]? = some (seat b.1))
    (hsD : ∀ b : {i // memMain lo i}, (seat b.1).1 < D.t₁) (hsB : ∀ i, (seat i).1 < base)
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook
      (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree a.1 = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats Lp a.1 = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits a.1 = true)
    (hpos : 2 ^ s.C.a ≤ 2 ^ (ProofFile.pAtK2 Z m).logN) (tree tnF skip aF : ℕ)
    (hfo : a'.1.live.frame.rows.fresh < a.1.book.place.size)
    (hfL : Lp.places[a'.1.live.frame.rows.fresh]? = some (tree, tnF)) (shF0 : TreeShape)
    (hfs : Lp.shapes[tree]? = some shF0) (hfa : shF0.logN = aF) (htD : tree < D.t₁)
    (htB : tree < base)
    (hfskip : shF0.mainWidth + (shF0.maskSymbols.extract 0 tnF).foldl (· + ·) 0 = skip)
    (hFr : ∀ t fx', doorZ Z m a'.1 = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' →
      (∃ B, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx'.st t.book t.roots
        (switchNotices fx'.T fx'.others) = some B) ∧
      (∀ b : {i // memMain lo i}, ∃ xo, (First.K2.skelOf fx').oracles[no b.1]? = some xo ∧
        xo.shape = (lo.get b.1).1) ∧
      (∃ xoF, (First.K2.skelOf fx').oracles[a'.1.live.frame.rows.fresh]? = some xoF ∧
        xoF.shape.maskRows = 2 ^ s.h) ∧
      keptCount a'.1.live.frame.rows.layout
        (fun w => ((First.K2.skelOf fx').oracles.getD
          (a'.1.live.frame.rows.layout.members.getD w 0) default).shape.mainRows)
        (List.range a'.1.live.frame.rows.layout.members.size) =
        a'.1.live.frame.rows.keptRows) :
    ∀ r t fx' W₀, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → doorZ Z m a'.1 = some t →
      First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' → First.K2.frameAt fx' = some W₀ →
      fx'.f.rows = (rdBK a'.1).1.rows ∧
      FrontFitsAt cs lo (memMain lo) s e
        (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
        hM hZ (fun a => kb a.1 = true) r.kept G
        seat (strsOf F a'.2) (ProofFile.pAtK2 Z m) t
        (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) (strsOf F a'.2)) (fun b => no b.1)
        (fun b => posOf lo b.1)
        (mWRaw cs lo (memMain lo) s e (fun i => layAt (sizesM lo kb) i.val)
          (fun i => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 = true) (strsOf F a.2) tree
          skip aF)
        (namesOf cs lo s e kb hM hZ no) fx' W₀ := by
  have eb : a'.1.book = a.1.book := by rw [ew]; exact wrK_book _ _ _
  obtain ⟨t1, t2, t3⟩ := tests_behind ew (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree Lp
  exact hF_of_door cs lo s e kb hM hZ no G seat Z lay m a a'.1 (strsOf F a'.2) tree skip aF
    (fun t hd => doorReads_door (hH t hd) t hd) hgood H hLm hLk hA hm hγ hk hh hord hS hSh
    (fun i x => hst _ x (hsB i)) (fun x => hst _ x htB) Lp
    (fun b => by
      have hb : planPubB G a'.1 Lp (no b.1) (seat b.1) (aOf cs (lo.get b.1).1) = true := by
        unfold planPubB at hPB ⊢
        rw [eb]
        exact hPB b
      exact planAt_below hb Z D hW (hPl b) (hsD b) _)
    (t1.trans hIn) (t2.trans hSe) (t3.trans hFi) hpos (by rw [eb]; exact hfo) tree tnF hfL shF0 hfs
    hfa (fun x _ => orcY_below Z D hW tree htD _ _) hfskip hFr

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hF_of_end
