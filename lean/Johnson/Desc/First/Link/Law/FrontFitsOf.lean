-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrontFitsOf.lean: **`FrontFitsAt` (CarryAtFull.lean: all that `hCar`'s
theorems ask of a front and its frame: fifteen clauses) WHOLE, FROM ITS CLAUSES' PAYERS JOINED**: at
the program's own layout (`groupLayK cs lo s e kb hM hZ`), the numbering no, ix a := posOf lo a.1,
the closing's files' names `namesOf … no` and the fresh mask's word off the raw columns (`mWRaw`).
A structure and a theorem.

  `PlanAt`: what is asked of the plan's list and of the oracles' reading AT ONE MESSAGE o WITH A
    SEAT: o is below the state's book's places · the plan's list has (tp, the seat's tenant) at o
    and a shape sh0 at tp · the tree is 2 ^ a leaves long · the reading at the key tp is Strs.col
    at the seat's tree, at every leaf · where the description tells the seat's tree, the listed
    shape's two skips in front of the tenant are the description's.
  `frontFitsAt_of`: **FrontFitsAt …, from:** the group's data are in order (Good) · ShapesAre T Gr
    lo kb no · the front's rows' layout has Gr's members and flags · AgreesWith · the four sizes ·
    the front's frame · the sentence on lo, kb, kl (KeptOrder's) · the front's statement has the
    written shape at no i · at every member: SeatFitAt · ShownAt · PlanAt · the three tests on the
    state · the book behind the sending · the positions are at most 2 ^ p.logN · at the fresh mask:
    the plan's list's entry, the reading, 2 ^ h mask rows · the kept members' main rows add up to
    rows.keptRows.
WHO IS CALLED: `laysFit_at` (LaysFitAt.lean) · `firstZ_at`, `all_of` (AllOf.lean) ·
`member_at`, `kept_at`, `names_at`, `places_at`, `keptOrder_of_shapes` (KeptPlaces.lean) ·
`keptSeat_of`, `bookSeat_of_tests` (K2Caller/KeptSeatOf.lean) · `maskSeat_of`
(MaskSeatOf.lean) · `bookMask_of_tests`, `freshSeat_of_tests`, `opens_of_tests` (BookOfTests.lean) ·
`mWRaw_fresh` (OpenWordFront.lean).
Limits. EVERY PREMISE STANDS; NONE IS SHOWN AT A VALUE OR AT A REACHED STATE. The three tests are
asked at the state that the way in lets in (BookOfTests.lean's Limits). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.KeptPlaces
import Johnson.Desc.First.Link.Law.AllOf
import Johnson.Desc.First.Link.Law.BookOfTests
import Johnson.Desc.First.Link.Law.LaysFitAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound (ShownAt)
open VerifiableInference.Desc.First.K2Caller (SeatFitAt keptSeat_of bookSeat_of_tests)
open VerifiableInference.Desc.First.Close (groupLayK namesOf posOf membersOf ShapesAre AgreesWith
  layAt sizesM sizesZ mem_members)
open _root_.Tw.K2 (switchNotices)

/-- **What is asked of the plan's list and of the oracles' reading at one message with a seat.** -/
structure PlanAt {Xi : Type} (G : FileDescription Xi) (t : First.S)
    (L : VerifiableInference.Desc.K12.Door.Laid) (orc : ℕ → ℕ → List UInt64) (Y : Strs) (o : ℕ)
    (seat : ℕ × ℕ) (a : ℕ) : Prop where
  is : o < t.book.place.size ∧ ∃ tp sh0, L.places[o]? = some (tp, seat.2) ∧
    L.shapes[tp]? = some sh0 ∧ sh0.logN = a ∧ (∀ x, x < 2 ^ a → orc tp x = Y.col seat.1 x) ∧
    ∀ d, G.oracleAt seat.1 = some d →
      (sh0.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 = d.mainSkip seat.2 ∧
      sh0.mainWidth + (sh0.maskSymbols.extract 0 seat.2).foldl (· + ·) 0 = d.maskSkip seat.2

/-- **FrontFitsAt, WHOLE.** -/
theorem frontFitsAt_of (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    (no : Fin lo.length → ℕ) (kl : List ℕ) {Xi : Type} (G : FileDescription Xi)
    (seat : Fin lo.length → ℕ × ℕ) (Y : Strs) (p : First.K2.P2) (t : First.S)
    (orc : ℕ → ℕ → List UInt64) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame)
    (hgood : (groupLayK cs lo s e kb hM hZ).Good) {T : Statement} {Gr : Group}
    (H : ShapesAre T Gr lo kb no) (hLm : fx.f.rows.layout.members = Gr.members)
    (hLk : fx.f.rows.layout.kept = Gr.kept) (hA : AgreesWith lo kb fx.f.rows.layout)
    (hm : fx.f.rows.masks = 2) (hγ : fx.f.rows.gamma.length = s.h + s.g)
    (hk : fx.f.rows.layout.k = s.h + s.g) (hh : fx.f.rows.layout.h = s.h)
    (hW : First.K2.frameAt fx = some W₀)
    (hord : ∀ i : Fin lo.length, memMain lo i → kb i = true →
      (keptNosOf lo kb)[kl.idxOf i.val]? = some (posOf lo i))
    (hsh : ∀ a : {i // memMain lo i}, ∃ xo, (First.K2.skelOf fx).oracles[no a.1]? = some xo ∧
      xo.shape = (lo.get a.1).1)
    (hS : ∀ a : {i // memMain lo i}, SeatFitAt G cs lo seat a.1)
    (hSh : ∀ a : {i // memMain lo i}, ShownAt G cs lo seat Y a.1)
    (Lp : VerifiableInference.Desc.K12.Door.Laid)
    (hP : ∀ a : {i // memMain lo i},
      PlanAt G t Lp orc Y (no a.1) (seat a.1) (aOf cs (lo.get a.1).1))
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook (First.K2.par9 p).firstTree t = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats Lp t = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits t = true) (B : TreeBook)
    (hB : First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
      (switchNotices fx.T fx.others) = some B)
    (hpos : 2 ^ s.C.a ≤ 2 ^ p.logN) (tree skip aF : ℕ)
    (hfo : fx.f.rows.fresh < t.book.place.size) (tpF tnF : ℕ)
    (hfL : Lp.places[fx.f.rows.fresh]? = some (tpF, tnF)) (shF0 : TreeShape)
    (hfs : Lp.shapes[tpF]? = some shF0) (xoF : OnBytes.Oracle)
    (hfx : (First.K2.skelOf fx).oracles[fx.f.rows.fresh]? = some xoF)
    (hfr : xoF.shape.maskRows = 2 ^ s.h) (hfa : shF0.logN = aF)
    (hforc : ∀ x, x < 2 ^ s.C.a → orc tpF (x % 2 ^ aF) = Y.col tree (x % 2 ^ aF))
    (hfskip : shF0.mainWidth + (shF0.maskSymbols.extract 0 tnF).foldl (· + ·) 0 = skip)
    (hkc : keptCount fx.f.rows.layout
      (fun w => ((First.K2.skelOf fx).oracles.getD (fx.f.rows.layout.members.getD w 0)
        default).shape.mainRows) (List.range fx.f.rows.layout.members.size) =
      fx.f.rows.keptRows) :
    FrontFitsAt cs lo (memMain lo) s e (fun i => layAt (sizesM lo kb) i.val)
      (fun i => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 = true) kl G seat Y p t orc
      (fun a => no a.1) (fun a => posOf lo a.1)
      (mWRaw cs lo (memMain lo) s e (fun i => layAt (sizesM lo kb) i.val)
        (fun i => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 = true) Y tree skip aF)
      (namesOf cs lo s e kb hM hZ no) fx W₀ := by
  have Ft := laysFit_at (cs := cs) (s := s) (e := e) (hM := hM) (hZ := hZ) H hLm hLk hA
  have hfz := firstZ_at cs lo s e kb hM hZ hA
  have hno : ∀ a : {i // memMain lo i},
      fx.f.rows.layout.members[posOf lo a.1]? = some (no a.1) :=
    fun a => member_at H hLm a.1 (mem_members.2 a.2)
  have hO := keptOrder_of_shapes (kl := kl) H hLm hLk hord
  have hso : singleRowsOracles fx.f.rows =
      fx.f.rows.layout.members.push fx.f.rows.fresh := by
    unfold singleRowsOracles
    simp [hm]
  have O : Opens p t fx B := opens_of_tests p t fx Lp hIn hSe hFi B hB fun o ho => by
    rw [hso, Array.toList_push, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · obtain ⟨w, hw, rfl⟩ := List.getElem_of_mem ho
      have hw' : w < fx.f.rows.layout.members.size := by simpa using hw
      obtain ⟨a, ha⟩ := Ft.onto w hw'
      have e1 := hno a
      rw [ha, Array.getElem?_eq_getElem hw'] at e1
      have e2 : fx.f.rows.layout.members.toList[w] = no a.1 := by
        rw [Array.getElem_toList]
        exact Option.some.inj e1
      rw [e2]
      obtain ⟨q1, tp, sh0, q2, q3, _⟩ := (hP a).is
      obtain ⟨xo, x1, _⟩ := hsh a
      exact ⟨q1, tp, _, sh0, xo, q2, q3, x1⟩
    · exact ⟨hfo, tpF, tnF, shF0, xoF, hfL, hfs, hfx⟩
  refine ⟨hgood, Ft, hfz, hm, hγ, hk, hh, hno, fun a h0 => ?_, fun a => ?_, ?_,
    kept_at cs lo s e kb hM hZ no kl hW hO hno hsh, fun q => ?_,
    names_at cs lo s e kb hM hZ no kl hW hO hno hsh,
    places_at cs lo s e kb hM hZ no kl hW hO hno hsh⟩
  · obtain ⟨q1, tp, sh0, q2, q3, q4, q5, q6⟩ := (hP a).is
    obtain ⟨xo, x1, x2⟩ := hsh a
    obtain ⟨_, _, _, _, _, _, _, s6, _, _⟩ := hS a
    have ea : (cMain cs (lo.get a.1).1).a = aOf cs (lo.get a.1).1 := s6.resolve_left h0
    exact keptSeat_of G cs lo seat a.1 (hS a) h0 p t fx orc Y (no a.1) (hSh a) fun d hd =>
      bookSeat_of_tests p t fx orc Y (no a.1) _ _ _ d Lp hIn hSe hFi B hB q1 tp q2 sh0 q3 xo x1 x2
        (by rw [ea, q4]) (fun x hx => q5 x (by rw [← ea]; exact hx)) (q6 d hd).1
  · obtain ⟨q1, tp, sh0, q2, q3, q4, q5, q6⟩ := (hP a).is
    obtain ⟨xo, x1, x2⟩ := hsh a
    exact maskSeat_of G cs lo seat a.1 (hS a) p t fx orc Y (no a.1) (2 ^ s.C.a) (hSh a) fun d hd =>
      bookMask_of_tests p t fx Lp hIn hSe hFi B hB orc Y (no a.1) _ _ _ _ d q1 tp q2 sh0 q3 xo x1 x2
        q4 hpos (fun x _ => q5 _ (Nat.mod_lt _ (Nat.two_pow_pos _))) (q6 d hd).2
  · exact mWRaw_fresh cs lo (memMain lo) s e _ _ hM hZ _ Y p t fx orc
      (freshSeat_of_tests p t fx Lp hIn hSe hFi B hB orc Y tree skip aF (2 ^ s.h) (2 ^ s.C.a) hfo
        tpF tnF hfL shF0 hfs xoF hfx hfr hfa hpos hforc hfskip)
  · refine all_of (groupLayK cs lo s e kb hM hZ) hgood (no := fun a => no a.1) Ft hfz hm hk hh hno
      (fun a => ?_) O orc hkc ?_ q.val
    · obtain ⟨xo, x1, x2⟩ := hsh a
      exact ⟨xo, x1, by rw [x2]; rfl, by rw [x2]; rfl⟩
    · rw [Array.getD_eq_getD_getElem?, hfx]
      exact hfr

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frontFitsAt_of
