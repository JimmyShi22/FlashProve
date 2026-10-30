-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05LayoutOk.lean: kind K5: THE PREMISE hok OF addrTie_of
(Johnson/Desc/First/Att/K05AddrTieOf.lean: LaidOkAt: the symbol arrays that are read are laid
lawfully in their oracles' tables, at the statement's numbers of bits) FROM THE PROGRAMS' OWN TEST
ON A LAYOUT (reqLayoutOk, OnBytes/Iop/ReqRows.lean), the guards of the caller's reading, and a Bool
on the record.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. No test is evaluated here.

Main names:
  `matrixOk_of_layoutOk`: an array of a lawful layout is laid lawfully (laidMatrixOk) in the table
    of the message that holds it: at ceilLog2 of that message's main rows and its code's logEll;
    that message has main rows. (The unfolding follows that of inside_of_layoutOk,
    Johnson/Desc/First/Batch/Law/Layout.lean, which draws another clause.)
  `seat_shape_of`, `seat_shape`: the shape, in the caller's list, of the message in which a cell has its seat is the
    shape of the message that FIRST held the cell's array: for the link's own arrays by the list's
    make; for an earlier link's by SymsOK.keptSame (Johnson/Desc/First/Att/K05AddrTieOf.lean).
  `laidOkAt_of`: **LaidOkAt**, from: reqLayoutOk D.codes D.shape D.layout = true · SymsOK ·
    FrameIs · shapesOnB (Johnson/Desc/First/Att/K05DoorB.lean) at pairs that name the members in
    which a symbol has its seat · the statement's codes are D's.
WHO PAYS WHAT. reqLayoutOk: the chain's start tests it (Johnson/Desc/First/State.lean); that its
letters are D's is not joined. SymsOK: paid from public tests in
Johnson/Desc/First/Att/K05SymsOf.lean. FrameIs, shapesOnB: Bools offered to the table's door. "The
statement's codes are D's": the first of three equations that whoever fills the promise's inOrder
owes. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05DoorLaws
import Johnson.Desc.First.Att.K05KeptBorn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.First.Look (Sent sigListCalls sigList seatCalls keptAt bornAt messagesAt
  laidPlace)

/-- **An array of a lawful layout is laid lawfully in its message's table.** -/
theorem matrixOk_of_layoutOk (codes : Codes) (s : ReqShape) (layout : ReqLayout)
    (h : reqLayoutOk codes s layout = true) (born : ℕ) (name : String) (a : ReqArray)
    (ha : OnBytes.reqArray layout born name = some a) :
    ∃ (L : ReqLink) (msg : ReqMessage) (c : Code), s.link[born]? = some L ∧
      L.messages[a.message]? = some msg ∧ codes.base[msg.shape.code]? = some c ∧
      msg.shape.mainRows ≠ 0 ∧ laidMatrixOk a (ceilLog2 msg.shape.mainRows) c.logEll = true ∧
      ∀ b ∈ a.blocks, b.firstRow + 2 ^ b.rowBits ≤ msg.shape.mainRows := by
  unfold OnBytes.reqArray at ha
  obtain ⟨arrays, h1, h2⟩ := Option.bind_eq_some_iff.mp ha
  have hmem : a ∈ arrays := List.mem_of_find?_eq_some h2
  simp only [reqLayoutOk, Bool.and_eq_true, beq_iff_eq, zipT_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨hb, e1⟩ := List.getElem?_eq_some_iff.mp h1
  have hb' : born < s.link.length := by rw [← hlen]; exact hb
  have hz : (s.link[born], arrays) ∈ s.link.zip layout.link := by
    rw [List.mem_iff_getElem?]
    refine ⟨born, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem hb', h1⟩
  obtain ⟨⟨⟨_, k2⟩, _⟩, k4⟩ := hall _ hz
  have hm : a.message < s.link[born].messages.length := by simpa using k2 a hmem
  have hzi : (s.link[born].messages[a.message], a.message) ∈ s.link[born].messages.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [hm]
  have ok2 := k4 _ hzi
  have hin : a ∈ arrays.filter fun x => x.message == a.message := by
    simp [List.mem_filter, hmem]
  simp only [reqMessageLayoutOk, Bool.or_eq_true, Bool.and_eq_true] at ok2
  rcases ok2 with he | ⟨hrows, hmatch⟩
  · have : (arrays.filter fun x => x.message == a.message) = [] := by simpa using he
    rw [this] at hin
    simp at hin
  · split at hmatch
    · rename_i c pad hc _
      simp only [Bool.and_eq_true, laidOk, List.all_eq_true] at hmatch
      refine ⟨s.link[born], s.link[born].messages[a.message], c, List.getElem?_eq_getElem hb',
        List.getElem?_eq_getElem hm, hc, by simpa using hrows, hmatch.1.1 a hin, fun b hb => ?_⟩
      have h5 := hmatch.2 b (List.mem_flatMap.2 ⟨a, hin, hb⟩)
      exact of_decide_eq_true h5.1
    · simp at hmatch

/-- The messages of a link, as the caller's file reads them. -/
theorem messagesAt_of {D : Sent} {i : ℕ} {L : ReqLink} (h : D.shape.link[i]? = some L) :
    messagesAt D i = L.messages := by
  unfold messagesAt
  rw [h]
  rfl

/-- A first stretch of a list has the list's own members. -/
theorem takeWhile_get {α : Type} (p : α → Bool) : ∀ (l : List α) (m : ℕ) (x : α),
    (l.takeWhile p)[m]? = some x → l[m]? = some x
  | [], _, _, h => by simp at h
  | a :: l, m, x, h => by
    by_cases hp : p a = true
    · rw [List.takeWhile_cons_of_pos hp] at h
      cases m with
      | zero => exact h
      | succ m => exact takeWhile_get p l m x h
    · rw [List.takeWhile_cons_of_neg hp] at h
      simp at h

/-- **The shape, in the caller's list, of the message in which a cell has its seat is the shape of
the message that first held the cell's array.** -/
theorem seat_shape_of {x : VerifiableInference.Desc.First.Look.Place} {D : Sent}
    {rad : OracleShape → Nat}
    (hks : ∀ k (hk : k < (keptAt D x.link).length),
      (((messagesAt D ((bornAt D x.link).getD k (0, 0)).1)[((bornAt D x.link).getD k (0, 0)).2]?).map
        (·.shape)) = some ((keptAt D x.link).get ⟨k, hk⟩).shape) {t r c : ℕ}
    {z : VerifiableInference.Desc.First.Look.Seat} (hz : seatCalls D x.link (.cell t r c) = some z)
    (hk : z.msg < (sigListCalls D rad x.link).length) :
    ∃ bn a msg, (D.arrayOf.getD x.link #[])[t]? = some bn ∧
      OnBytes.reqArray D.layout bn.1 bn.2 = some a ∧ (messagesAt D bn.1)[a.message]? = some msg ∧
      ((sigListCalls D rad x.link).get ⟨z.msg, hk⟩).1 = msg.shape := by
  have hget : (sigListCalls D rad x.link)[z.msg]? =
      some ((sigListCalls D rad x.link).get ⟨z.msg, hk⟩) := List.getElem?_eq_getElem hk
  generalize (sigListCalls D rad x.link).get ⟨z.msg, hk⟩ = e at hget ⊢
  unfold seatCalls at hz
  obtain ⟨bn, hbn, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨a, ha, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨rp, _, hz⟩ := Option.bind_eq_some_iff.1 hz
  unfold sigListCalls at hget
  by_cases hb : (bn.1 == x.link) = true
  · rw [if_pos hb] at hz
    obtain rfl := Option.some.inj hz
    have hbe : bn.1 = x.link := by simpa using hb
    rw [List.getElem?_append_right (by simp)] at hget
    simp only [List.length_map, Nat.add_sub_cancel_left] at hget
    unfold sigList at hget
    rw [List.getElem?_map] at hget
    obtain ⟨msg, hmsg, he⟩ := Option.map_eq_some_iff.1 hget
    refine ⟨bn, a, msg, hbn, ha, ?_, ?_⟩
    · rw [hbe]
      exact takeWhile_get _ _ _ _ hmsg
    · rw [← he]
  · rw [if_neg hb] at hz
    obtain ⟨k, hkk, rfl⟩ := Option.map_eq_some_iff.1 hz
    unfold Array.idxOf? at hkk
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hkk
    have hq2 := (Array.finIdxOf?_eq_some_iff.1 hq).1
    have hqe : (bornAt D x.link)[q] = (bn.1, a.message) := by simpa using hq2
    have hkl : q.val < (keptAt D x.link).length := by
      rw [kept_born]
      exact q.2
    rw [List.getElem?_append_left (by simpa using hkl), List.getElem?_map,
      List.getElem?_eq_getElem hkl] at hget
    have he : (((keptAt D x.link)[q.val]).shape, rad ((keptAt D x.link)[q.val]).shape) = e :=
      Option.some.inj hget
    have hs := hks q.val hkl
    have hgd : (bornAt D x.link).getD q.val (0, 0) = (bn.1, a.message) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem q.2]
      exact hqe
    rw [hgd] at hs
    obtain ⟨msg, hmsg, hsh⟩ := Option.map_eq_some_iff.1 hs
    refine ⟨bn, a, msg, hbn, ha, hmsg, ?_⟩
    rw [← he, hsh]
    rfl

/-- The same, under SymsOK. -/
theorem seat_shape {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} (hR : SymsOK x tl D rad) {t r c : ℕ}
    {z : VerifiableInference.Desc.First.Look.Seat} (hz : seatCalls D x.link (.cell t r c) = some z)
    (hk : z.msg < (sigListCalls D rad x.link).length) :
    ∃ bn a msg, (D.arrayOf.getD x.link #[])[t]? = some bn ∧
      OnBytes.reqArray D.layout bn.1 bn.2 = some a ∧ (messagesAt D bn.1)[a.message]? = some msg ∧
      ((sigListCalls D rad x.link).get ⟨z.msg, hk⟩).1 = msg.shape :=
  seat_shape_of hR.keptSame hz hk

/-- **The symbol arrays that are read are laid lawfully at the statement's numbers of bits.** -/
theorem laidOkAt_of {x : VerifiableInference.Desc.First.Look.Place}
    {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat} {s : First.S} {L : LinkCtx}
    (hlo : reqLayoutOk D.codes D.shape D.layout = true) (hR : SymsOK x tl D rad)
    (hF : FrameIs D x.link L.check.frame) (hL : s.link? = some L)
    (qs : List (ℕ × OracleShape)) (hB3 : shapesOnB (keptAt D x.link).length qs s = true)
    (hq : ∀ k : Fin (sigListCalls D rad x.link).length, ReadMsg (ReadAddr tl []) D x.link k.val →
      (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hc : s.st.codes = D.codes) : LaidOkAt x tl D L.check.frame s.st := by
  intro μ i' c bn a o hbn ha hw
  obtain ⟨z, hz, hfit⟩ := hR.seated μ i' c
  obtain ⟨hk, _⟩ := id hfit
  obtain ⟨bn1, a1, msg, hbn1, ha1, hmsg, hsh⟩ := seat_shape hR hz hk
  obtain rfl : bn1 = bn := Option.some.inj (hbn1.symm.trans hbn)
  obtain rfl : a1 = a := Option.some.inj (ha1.symm.trans ha)
  obtain ⟨bn2, a2, hbn2, ha2, _, _, hw2⟩ := whereIs_cell hF (kept_born D x.link) hz
  obtain rfl : bn2 = bn1 := Option.some.inj (hbn2.symm.trans hbn)
  obtain rfl : a2 = a1 := Option.some.inj (ha2.symm.trans ha)
  rw [hw] at hw2
  obtain ⟨o', y, b1, b2, b3⟩ :=
    shapesOnB_at hB3 hL (hq ⟨z.msg, hk⟩ ⟨_, z, Or.inl ⟨μ, i', c, rfl⟩, hz, rfl⟩)
  obtain rfl : o = o' := Option.some.inj (hw2.trans b1)
  rw [hsh] at b3
  obtain ⟨Lk, msg', c0, hlk, hmsg', hcode, hrows, hmx, _⟩ :=
    matrixOk_of_layoutOk D.codes D.shape D.layout hlo bn2.1 bn2.2 a2 ha
  rw [messagesAt_of hlk] at hmsg
  obtain rfl : msg' = msg := Option.some.inj (hmsg'.symm.trans hmsg)
  have er : s.st.rowBits o .main = ceilLog2 msg'.shape.mainRows := by
    unfold Statement.rowBits
    rw [b2]
    show ceilLog2 (y.shape.rows .main) = _
    rw [b3]
    rfl
  have ep : s.st.placeBits o .main = c0.logEll := by
    unfold Statement.placeBits
    rw [b2]
    show (if y.shape.rows .main == 0 then 0 else (s.st.codes.base.getD y.shape.code default).logEll) = _
    rw [b3, hc]
    have h0 : (msg'.shape.rows .main == 0) = false := by
      show (msg'.shape.mainRows == 0) = false
      simpa using hrows
    rw [h0, Array.getD_eq_getD_getElem?, hcode]
    rfl
  rw [er, ep]
  exact hmx

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.matrixOk_of_layoutOk
#print axioms VerifiableInference.Desc.First.Att.P.seat_shape_of
#print axioms VerifiableInference.Desc.First.Att.P.seat_shape
#print axioms VerifiableInference.Desc.First.Att.P.laidOkAt_of
