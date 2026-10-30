-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LaidLaw.lean: WHAT LAYS DATA AT A PLACE IS NO COIN's PLACE AT THE
SEAT: laws on the filling laidData (Johnson/Desc/ProofFile/Honest/LaidData.lean).

Main names.
  back_rect       what the way back hands out lies in the laid block's rectangle.
  lays_says       what "lays" says: the seat names a listed message, which is sampled and whose
    arrays pass the plan's own test; a laid block of one of its arrays holds the place.
  pad_mem, pad_has   every place of padInMain is a main place of the sample's pad as the programs
    lay it (Send.pad), at any number of answers.
  lays_clear      THE LAW, WHERE THE CODE's MESSAGE LENGTH IS A POWER OF TWO (OnBytes.powerOfTwo;
    Codes.lengthsOk gives it): where data is laid, the row is a main row that is sent, the place
    lies inside the code's message length, it is no place of the sample's pad, and the message is
    sampled.
  clear_of_seat   so, under the same premise, RowData.clear holds at every address that the seat
    names, at its message's shape and code.
  nth_of_zipIdx, first_seat   the seat is the sender's at the first segment's opening: the shape at
    which the test is held is the shape of the sender's message of that number; the codes are the
    sender's.

How. reqMessageLaid_eq (Johnson/Desc/Own/ReqAgree.lean); four of the library's lemmas on the
public layout: block_of_message, covers_of_rect, aligned_inside, le_pow_ceil
(Johnson/Goal/Meaning/LaidInside.lean). THAT FILE LIES UNDER Johnson/Goal/: it states no goal, and
this file holds laws alone: no definition of the honest side imports it. NOTHING ELSE OF THAT FOLDER
IS CALLED HERE; what that file imports beneath it is not read here.

Kin. laidAt_geometry, laidAt_inside (LaidInside.lean) and padB_off
(Johnson/Desc/Kinds/Law/LaidOffPad.lean): the same matter forward, from an array's element to its
place, the pad at one answer.

Limits. The pad's places are those of padInMain (Johnson/Desc/ProofFile/Honest/RowData.lean) and of
the programs' Send.pad; that the sender's own text lays its coins at just these places, and coins
everywhere in a message without a sample, is not proved here. The seat is tied to the sender's at
the first segment's opening alone. WITHOUT THE PREMISE ON THE LENGTH clear CAN REFUSE WHERE msgFits
ACCEPTS (Honest/LaidData.lean's head). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K1.FirstData
import Johnson.Desc.K1.First
import Johnson.Desc.Own.ReqAgree
import Johnson.Goal.Meaning.LaidInside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open ProofFile.Honest.K1
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)
open VerifiableInference.Desc (Own.reqMessageLaid)

/-- What the way back hands out lies in the laid block's rectangle. -/
theorem back_rect :
  ∀ (b : LaidBlock) (r j : Nat) (e : Nat × Nat), blockBack b r j = some e →
    b.firstRow ≤ r ∧ r < b.firstRow + 2 ^ b.rowBits ∧ b.firstPlace ≤ j ∧
      j < b.firstPlace + 2 ^ b.placeBits := by
  intro b r j e h
  unfold blockBack at h
  simp only at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
  · cases h

/-- What "lays" says. -/
theorem lays_says :
  ∀ (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals) (a : MsgAddr)
    (r j : Nat), (laidData codes s lay seat heard V).lays a r j = true →
    ∃ l m M A b e, seat a = some (l, m) ∧ (s.link.getD l default).messages[m]? = some M ∧
      M.shape.answers ≠ 0 ∧
      Own.reqMessageLaid codes M.shape ((lay.link.getD l []).filter fun x => x.message == m) =
        true ∧
      A ∈ (lay.link.getD l []).filter (fun x => x.message == m) ∧ b ∈ A.blocks ∧
      blockBack b r j = some e := by
  intro codes s lay seat heard V a r j h
  change (match seat a with
    | some (l, m) =>
      msgFits codes s lay l m && (laidBack lay l m r j).any fun x =>
        (V.size l x.1.name).any fun z => decide (x.2.1 < z.1 ∧ x.2.2 < z.2)
    | none => false) = true at h
  cases hs : seat a with
  | none => rw [hs] at h; cases h
  | some lm =>
    obtain ⟨l, m⟩ := lm
    rw [hs] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hf, hb⟩ := h
    obtain ⟨x, hx, -⟩ := (Option.any_eq_true _ _).1 hb
    unfold laidBack at hx
    obtain ⟨A, hA, hA2⟩ := List.exists_of_findSome?_eq_some hx
    obtain ⟨p, hp, -⟩ := Option.map_eq_some_iff.1 hA2
    unfold arrayBack at hp
    obtain ⟨b, hb1, hb2⟩ := List.exists_of_findSome?_eq_some hp
    unfold msgFits at hf
    obtain ⟨M, hM, hM2⟩ := (Option.any_eq_true _ _).1 hf
    have hne : ((lay.link.getD l []).filter fun a => a.message == m).isEmpty = false := by
      cases hq : (lay.link.getD l []).filter fun a => a.message == m with
      | nil => rw [hq] at hA; cases hA
      | cons _ _ => rfl
    rw [hne, Bool.false_or, Bool.and_eq_true] at hM2
    exact ⟨l, m, M, A, b, p, rfl, hM, by simpa using hM2.1, hM2.2, hA, hb1, hb2⟩

/-- The i-th of the pad's places, in the programs' list: E places an answer. -/
theorem pad_mem (E answers len rows R i : Nat) (hE : 0 < E) (hi : i < E * answers) :
    ∃ q ∈ (List.range answers).flatMap (fun i' => (List.range E).map fun t =>
        ({ part := .main, index := rows - 1 + (len - E * answers + E * i' + t) * 2 ^ R,
           answer := i', basis := OnBytes.thetaE t } : OnBytes.PadPlace)),
      q.part = .main ∧ q.index = rows - 1 + (len - E * answers + i) * 2 ^ R := by
  refine ⟨_, List.mem_flatMap.2 ⟨i / E,
    List.mem_range.2 ((Nat.div_lt_iff_lt_mul hE).2 (by rw [Nat.mul_comm]; exact hi)),
    List.mem_map.2 ⟨i % E, List.mem_range.2 (Nat.mod_lt _ hE), rfl⟩⟩, rfl, ?_⟩
  show rows - 1 + (len - E * answers + E * (i / E) + i % E) * 2 ^ R = _
  rw [Nat.add_assoc (len - E * answers), Nat.div_add_mod]

/-- Every place of padInMain is a main place of the sample's pad as the programs lay it. -/
theorem pad_has {codes : OnBytes.Codes} {o : OnBytes.OracleShape} {pad : List OnBytes.PadPlace}
    (hp : OnBytes.Send.pad codes o = some pad) {r j : Nat}
    (h : (r, j) ∈ padInMain (codes.base.getD o.code default).ell o) :
    ∃ q ∈ pad, q.part = .main ∧ q.index = r + j * 2 ^ OnBytes.ceilLog2 o.mainRows := by
  unfold padInMain at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, not_not] at hc
    obtain ⟨hm0, hr0⟩ := hc
    obtain ⟨i, hi, e⟩ := List.mem_map.1 h
    rw [List.mem_range] at hi
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e.symm
    have hpos : 0 < o.mainRows := Nat.pos_of_ne_zero hr0
    unfold OnBytes.Send.pad OnBytes.Send.cube at hp
    simp only [hm0, hpos, Nat.lt_irrefl, decide_false, decide_true, Bool.false_eq_true, if_false,
      if_true, Bool.false_or] at hp
    generalize (if (o.mainDeg == 3) = true then 1 else 3) = E at hp hi ⊢
    by_cases hE : 0 < E
    · split at hp
      · cases hp
      · obtain rfl := Option.some.inj hp
        exact pad_mem E o.answers _ o.mainRows _ i hE hi
    · have : E = 0 := by omega
      subst this
      omega

/-- **THE LAW, WHERE THE CODE's MESSAGE LENGTH IS A POWER OF TWO.** -/
theorem lays_clear :
  ∀ (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals) (a : MsgAddr)
    (r j l m : Nat) (M : OnBytes.Params.ReqMessage) (c : OnBytes.Code),
    (laidData codes s lay seat heard V).lays a r j = true → seat a = some (l, m) →
    (s.link.getD l default).messages[m]? = some M → codes.base[M.shape.code]? = some c →
    OnBytes.powerOfTwo c.ell = true →
    r < M.shape.mainRows ∧ j < c.ell ∧ (r, j) ∉ padInMain c.ell M.shape ∧ M.shape.answers ≠ 0 := by
  intro codes s lay seat heard V a r j l m M c h hs hM hc hpow
  obtain ⟨l', m', M', A, b, e, hs', hM', ha, hfit, hA, hb, hbk⟩ :=
    lays_says codes s lay seat heard V a r j h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hs'.symm.trans hs))
  obtain rfl := Option.some.inj (hM'.symm.trans hM)
  have rect := back_rect b r j e hbk
  rw [VerifiableInference.Desc.Own.reqMessageLaid_eq] at hfit
  obtain ⟨pad, -, hp, hok, hr, hq⟩ := Meaning.block_of_message hfit hA hb
  have ec : codes.base.getD M'.shape.code default = c := by
    simp [Array.getD_eq_getD_getElem?, hc]
  rw [ec] at hok
  have hell : 2 ^ c.logEll = c.ell := by
    unfold OnBytes.powerOfTwo at hpow
    simp only [Bool.and_eq_true, beq_iff_eq] at hpow
    exact hpow.2
  have hrow : r < M'.shape.mainRows := lt_of_lt_of_le rect.2.1 hr
  unfold OnBytes.laidBlockOk OnBytes.laidAligned at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  have hin := Meaning.aligned_inside hok.1.1.1.1.1.1.2 hok.1.1.2.2 hok.2
  refine ⟨hrow, by omega, fun hpad => ?_, ha⟩
  rw [← ec] at hpad
  obtain ⟨q, hq1, hq2, hq3⟩ := pad_has hp hpad
  have := hq q hq1 hq2
  rw [hq3, Meaning.covers_of_rect (lt_of_lt_of_le hrow (Meaning.le_pow_ceil _)) rect] at this
  cases this

/-- So, where the code's message length is a power of two, RowData.clear holds at every address that
the seat names, at its message's shape and code. -/
theorem clear_of_seat :
  ∀ (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals) (a : MsgAddr)
    (l m : Nat) (M : OnBytes.Params.ReqMessage) (c : OnBytes.Code), seat a = some (l, m) →
    (s.link.getD l default).messages[m]? = some M → codes.base[M.shape.code]? = some c →
    OnBytes.powerOfTwo c.ell = true →
    (laidData codes s lay seat heard V).clear a c.ell M.shape = true := by
  intro codes s lay seat heard V a l m M c hs hM hc hpow
  unfold RowData.clear
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨⟨fun p hp => ?_, ?_⟩, fun r _ => ?_⟩
  · cases hl : (laidData codes s lay seat heard V).lays a p.1 p.2 with
    | false => rfl
    | true =>
      exact absurd hp
        (lays_clear codes s lay seat heard V a p.1 p.2 l m M c hl hs hM hc hpow).2.2.1
  · cases hl : (laidData codes s lay seat heard V).lays a M.shape.mainRows 0 with
    | false => rfl
    | true =>
      exact absurd (lays_clear codes s lay seat heard V a _ 0 l m M c hl hs hM hc hpow).1
        (Nat.lt_irrefl _)
  · cases hl : (laidData codes s lay seat heard V).lays a r c.ell with
    | false => rfl
    | true =>
      exact absurd (lays_clear codes s lay seat heard V a r _ l m M c hl hs hM hc hpow).2.1
        (Nat.lt_irrefl _)

/-- The k-th of the numbered members that pass a test: it is the k-th of the members that pass, and
it stands in the list at its number. -/
theorem nth_of_zipIdx {α : Type} (L : List α) (p : α → Bool) (k : Nat) (x : α × Nat)
    (h : (L.zipIdx.filter fun y => p y.1)[k]? = some x) :
    (L.filter p)[k]? = some x.1 ∧ L[x.2]? = some x.1 := by
  constructor
  · have e : L.filter p = (L.zipIdx.filter fun y => p y.1).map (·.1) := by
      have := List.filter_map (f := fun y : α × Nat => y.1) (p := p) (l := L.zipIdx)
      rw [List.zipIdx_map_fst] at this
      exact this
    rw [e, List.getElem?_map, h]
    rfl
  · have hm : x ∈ L.zipIdx := (List.mem_filter.1 (List.mem_of_getElem? h)).1
    exact List.mem_zipIdx_iff_getElem?.1 hm

/-- **The seat is the sender's, at the first segment's opening.** -/
theorem first_seat :
  ∀ (q : OnBytes.Params.First) (gp : Desc.Plain.GPar) (part k l m : Nat),
    firstSeat q.shape part ⟨⟨⟨1, some 0, 1, .K1⟩, part⟩, k⟩ = some (l, m) →
    l = 0 ∧ (VerifiableInference.Desc.K1.firstPar q gp).codes = q.codes ∧
      ((VerifiableInference.Desc.K1.firstPar q gp).sent[k]?).map (·.shape) =
        ((q.shape.link.getD 0 default).messages[m]?).map (·.shape) := by
  intro q gp part k l m h
  unfold firstSeat momentSeat at h
  simp only [beq_self_eq_true, Nat.zero_le, and_self, if_true, Nat.sub_zero] at h
  obtain ⟨m', hm, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  refine ⟨rfl, rfl, ?_⟩
  unfold msgNo at hm
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hm
  obtain ⟨h1, h2⟩ := nth_of_zipIdx _ (fun M => M.moment == 0) k x hx
  rw [h2]
  have hlink : ((q.shape.link[0]?.map (·.messages)).getD []) =
      (q.shape.link.getD 0 default).messages := by
    cases q.shape.link <;> rfl
  have hown : ((VerifiableInference.Desc.K1.frame₀ q).atMoment 0)[k]? = some x.1 := by
    unfold OnBytes.ReqFrame.atMoment VerifiableInference.Desc.K1.frame₀
    show (((q.shape.link[0]?.map (·.messages)).getD []).filter fun M => M.moment == 0)[k]? = _
    rw [hlink]
    exact h1
  have hlt : k < ((VerifiableInference.Desc.K1.frame₀ q).atMoment 0).length :=
    (List.getElem?_eq_some_iff.1 hown).1
  unfold VerifiableInference.Desc.K1.Par.sent VerifiableInference.Desc.K1.firstPar
    VerifiableInference.Desc.K1.firstParts VerifiableInference.Desc.K1.firstLaid
    OnBytes.ReqFrame.notices
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.getElem?_toArray]
  rw [List.getElem?_append_left (by simpa using hlt)]
  simp [hown]

end ProofFile.Honest

#print axioms ProofFile.Honest.back_rect
#print axioms ProofFile.Honest.lays_says
#print axioms ProofFile.Honest.pad_mem
#print axioms ProofFile.Honest.pad_has
#print axioms ProofFile.Honest.lays_clear
#print axioms ProofFile.Honest.clear_of_seat
#print axioms ProofFile.Honest.nth_of_zipIdx
#print axioms ProofFile.Honest.first_seat
