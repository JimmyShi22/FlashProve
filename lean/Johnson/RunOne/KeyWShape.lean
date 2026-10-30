-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyWShape.lean (over the key file's tables, with their clause on the book: moreB's last conjunct at border 18 is earned by Laid17.step): THE KEY FILE's ROW 1.17 (w.1.send): (yes): FROM THE TABLES' BOOK-KEEPING AND LAST LETTER AT BORDER 17: THOSE AT BORDER 18. By row 1.1's pattern (KeySendYes1.lean: front1 · shape_send1 · free_send1 · back_send1).
OBJECT: shape₁ | free₁ at border 18 · USER: row 1.17's Keeps · LETTERS: F G at_ one R coll.
  front17       PROVED: what the book-keeping at border 17 says of the state in front: the counts (1 + 2 st, st, st + 1) · the claim's masks' messages are just [0]
  shape_send17  PROVED: the book-keeping at border 18: the ties (own | w laid; the record calls the message behind W its mask; lin.w is the plan's number of the witness's message 2; THE CLAUSE ON THE CLAIM's MASK ENTRIES KEPT: the claim is unturned) and core₁ (eval | g there · message 2 sent · ownB · handed)
  open₁_send17 | open₁_at17 | pinned_at17 | pinned_at18   PROVED by the kernel
  free_send17   PROVED: the promise's last letter at border 18: EvalIs · OpenIn at the last group · SampleIn · MaskWith w (w + 1) · Placed at [0, 2] · ShownAt
  back_send17   PROVED: the five older items ride back: unmarked · pinT · pin 0 · srow 0 · pile
Nothing on soundness.
-/
import Johnson.RunOne.KeyWLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)

/-- What the tables' book-keeping at border 17 says of the state in front. -/
theorem front17 (one : OneTime) (s : FirstState) (h : shape₁' one 17 s = true) :
    s.d.st.oracles.size = wAt one ∧ s.d.st.groups.size = one.ranges.stages.length ∧ s.d.book.trees.size = one.ranges.stages.length + 1 ∧ s.d.book.place.size = wAt one ∧
      (∀ l, s.lin = some l → listOfT (l.claim.masks.toList.map (·.oracle)) = [0]) := by
  have ht : ties₁ one 17 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ sizesB at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, counts₁] at ht
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, -⟩, m⟩, -⟩, -⟩⟩ := ht
  have a' : s.d.st.oracles.size = wAt one := a
  refine ⟨a', b, c, by rw [d]; exact a', fun l hl => ?_⟩
  have m' := m.resolve_left (by decide)
  rw [hl] at m'
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at m'
  exact m'.1

theorem open₁_send17 : open₁ 2 18 = open₁ 2 17 ++ [.pin 2, .srow 2] := by decide +kernel
theorem open₁_at17 : open₁ 2 17 = [.unmarked, .pinT, .pin 0, .srow 0, .pile] := by decide +kernel
theorem pinned_at17 : pinned (open₁ 2 17) = [0] := by decide +kernel
theorem pinned_at18 : pinned (open₁ 2 18) = [0, 2] := by decide +kernel

/-- An elder message that was sent and sampled is so behind. -/
theorem sentB_old (one : OneTime) (s s' : FirstState) (H : Laid17 one s s') (k o : Nat) (ho : (plan₁ one).orc k = some o)
    (h : sentB (plan₁ one) (readers₁ one) s k = true) : sentB (plan₁ one) (readers₁ one) s' k = true := by
  unfold sentB at h ⊢
  rw [ho] at h ⊢
  have h' : (match s.d.st.oracles[o]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = true := h
  show (match s'.d.st.oracles[o]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = true
  cases hx : s.d.st.oracles[o]? with
  | none => rw [hx] at h'; cases h'
  | some x =>
    rw [hx] at h'
    obtain ⟨q, hq⟩ := H.msgOld o x hx
    rw [hq]
    exact h'

/-- The groups behind are the groups in front and the own group. -/
theorem groups_send17 (one : OneTime) (s s' : FirstState) (H : Laid17 one s s') (hg : s.d.st.groups.size = one.ranges.stages.length) (G : OnBytes.Group)
    (hG : s'.d.st.groups[one.ranges.stages.length]? = some G) : s'.d.st.groups.toList = s.d.st.groups.toList ++ [G] := by
  refine List.ext_getElem? fun i => ?_
  rw [Array.getElem?_toList]
  by_cases hi : i < one.ranges.stages.length
  · rw [H.grpOld i hi, List.getElem?_append_left (by rw [Array.length_toList, hg]; exact hi), Array.getElem?_toList]
  · by_cases he : i = one.ranges.stages.length
    · subst he
      rw [hG, List.getElem?_append_right (by rw [Array.length_toList, hg]), Array.length_toList, hg, Nat.sub_self]
      rfl
    · rw [Array.getElem?_eq_none (by rw [H.gsize]; omega), List.getElem?_eq_none (by rw [List.length_append, Array.length_toList, hg]; simp; omega)]

/-- **The book-keeping at border 18.** -/
theorem shape_send17 (one : OneTime) (hsm : wAt one + 1 < noId) (s s' : FirstState) (H : Laid17 one s s') (h : shape₁' one 17 s = true) : shape₁' one 18 s' = true := by
  have ht : ties₁ one 17 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  have hc : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 17 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).2
  obtain ⟨z0, zg, -, -, -⟩ := front17 one s h
  obtain ⟨l, L, G, row, hl, hL, hcl, hw, hown, hmask, hG, hGm, hGr, hGi, hk, hrow⟩ := H.lin
  obtain ⟨xW, hxW, hxWa, hxWb, hxWc, hxWd⟩ := H.msgW
  obtain ⟨xM, hxM, hxMa, hxMb, hxMc⟩ := H.msgM
  have hlist := groups_send17 one s s' H zg G hG
  have hc' : ((((((((sentB (plan₁ one) (readers₁ one) s 0 = true ∧ sentB (plan₁ one) (readers₁ one) s 1 = true) ∧ ((book₁ one).ledger s).isNone = true) ∧ (book₁ one).heard s = false) ∧
      doneB (plan₁ one) (readers₁ one) 2 2 s = true) ∧ groupB (readers₁ one) s true 0 = true) ∧ ((readers₁ one).pile s).isSome = true) ∧ ((readers₁ one).eval s).isNone = true) ∧
      sentB (plan₁ one) (readers₁ one) s 2 = false) := by
    simpa [core₁, and_assoc] using hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, -⟩, -⟩, -⟩ := hc'
  have e0 := sentB_old one s s' H 0 0 rfl c0
  have e1 := sentB_old one s s' H 1 1 rfl c1
  have e2 : sentB (plan₁ one) (readers₁ one) s' 2 = true := by
    show (match s'.d.st.oracles[wAt one]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = true
    rw [hxW]
    simp [hxWa, hxWc]
  have eL : ((book₁ one).ledger s').isNone = true := by
    have e : (book₁ one).ledger s' = (book₁ one).ledger s := by
      show s'.base.fork.map _ = s.base.fork.map _
      rw [H.base]
    rw [e]; exact c2
  have eH : (book₁ one).heard s' = false := by
    have e : (book₁ one).heard s' = (book₁ one).heard s := by
      show s'.base.heard.isSome = s.base.heard.isSome
      rw [H.base]
    rw [e]; exact c3
  have eD : doneB (plan₁ one) (readers₁ one) 2 2 s' = true := by
    have r0 : ∀ i, (readers₁ one).rowsAt s' i = (readers₁ one).rowsAt s i := fun i => by
      show s'.base.rows[i]? = s.base.rows[i]?
      rw [H.base]
    have k0 : ∀ i, (readers₁ one).keysAt s' i = (readers₁ one).keysAt s i := fun i => by
      show (s'.base.keys[i]?).bind _ = (s.base.keys[i]?).bind _
      rw [H.base]
    unfold doneB at c4 ⊢
    simp only [r0, k0]
    exact c4
  -- B's group lies in front of the own one
  have c5' : (match (if s.grp == noId then none else some s.grp).bind fun g => s.d.st.groups[g]? with | some G => G.inRun == true && G.rows.size == 0 | none => false) = true := c5
  have hgl : s.grp < one.ranges.stages.length := by
    by_contra c
    have e : (if s.grp == noId then none else some s.grp).bind (fun g => s.d.st.groups[g]?) = none := by
      split
      · rfl
      · exact Array.getElem?_eq_none (by rw [zg]; exact Nat.le_of_not_lt c)
    rw [e] at c5'
    cases c5'
  have eG : groupB (readers₁ one) s' true 0 = true := by
    show (match (if s'.grp == noId then none else some s'.grp).bind fun g => s'.d.st.groups[g]? with | some G => G.inRun == true && G.rows.size == 0 | none => false) = true
    have e : (if s'.grp == noId then none else some s'.grp).bind (fun g => s'.d.st.groups[g]?) = (if s.grp == noId then none else some s.grp).bind (fun g => s.d.st.groups[g]?) := by
      rw [H.grp]
      split
      · rfl
      · exact H.grpOld _ hgl
    rw [e]
    exact c5'
  have eP : ((readers₁ one).pile s').isSome = true := by
    show (s'.lin.map _).isSome = true
    rw [hL]; rfl
  have eE : ((readers₁ one).eval s').isSome = true := by
    show (s'.lin.bind fun L => (s'.d.st.groups[L.own]?).bind fun G => G.rows[0]?).isSome = true
    rw [hL]
    show ((s'.d.st.groups[L.own]?).bind fun G => G.rows[0]?).isSome = true
    rw [hown, hG]
    show (G.rows[0]?).isSome = true
    rw [hGr]; rfl
  have eg : ((readers₁ one).g s').isSome = true := by
    show (s'.lin.map _).isSome = true
    rw [hL]; rfl
  have eO : ownB (plan₁ one) (readers₁ one) (book₁ one) s' = true := by
    have o3 : (book₁ one).own s' = some one.ranges.stages.length := by
      show s'.lin.map (·.own) = _
      rw [hL]
      exact congrArg some hown
    unfold ownB
    have o1 : (plan₁ one).orc 0 = some 0 := rfl
    have o2 : (plan₁ one).orc 2 = some (wAt one) := rfl
    rw [o1, o2, o3]
    show (s'.d.st.oracles.size == wAt one + 2 && ((s'.d.st.oracles[wAt one + 1]?).any fun x => !x.sampled && !x.spentAsMask) && one.ranges.stages.length + 1 == s'.d.st.groups.size &&
      ((s'.d.st.groups[one.ranges.stages.length]?).any fun G => G.members.toList == [0, wAt one] && G.rows.size == 1 && !G.inRun)) = true
    rw [H.size, hxM, H.gsize, hG]
    simp [hxMa, hxMc, hGm, hGr, hGi]
  have eHd : (book₁ one).handed s' = true := by
    show KeyRows23.handedSt one.given.plan.samples [0] s'.d.st = true
    unfold KeyRows23.handedSt LKFU.Shape23.msgIs LKFU.Shape23.grpIs LKFU.Shape23.plainRows LKFU.Shape23.genRows
    have a1 : s'.d.st.oracles.size - 2 = wAt one := by rw [H.size]; omega
    have a2 : s'.d.st.oracles.size - 1 = wAt one + 1 := by rw [H.size]; omega
    have a3 : s'.d.st.groups.size - 1 = one.ranges.stages.length := by rw [H.gsize]; omega
    rw [a1, a2, a3, hxW, hxM, hG]
    simp [hxWa, hxWb, hxWd, hxMa, hxMb, hxMc, hGm, hGr, hGi, hk]
  unfold ties₁ at ht
  obtain ⟨⟨tA, tM⟩, tS⟩ : (tiesA one 17 s = true ∧ moreB 17 s = true) ∧ sizesB one 17 s = true := by
    simpa [Bool.and_eq_true] using ht
  refine (shape₁_iff _ _ _ _ _ _ _).2 ⟨?_, ?_⟩
  · show ties₁ one 18 s' = true
    have uA : tiesA one 18 s' = true := by
      unfold tiesA at tA ⊢
      rw [H.codes, H.idx]
      simpa using tA
    have uM : moreB 18 s' = true := by
      unfold moreB at tM ⊢
      rw [H.base, H.atEnd, H.grp, hL, hlist]
      have hd : ((s.d.st.groups.toList ++ [G]).drop s.grp).dropLast = s.d.st.groups.toList.drop s.grp := by
        rw [List.drop_append_of_le_length (by rw [Array.length_toList, zg]; exact Nat.le_of_lt hgl), List.dropLast_concat]
      have n1 : L.own ≠ noId := by rw [hown]; unfold wAt at hsm; omega
      have n2 : wAt one ≠ noId := by omega
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, done₁] at tM ⊢
      simp only [hd]
      simp [n1, hmask, hw] at tM ⊢
      exact ⟨⟨⟨tM.1.1, n2⟩, tM.1.2⟩, H.step tM.2⟩
    have uS : sizesB one 18 s' = true := by
      unfold sizesB at tS ⊢
      rw [hl] at tS
      rw [H.size, H.gsize, H.trees, H.places, hL]
      simp [counts₁, hcl, hw] at tS ⊢
      refine ⟨⟨⟨by unfold wAt; omega, ?_⟩, ?_⟩, ?_⟩
      · exact tS.1.2
      · rfl
      · exact tS.2
    unfold ties₁
    rw [uA, uM, uS]
    rfl
  · show core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 18 s' = true
    unfold core₁
    simp [e0, e1, e2, eL, eH, eD, eG, eP, eE, eg, eO, eHd]

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- The elder pin's sample rides. -/
theorem smp_send17 (hG : SmpOwn G at_ one) (p : Xi) (s s' : FirstState) (H : Laid17 one s s') (z : s.d.st.oracles.size = wAt one) :
    G.smp (p, s') (at_ 0).1 (at_ 0).2 = G.smp (p, s) (at_ 0).1 (at_ 0).2 := by
  have hx : s.d.st.oracles[0]? = some (s.d.st.oracles[0]'(by rw [z]; unfold wAt; omega)) := Array.getElem?_eq_getElem _
  obtain ⟨q, hq⟩ := H.msgOld 0 _ hx
  exact hG p s s' 0 0 _ q rfl H.codes hx hq

/-- **The promise's last letter at border 18.** -/
theorem free_send17 (hR : RecStays G) (hcoll : CollCell coll) (hat : at_ 2 = (one.ranges.stages.length + 1, 0)) (p : Xi) (s s' : FirstState) (y y' : Strs) (H : Laid17 one s s')
    (Hy : StrsStay F at_ (open₁ 2 17) y y') (hN : ShownAt F at_ 2 y') (h : free₁ F G at_ one R coll 17 (p, s) y) : free₁ F G at_ one R coll 18 (p, s') y' := by
  obtain ⟨⟨r, hr, hn⟩, h2, h3, -, -, -, -, h8, h9, -, -⟩ := h
  obtain ⟨l, L, Gp, row, hl, hL, hcl, hw, hown, hmask, hGp, hGm, hGr, hGi, hk, hrow⟩ := H.lin
  refine ⟨⟨r, (hR p s s').trans hr, fun hc => hn (hcoll y y' r Hy.cell hc)⟩, h2, ?_, fun _ => ?_, ?_, fun _ => ?_, H.order, ?_, h9,
    fun h15 => absurd h15.2 (by decide), fun _ o ho => ?_⟩
  · intro k hk'
    rw [pinned_at18] at hk'
    rcases (by simpa using hk' : k = 0 ∨ k = 2) with rfl | rfl
    · obtain ⟨o, t, ho, ht, e⟩ := h3 0 (by rw [pinned_at17]; exact List.mem_singleton.2 rfl)
      obtain rfl : 0 = o := Option.some.inj ho
      exact ⟨0, t, rfl, (H.placeOld 0 (by unfold wAt; omega)).trans ht, e⟩
    · exact ⟨wAt one, (one.ranges.stages.length + 1, 0), rfl, H.placeW, hat⟩
  · refine ⟨L, row, hL, ?_, ?_⟩
    · show linEvalRow one.lin L.claim L.w (linLayW s'.d.st.codes one.lin) = some row
      rw [hcl, hw, H.codes]
      exact hrow
    · show (s'.d.st.groups[L.own]?).bind (·.rows[0]?) = some row
      rw [hown, hGp]
      show Gp.rows[0]? = some row
      rw [hGr]
      rfl
  · intro j _ o _ x hx r' hr'
    exact H.order.samples o x hx r' hr'
  · intro G' hG' r' hr'
    exact H.order.rows _ G' hG' r' hr'
  · intro j hj
    rw [pinned_at18] at hj
    rcases (by simpa using hj : j = 0 ∨ j = 2) with rfl | rfl
    · exact shownAt_ride F at_ 0 y y' (Hy.word 0 (by rw [pinned_at17]; exact List.mem_singleton.2 rfl)) (h8 0 (by rw [pinned_at17]; exact List.mem_singleton.2 rfl))
    · exact hN
  · obtain rfl : wAt one = o := Option.some.inj ho
    exact ⟨one.ranges.stages.length + 1, 0, H.placeW, H.placeM⟩

/-- **The five older items ride back.** -/
theorem back_send17 {K : Type} [CommRing K] (ρ : Model.Reading K) (hs : R.same = fun a b => ρ.val a = ρ.val b) (hR : RecStays G) (p : Xi) (s s' : FirstState) (y y' : Strs)
    (w : Wit Cells Unit M) (H : Laid17 one s s') (z : s.d.st.oracles.size = wAt one) (hI : Means.InOrder s.d.st) (e : G.smp (p, s') (at_ 0).1 (at_ 0).2 = G.smp (p, s) (at_ 0).1 (at_ 0).2)
    (Hy : StrsStay F at_ (open₁ 2 17) y y')
    (h : relAt F G at_ (meaning₁At one R) (open₁ 2 17 ++ [.pin 2, .srow 2]) (p, s') y' w) : relAt F G at_ (meaning₁At one R) (open₁ 2 17) (p, s) y w := by
  intro i hi
  have Hi := h i (List.mem_append_left _ hi)
  have hi' : i = .unmarked ∨ i = .pinT ∨ i = .pin 0 ∨ i = .srow 0 ∨ i = .pile := by
    rw [open₁_at17] at hi
    simpa using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · exact rfl
  · obtain ⟨r, h1, h2⟩ := Hi
    exact ⟨r, (hR p s s') ▸ h1, Hy.cell ▸ h2⟩
  · exact rides_pin2_at F G _ _ (p, s) (p, s') y y' w e (Hy.word 0 (by rw [pinned_at17]; exact List.mem_singleton.2 rfl)) Hi
  · obtain ⟨o, x', ho, hx', h1, h2, h3⟩ := Hi
    obtain rfl : 0 = o := Option.some.inj ho
    have hx'' : s'.d.st.oracles[0]? = some x' := hx'
    have hx : s.d.st.oracles[0]? = some (s.d.st.oracles[0]'(by rw [z]; unfold wAt; omega)) := Array.getElem?_eq_getElem _
    obtain ⟨q, hq⟩ := H.msgOld 0 _ hx
    obtain rfl := Option.some.inj (hq.symm.trans hx'')
    refine ⟨0, _, rfl, hx, h1, h2, fun r hr => ?_⟩
    have hh := h3 r hr
    rw [hs] at hh ⊢
    have hin := hI.samples 0 _ hx r hr
    -- the tools called as they lie (the private rowHolds_ext of KeySendYes1.lean and rowHolds_extends of Johnson/Desc/Key/RowsCarry.lean say this as a lemma; neither can be imported here)
    have i1 := rowHolds_iff_says_of_rowIn ρ s'.d.st _ (valOf (plan₁ one) R w) r (Means.RowIn.extends H.ext (fun _ c => c) hin)
    have i2 := rowHolds_iff_says_of_rowIn ρ s.d.st _ (valOf (plan₁ one) R w) r hin
    exact i2.2 ((Means.says_extends ρ H.ext hin _).1 (i1.1 hh))
  · obtain ⟨l, L, Gp, row, hl, hL, hcl, -⟩ := H.lin
    obtain ⟨x, hx, hh⟩ := Hi
    refine ⟨x, ?_, hh⟩
    have hx' : s'.lin.map (fun L => rowOfLinClaim L.claim) = some x := hx
    show s.lin.map (fun L => rowOfLinClaim L.claim) = some x
    rw [hL] at hx'
    rw [hl]
    show some (rowOfLinClaim l.claim) = some x
    rw [← hcl]
    exact hx'

end

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.smp_send17
#print axioms Johnson.RunOne.KeyRows1.free_send17
#print axioms Johnson.RunOne.KeyRows1.back_send17
#print axioms Johnson.RunOne.KeyRows1.shape_send17
#print axioms Johnson.RunOne.KeyRows1.front17
#print axioms Johnson.RunOne.KeyRows1.open₁_send17
