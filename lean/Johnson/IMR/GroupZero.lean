-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupZero.lean: Johnson/IMR/GroupFill.lean's AND Johnson/IMR/GroupKept.lean's TOPS AT
LINK 0, whose first sub-protocol is kind K1's opening and no code switching.
  fill_rest: general, l < 24: from behind the link's first sub-protocol to in front of its batching:
    the two later sendings lay their new numbers and flags behind what the group holds.
  opening_holds: behind an accept of the opening: the new group's members are the first of the
    sending's new numbers, as many as the link's messages of moment 0, with the flags "life > 0"
    (kind K1's firstAtS_arrays; the rest of the sending's numbers are the fold's mask and what
    rides at the start: they join no group).
  keptOf_lists, firstAtS_two: small tools.
  entry_zero: behind the whole first sub-protocol of link 0: Holds 0 at these lists, and the open
    link's frame's moment is 1.
  moment_zero: in front of both later sendings the frame's moment is at least 1.
  kept_one: THE TOP: what the code switching into group 1 keeps: the numbers n₀ + j of link 0's
    messages of moment 0 with a life; n₀ the number of messages at the first state.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: kind K2's files; kind K10's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- Three lists one behind the other, the flags of the second and the third all false. -/
theorem keptOf_lists {a i₃ i₅ : List Nat} {fa f₃ f₅ : List Bool} (h0 : a.length = fa.length)
    (h3 : i₃.length = f₃.length) (F3 : ∀ b ∈ f₃, b = false) (F5 : ∀ b ∈ f₅, b = false) :
    keptOf (a ++ i₃ ++ i₅).toArray (fa ++ f₃ ++ f₅).toArray = keptOf a.toArray fa.toArray := by
  have a1 : (a ++ i₃ ++ i₅).toArray = (a.toArray ++ i₃.toArray) ++ i₅.toArray := by simp
  have a2 : (fa ++ f₃ ++ f₅).toArray = (fa.toArray ++ f₃.toArray) ++ f₅.toArray := by simp
  rw [a1, a2, keptOf_append (by simp [h0, h3]), keptOf_append (by simp [h0]),
    keptOf_none (a := i₃.toArray) (k := f₃.toArray) (by simpa using F3),
    keptOf_none (a := i₅.toArray) (k := f₅.toArray) (by simpa using F5), Array.append_empty,
    Array.append_empty]

theorem firstAtS_two {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s m : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening q gp : Block S Unit).decide s rs gs = .ok m) : ∃ r₁ r₂, rs = [r₁, r₂] := by
  unfold K1.firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, -, hb⟩ := bindE h
  obtain ⟨⟨c', d'⟩, h2, -⟩ := bindE hb
  obtain ⟨g, d₁, ids, d₂, -, hs, -⟩ := K1.firstOwn_ok _ _ _ c' _ d' rs h2
  exact two_of_send hs

/-- **Behind an accept of kind K1's opening.** -/
theorem opening_holds {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s m : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening q gp : Block S Unit).decide s rs gs = .ok m) :
    Holds s.st.groups.size
      ((List.range (s.check.frame.atMoment 0).length).map (· + s.st.oracles.size))
      ((s.check.frame.atMoment 0).map fun x => decide (0 < x.life)) m := by
  obtain ⟨r₁, r₂, rfl⟩ := firstAtS_two h
  obtain ⟨G', hG', m1, m2⟩ := K1.firstAtS_arrays q gp s m r₁ r₂ gs h
  obtain ⟨g', mask, -, -, lt⟩ := K1.firstAtS_frame q gp s m r₁ r₂ gs h
  have hsz := (K1.firstAtS_seated q gp s m r₁ r₂ gs h).msgs
  refine ⟨G', hG', ?_, m2, by simp, fun o ho => ?_, ?_⟩
  · rw [m1]
    apply Array.toList_inj.1
    rw [Array.toList_extract, K1.ids_list]
    simp only [List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
    rw [← List.map_take, List.take_range, Nat.min_eq_left (Nat.le_of_lt lt)]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
    have := List.mem_range.1 hi
    omega
  · exact (K2.rising_range _ _).imp fun k => Nat.ne_of_lt k

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **FROM BEHIND THE FIRST SUB-PROTOCOL OF LINK l < 24 TO IN FRONT OF ITS BATCHING.** -/
theorem fill_rest (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ R₃ R₅ Ru : List Fmt.RoundView}
    {C C₁ C₃ C₅ Cu : List VerifiableInference.Desc.OpenedColumn} {t₁ t₃ t₅ u : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (f₅ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 7)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅))
    (fu : foldBlocks 0 (c.blocksInOrder.take (14 * l + 9)) (ProofFile.startS Z p) R C = .ok (u, Ru, Cu))
    {mem : List Nat} {fl : List Bool} (H1 : Holds l mem fl t₁) :
    ∃ (L₃ L₅ : LinkCtx) (Q₃ Q₅ : K1.Par), t₃.link? = some L₃ ∧ t₅.link? = some L₅ ∧
      (K1.idsOf Q₃ t₃.st.oracles.size).toList.length = (K1.flagsAt L₃.check.frame).length ∧
      (K1.idsOf Q₅ t₅.st.oracles.size).toList.length = (K1.flagsAt L₅.check.frame).length ∧
      Holds l
        (mem ++ (K1.idsOf Q₃ t₃.st.oracles.size).toList ++ (K1.idsOf Q₅ t₅.st.oracles.size).toList)
        (fl ++ K1.flagsAt L₃.check.frame ++ K1.flagsAt L₅.check.frame) u := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  have hearAt : ∀ j < 7, ∃ b, Lk.hear[j]? = some b ∧ c.blocksInOrder[14 * l + 2 + j]? = some b := by
    intro j hj
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[j]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : j < Lk.hear.length)⟩
    refine ⟨b, e, ?_⟩
    have q := IM.hear_at_flat eL e
    rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) j).trans
      (by omega : 14 * l + j + 2 = 14 * l + 2 + j)] at q
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 14 * l + 4) 1 f₃
  obtain ⟨t₄, R₄, C₄, f₄⟩ := fold_cut (k := 14 * l + 6) 1 f₅
  obtain ⟨t₆, R₆, C₆, f₆⟩ := fold_cut (k := 14 * l + 8) 1 fu
  have stQ : ∀ j, (j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6) → ∀ s r q s' r' q',
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q') →
      s'.st = s.st := by
    intro j hj s r q s' r' q' g g'
    obtain ⟨b, e, ib⟩ := hearAt j (by omega)
    obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
    exact (hear_quiet hS hR O h24 hj eL e s rs' gs' s' d').1.1
  have H3 : Holds l _ _ t₃ := holds_st (stQ 2 (by omega) t₂ R₂ C₂ t₃ R₃ C₃ f₂ f₃)
    (holds_st (stQ 1 (by omega) t₁ R₁ C₁ t₂ R₂ C₂ f₁ f₂) H1)
  obtain ⟨L₃, hL₃, -, g₃⟩ := group_open hS hR O h24 2 (by omega) t₃ R₃ C₃ f₃
  obtain ⟨L₅, hL₅, -, g₅⟩ := group_open hS hR O h24 4 (by omega) t₅ R₅ C₅ f₅
  obtain ⟨b3, e3, i3⟩ := hearAt 3 (by omega)
  obtain ⟨rs3, gs3, d3⟩ := fold_next i3 f₃ f₄
  obtain ⟨Q₃, lk3, mo3, ar3, v3, rs3', gs3', c3, s3⟩ :=
    hear_commit hS hR O h24 (Or.inl rfl) eL e3 d3
  have H4 : Holds l _ _ t₄ := holds_st s3 (g₃ ▸ holds_commit c3 hL₃ (g₃.symm ▸ H3))
  have H5 : Holds l _ _ t₅ := holds_st (stQ 4 (by omega) t₄ R₄ C₄ t₅ R₅ C₅ f₄ f₅) H4
  obtain ⟨b5, e5, i5⟩ := hearAt 5 (by omega)
  obtain ⟨rs5, gs5, d5⟩ := fold_next i5 f₅ f₆
  obtain ⟨Q₅, lk5, mo5, ar5, v5, rs5', gs5', c5, s5⟩ :=
    hear_commit hS hR O h24 (Or.inr rfl) eL e5 d5
  have H6 : Holds l _ _ t₆ := holds_st s5 (g₅ ▸ holds_commit c5 hL₅ (g₅.symm ▸ H5))
  have n3 : (K1.idsOf Q₃ t₃.st.oracles.size).toList.length =
      (K1.flagsAt L₃.check.frame).length := by
    obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two c3
    exact commit_len c3 hL₃
  have n5 : (K1.idsOf Q₅ t₅.st.oracles.size).toList.length =
      (K1.flagsAt L₅.check.frame).length := by
    obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two c5
    exact commit_len c5 hL₅
  exact ⟨L₃, L₅, Q₃, Q₅, hL₃, hL₅, n3, n5,
    holds_st (stQ 6 (by omega) t₆ R₆ C₆ u Ru Cu f₆ fu) H6⟩

/-- What the opening's accept gives behind the whole first sub-protocol of link 0. -/
theorem entry_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    Holds 0
      ((List.range ((ProofFile.startS Z p).check.frame.atMoment 0).length).map
        (· + (ProofFile.startS Z p).st.oracles.size))
      (((ProofFile.startS Z p).check.frame.atMoment 0).map fun x => decide (0 < x.life)) t₁ ∧
      ∃ L, t₁.link? = some L ∧ L.check.frame.moment = 1 := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * 0 + 2) f₁
  have e0s := laid_is_start hS hR O f₀
  obtain ⟨L, hL, -, -⟩ := entry_group hS hR O (by omega : 0 < 24) f₀ f₁
  obtain ⟨hB, -⟩ := laid_at hS hR O (by omega : 0 < 25) f₀
  obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
  have i0 : c.blocksInOrder[14 * 0 + 2]? = some b := by
    have k := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : 0 ≤ 24) 0).trans
      (by omega : 14 * 0 + 0 + 2 = 14 * 0 + 2)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, f, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y' : (K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Unit).decide t₀ rs' gs' = .ok m := y1
  have H := opening_holds y'
  rw [e0s, start_groups O.pub p] at H
  refine ⟨holds_st (framesOf_st hfs f (List.mem_of_getElem? hf) m t₁ y3) H, L, hL, ?_⟩
  obtain ⟨r₁, r₂, er⟩ := firstAtS_two y'
  rw [er] at y'
  obtain ⟨g', mask, e, -, -⟩ := K1.firstAtS_frame _ _ t₀ m r₁ r₂ _ y'
  have hR0 : t₀.roots = t₀.book.trees.size := by
    rw [e0s, (start_empty O.pub p).1, (start_empty O.pub p).2]
    rfl
  have hK : t₀.check.frame.keptBefore = #[] := by
    rw [e0s]
    exact start_kept O.pub p
  obtain ⟨-, mB⟩ := opening_lists y' hB hR0 hK
  have v := ((framesOf_live hfs f (List.mem_of_getElem? hf)).2.1 m t₁ y3).1
  rw [← live_open hL, v, live_between mB, e]

/-- In front of hearing sub-protocol number n + 1 of link 0, n ≤ 6: the moment is at least 1. -/
theorem moment_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 6, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∃ L, t.link? = some L ∧ 1 ≤ L.check.frame.moment
  | 0, _, t, R', C', f => by
    obtain ⟨-, L, hL, e⟩ := entry_zero hS hR O f
    exact ⟨L, hL, by omega⟩
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * 0 + 3 + n) f
    obtain ⟨L, hL, e1⟩ := moment_zero hS hR O n (by omega) u Ru Cu fu
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr 0 (by omega)
    rw [if_neg (by omega : ¬ 0 = 24)] at hlen
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 1]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : n + 1 < Lk.hear.length)⟩
    have ib : c.blocksInOrder[14 * 0 + 3 + n]? = some b := by
      have q := IM.hear_at_flat eL e
      rwa [(IM.flatIx_scope hS hR O (by omega : 0 ≤ 24) (n + 1)).trans
        (by omega : 14 * 0 + (n + 1) + 2 = 14 * 0 + 3 + n)] at q
    obtain ⟨rs, gs, d⟩ := fold_next ib fu f
    obtain ⟨L', hL', g1⟩ := hear_by moUp_trans (fun _ _ => moUp_of_quiet)
      (fun _ _ _ _ _ _ _ _ => moUp_commit) hS hR O (by omega : 0 < 24) (by omega) (by omega) eL e
      u rs gs t d L hL
    exact ⟨L', hL', by omega⟩

/-- **WHAT THE CODE SWITCHING INTO GROUP 1 KEEPS.** -/
theorem kept_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (0 + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    switchKept t₂.check.frame.rows =
      (((((List.range ((ProofFile.startS Z p).check.frame.atMoment 0).length).map
          (· + (ProofFile.startS Z p).st.oracles.size)).zip
        (((ProofFile.startS Z p).check.frame.atMoment 0).map fun x => decide (0 < x.life))).filter
          (·.2)).map (·.1)).toArray := by
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * 0 + 3) 13 f₂
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * 0 + 5) 11 f₂
  obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 14 * 0 + 7) 9 f₂
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut (k := 14 * 0 + 9) 7 f₂
  obtain ⟨H1, -⟩ := entry_zero hS hR O f₁
  obtain ⟨L₃, L₅, Q₃, Q₅, hL₃, hL₅, n3, n5, G, hG, em, ek, -, -, -⟩ :=
    fill_rest hS hR O (by omega : 0 < 24) f₁ f₃ f₅ fu H1
  obtain ⟨L, G', -, -, -, hG', m1, m2, -⟩ := tail_rows hS hR O (by omega : 0 < 24) fu f₂
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  have R3 : RecAll Z.first.codes Z.first.shape t₃ := open_recAll hS hR O (by omega)
    (draw_in_front hS hR O (l := 0) (i := 3) (by omega) (by omega)) f₃
  have R5 : RecAll Z.first.codes Z.first.shape t₅ := open_recAll hS hR O (by omega)
    (draw_in_front hS hR O (l := 0) (i := 5) (by omega) (by omega)) f₅
  obtain ⟨M₃, hM₃, mo3⟩ := moment_zero hS hR O 2 (by omega) t₃ R₃ C₃ f₃
  obtain ⟨M₅, hM₅, mo5⟩ := moment_zero hS hR O 4 (by omega) t₅ R₅ C₅ f₅
  obtain rfl : L₃ = M₃ := Option.some.inj (hL₃.symm.trans hM₃)
  obtain rfl : L₅ = M₅ := Option.some.inj (hL₅.symm.trans hM₅)
  have F3 := flags_false R3.ok (link_frame R3 hL₃).shape mo3
  have F5 := flags_false R5.ok (link_frame R5 hL₅).shape mo5
  rw [switchKept_eq, m1, m2, em, ek]
  rw [keptOf_lists (by simp) n3 F3 F5]
  apply Array.toList_inj.1
  rw [keptOf_toList]

end

#print axioms opening_holds
#print axioms fill_rest
#print axioms entry_zero
#print axioms kept_one

end Meaning.K2
