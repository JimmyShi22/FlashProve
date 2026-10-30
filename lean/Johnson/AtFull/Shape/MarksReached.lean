-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/MarksReached.lean: IN FRONT OF THE FIRST SUB-PROTOCOL OF LINK m + 1 (m < 24) OF
THE PROOF FILE's OWN FIRST CHAIN EACH MESSAGE OF THE CARRIED ROWS' LAYOUT HAS THE LIST OF GROUPS
[m]. At the proof file's seat, in the goals' scope, from the fold's return alone; whoever plays.

How. (1) THE MARKS, ON THE STATE: behind the closing of link l < 24 (the cut 14 l + 13) the group l
bears the mark "its proximity test has begun": the closing's own yes leaves the statement
spent (begun S g G) id at the open frame's group (closeFrame_st,
Johnson/Desc/First/Close/Law/StBehind.lean), and that group is l (group_open,
Johnson/IMR/GroupRest.lean); the closing is found in the flat list as in tail_rows
(Johnson/IMR/GroupTail.lean). The plain changes take off no mark: so it is borne at every later cut.
(2) So at the cut 14 m + 2 the statement is Shut m N, N its number of messages (the members are
below N because the statement is tidy), and so it is at the cut 14 (m + 1) + 2. (3) The layout's
members are the group m's (tail_rows), and for 1 ≤ m they are numbered from N on (fill_at,
Johnson/IMR/GroupFill.lean); the statement has m + 1 groups (count_at, Johnson/IMR/GroupCount.lean).
(4) list_one (ListsTidy.lean).

  Marked g T, plain_marked; Big N T, plain_big; MemberOf g o T, plain_member: three more properties
    that the plain changes keep: the group g bears the mark; the statement has at least N messages;
    o is a member of the group g. three_can_fail: CONTROLS.
  mark_behind_closing, marked_at: (1). statement_shut_below: (2), at any cut behind the closing of
    link m - 1 and in front of the sub-protocols behind the last link.
  front_size, gain_ge: the switch's front has as many messages as the statement; what the switch and
    the link's first sending join is numbered from their number on.
  **lists_at_switch**: the top.

Limits. The cuts 14 (m + 1) + 2, m < 24: in front of the switch at the links 1 to 23; AT LINK 24
(338) IN FRONT OF THE PLACE "H:1", NOT OF THE HEAD's SWITCH (339): that, and the place behind the
last segment: LeafOkArms.lean. Of the layout's members alone: nothing on the fresh mask's message.
The premises are a law's: that a fold returns is shown of no proof here. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.ListsReached
import Johnson.IMR.GroupTail
import Johnson.IMR.GroupFill
import Johnson.IMR.AtReach
import Johnson.Desc.First.Close.Law.StBehind
import Johnson.IMR.FinPin
import Johnson.Top.H0.Tw.K2C.FrontGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (closeFrame_st behind_group)
open Meaning.K2 (frontOf front_len fold_back fold_next fold_cut_le group_open closing_yes tail_rows
  fill_at count_at Holds)
open ProofFile (Cl)

/-! ## 1 Three more properties that the plain changes keep -/

/-- The group g bears the mark. -/
def Marked (g : Nat) (T : Statement) : Prop := markAt T g = some true

/-- The plain changes take off no mark. -/
theorem plain_marked (g : Nat) : PlainKeeps (Marked g) where
  oracle := fun _ _ _ _ h => h
  group := fun T j f hf h => markAt_modify T j f (fun G => (hf G).2) g h
  sent := fun _ _ h => h
  fresh := fun T a b h => group_new_old T a b (·.inRun) h
  joined := fun T g' o kept G _ _ _ _ h => by
    unfold Marked
    rw [markAt_joined]
    exact h

/-- The statement has at least N messages. -/
def Big (N : Nat) (T : Statement) : Prop := N ≤ T.oracles.size

/-- The plain changes take away no message. -/
theorem plain_big (N : Nat) : PlainKeeps (Big N) where
  oracle := fun T k f _ h => by
    show N ≤ (T.oracles.modify k f).size
    rw [Array.size_modify]
    exact h
  group := fun _ _ _ _ h => h
  sent := fun T sent h => by
    show N ≤ (T.oracles ++ sent.map fun n => ({ shape := n.shape } : Oracle)).size
    rw [Array.size_append]
    exact Nat.le_trans h (Nat.le_add_right _ _)
  fresh := fun _ _ _ h => h
  joined := fun T g o kept G _ _ _ _ h => by
    show N ≤ (T.oracles.modify o fun x => { x with groups := x.groups ++ [g] }).size
    rw [Array.size_modify]
    exact h

/-- o is a member of the group g. -/
def MemberOf (g o : Nat) (T : Statement) : Prop := ∃ M, membersAt T g = some M ∧ o ∈ M

/-- Once a member, always a member. -/
theorem plain_member (g o : Nat) : PlainKeeps (MemberOf g o) where
  oracle := fun _ _ _ _ h => h
  group := fun T j f hf h => by
    obtain ⟨M, hM, ho⟩ := h
    exact ⟨M, by rw [membersAt_modify T j f fun G => (hf G).1]; exact hM, ho⟩
  sent := fun _ _ h => h
  fresh := fun T a b h => by
    obtain ⟨M, hM, ho⟩ := h
    exact ⟨M, group_new_old T a b (·.members) hM, ho⟩
  joined := fun T g' o' kept G _ _ _ _ h => by
    obtain ⟨M, hM, ho⟩ := h
    unfold MemberOf
    rw [membersAt_joined]
    split
    · rename_i e
      subst e
      rw [hM]
      exact ⟨_, rfl, VerifiableInference.Desc.mem_insertIfIn _ _ _ _ ho⟩
    · exact ⟨M, hM, ho⟩

/-- CONTROLS: each of the three can fail: a group without the mark; a statement without a message; a
group that has another member alone. -/
theorem three_can_fail : ¬ Marked 0 { groups := #[{ code := 0 }] } ∧ ¬ Big 1 {} ∧
    ¬ MemberOf 0 1 { groups := #[{ code := 0, members := #[0] }] } := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp [Marked, markAt] at h
  · simp [Big] at h
  · obtain ⟨M, hM, ho⟩ := h
    obtain rfl : #[0] = M := Option.some.inj hM
    simp at ho

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-! ## 2 The marks -/

/-- **Behind the closing of link l the group l bears the mark.** -/
theorem mark_behind_closing (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₄ : List Fmt.RoundView} {C C₄ : List VerifiableInference.Desc.OpenedColumn} {s₄ : S}
    (g₄ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 12 + 1)) (ProofFile.startS Z p) R C = .ok (s₄, R₄, C₄)) :
    Marked l s₄.st := by
  obtain ⟨s₃, r₃, q₃, g₃⟩ := fold_back (k := 14 * l + 12) g₄
  obtain ⟨L₃, hL₃, -, eg₃⟩ := group_open hS hR O h24 9 (by omega) s₃ r₃ q₃
    (by rw [show 14 * l + 3 + 9 = 14 * l + 12 by omega]; exact g₃)
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  obtain ⟨Lk2, pw, Q, eL2, -, -, hall⟩ := IM.close_of hS hR O l (by omega)
  obtain rfl : Lk = Lk2 := Option.some.inj (eL.symm.trans eL2)
  obtain ⟨b', x, e1, e2, la⟩ := hall 1 .K10 rfl
  have ib := IM.close_numbers hS hR O (by omega : l < 25) eL e1
  rw [hlen, show 14 * l + 7 + 4 + 1 = 14 * l + 12 by omega] at ib
  obtain ⟨rs, gs, d⟩ := fold_next ib g₃ g₄
  have dx : x.retype.decide s₃ rs gs = .ok s₄ :=
    ((IM.yes_alone la (by intro k; cases k) s₃ s₄ rs gs).1 d).1
  obtain rfl : VerifiableInference.Desc.K9.closing Q = x := Option.some.inj e2
  obtain ⟨y, hy, -, est⟩ := closing_yes (C := Unit) dx hL₃
  obtain ⟨G, id, -, hG, ey⟩ := closeFrame_st hy
  unfold Marked markAt
  rw [est, ey, eg₃]
  rw [eg₃] at hG
  rw [behind_group s₃.st l G id hG]
  rfl

/-- So at every later cut in front of the sub-protocols behind the last link. -/
theorem marked_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g k : Nat} (hg : g < 24)
    (h1 : 14 * g + 12 + 1 ≤ k) (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub}
    {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {s : S}
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (s, R', C')) :
    Marked g s.st := by
  obtain ⟨t, r, q, fj⟩ := fold_cut_le h1 f
  exact plain_folds (plain_marked g) O h1 hk fj f (mark_behind_closing hS hR O hg fj)

/-- **At a cut behind the closing of link m - 1, and in front of the sub-protocols behind the last
link, the statement is shut below m**, at its own number of messages. -/
theorem statement_shut_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m k : Nat} (hm : m ≤ 24)
    (hmk : 14 * m ≤ k + 1) (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub} {R R' : List Fmt.RoundView}
    {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    Shut m t.st.oracles.size t.st := by
  intro g hg
  have hM : markAt t.st g = some true := marked_at hS hR O (by omega) (by omega) hk f
  refine ⟨hM, ?_⟩
  have hT := tidy_fold O hk f
  unfold markAt at hM
  cases hG : t.st.groups[g]? with
  | none => rw [hG] at hM; cases hM
  | some G =>
    have hMem : membersAt t.st g = some G.members := by
      unfold membersAt
      rw [hG]
      rfl
    refine ⟨G.members, hMem, fun o ho => ?_⟩
    obtain ⟨l, hl, -⟩ := hT.listed g G.members o hMem ho
    unfold listAt at hl
    cases hx : t.st.oracles[o]? with
    | none => rw [hx] at hl; cases hl
    | some x => exact (Array.getElem?_eq_some_iff.1 hx).1

/-! ## 3 The numbers of what joins -/

/-- The switch's front has as many messages as the statement. -/
theorem front_size {T : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : _root_.Tw.K2.firstFront T f = .ok x) : x.st.oracles.size = T.oracles.size := by
  rw [(VerifiableInference.Desc.First.K2.firstFront_st h).1]
  rfl

/-- What the switch and the link's first sending join is numbered from the front's number of
messages on. -/
theorem gain_ge (x : _root_.Tw.K2.Front) (o : Nat)
    (h : o ∈ (VerifiableInference.Desc.First.K2.switchGain x ++
      VerifiableInference.Desc.First.K2.ownGain x).map (·.1)) : x.st.oracles.size ≤ o := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
  rcases List.mem_append.1 hy with hy | hy
  · unfold VerifiableInference.Desc.First.K2.switchGain at hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Nat.le_refl _
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      obtain ⟨i, -, e⟩ := List.mem_map.1 (List.of_mem_zip (a := q.1) (b := q.2) hq).1
      show x.st.oracles.size ≤ q.1
      omega
  · unfold VerifiableInference.Desc.First.K2.ownGain at hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    obtain ⟨i, -, e⟩ := List.mem_map.1 (List.of_mem_zip (a := q.1) (b := q.2) hq).2
    show x.st.oracles.size ≤ q.2
    omega

/-! ## 4 The top -/

/-- **IN FRONT OF THE FIRST SUB-PROTOCOL OF LINK m + 1 EACH MESSAGE OF THE CARRIED ROWS' LAYOUT HAS
THE LIST [m].** -/
theorem lists_at_switch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h24 : m < 24)
    {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (m + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∀ o ∈ t₂.check.frame.rows.layout.members, listAt t₂.st o = some [m] := by
  have hlen := front_len hS hR O
  have hk₂ : 14 * (m + 1) + 2 ≤ (frontOf c).length := by omega
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut_le (by omega : 14 * m + 9 ≤ 14 * (m + 1) + 2) f₂
  obtain ⟨L, G, -, -, -, hG, em, -, -, -, calm⟩ := tail_rows hS hR O h24 fu f₂
  have hT := tidy_fold O hk₂ f₂
  have hn : t₂.st.groups.size = m + 1 := count_at hS hR O (m + 1) (by omega) t₂ R₂ C₂ f₂
  have hM : membersAt t₂.st m = some G.members := by
    have q := calm.2 m
    rw [hG] at q
    unfold membersAt
    cases hx : t₂.st.groups[m]? with
    | none => rw [hx] at q; cases q
    | some G' =>
      rw [hx] at q
      exact congrArg some (congrArg Prod.fst (Option.some.inj q))
  intro o ho
  rw [em] at ho
  rcases Nat.eq_zero_or_pos m with rfl | h1
  · exact list_one hT (N := 0) (fun g hg => absurd hg (Nat.not_lt_zero g)) hn hM ho (Nat.zero_le o)
  · obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_cut_le (by omega : 14 * m + 2 ≤ 14 * (m + 1) + 2) f₂
    obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut_le (by omega : 14 * m + 5 ≤ 14 * (m + 1) + 2) f₂
    obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut_le (by omega : 14 * m + 7 ≤ 14 * (m + 1) + 2) f₂
    obtain ⟨x, L₃, L₅, Q₃, Q₅, hx, -, -, -, -, G', hG', eM, -, -, -, -⟩ :=
      fill_at hS hR O h1 h24 f₀ f₃ f₅ fu
    obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
    have hS₀ := statement_shut_below hS hR O (by omega : m ≤ 24) (by omega) (by omega) f₀
    have hS₂ : Shut m t₀.st.oracles.size t₂.st :=
      plain_folds (plain_shut m _) O (by omega) hk₂ f₀ f₂ hS₀
    refine list_one hT hS₂ hn hM ho ?_
    rw [eM] at ho
    have ho' := List.mem_toArray.1 ho
    rcases List.mem_append.1 ho' with ho' | ho'
    · rcases List.mem_append.1 ho' with ho' | ho'
      · rw [← front_size hx]
        exact gain_ge x o ho'
      · exact Nat.le_trans
          (plain_folds (plain_big _) O (by omega) (by omega) f₀ f₃ (Nat.le_refl _))
          (VerifiableInference.Desc.K1.ids_ge Q₃ _ o ho')
    · exact Nat.le_trans
        (plain_folds (plain_big _) O (by omega) (by omega) f₀ f₅ (Nat.le_refl _))
        (VerifiableInference.Desc.K1.ids_ge Q₅ _ o ho')

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.Marked
#print axioms Johnson.AtFull.Shape.plain_marked
#print axioms Johnson.AtFull.Shape.Big
#print axioms Johnson.AtFull.Shape.plain_big
#print axioms Johnson.AtFull.Shape.MemberOf
#print axioms Johnson.AtFull.Shape.plain_member
#print axioms Johnson.AtFull.Shape.three_can_fail
#print axioms Johnson.AtFull.Shape.mark_behind_closing
#print axioms Johnson.AtFull.Shape.marked_at
#print axioms Johnson.AtFull.Shape.statement_shut_below
#print axioms Johnson.AtFull.Shape.front_size
#print axioms Johnson.AtFull.Shape.gain_ge
#print axioms Johnson.AtFull.Shape.lists_at_switch
