-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchOrder.lean: a code switch of the proximity test keeps the statement in
order (`Means.InOrder`, Johnson/Desc/Means/Order.lean), and with that the batching behind it is
paid, but for the plan's count of rows.

Main names (namespace `Johnson.Prover.Link`).
  `addRowS_iff`, `joinS_iff`   two bridges between texts: the switch's own adding of a row and
      joining (`Tw.L9.addRowS`, `Tw.L9.joinS`, Johnson/Top/H0/Tw/L9/Switch.lean) say yes just where
      the named clauses of the ground's functions hold (`Ground.rowL`, `Ground.joinL`,
      Johnson/Desc/First/Base/Ground.lean), and then leave `withRow`, `withMessageInGroup`
  `rowIn_of_add`   a yes of the adding: the row has passed the tests at its group (`Means.RowIn`)
  `inOrder_addRows`, `inOrder_join`   the two effects keep a statement in order
  `sample_on`   the sample row that the sending makes is on the new message (`Means.RowOn`)
  `inOrder_switch`   `SwitchFront` (Johnson/Prover/Link/FormSwitch.lean), the statement in front in
      order, the codes' lengths in order: the statement behind the switch is in order
  `behindFront_of`   and then, with the plan's count: there is a row with `BehindFront`, and the
      statement behind the batching is in order

By: `rowIn_of_rowL`, `joinP_keeps`, `InOrder.onOracle` (Johnson/Desc/Means/Page.lean),
`InOrder.stSent`, `InOrder.admitted`, `InOrder.withRow`, `InOrder.begun`, `begin_inOrder`
(Johnson/Desc/Means/Order.lean), `rowsFor_on`, `sampleFit_of` (Johnson/Desc/K12/Law/RowsForOn.lean),
`batch_agrees` (Johnson/Desc/Own/BatchAgree.lean).

Limits. `SwitchFront` is asked: its clause `add` is spent here, not paid. The count is the plan's.
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSwitchLaws
import Johnson.Desc.Means.Page
import Johnson.Desc.K12.Law.RowsForOn
import Johnson.Desc.Own.BatchAgree
import Johnson.Desc.Own.SentAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

/-- **A bridge**: the switch's own adding of a row says yes just where the ground's clauses hold. -/
theorem addRowS_iff (S S' : Statement) (g : Nat) (row : Row) :
    Tw.L9.addRowS S g row = .ok S' ↔
      Ground.ok (Ground.rowL S g row) = true ∧ S' = withRow S g row := by
  unfold Tw.L9.addRowS
  cases hG : S.groups[g]? with
  | none => simp [Ground.ok, Ground.rowL, hG]
  | some G =>
    simp only [Ground.ok, Ground.rowL, hG, Ground.has, Option.map_some, Option.getD_some,
      Option.isSome_some, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and,
      Bool.and_eq_true]
    constructor
    · intro h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | skip
      rename_i a1 a2 a3 a4 a5 a6
      cases h
      simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at a1 a2 a3 a4 a5 a6
      exact ⟨⟨a1.1, a1.2, a2, a3, a4, a5, a6⟩, rfl⟩
    · rintro ⟨⟨b1, b2, b3, b4, b5, b6, b7⟩, rfl⟩
      simp only [b1, b2, b3, b4, b5, b6, b7, Bool.and_self, Bool.not_true, Bool.false_eq_true,
        if_false]
      rfl

/-- **A bridge**: the switch's own joining says yes just where the ground's clauses hold. -/
theorem joinS_iff (S S' : Statement) (g o : Nat) (kept : Bool) :
    Tw.L9.joinS S g o kept = .ok S' ↔
      Ground.ok (Ground.joinL S g o kept) = true ∧
        ∃ G, S.groups[g]? = some G ∧ S' = withMessageInGroup S g o kept G := by
  unfold Tw.L9.joinS
  cases hG : S.groups[g]? with
  | none => simp [Ground.ok, Ground.joinL, hG]
  | some G =>
    cases hx : S.oracles[o]? with
    | none => simp [Ground.ok, Ground.joinL, hG, hx]
    | some x =>
      simp only [Ground.ok, Ground.joinL, hG, hx, Ground.has, Option.map_some, Option.getD_some,
        Option.isSome_some, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and,
        Bool.and_eq_true]
      constructor
      · intro h
        repeat' split at h
        all_goals first
          | (cases h; done)
          | skip
        rename_i a1 a2 a3 a4 a5
        cases h
        simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at a1 a2 a3 a4 a5
        exact ⟨⟨a1.1, a1.2, a2, a3, by simpa using a4, a5⟩, G, rfl, rfl⟩
      · rintro ⟨⟨b1, b2, b3, b4, b5, b6⟩, G', e, rfl⟩
        obtain rfl := Option.some.inj e
        have b5' : G.members.contains o = false := by simpa using b5
        simp only [b1, b2, b3, b4, b5', b6, Bool.and_self, Bool.not_true, Bool.false_eq_true,
          if_false]
        rfl

/-- O1. A yes of the adding: the row has passed the tests at its group. -/
theorem rowIn_of_add {S S' : Statement} {g : Nat} {G : Group} {row : Row}
    (h : Tw.L9.addRowS S g row = .ok S') (hG : S.groups[g]? = some G) : Means.RowIn S G row := by
  obtain ⟨G', hG', hr⟩ := Means.rowIn_of_rowL ((addRowS_iff S S' g row).1 h).1
  obtain rfl := Option.some.inj (hG.symm.trans hG')
  exact hr

/-- O2. The adding of rows keeps a statement in order. -/
theorem inOrder_addRows (g : Nat) : ∀ (l : List Row) (S S' : Statement), Means.InOrder S →
    l.foldlM (fun S r => Tw.L9.addRowS S g r) S = .ok S' → Means.InOrder S'
  | [], S, S', hS, h => by
    cases h
    exact hS
  | r :: l, S, S', hS, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := H2K.FoldLaw.bind_ok h
    obtain ⟨hok, rfl⟩ := (addRowS_iff S S1 g r).1 h1
    obtain ⟨G, hG, hr⟩ := Means.rowIn_of_rowL hok
    exact inOrder_addRows g l _ _ (hS.withRow g G r hG hr) h2

/-- O3. The joining keeps a statement in order. -/
theorem inOrder_join {S S' : Statement} {g o : Nat} {kept : Bool} (hS : Means.InOrder S)
    (h : Tw.L9.joinS S g o kept = .ok S') : Means.InOrder S' := by
  obtain ⟨hok, G, hG, rfl⟩ := (joinS_iff S S' g o kept).1 h
  have hp : Ground.joinP (⟨S, {}, 0, [], ()⟩ : Desc.Plain.DState Unit) g o kept =
      some ⟨withMessageInGroup S g o kept G, {}, 0, [], ()⟩ := by
    unfold Ground.joinP
    rw [if_pos hok]
    show (S.groups[g]?).map _ = _
    rw [hG]
    rfl
  exact Means.joinP_keeps hp hS

variable {p : P12} {n : IoppStage} {last : Bool} {dS dC : Fmt.DeclaredRound} {t : T12}
  {rS rC : Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {rows : SingleRows} {gp : Nat}
  {D : Taken} {j : Nat} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext}

/-- **The sample row that the sending makes is on the new message.** -/
theorem sample_on (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x)
    (hl : t.st.codes.lengthsOk = true) :
    Means.RowOn (stSent t.st (swNotices p n last)) t.st.oracles.size D.sample := by
  have e := swNotices_eq p n last
  have hx : (stSent t.st (swNotices p n last)).oracles[t.st.oracles.size]? =
      some { shape := (swTarget p n).shape } := by
    rw [e]
    exact sent_first t.st _ _
  have hfit : Blk.shapeOk t.st.codes (swTarget p n).shape = true := by
    have h := F.recv
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true] at h
    have h1 := h.1.1
    rw [e, Array.all_eq_true_iff_forall_mem] at h1
    exact h1 ⟨(swTarget p n).shape, (swTarget p n).leafClass⟩ (by simp)
  have hlen : (rS.drawn.elems.map E.ofTriple).length =
      (Send.cube t.st.codes (swTarget p n).shape).bits + 1 := by
    have := congrArg List.length F.seed
    rw [List.length_drop] at this
    simp only [List.length_cons, List.length_nil] at this
    omega
  have H := H2K.Out.sampleFit_of (stSent t.st (swNotices p n last))
    { shape := (swTarget p n).shape }
    [⟨(rS.drawn.elems.map E.ofTriple).take (Send.cube t.st.codes (swTarget p n).shape).bits,
      D.beta⟩] D.places hl hfit
    (fun sd hsd => by
      obtain rfl := List.mem_singleton.1 hsd
      show (Send.cube t.st.codes (swTarget p n).shape).bits ≤ (List.take _ _).length
      rw [List.length_take, hlen]
      omega)
    F.pad
  have hr : Desc.Plain.rowsFor t.st.codes (swTarget p n).shape t.st.oracles.size
      [⟨(rS.drawn.elems.map E.ofTriple).take (Send.cube t.st.codes (swTarget p n).shape).bits,
        D.beta⟩] [0] [D.alpha] #[] = some (#[D.sample], []) := by
    simp only [Desc.Plain.rowsFor, List.getElem?_cons_zero, F.form]
    rfl
  exact H2K.Out.rowsFor_on _ _ _ hx _ H [0] [D.alpha] [] #[] #[D.sample]
    (fun r hr' => by simp at hr') hr D.sample (by simp)

/-- O4. **The switch keeps the statement in order.** -/
theorem inOrder_switch (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x)
    (hS : Means.InOrder t.st) (hl : t.st.codes.lengthsOk = true) :
    Means.InOrder (D.stR (swTarget p n) gp (othersOf last n) t.st) := by
  have e := swNotices_eq p n last
  have h2 : Means.InOrder (D.stA (swTarget p n) (othersOf last n) t.st) := by
    have h := (hS.stSent (swNotices p n last)).admitted t.st.oracles.size (swTarget p n).shape
      D.places #[D.sample] (fun r hr => by
        obtain rfl : r = D.sample := by simpa using hr
        exact sample_on F hl)
    rw [e] at h
    exact h
  have h3 : Means.InOrder (ledgerShut (D.stA (swTarget p n) (othersOf last n) t.st)
      (swTarget p n) t.st.oracles.size) := by
    unfold ledgerShut
    split
    · exact Means.InOrder.onOracle h2 _ _ (fun _ => rfl) (fun _ => rfl)
    · exact h2
  exact inOrder_addRows gp D.rows _ _ (inOrder_join h3 F.join) F.add

/-- O5. **The batching behind the switch is paid**, but for the plan's count. -/
theorem behindFront_of (F : SwitchFacts p n last dS dC t rS rC gs rows gp D j next B x)
    (hS : Means.InOrder t.st) (hl : t.st.codes.lengthsOk = true) (hm : D.G.members = #[])
    (hcount : dC.entry.rows =
      (runRows (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st)).size)
    (hne : dC.entry.rows ≠ 0) :
    ∃ row, BehindFront p n last dC t gp D (E.ofTriple x) row
        (Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st)) ∧
      Means.InOrder (behindT p n last t rC gp D B row
        (Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st))).st := by
  have F1 := front_of_facts F
  have hO := inOrder_switch F1 hS hl
  have hgrp : (D.stR (swTarget p n) gp (othersOf last n) t.st).groups[gp]? =
      some (D.grown t.st) :=
    withRows_group gp D.rows _ _ (joined_group _ gp _ false D.G F.group)
  obtain ⟨S2, h2⟩ := ok_of_isSome F.joinOk
  obtain ⟨G, hG, hrun, -⟩ := joinS_ok h2
  obtain rfl : G = D.G := Option.some.inj (hG.symm.trans F.group)
  have ρ : Model.Reading PUnit :=
    ⟨fun _ => PUnit.unit, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨hlay, row, hrow, -⟩ := Means.begin_inOrder ρ hO gp (D.grown t.st) (E.ofTriple x) hgrp
  have elay : Means.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st) =
      Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st) :=
    Option.some.inj (hlay.symm.trans (Own.layout_of_group hgrp))
  rw [elay] at hrow
  have hthere := (hO.groups gp _ hgrp).there
  refine ⟨row, ⟨F.early, ?_, hgrp, rfl, hcount, hne, hrow⟩, hO.begun gp _ hgrp⟩
  simp only [Ground.ok, Ground.beginRunL, hgrp, Ground.has, Option.map_some, Option.getD_some,
    Option.isSome_some, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and,
    Bool.and_eq_true]
  refine ⟨by
    show (!D.G.inRun) = true
    rw [hrun]
    rfl, by
    show (!(D.G.members.insertIdxIfInBounds _ _).isEmpty) = true
    rw [hm]
    simp, ?_⟩
  rw [Array.all_eq_true_iff_forall_mem]
  intro o ho
  exact decide_eq_true (hthere o (Array.mem_toList_iff.2 ho))

end Johnson.Prover.Link
