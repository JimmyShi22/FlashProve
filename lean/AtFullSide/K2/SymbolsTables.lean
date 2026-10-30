-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/SymbolsTables.lean: the table of a tree that a code switch reads is a sending's table,
at the joined Script: treeTables at the sender's rows, for a sender of the shared kind and for the
switch in front.

  core_tables_are      the switch's sender lays the tables that treeTables makes of its rows
  switch_table_is      the table number j of a switch's sending, where its rows are V
  k1_table_at_join     the thread's table of a tree of a job of the joined list
  switch_table_at_join the thread's table of a tree of a switch in front

Limits. Where the list is fit, the coins are lent and the rows are laid: premises, all of them.
-/
import Johnson.Desc.ProofFile.Honest.K2.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.SeatedL
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysSeated
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (JoinFit Others joinQ join_trees_k1_fit)
open ProofFile.Honest.K1 (PlaceIn SendJob dueR lentCut rowsLaid treeTables treeTables_length)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type}

/-- **The switch's sender lays the tables that treeTables makes of its rows.** -/
theorem core_tables_are (table : FreshTable) (codes : OnBytes.Codes)
    (sent : Array OnBytes.OracleNotice) (fresh : Option (Nat × Nat))
    (data : Nat → Nat → Nat → Cb.Gl.E) (c : Cs (sendingDue codes sent fresh)) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll table codes sent fresh data c = .ok V) :
    (coreSender table).tables codes sent fresh data c =
      .ok (treeTables (sendingPar codes sent) V) := by
  have ht : (sendingPar codes sent).trees =
      ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).shapes.toList := by
    unfold VerifiableInference.Desc.K1.Par.trees
    rw [sendingPar_sent]
    show ((VerifiableInference.Desc.Own.treesMade codes sent).map (·.shapes.toList)).getD [] = _
    cases VerifiableInference.Desc.Own.treesMade codes sent <;> rfl
  show ((rowsAll table codes sent fresh data c).map _) = _
  rw [hV]
  refine congrArg Except.ok ?_
  unfold treeTables
  rw [ht]

/-- **The table number j of a switch's sending**, where the frame hands the part c₀ and its rows are
V. -/
theorem switch_table_is (chain : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (h : List Fmt.Drawn) (c₀ : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (hc : lendPart Bk (Bk.rowsOf chain) (k.look chain) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) = .ok c₀)
    {V : Nat → Johnson.Prover.Send.Rows} (hV : switchRowsLaid D readers closing p c₀ w h = .ok V) {j : Nat}
    (hj : j < (treeTables (switchPar p) V).length) :
    (treeTables (switchPar p) V)[j]? =
      some (switchTableAt Bk chain (coreSender freshTable) D readers closing p k w h j) := by
  have hsay : (moveOne (coreSender freshTable) p.sizes p.others p.foldVars p.carries).say c₀ noSeen
      ⟨switchWit D readers closing p w, h, ()⟩ = .ok ⟨[], treeTables (switchPar p) V⟩ := by
    unfold switchRowsLaid at hV
    by_cases hs : p.sizes.serves = true
    · by_cases hr : p.sizes.roomy = true
      · simp only [hs, hr, Bool.not_true, Bool.false_eq_true, if_false] at hV
        cases hD : switchRowsAt p.sizes p.carries c₀.2.2
            ⟨switchWit D readers closing p w, h, ()⟩ 0 with
        | error e =>
          rw [hD] at hV
          cases hV
        | ok M =>
          rw [hD] at hV
          have hT := core_tables_are freshTable p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) M c₀.1 hV
          show (if !p.sizes.serves then _ else if !p.sizes.roomy then _ else
            (switchRowsAt p.sizes p.carries c₀.2.2
              ⟨switchWit D readers closing p w, h, ()⟩ 0).bind _) = _
          rw [hs, hr, hD]
          show ((coreSender freshTable).tables p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) M c₀.1).map _ = _
          rw [hT]
          rfl
      · simp only [hs, hr, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false,
          if_true] at hV
        cases hV
    · simp only [hs, Bool.not_false, if_true] at hV
      cases hV
  rw [tableAt_is Bk chain (coreSender freshTable) D readers closing p k w h c₀ _ hc hsay j,
    List.getElem?_eq_getElem hj]
  rfl

variable {front : Nat} {bs : List (Block S ProofFile.Cl)} {arr : Nat → Nat → Nat}
  {seats : List (Nat × Nat)} {Wl Xj X Cells Tok V X' Pb : Type} {wit : Wl → PlaceIn Xj} {own₀ : X}
  {jobs : List (Nat × SendJob (PlaceIn Xj) X)}

/-- **The thread's table of a tree of a job of the joined list** is the job's table at the rows that
it lays at the thread's own number of challenges. -/
theorem k1_table_at_join {cF : VerifiableInference.Desc.Chain S ProofFile.Cl} {O : Others Bk Wl}
    (F : JoinFit cF.blocksInOrder front arr seats wit own₀ jobs O) (cells : Wl → Cells) (tok : Wl → Tok)
    (T : Thread Bk S ProofFile.Cl V Wl X' Pb) (hbs : T.bs = cF.blocksInOrder) (hfr : T.front = front)
    (htab : T.table = (joinQ cF.blocksInOrder front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder front cells tok arr wit own₀ jobs O).fixed)
    {x : Nat × SendJob (PlaceIn Xj) X} (hx : x ∈ jobs) (k : Coins Bk) (m : Mid Wl X')
    {cs : Cs (dueR x.2.P x.2.ride)} (ho : lentCut k 0 ⟨x.2.P.place, 0⟩ (dueR x.2.P x.2.ride) = some cs)
    {τ : Nat} (hτ : τ < x.2.P.trees.length) :
    (treeTables x.2.P (rowsLaid x.2 own₀ cs (wit m.st.input)
        (m.st.heard.take (front + roundsTo cF.blocksInOrder x.1))))[τ]? =
      some (T.tableAt (.own (treesTo cF.blocksInOrder x.1 + τ)) k m).2 := by
  obtain ⟨blk, hb, -, OT⟩ := join_trees_k1_fit F cells tok T hbs hfr htab hfix hx
  have hlen : τ < (blk.oracles.flatMap id).length := by
    rw [F.fits x hx blk hb]
    exact hτ
  have e2 := OT.fixed τ hlen
  rw [hbs, hfr] at e2
  have e1 := OT.table τ hlen k m.st.input (m.st.heard.take (front + roundsTo cF.blocksInOrder x.1))
  rw [hbs] at e1
  have hl : τ < (treeTables x.2.P (rowsLaid x.2 own₀ cs (wit m.st.input)
      (m.st.heard.take (front + roundsTo cF.blocksInOrder x.1)))).length := by
    rw [treeTables_length]
    exact hτ
  unfold Thread.tableAt
  rw [e2, Nat.add_zero, e1, List.getElem?_eq_getElem hl]
  show _ = some (ProofFile.Honest.K1.treeTbl 0 wit x.2 own₀ τ k m.st.input _).2
  unfold ProofFile.Honest.K1.treeTbl
  rw [ho]
  show _ = some (((treeTables x.2.P _)[τ]?).getD _)
  rw [List.getElem?_eq_getElem hl]
  rfl

end AtFullSide.K2

#print axioms AtFullSide.K2.core_tables_are
#print axioms AtFullSide.K2.switch_table_is
#print axioms AtFullSide.K2.k1_table_at_join
