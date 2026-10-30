-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CoreSenderLaw.lean: the kind "the code switch" (K2): THE FIRST LAW
ON THE SENDER (`SendSameLaw`, Honest/K2/Exact.lean), AT THE CORE's OWN SENDER (`coreSender`,
Honest/K2/Sending.lean), FROM THE SHARED SENDING's LAW ON ROWS (`Spec.rowsExact`,
Johnson/SendSim/At/Sim.lean), WHICH IS ANOTHER WRITER's STATEMENT, IS NOT PROVED IN THE FILE THAT
STATES IT, AND STANDS HERE AS A PREMISE. Two definitions; statements with their proofs.

  `map_cast`     uniform coins under another spelling of their count
  `zipIdx_map_zipIdx`, `zip_map_zipIdx`, `nodup_eraseDups`, `eraseDups_card`   on lists
  `col_rows`, `held_rows`   the core's written column and held words read the rows of the place's
                 own messages alone
  `trees_core`, `stAt_core`, `tables_core`, `answers_core`   the core's sender in the shared
                 sending's terms: its trees, the statement at which it makes its answers, its two
                 fields as maps of `rowsAll`
  `unGot`, `backShown`   what this kind's statement reads of a sending, as a function of the place's
                 public trees and of what the shared sending's two moves show: it is handed no coin
                 and no datum
  `shows_of_rows`, `shows_back`   POINTWISE, at every data, seeds, lists and coins: `senderShows`
                 at the core's sender is `backShown` of `shownR` at the same coins under the other
                 count
  `seeds_shared`, `bud_shared`   this kind's premises on seeds and on positions give the shared
                 law's
  `bud_back`, `asksWithin_iff_bud`, `switchBud_iff_bud`   THIS KIND's COUNT ON THE POSITIONS IS THE
                 SHARED LAW's, BOTH WAYS; so is the part's, at the lists as the frame hands them
  `sendSameLaw_of_rowsExact`   THE END

Limits. THE END IS AS GOOD AS ITS PREMISE: no file that this one imports proves `Spec.rowsExact`. It
stands at a sending in which every message with a main row is sampled (`NoWord`,
Honest/K2/Law/Counts.lean) and at a table that is the shared sending's own for a fresh mask: the
first is shown at the places of the kind's lot in Honest/K2/Law/SampledOpen.lean, not here. The
law's hypothesis "the table that rides has one row" is not spent here: the premise has no such
clause; it stays in the law's own statement, which this file does not turn. Nothing on the second
law. Nothing here says what the law would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Exact
import Johnson.Desc.ProofFile.Honest.K2.Law.SameRows
import Johnson.SendSim.At.Sim
import Johnson.Desc.K1.Law.OkView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (zeroG)
open Johnson.Prover.Send (Rows)
open OnBytes.Slice (toE ofE readE)
open OnBytes.SendSim.At (shownR budAt asked)

/-! ## 1 General -/

/-- Uniform coins under another spelling of their count. -/
theorem map_cast {β : Type} {d d' : Due} (h : d = d') (f : Cs d' → β) :
    (Prob.unif (Cs d)).map (fun c => f (h ▸ c)) = (Prob.unif (Cs d')).map f := by
  subst h
  rfl

theorem zipIdx_map_zipIdx {α β : Type} (L : List α) (mk : α × Nat → β) :
    (L.zipIdx.map mk).zipIdx = L.zipIdx.map fun y => (mk y, y.2) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem zip_map_zipIdx {α β : Type} (L : List α) (h : α × Nat → β) :
    L.zip (L.zipIdx.map h) = L.zipIdx.map fun y => (y.1, h y) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- By the list's length. -/
theorem nodup_eraseDups_le : ∀ (n : Nat) (l : List Nat), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => absurd h (by simp)
  | n + 1, a :: l, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_eraseDups_le n _ ?_⟩
    · have h1 := (List.mem_filter.1 (List.mem_eraseDups.1 hm)).2
      simp at h1
    · exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_succ_le_succ h)

/-- The list without its doubles has no doubles. -/
theorem nodup_eraseDups (l : List Nat) : l.eraseDups.Nodup :=
  nodup_eraseDups_le l.length l (Nat.le_refl _)

/-- A list has as many distinct members as the list without its doubles is long. -/
theorem eraseDups_card (l : List Nat) : l.eraseDups.length = l.toFinset.card := by
  have h : l.toFinset = l.eraseDups.toFinset := by
    ext a
    rw [List.mem_toFinset, List.mem_toFinset, List.mem_eraseDups]
  rw [h, List.toFinset_card_of_nodup (nodup_eraseDups l)]

/-! ## 2 The core reads the rows of the place's own messages alone -/

theorem col_rows (P : VerifiableInference.Desc.K1.Par) {V V' : Nat → Rows}
    (h : ∀ k, k < P.sent.size → V k = V' k) (τ x : Nat) :
    Johnson.Prover.Send.col P V τ x = Johnson.Prover.Send.col P V' τ x := by
  have key : ∀ k ∈ (List.range P.sent.size).filter fun k =>
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? == some τ,
      Johnson.Prover.Send.mainSyms P V k x = Johnson.Prover.Send.mainSyms P V' k x ∧
        Johnson.Prover.Send.maskSyms P V k x = Johnson.Prover.Send.maskSyms P V' k x := by
    intro k hk
    have hk' := List.mem_range.1 (List.mem_filter.1 hk).1
    unfold Johnson.Prover.Send.mainSyms Johnson.Prover.Send.maskSyms
    rw [h k hk']
    exact ⟨rfl, rfl⟩
  unfold Johnson.Prover.Send.col
  exact congrArg₂ (· ++ ·)
    (congrArg List.flatten (List.map_congr_left fun k hk => (key k hk).1))
    (congrArg List.flatten (List.map_congr_left fun k hk => (key k hk).2))

theorem held_rows (w : OnBytes.Means.Words Cb.Gl.E) (first : Nat)
    (P : VerifiableInference.Desc.K1.Par) {V V' : Nat → Rows}
    (h : ∀ k, k < P.sent.size → V k = V' k) :
    Johnson.Prover.Send.held w first P V = Johnson.Prover.Send.held w first P V' := by
  funext o part i
  unfold Johnson.Prover.Send.held
  by_cases hc : first ≤ o ∧ o < first + P.sent.size
  · rw [if_pos hc, if_pos hc, h (o - first) (by omega)]
  · rw [if_neg hc, if_neg hc]

/-! ## 3 The core's sender in the shared sending's terms -/

theorem trees_core (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    (sendingPar codes sent).trees =
      ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).shapes.toList := by
  unfold VerifiableInference.Desc.K1.Par.trees
  rw [sendingPar_sent]
  show ((VerifiableInference.Desc.Own.treesMade codes sent).map (·.shapes.toList)).getD [] = _
  cases VerifiableInference.Desc.Own.treesMade codes sent with
  | none => rfl
  | some L => rfl

theorem stAt_core (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    K1.stAt (sendingPar codes sent) 0 =
      { codes := codes, oracles := sent.map fun n => { shape := n.shape } } := by
  unfold K1.stAt OnBytes.Slice.stSent
  rw [sendingPar_sent]
  simp only [Array.replicate_zero, Array.empty_append]
  rfl

theorem tables_core (table : FreshTable) (codes : OnBytes.Codes)
    (sent : Array OnBytes.OracleNotice) (fresh : Option (Nat × Nat))
    (data : Nat → Nat → Nat → Cb.Gl.E) (c : Cs (sendingDue codes sent fresh)) :
    (coreSender table).tables codes sent fresh data c =
      (rowsAll table codes sent fresh data c).map (K1.treeTables (sendingPar codes sent)) :=
  congrArg (fun f => (rowsAll table codes sent fresh data c).map f) (funext fun V => by
    unfold K1.treeTables
    rw [trees_core])

theorem answers_core (table : FreshTable) (codes : OnBytes.Codes)
    (sent : Array OnBytes.OracleNotice) (fresh : Option (Nat × Nat))
    (data : Nat → Nat → Nat → Cb.Gl.E) (c : Cs (sendingDue codes sent fresh))
    (seeds : List Fmt.Ext3) :
    (coreSender table).answers codes sent fresh data c seeds =
      (rowsAll table codes sent fresh data c).map fun V =>
        (Johnson.Prover.Send.answers (sendingPar codes sent) (K1.stAt (sendingPar codes sent) 0) 0
          (Johnson.Prover.Send.held (fun _ _ _ => 0) 0 (sendingPar codes sent) V)
          (K1.seedsAt (sendingPar codes sent) [⟨seeds, [], [], none⟩])).map toE := by
  rw [stAt_core]
  show (rowsAll table codes sent fresh data c).map (fun V =>
    (Johnson.Prover.Send.answers (sendingPar codes sent)
      { codes := codes, oracles := sent.map fun n => { shape := n.shape } } 0
      (Johnson.Prover.Send.held (fun _ _ _ => zeroG) 0 (sendingPar codes sent) V)
      (VerifiableInference.Desc.K1.cutSeeds (sendingPar codes sent).coordinates
        (sendingPar codes sent).seeds (seeds.map OnBytes.E.ofTriple))).map toE) = _
  rw [zeroG_eq]
  rfl

/-! ## 4 What this kind's statement reads, of what the shared sending's two moves show -/

/-- An answer as a view shows it, read back; 0 at any other item. -/
def unGot : Fmt.ItemValue → Cb.Gl.E
  | .answer t => toE t
  | _ => 0

/-- Of the place's public trees and of what two moves show: each tree's stated length and width with
its columns; the answers. -/
def backShown (P : VerifiableInference.Desc.K1.Par) (sh : List Shown) :
    Option (List ((Nat × Nat) × List (Nat × List UInt64)) × List Cb.Gl.E) :=
  some ((P.trees.zip (sh.getD 0 ⟨[], []⟩).cols).map
      (fun x => ((x.1.logN, x.1.mainWidth + x.1.maskWidth), x.2)),
    (sh.getD 1 ⟨[], []⟩).vals.map unGot)

/-- At any place, rows, answers in words and lists. -/
theorem shows_of_rows (P : VerifiableInference.Desc.K1.Par) (V : Nat → Rows)
    (A : List Fmt.Ext3) (asks : List (List Nat)) :
    some ((K1.treeTables P V).zipIdx.map (fun t =>
        ((t.1.logLength, t.1.words), ((asks[t.2]?).getD []).map fun x => (x, t.1.col x))),
      A.map toE) =
      backShown P [⟨[], (K1.treeTables P V).zipIdx.map fun t =>
          (asked [asks] t.2).map fun p => (p, t.1.col p)⟩,
        ⟨A.map fun a => (Said.answer (toE a)).got, []⟩] := by
  have h1 : (K1.treeTables P V).zipIdx.map (fun t =>
      ((t.1.logLength, t.1.words), ((asks[t.2]?).getD []).map fun x => (x, t.1.col x))) =
      (P.trees.zip ((K1.treeTables P V).zipIdx.map fun t =>
        (asked [asks] t.2).map fun p => (p, t.1.col p))).map
        (fun x => ((x.1.logN, x.1.mainWidth + x.1.maskWidth), x.2)) := by
    unfold K1.treeTables
    rw [zipIdx_map_zipIdx, List.map_map, List.map_map, zip_map_zipIdx, List.map_map]
    rfl
  have h2 : A.map toE = (A.map fun a => (Said.answer (toE a)).got).map unGot := by
    rw [List.map_map]
    refine List.map_congr_left fun a _ => ?_
    show toE a = toE (ofE (toE a))
    rw [OnBytes.Slice.toE_ofE]
  rw [h1, h2]
  rfl

/-- **Pointwise**: at every data, seeds, lists and coins. -/
theorem shows_back {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j)
    (data : Nat → Nat → Nat → Cb.Gl.E) (seeds : List Fmt.Ext3) (asks : List (List Nat))
    (c : Cs (sendingDue codes sent fresh)) :
    senderShows (coreSender table) codes sent fresh data seeds asks c =
      backShown (sendingPar codes sent)
        (shownR (sendingPar codes sent) 0 (rideOf sent fresh) (dataShared sent data)
          [⟨seeds, [], [], none⟩] [asks] (sendingDue_shared hf hw ▸ c)) := by
  obtain ⟨V, hV⟩ := rowsAll_returns hf table data c
  have hVR : ∀ k, k < (sendingPar codes sent).sent.size →
      V k = K1.rowsR (sendingPar codes sent) (rideOf sent fresh) (dataShared sent data)
        (sendingDue_shared hf hw ▸ c) k := by
    intro k hk
    rw [sendingPar_sent] at hk
    exact rowsAll_shared hw htab hV _ hk
  have hT : K1.treeTables (sendingPar codes sent) V =
      K1.treeTables (sendingPar codes sent) (K1.rowsR (sendingPar codes sent) (rideOf sent fresh)
        (dataShared sent data) (sendingDue_shared hf hw ▸ c)) := by
    unfold K1.treeTables
    simp only [col_rows (sendingPar codes sent) hVR]
  have e1 : senderShows (coreSender table) codes sent fresh data seeds asks c =
      some ((K1.treeTables (sendingPar codes sent) V).zipIdx.map (fun t =>
          ((t.1.logLength, t.1.words), ((asks[t.2]?).getD []).map fun x => (x, t.1.col x))),
        (Johnson.Prover.Send.answers (sendingPar codes sent) (K1.stAt (sendingPar codes sent) 0) 0
          (Johnson.Prover.Send.held (fun _ _ _ => 0) 0 (sendingPar codes sent) V)
          (K1.seedsAt (sendingPar codes sent) [⟨seeds, [], [], none⟩])).map toE) := by
    unfold senderShows
    rw [tables_core, answers_core, hV]
    rfl
  rw [e1, hT, held_rows _ 0 (sendingPar codes sent) hVR, shows_of_rows]
  rfl

/-! ## 5 This kind's premises give the shared law's -/

theorem seeds_shared {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {seeds : List Fmt.Ext3} (hs : seedsFit codes sent seeds) :
    K1.seedsFit (sendingPar codes sent) [⟨seeds, [], [], none⟩] = true ∧
      ∀ s ∈ K1.seedsAt (sendingPar codes sent) [⟨seeds, [], [], none⟩], readE s.2 ≠ 0 := by
  refine ⟨beq_iff_eq.2 hs.1, fun s hm h0 => ?_⟩
  have hok : OnBytes.okE s.2 = true :=
    VerifiableInference.Desc.K1.cutSeeds_ok _ _ _ (fun e he => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      have h3 := hs.2.1 x hx
      refine VerifiableInference.Desc.K1.okE_ofTriple x ?_
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨h3.1, h3.2.1⟩, h3.2.2⟩) s hm
  have h1 := hs.2.2 s hm
  rw [(OnBytes.Slice.isZeroE_iff s.2 hok).2 h0] at h1
  cases h1

theorem bud_shared {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {asks : List (List Nat)} (ha : asksWithin codes sent asks) :
    budAt (sendingPar codes sent) [asks] := by
  intro k τ hk ht
  rw [sendingPar_sent] at hk ht
  rw [sendingPar_shape]
  show ((sent.getD k default).shape.mainRows ≠ 0 →
      ((((asks[τ]?).getD []).map
        (· % 2 ^ (codes.base.getD (sent.getD k default).shape.code default).logN)).toFinset.card
        ≤ (codes.base.getD (sent.getD k default).shape.code default).r)) ∧
    ((sent.getD k default).shape.maskRows ≠ 0 →
      ((((asks[τ]?).getD []).map
        (· % 2 ^ (codes.mask.getD (sent.getD k default).shape.maskCode default).logN)).toFinset.card
        ≤ (codes.mask.getD (sent.getD k default).shape.maskCode default).r))
  cases hl : asks[τ]? with
  | none => exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | some l =>
    have h := ha τ l hl k hk ht
    exact ⟨fun h0 => (eraseDups_card _) ▸ h.1 h0, fun h0 => (eraseDups_card _) ▸ h.2 h0⟩

/-- The way back. -/
theorem bud_back {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {asks : List (List Nat)} (hb : budAt (sendingPar codes sent) [asks]) :
    asksWithin codes sent asks := by
  intro τ l hl k hk ht
  have h := hb k τ (by rw [sendingPar_sent]; exact hk) (by rw [sendingPar_sent]; exact ht)
  rw [sendingPar_shape] at h
  have h' : ((sent.getD k default).shape.mainRows ≠ 0 →
      ((((asks[τ]?).getD []).map
        (· % 2 ^ (codes.base.getD (sent.getD k default).shape.code default).logN)).toFinset.card
        ≤ (codes.base.getD (sent.getD k default).shape.code default).r)) ∧
    ((sent.getD k default).shape.maskRows ≠ 0 →
      ((((asks[τ]?).getD []).map
        (· % 2 ^ (codes.mask.getD (sent.getD k default).shape.maskCode default).logN)).toFinset.card
        ≤ (codes.mask.getD (sent.getD k default).shape.maskCode default).r)) := h
  rw [hl] at h'
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · unfold distinctMod
    rw [eraseDups_card]
    exact h'.1 h0
  · unfold distinctMod
    rw [eraseDups_card]
    exact h'.2 h0

/-- **This kind's count on the positions is the shared law's.** -/
theorem asksWithin_iff_bud {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {asks : List (List Nat)} :
    asksWithin codes sent asks ↔ budAt (sendingPar codes sent) [asks] :=
  ⟨bud_shared, bud_back⟩

/-- **The part's count is the shared law's**, at the lists as the frame hands them. -/
theorem switchBud_iff_bud (p : SwitchPlace) (n : Nat) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    switchBud p n ds asks ↔
      budAt (sendingPar p.sizes.codes (switchSent p.sizes p.others)) asks := by
  have e : budAt (sendingPar p.sizes.codes (switchSent p.sizes p.others)) asks ↔
      budAt (sendingPar p.sizes.codes (switchSent p.sizes p.others)) [asks.headD []] := by
    cases asks with
    | nil => exact Iff.rfl
    | cons a l => exact Iff.rfl
  rw [e]
  exact asksWithin_iff_bud

/-! ## 6 The end -/

/-- **From the shared sending's law on rows: the first law on the sender, at the core's own
sender**: at a sending in which every message with a main row is sampled, at the shared sending's
own table for a fresh mask. hX: another writer's statement, not proved here: a premise. -/
theorem sendSameLaw_of_rowsExact (hX : OnBytes.SendSim.At.Spec.rowsExact) {table : FreshTable}
    {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    (hw : NoWord sent) (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j) :
    SendSameLaw (coreSender table) codes sent fresh := by
  intro hf _ data data' seeds asks hs ha
  have hx := hX (sendingPar codes sent) 0 (rideOf sent fresh) (dataShared sent data)
    (dataShared sent data') [⟨seeds, [], [], none⟩] [asks] hf (seeds_shared hs).1
    (seeds_shared hs).2 (bud_shared ha)
  have side : ∀ D : Nat → Nat → Nat → Cb.Gl.E,
      (Prob.unif (Cs (sendingDue codes sent fresh))).map
          (senderShows (coreSender table) codes sent fresh D seeds asks) =
        ((Prob.unif (Cs (K1.dueR (sendingPar codes sent) (rideOf sent fresh)))).map
          (shownR (sendingPar codes sent) 0 (rideOf sent fresh) (dataShared sent D)
            [⟨seeds, [], [], none⟩] [asks])).map (backShown (sendingPar codes sent)) := by
    intro D
    rw [PMF.map_comp, ← map_cast (sendingDue_shared hf hw)]
    exact congrArg (fun f => PMF.map f (Prob.unif (Cs (sendingDue codes sent fresh))))
      (funext fun c => shows_back hf hw htab D seeds asks c)
  rw [side data, side data', hx]

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.map_cast
#print axioms ProofFile.Honest.K2.zipIdx_map_zipIdx
#print axioms ProofFile.Honest.K2.zip_map_zipIdx
#print axioms ProofFile.Honest.K2.nodup_eraseDups_le
#print axioms ProofFile.Honest.K2.nodup_eraseDups
#print axioms ProofFile.Honest.K2.eraseDups_card
#print axioms ProofFile.Honest.K2.col_rows
#print axioms ProofFile.Honest.K2.held_rows
#print axioms ProofFile.Honest.K2.trees_core
#print axioms ProofFile.Honest.K2.stAt_core
#print axioms ProofFile.Honest.K2.tables_core
#print axioms ProofFile.Honest.K2.answers_core
#print axioms ProofFile.Honest.K2.shows_of_rows
#print axioms ProofFile.Honest.K2.shows_back
#print axioms ProofFile.Honest.K2.seeds_shared
#print axioms ProofFile.Honest.K2.bud_shared
#print axioms ProofFile.Honest.K2.bud_back
#print axioms ProofFile.Honest.K2.asksWithin_iff_bud
#print axioms ProofFile.Honest.K2.switchBud_iff_bud
#print axioms ProofFile.Honest.K2.sendSameLaw_of_rowsExact
