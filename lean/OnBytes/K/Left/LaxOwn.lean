-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxOwn.lean: the field `rows` of OnBytes/K/Left/Lax.lean's `LaxDebts`, at what the
strict reader with stored tables has read.



`LaxDebts.rows` asks `RowsL` (OnBytes/TypedOracleCompiler/Run/PageIsForest.lean) at the table `tblOf` of the own
openings of what was read: round by round and tree by tree, the table has a record and "read" means
"listed in it", or it has none and nothing is read. OnBytes/TypedOracleCompiler/Run/PageIsAfter.lean's `rows_top`
gives `RowsL` for a chain without stored tables, at the table `opensB`, from `LaxFacts` and "the
typed draws are the reader's". Here the two are joined by OnBytes/K/OpenedRead.lean's `read_parts`.
For proofs only; the program does not import this file.

Main theorems.
 `tblOf_own`       the table of the own openings of what was read is `opensB` of the chain without
                  the stored tables' openings.
 `rowsL_vals`      `RowsL` reads of a round as read its values alone.
 `rows_core`       `RowsL` at that table, the plan's number of salt bytes and the rounds as read,
                  for any test that says yes exactly at the positions that the written protocol
                  reads at verifier messages whose draws are the reader's.
 `rowsL_read`      the same in the letters of `LaxDebts.rows`.

What is not claimed. Nothing on soundness; no probability; nothing on any hash. That the reader
reads any file. That typed verifier messages with the reader's draws exist: that is the field
`chain`.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.OpenedRead
import OnBytes.TypedOracleCompiler.Slice.EntryOpened
import OnBytes.TypedOracleCompiler.Run.PageIsAfter

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf RowsT RowsL ownOut read_parts rows_top tab_row specX_shape inFile)
open _root_.Run.PQ (View SgX LaxFacts stripR stripO)
open _root_.Run (OpenB opensB)
open OnBytes.Tie (roundWithStoredOpenings StoredFact)

/-- a row of the table of OnBytes/TypedOracleCompiler -/
def rowOfOpen (x : _root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut) : ℕ × ℕ × OpenB :=
  (x.1.tree, x.1.W, ⟨x.1.a, x.2.1, x.2.2.cols, x.2.2.salts, x.2.2.given⟩)

/-- The table of one round's openings of own trees: a row for each, in the file's order. -/
theorem rows_opens (c r : ℕ) :
    ∀ (l : List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) (k : ℕ),
    tblOf (((l.zipIdx k).map fun x => (⟨c, r, x.2, x.1.1, x.1.2.1, x.1.2.2⟩ : OpAt)).filter
      fun op => !op.sh.stored) = (l.filter fun x => !x.1.stored).map rowOfOpen
  | [], _ => rfl
  | x :: l, k => by
      rw [List.zipIdx_cons, List.map_cons, List.filter_cons, List.filter_cons]
      cases hx : x.1.stored with
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          exact rows_opens c r l (k + 1)
      | false =>
          simp only [Bool.not_false, if_true]
          show rowOfOpen x :: tblOf _ = rowOfOpen x :: _
          rw [rows_opens c r l (k + 1)]

/-- The same of all rounds. -/
theorem rows_rounds (c : ℕ) : ∀ (rs : List _root_.Fmt.RoundOut) (n : ℕ),
    tblOf (((rs.zipIdx n).flatMap fun r =>
      r.1.opens.zipIdx.map fun x => (⟨c, r.2, x.2, x.1.1, x.1.2.1, x.1.2.2⟩ : OpAt)).filter
      fun op => !op.sh.stored) =
        rs.flatMap fun r => (r.opens.filter fun x => !x.1.stored).map rowOfOpen
  | [], _ => rfl
  | r :: rs, n => by
      rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons, List.filter_append]
      show tblOf _ = _
      unfold tblOf
      rw [List.map_append]
      exact congrArg₂ _ (rows_opens c n r.opens 0) (rows_rounds c rs (n + 1))

/-- The table of the own openings of what was read is `opensB` of the chain without the stored
tables' openings. rc: one member a round: the round without these openings, and these openings. -/
theorem tblOf_own
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (h1 : ∀ p ∈ rc, ∀ y ∈ p.2, y.1.stored = true)
    (h0 : ∀ p ∈ rc, ∀ x ∈ p.1.opens, x.1.stored = false) (o oo : _root_.Fmt.ChainOut)
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hoo : oo.rounds.toList = rc.map fun p => stripR p.1) :
    tblOf ((opsOf 1 o).filter fun op => !op.sh.stored) = opensB oo := by
  unfold opsOf opensB
  rw [rows_rounds 1 o.rounds.toList 0, ho, hoo, List.flatMap_map, List.flatMap_map]
  refine List.flatMap_congr fun p hp => ?_
  show ((p.2 ++ p.1.opens).filter fun x => !x.1.stored).map rowOfOpen = _
  rw [List.filter_append, List.filter_eq_nil_iff.2 (fun y hy => by rw [h1 p hp y hy]; decide),
    List.nil_append, List.filter_eq_self.2 (fun x hx => by rw [h0 p hp x hx]; rfl)]
  unfold stripR
  dsimp only
  rw [List.map_map]
  rfl

/-- `RowsL` reads of a round as read its values alone. -/
theorem rowsL_vals (C : PQ.CK) (tbl : List (ℕ × ℕ × OpenB)) (sb : ℕ) :
    ∀ (ds : List PQ.RD) (ros ros' : List _root_.Fmt.RoundOut) (isRead : OPos (PQ.uL C ds) → Bool),
      List.Forall₂ (fun a b => a.vals = b.vals) ros ros' → RowsL C tbl sb ds ros isRead →
        RowsL C tbl sb ds ros' isRead
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, h => h.elim
  | _ :: ds, _ :: ros, _, isRead, .cons e t, h =>
      ⟨e ▸ h.1, rowsL_vals C tbl sb ds ros _ (fun p => isRead (.inr p)) t h.2⟩

/-- What holds along two lists holds of each member of the second, with some member of the first. -/
theorem rows_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil, _, hb => absurd hb List.not_mem_nil
  | _, _, .cons h t, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨a, ha, r⟩ := rows_right t b hb
        exact ⟨a, List.mem_cons_of_mem _ ha, r⟩

/-- `RowsL` from a yes of the reader. S: the description under which the strict reader, at the
hash over any function O, has read o; its own part is within the limits of OnBytes/TypedOracleCompiler and the chain
has random bytes. C: any kit of verifier messages. ρ: typed verifier messages of the rounds whose
draws are the reader's. `isRead` says yes exactly at the positions that the written protocol reads
at ρ.
-/
theorem rows_core (C : PQ.CK) (S : _root_.Fmt.SpecX) (O : ByteArray → ByteArray)
    (hokb : PQ.ok (inFile S.base) = true) (hn : S.base.rand.isNone = false)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j))
    (ρ : Rho (PQ.uL C (PQ.rds (inFile S.base))))
    (hd : PQ.drawnSL C (PQ.rds (inFile S.base)) ρ = o.rounds.toList.map (·.drawn))
    (pls : Plains (_root_.Run.Twin.up (SOf C (PQ.rds (inFile S.base)))))
    (isRead : OPos (PQ.uL C (PQ.rds (inFile S.base))) → Bool)
    (hrd : ∀ q, isRead q = true ↔
      Sum.inr q ∈ (PQ.PSof C (PQ.rds (inFile S.base)) fun _ => true).reads () (default, ρ) pls) :
    RowsL C (tblOf ((opsOf 1 o).filter fun op => !op.sh.stored)) S.base.plan.salt
      (PQ.rds (inFile S.base)) o.rounds.toList isRead := by
  obtain ⟨hSok, R, rho0, rc, -, -, ho, hL, -, -, -, hF⟩ := read_parts S O hokb hn seen b i o j e
  have hoo : (ownOut o.pd R rho0 o.rho rc).rounds.toList = rc.map fun p => stripR p.1 := by
    simp [ownOut]
  have hd' : PQ.drawnSL C (PQ.rds (inFile S.base)) ρ =
      (ownOut o.pd R rho0 o.rho rc).rounds.toList.map (·.drawn) := by
    rw [hoo, List.map_map]
    refine hd.trans ?_
    rw [ho, List.map_map]
    rfl
  have h := rows_top (_root_.Fmt.HO O) (inFile S.base) C (fun _ => true)
    (ownOut o.pd R rho0 o.rho rc) ρ pls hokb hL hd'
  have h1 : ∀ p ∈ rc, ∀ y ∈ p.2, y.1.stored = true := by
    intro p hp y hy
    obtain ⟨ts, hts, hf⟩ := rows_right hF p hp
    obtain ⟨t, ht, f⟩ := rows_right hf y hy
    rw [f.sh]
    exact (specX_shape S hSok t (List.mem_flatten.2 ⟨ts, hts, ht⟩)).1
  have h0 : ∀ p ∈ rc, ∀ x ∈ p.1.opens, x.1.stored = false := by
    intro p hp x hx
    obtain ⟨n, -, row⟩ := tab_row (_root_.Fmt.HO O) (inFile S.base) (ownOut o.pd R rho0 o.rho rc)
      hokb hL (stripR p.1) (by rw [hoo]; exact List.mem_map.2 ⟨p, hp, rfl⟩)
      (x.1, x.2.1, stripO x.2.2) (List.mem_map.2 ⟨x, hx, rfl⟩)
    exact row.plain
  rw [← tblOf_own rc h1 h0 o _ ho hoo] at h
  have hv : List.Forall₂ (fun a b : _root_.Fmt.RoundOut => a.vals = b.vals)
      (ownOut o.pd R rho0 o.rho rc).rounds.toList o.rounds.toList := by
    rw [hoo, ho]
    exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun _ _ => rfl))
  have h' := rowsL_vals _ _ _ _ _ _ _ hv h
  have hfun : isRead = _ :=
    funext fun q => Bool.eq_iff_iff.2 ((hrd q).trans decide_eq_true_iff.symm)
  rw [hfun]
  exact h'

/-- The field `rows`, in its own letters. D: the typed description; its rounds' data are those
of S's own part (`hds`). ρ: what the typed chain draws; its draws are the reader's (`hd`). pls: any
plain parts: the written link's reads do not look at them. -/
theorem rowsL_read {X : Type} (D : XD) (dec : X → View → Bool) (S : _root_.Fmt.SpecX)
    (O : ByteArray → ByteArray) (hds : D.ds = PQ.rds (inFile S.base))
    (hokb : PQ.ok (inFile S.base) = true) (hn : S.base.rand.isNone = false)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j)) (x : X)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds)))
    (hd : PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (pls : Plains (_root_.Run.Twin.up (SOf D.C D.ds))) :
    RowsL D.C (tblOf ((opsOf 1 o).filter fun op => !op.sh.stored)) S.base.plan.salt D.ds
      o.rounds.toList fun q =>
        (haveI := (wqXE D dec).decO
         decide (Sum.inr q ∈ (PSXE D dec).up.loc.reads x ρ pls)) := by
  have key : ∀ (ds : List PQ.RD), ds = PQ.rds (inFile S.base) →
      ∀ (ρ : Rho (_root_.Run.Twin.up (SOf D.C ds))),
        PQ.drawnSL D.C ds ρ.2 = o.rounds.toList.map (·.drawn) →
        ∀ (pls : Plains (_root_.Run.Twin.up (SOf D.C ds))) (isRead : OPos (PQ.uL D.C ds) → Bool),
          (∀ q, isRead q = true ↔
            Sum.inr q ∈ (PQ.skeletonOverBothExternalStrings D.C ds D.a D.xs fun _ => true).reads () ρ pls) →
          RowsL D.C (tblOf ((opsOf 1 o).filter fun op => !op.sh.stored)) S.base.plan.salt ds
            o.rounds.toList isRead := by
    intro ds hds ρ hd pls isRead hrd
    subst hds
    exact rows_core D.C S O hokb hn seen b i o j e ρ.2 hd pls isRead hrd
  exact key D.ds hds ρ hd pls _ fun q => decide_eq_true_iff

end OnBytes.K.Left
