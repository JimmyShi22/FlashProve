-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxViewOwn.lean: at the typed string that the typing makes of what was read, every
column that the reader lists in an opening of one of the chain's own trees is the column of the
typed string's opening at that position.



The protocol's decision sees a chain as a view. OnBytes/TypedOracleCompiler/Run/ViewERead.lean (`viewX_cols_tr`)
shows that the typed transcript's view is the strict reader's, from two hypotheses on columns: one
on the chain's own trees (hcol), one on the stored tables (hy). OnBytes/TypedOracleCompiler/Run/ViewOp.lean
(`hcol_of_op`) draws the first from the typed string's openings, and OnBytes/TypedOracleCompiler/Run/ViewERead3.lean
(`cols_of_table`) from a typing's table. This file says it at the table and the openings of
`assembleS` (OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean).

Main theorems.
 `opsOf_mem`     an opening of a round that was read is a member of the typing's list of openings.
 `zip_salt`      a listed (place, column) has its salt, where there are as many salts as columns.
 `trace_open`    every opening in a lenient reading's rounds goes with an opening of the description
                 (`OpenFacts`, library, Run/PageIs.lean).
 `own_cols`      the statement: the hypothesis of `hcol_of_op` at `opLS D.C (lookE run tab) 0 D.ds`,
                 with tab the typing's own table.

Asked by `own_cols`: the rounds as read are the own parts joined with the stored openings; the own
parts, stripped, are a lenient reading's rounds at the description; every opening of the description
is some own tree's (`TabGood`); the table is the typing's; two rows of it under one key have one
column (`Agree`).

Not claimed. `Agree` at any table. The stored tables' half. The decision. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Run.ViewERead3
import OnBytes.TypedOracleCompiler.Run.ViewOp
import OnBytes.TypedOracleCompiler.Slice.EntryTyping
import OnBytes.Tie.StoredRead

set_option autoImplicit false

namespace OnBytes.K.Left
open _root_.Compile (Opening)
open _root_.Iop (OPos OSym)
open TypedOracleCompiler.Run.PQ (XD uL posAtS colS treeSh TabGood Agree cols_of_table)
open TypedOracleCompiler.Slice (OpAt opsOf tabOf opLS lookE)
open _root_.Run (HId OpenB)
open _root_.Run.PQ (TraceL OpenFacts stripR stripO)
open _root_.Run.WalkTie (listOK_spec)
open OnBytes.Tie (roundWithStoredOpenings)
open _root_.Fmt (RoundOut ChainOut OpenOut)

/-- An opening of a round that was read is a member of the typing's list of openings. -/
theorem opsOf_mem {c : ℕ} {o : ChainOut} {r : RoundOut} (hr : r ∈ o.rounds.toList)
    {x : _root_.Fmt.Shape × List ℕ × OpenOut} (hx : x ∈ r.opens) :
    ∃ i k, (⟨c, i, k, x.1, x.2.1, x.2.2⟩ : OpAt) ∈ opsOf c o := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  refine ⟨i, k, ?_⟩
  unfold opsOf
  refine List.mem_flatMap.2 ⟨(o.rounds.toList[i], i), ?_, List.mem_map.2
    ⟨((o.rounds.toList[i]).opens[k], k), ?_, rfl⟩⟩
  · exact List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi)
  · exact List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hk)

/-- A listed (place, column) has its salt, where there are at least as many salts as columns. -/
theorem zip_salt {α β γ : Type} : ∀ (xs : List α) (cols : List β) (salts : List γ),
    cols.length ≤ salts.length → ∀ zc ∈ xs.zip cols, ∃ sl, (zc.1, zc.2, sl) ∈ xs.zip (cols.zip
    salts)
  | [], _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | _ :: _, _ :: _, [], hl, _, _ => by cases hl
  | x :: xs, c :: cols, s :: salts, hl, zc, h => by
      rcases List.mem_cons.1 h with rfl | h'
      · exact ⟨s, List.mem_cons_self⟩
      · obtain ⟨sl, hs⟩ := zip_salt xs cols salts (Nat.le_of_succ_le_succ hl) zc h'
        exact ⟨sl, List.mem_cons_of_mem _ hs⟩

/-- The columns of an opening that passes the parser's own test have the width asked. -/
theorem okb_width (Ob : _root_.Run.OpenB) (sb W : ℕ) (h : Ob.ok sb W = true) :
    ∀ c ∈ Ob.cols, c.length = W := by
  unfold _root_.Run.OpenB.ok at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨-, h5⟩, -⟩, -⟩, -⟩ := h
  exact h5

/-- Of two lists that go together, every member of the second goes with a member of the first. -/
theorem forall₂_right {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | _, _, .nil, _, hy => by cases hy
  | _, _, .cons hab hl, y, hy => by
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact ⟨_, List.mem_cons_self, hab⟩
      · obtain ⟨x, hx, hr⟩ := forall₂_right hl y hy'
        exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- Every opening in a lenient reading's rounds goes with an opening of the description. -/
theorem trace_open (h : HId) (P : _root_.Fmt.Plan) :
    ∀ (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : _root_.Fmt.Chain)
      (roots : Array ByteArray), TraceL h P rs ros c roots →
      ∀ ro ∈ ros, ∀ y ∈ ro.opens, ∃ r ∈ rs, ∃ x ∈ r.opens, ∃ R poss, OpenFacts P R poss x y
  | [], [], _, _, _, _, hro, _, _ => by cases hro
  | [], _ :: _, _, _, ht, _, _, _, _ => ht.elim
  | _ :: _, [], _, _, ht, _, _, _, _ => ht.elim
  | r :: rs, ro' :: ros, c, roots, ht, ro, hro, y, hy => by
      obtain ⟨-, -, -, -, hF, hT⟩ := ht
      rcases List.mem_cons.1 hro with rfl | hro'
      · obtain ⟨x, hx, hxy⟩ := forall₂_right hF y hy
        exact ⟨r, List.mem_cons_self, x, hx, _, _, hxy⟩
      · obtain ⟨r', hr', x, hx, R, poss, hf⟩ := trace_open h P rs ros _ _ hT ro hro' y hy
        exact ⟨r', List.mem_cons_of_mem _ hr', x, hx, R, poss, hf⟩

/-- At the typing's own table: every column that the reader lists in an opening of an own tree is
the column of the typed string's opening at that position. -/
theorem own_cols (h : HId) (D : XD) (o : ChainOut) (c : _root_.Fmt.Chain)
    (rc : List (RoundOut × List (_root_.Fmt.Shape × List ℕ × OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (htr : TraceL h D.base.plan D.base.rounds (rc.map fun p => stripR p.1) c #[])
    (hg : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, ∃ n, TabGood D.base x n)
    (run : ByteArray) (tab : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row))
    (htab : tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored) = some tab)
    (hA : Agree tab) :
    ∀ ro ∈ rc.map (fun p => stripR p.1), ∀ x ∈ ro.opens, ∀ zc ∈ x.2.1.zip x.2.2.cols,
      ∃ (q : OPos (uL D.C D.ds)) (z : Opening 256 (OSym (uL D.C D.ds) q)),
        posAtS D.C D.ds (x.1.tree - D.base.firstTree) zc.1 = some q ∧
          opLS D.C (lookE run tab) 0 D.ds q = some z ∧ colS D.C D.ds q z.sym = zc.2 := by
  intro ro hro y hy zc hzc
  obtain ⟨r, hr, x, hx, R, poss, hf⟩ := trace_open h _ _ _ _ _ htr ro hro y hy
  obtain ⟨n, hn⟩ := hg r hr x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hro
  obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 (show y ∈ p.1.opens.map
    fun x => (x.1, x.2.1, stripO x.2.2) from hy)
  have hsh : y0.1 = x.1 := hf.sh
  have hmem : y0 ∈ (roundWithStoredOpenings p).opens := List.mem_append_right _ hy0
  have hrd : roundWithStoredOpenings p ∈ o.rounds.toList := by rw [ho]; exact List.mem_map.2 ⟨p, hp, rfl⟩
  obtain ⟨i, k, hop⟩ := opsOf_mem (c := 1) hrd hmem
  have hop' : (⟨1, i, k, y0.1, y0.2.1, y0.2.2⟩ : OpAt) ∈
      (opsOf 1 o).filter fun op => !op.sh.stored :=
    List.mem_filter.2 ⟨hop, by show (!y0.1.stored) = true; rw [hsh, hn.plain]; rfl⟩
  obtain ⟨l1, l2, -⟩ := _root_.Run.TieTree.ok_spec _ _ _ hf.okb
  obtain ⟨sl, hz⟩ := zip_salt y0.2.1 y0.2.2.cols y0.2.2.salts
    (by show y0.2.2.cols.length ≤ y0.2.2.salts.length
        have e1 : y0.2.2.cols.length = y0.2.1.length := l1
        have e2 : y0.2.2.salts.length = y0.2.1.length := l2
        omega) zc hzc
  have htree : y0.1.tree - D.base.firstTree = n := by rw [hsh, hn.tree]; omega
  have hlt : zc.1 < 2 ^ y0.1.a := by
    rw [hsh]
    exact (listOK_spec _ _ hf.okl).2.2 _ (List.of_mem_zip hzc).1
  have hw : zc.2.length = y0.1.W := by
    rw [hsh]
    exact okb_width _ _ _ hf.okb _ (List.of_mem_zip hzc).2
  show ∃ q z, posAtS D.C D.ds (y0.1.tree - D.base.firstTree) zc.1 = some q ∧ _
  rw [htree]
  exact cols_of_table D.C D.ds 0 n (fun _ => run) (fun s => s.tree) htab hA hop' hz
    (by show treeSh D.ds n = some y0.1; rw [hsh]; exact hn.sh) rfl hlt hw

end OnBytes.K.Left
