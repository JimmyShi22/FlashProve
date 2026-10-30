-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ViewERead3.lean: FROM A TYPING's TABLE OF OPENINGS (tabOf | lookF | opLS) TO "EVERY
COLUMN THAT THE READER LISTS IS THE TYPED STRING's AT THAT POSITION". The third step of the view
(Run/ViewERead.lean: viewX_cols_tr; Run/ViewOp.lean: hcol_of_op). A piece of "the tie at H_b"
(LinkE; the tools serve LinkF).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY (at assembleS: opens (.inr q) := opLS D.C (lookE run tab) 0 D.ds q, lookE run tab := fun _ s x
=> lookF (fun _ => run) tab s.tree s x, tab := tabOf (fun op => op.sh.tree) (the chain's openings
that are not stored)). WHAT NEEDS Slice/Batch3SStrings | Batch3STyping | Batch3SWhole ALONE IS HERE;
the statement at assembleS itself wants Slice/EntryTyping | EntryPS.
  opTS_at, opLS_at     FORWARDS (at_tree goes backwards): if tree n of the rounds ds has the form s
                       and the table has an opening o at (m + n, s, x): posAtS names a position q
                       for (n, x), the typed string's opLS C look m ds has an opening there, and its
                       symbol's column (Run/ViewOp.lean: colS) is o's
  lookF_of_lookup          FORWARDS (lookF_some goes backwards): a row (col, salt, path) under (n,
                           x) with col.length = s.W gives an opening with that column
  mapM_mem, tabOf_mem FORWARDS (tabOf_lookup goes backwards): every listed (place, column, salt) of
  every opening of the list has its row in the table, under (num op, place)
  tabOf_row                BACKWARDS, for a MEMBER (tabOf_lookup is for a look-up): a row of the
                           table comes from an opening
  agree_of_once        Agree (Run/ViewERead.lean) FROM "ONCE": if unlike openings of the list have
                       unlike numbers and no opening lists a place twice, a key has ONE row. [FOR E
                       AT THE DEFAULT: record_opens_own | record_pair_places, by the kernel: no own
                       tree and no stored table (BY ITEM) is opened twice; listOf lists no place
                       twice.]
  cols_of_table        ALL TOGETHER, general in num, ops, the rounds: Agree tab; op ∈ ops; (z, c,
                       sl) listed; tree n has op's form s := op.sh, z < 2 ^ s.a, c.length = s.W; the
                       table is keyed as the look-up asks (key s = num op) ⇒ ∃ q w, posAtS C ds n z
                       = some q ∧ opLS C (fun _ s x => lookF runOf tab (key s) s x) m ds q = some w
                       ∧ colS C ds q w.sym = c:
                           hcol_of_op's hypothesis, opening by opening
WHAT IS NOT SAID. The statement at assembleS (the reader's stripped rounds' openings against opsOf 1
o's members; TabGood's n against x.1.tree − firstTree). The stored tables' half hy at extE (the same
tools: tabOf_mem, lookup_agree at tx keyed by whichOf). Agree WITHOUT "once" (F: trees opened
twice): from NoClash by openings_agree_any.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.ViewOp
import OnBytes.TypedOracleCompiler.Slice.Batch3SWhole

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open TypedOracleCompiler.Slice (Look opTS opLS lookF tabOf rowsOf OpAt mem_of_mapM rowsOf_mem)

/-! ## The typed string's opening at the position of (tree, place) -/

theorem opTS_at {lam : ℕ} (look : Look lam) :
    ∀ (ts : List _root_.Fmt.Shape) (n k : ℕ) (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a))
        (o : Opening lam (Fin s.W → UInt64)), ts[k]? = some s → look (n + k) s x = some o →
      ∃ (p : PosT ts) (w : Opening lam (SymT ts p)),
        posAtT ts k x.val = some p ∧ opTS look n ts p = some w ∧ colT ts p w.sym = List.ofFn o.sym
  | [], _, _, _, _, _, h, _ => by simp at h
  | s' :: _, n, 0, s, x, o, h, ho => by
      obtain rfl : s' = s := by simpa using h
      refine ⟨.inl x, o, ?_, ho, rfl⟩
      simp only [posAtT]
      rw [dif_pos x.isLt]
  | _ :: ts, n, k + 1, s, x, o, h, ho => by
      obtain ⟨p, w, h1, h2, h3⟩ := opTS_at look ts (n + 1) k s x o (by simpa using h)
        (by rwa [show n + 1 + k = n + (k + 1) by omega])
      refine ⟨.inr p, w, ?_, h2, h3⟩
      show (posAtT ts k x.val).map Sum.inr = _
      rw [h1]
      rfl

/-- Along the rounds. -/
theorem opLS_at (C : CK) (look : Look 256) :
    ∀ (ds : List RD) (m n : ℕ) (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a))
        (o : Opening 256 (Fin s.W → UInt64)),
      treeSh ds n = some s → look (m + n) s x = some o →
      ∃ (q : OPos (uL C ds)) (w : Opening 256 (OSym (uL C ds) q)),
        posAtS C ds n x.val = some q ∧ opLS C look m ds q = some w ∧
            colS C ds q w.sym = List.ofFn o.sym
  | [], _, _, _, _, _, h, _ => by cases h
  | d :: ds, m, n, s, x, o, h, ho => by
      have h0 : (if n < d.trees.length then d.trees[n]? else treeSh ds (n - d.trees.length)) = some
          s := h
      by_cases hn : n < d.trees.length
      · rw [if_pos hn] at h0
        obtain ⟨p, w, h1, h2, h3⟩ := opTS_at look d.trees m n s x o h0 ho
        refine ⟨.inl p, w, ?_, h2, h3⟩
        show (if n < d.trees.length then (posAtT d.trees n x.val).map Sum.inl else _) = _
        rw [if_pos hn, h1]
        rfl
      · rw [if_neg hn] at h0
        obtain ⟨q, w, h1, h2, h3⟩ := opLS_at C look ds (m + d.trees.length)
            (n - d.trees.length) s x o h0
          (by rwa [show m + d.trees.length + (n - d.trees.length) = m + n by omega])
        refine ⟨.inr q, w, ?_, h2, h3⟩
        show (if n < d.trees.length then _ else (posAtS C ds (n - d.trees.length) x.val).map
            Sum.inr) = _
        rw [if_neg hn, h1]
        rfl

/-! ## The table -/

theorem lookF_of_lookup (runOf : ℕ → ByteArray) (tab : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row))
    (n : ℕ)
    (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (row : TypedOracleCompiler.Slice.Row)
        (hl : tab.lookup (n, x.val) = some row)
    (hw : row.1.length = s.W) :
    ∃ o : Opening 256 (Fin s.W → UInt64), lookF runOf tab n s x = some o ∧
        List.ofFn o.sym = row.1 := by
  obtain ⟨col, salt, path⟩ := row
  unfold lookF
  rw [hl]
  refine ⟨_, dif_pos hw, ?_⟩
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact hw.symm
  · intro i h1 h2
    rw [List.getElem_ofFn]

theorem mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → ∀ z ∈ l, ∃ y ∈ l', f z = some y
  | [], _, _, _, hz => by cases hz
  | a :: l, l', h, z, hz => by
      rw [List.mapM_cons] at h
      cases hb : f a with
      | none => rw [hb] at h; cases h
      | some b =>
        cases hbs : l.mapM f with
        | none => rw [hb, hbs] at h; cases h
        | some bs =>
          rw [hb, hbs] at h
          obtain rfl : b :: bs = l' := Option.some.inj h
          rcases List.mem_cons.1 hz with rfl | hz
          · exact ⟨b, List.mem_cons_self, hb⟩
          · obtain ⟨y, hy, hf⟩ := mapM_mem f l bs hbs z hz
            exact ⟨y, List.mem_cons_of_mem _ hy, hf⟩

/-- Every listed place of every opening has its row. -/
theorem tabOf_mem {num : OpAt → ℕ} {ops : List OpAt} {tab : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row)}
    (h : tabOf num ops = some tab) {op : OpAt} (hop : op ∈ ops) {z : ℕ × List UInt64 × ByteArray}
    (hz : z ∈ op.xs.zip (op.out.cols.zip op.out.salts)) :
    ∃ path, ((num op, z.1), (z.2.1, z.2.2, path)) ∈ tab := by
  unfold tabOf at h
  obtain ⟨ls, hls, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨l', hl', hf⟩ := mapM_mem _ _ _ hls op hop
  obtain ⟨l, hrows, rfl⟩ := Option.map_eq_some_iff.1 hf
  unfold rowsOf at hrows
  obtain ⟨y, hy, hfy⟩ := mapM_mem _ _ _ hrows z hz
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 hfy
  exact ⟨p, List.mem_flatten.2 ⟨_, hl', List.mem_map.2 ⟨_, hy, rfl⟩⟩⟩

/-- a row of the table comes from an opening -/
theorem tabOf_row {num : OpAt → ℕ} {ops : List OpAt} {tab : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row)}
    (h : tabOf num ops = some tab) {k : ℕ × ℕ} {row : TypedOracleCompiler.Slice.Row} (hm : (k, row) ∈ tab) :
    ∃ op ∈ ops, num op = k.1 ∧ (k.2, row.1, row.2.1) ∈ op.xs.zip
        (op.out.cols.zip op.out.salts) := by
  unfold tabOf at h
  obtain ⟨ls, hls, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨l', hl', hm'⟩ := List.mem_flatten.1 hm
  obtain ⟨op, hop, hf⟩ := mem_of_mapM _ _ _ hls _ hl'
  obtain ⟨l, hrows, rfl⟩ := Option.map_eq_some_iff.1 hf
  obtain ⟨z, hz, e⟩ := List.mem_map.1 hm'
  cases e
  exact ⟨op, hop, rfl, (rowsOf_mem hrows hz).1⟩

/-- in a list without repeats a member of its zip is fixed by its first part -/
theorem zip_unique {α β : Type} : ∀ (l : List α) (l' : List β), l.Nodup → ∀ (a : α) (b b' : β),
    (a, b) ∈ l.zip l' → (a, b') ∈ l.zip l' → b = b'
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _ => by simp at h
  | x :: l, y :: l', hn, a, b, b', h, h' => by
      rw [List.zip_cons_cons] at h h'
      have hx : x ∉ l := (List.nodup_cons.1 hn).1
      rcases List.mem_cons.1 h with e | h1
      · rcases List.mem_cons.1 h' with e' | h2
        · exact (congrArg Prod.snd e).trans (congrArg Prod.snd e').symm
        · have ea : a = x := congrArg Prod.fst e
          exact absurd (ea ▸ (List.of_mem_zip h2).1) hx
      · rcases List.mem_cons.1 h' with e' | h2
        · have ea : a = x := congrArg Prod.fst e'
          exact absurd (ea ▸ (List.of_mem_zip h1).1) hx
        · exact zip_unique l l' (List.nodup_cons.1 hn).2 a b b' h1 h2

/-- Agree from "once". -/
theorem agree_of_once {num : OpAt → ℕ} {ops : List OpAt}
    {tab : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row)}
    (h : tabOf num ops = some tab) (h1 : ∀ a ∈ ops, ∀ b ∈ ops, num a = num b → a = b)
    (h2 : ∀ a ∈ ops, a.xs.Nodup) : Agree tab := by
  intro k a b ha hb
  obtain ⟨oa, hoa, na, za⟩ := tabOf_row h ha
  obtain ⟨ob, hob, nb, zb⟩ := tabOf_row h hb
  obtain rfl := h1 oa hoa ob hob (na.trans nb.symm)
  have e : (a.1, a.2.1) = (b.1, b.2.1) :=
    zip_unique oa.xs (oa.out.cols.zip oa.out.salts) (h2 oa hoa) k.2 (a.1, a.2.1) (b.1, b.2.1) za zb
  exact (Prod.mk.inj e).1

/-- All together: the typed string's opening at a listed place spells the listed column. -/
theorem cols_of_table (C : CK) (ds : List RD) (m n : ℕ) (runOf : ℕ → ByteArray)
    (key : _root_.Fmt.Shape → ℕ)
    {num : OpAt → ℕ} {ops : List OpAt} {tab : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row)}
        (h : tabOf num ops = some tab)
    (hA : Agree tab) {op : OpAt} (hop : op ∈ ops) {z : ℕ × List UInt64 × ByteArray}
    (hz : z ∈ op.xs.zip (op.out.cols.zip op.out.salts)) (ht : treeSh ds n = some op.sh)
        (hk : key op.sh = num op)
    (hlt : z.1 < 2 ^ op.sh.a) (hw : z.2.1.length = op.sh.W) :
    ∃ (q : OPos (uL C ds)) (w : Opening 256 (OSym (uL C ds) q)),
      posAtS C ds n z.1 = some q ∧ opLS C (fun _ s x => lookF runOf tab (key s) s x) m
          ds q = some w ∧
        colS C ds q w.sym = z.2.1 := by
  obtain ⟨path, hm⟩ := tabOf_mem h hop hz
  obtain ⟨row, hl, hc⟩ := lookup_agree tab hA (num op, z.1) (z.2.1, z.2.2, path) hm
  obtain ⟨o, ho, hs⟩ := lookF_of_lookup runOf tab (key op.sh) op.sh ⟨z.1, hlt⟩ row
      (by rw [hk]; exact hl)
    (by rw [hc]; exact hw)
  obtain ⟨q, w, a1, a2, a3⟩ := opLS_at C (fun _ s x => lookF runOf tab (key s) s x) ds m n op.sh
      ⟨z.1, hlt⟩ o ht ho
  exact ⟨q, w, a1, a2, by rw [a3, hs, hc]⟩

end TypedOracleCompiler.Run.PQ
