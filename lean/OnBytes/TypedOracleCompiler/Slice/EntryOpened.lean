-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryOpened.lean: AT THE ENTRY's TYPED STRING (Slice/EntryTyping.lean:
assembleS) EVERY READ POSITION HAS AN OPENING: SO checksB | checksExt ARE "some": THE FIELDS "own"
AND "ext" OF THE RECORD LaxYes (written in a file of this project that is not in this library).
Lemmas with proofs.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. LaxYes' fields "own" and "ext" ask that checksB | checksExt give "some".
THE INTERFACE TO WHAT IS HAD. For own trees: THE SIBLING's OWN RowsL (Run/PageIsForest.lean): round
by round, tree by tree: the table has a record and "read" means "listed in it", or it has none and
nothing is read. Run/PageIsAfter.lean's rows_top gives it of what a reader hands out, from LaxFacts
and "the typed draws are the reader's". Here it is asked at the table tblOf ops of the typing's own
list of openings. For the two stored tables: "a read position is listed in a stored opening of its
table" (ListedX), which readOf | StoOK (under OnBytes/Tie/) are to give.
  tblOf ops              the sibling's table (the form's number ↦ width, record) of a list of
    openings;   tblOf_lookup: a record of it is an opening of the list
  rowsT_at               the row of the i-th tree from k on, WITH "nothing is read" where the table
    has no record (the sibling's RowsT_at drops that half)
  opTS_isSome            a position's opening by opTS is there exactly if the table of openings has
    one at (the count, the tree's form, the place)
  mem_mapM, tabOf_mem    a listed place of an opening of the list stands in the typing's table;
    lookup_isSome
  zip_mem                a member of a list has a partner in a zip with a list of the same length
  lookE_isSome           the table has a row at (s.tree, x) whose column has s.W words ⇒ lookE … s x
    is some
  ColsFit ops        every column of every opening has its form's width, and two openings of one
    number have one width
  own_opened         RowsL D.C (tblOf ops) sb ds ros isRead, tabOf … ops = some tab, ColsFit ops
    ⇒ every read position's opLS D.C (lookE run tab) n ds q is some
  ListedX D a ops isReadE, ext_opened      the like for the two tables
  assembleS_own, assembleS_ext     AT assembleS's STRING: ∃ a, checksB … = some a; ∃ b,
    checksExt … = some b
WHAT IS NOT SAID. RowsL and ListedX at a real reading (to be had from the trace of
OnBytes/Tie/TraceStrict.lean and the chain's half). tblOf ((opsOf 1 o).filter not stored) = the
sibling's opensB (offStored …): not shown.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryWhole
import OnBytes.TypedOracleCompiler.Run.PageIsForest

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf RowsT RowsL)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom rootsB OpenB)

/-! ## Lists -/

theorem mem_mapM {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → ∀ a ∈ l, ∃ b ∈ l', f a = some b
  | [], _, _, _, ha => absurd ha List.not_mem_nil
  | x :: l, l', h, a, ha => by
      rw [List.mapM_cons] at h
      cases hb : f x with
      | none => rw [hb] at h; cases h
      | some b =>
        cases hbs : l.mapM f with
        | none => rw [hb, hbs] at h; cases h
        | some bs =>
          rw [hb, hbs] at h
          obtain rfl : b :: bs = l' := Option.some.inj h
          rcases List.mem_cons.1 ha with rfl | ha
          · exact ⟨b, List.mem_cons_self, hb⟩
          · obtain ⟨c, hc, e⟩ := mem_mapM f l bs hbs a ha
            exact ⟨c, List.mem_cons_of_mem _ hc, e⟩

theorem lookup_isSome {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), (k, v) ∈ l → (l.lookup k).isSome = true
  | [], _, _, h => absurd h List.not_mem_nil
  | (k', v') :: l, k, v, h => by
      rw [List.lookup_cons]
      split
      · rfl
      · rename_i hk
        rcases List.mem_cons.1 h with e | h
        · cases e
          simp at hk
        · exact lookup_isSome l k v h

theorem zip_mem {α β : Type} : ∀ (xs : List α) (ys : List β), ys.length = xs.length → ∀ x ∈ xs, ∃ y,
    (x, y) ∈ xs.zip ys
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | _ :: _, [], h, _, _ => by cases h
  | a :: xs, b :: ys, h, x, hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, List.mem_cons_self⟩
      · obtain ⟨y, hy⟩ := zip_mem xs ys (by simpa using h) x hx
        exact ⟨y, List.mem_cons_of_mem _ hy⟩

/-- a listed place of an opening of the list stands in the typing's table -/
theorem tabOf_mem {num : OpAt → ℕ} {ops : List OpAt} {tab : List ((ℕ × ℕ) × Row)}
    (h : tabOf num ops = some tab)
    {op : OpAt} (hop : op ∈ ops) {z : ℕ × List UInt64 × ByteArray}
        (hz : z ∈ op.xs.zip (op.out.cols.zip op.out.salts)) :
    ∃ path, ((num op, z.1), (z.2.1, z.2.2, path)) ∈ tab := by
  unfold tabOf at h
  obtain ⟨ls, hls, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨l', hl', hf⟩ := mem_mapM _ _ _ hls op hop
  obtain ⟨l, hrows, rfl⟩ := Option.map_eq_some_iff.1 hf
  unfold rowsOf at hrows
  obtain ⟨r, hr, hfr⟩ := mem_mapM _ _ _ hrows z hz
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 hfr
  exact ⟨p, List.mem_flatten.2 ⟨_, hl', List.mem_map.2 ⟨_, hr, rfl⟩⟩⟩

/-! ## The sibling's table -/

/-- the sibling's table of a list of openings -/
def tblOf (ops : List OpAt) : List (ℕ × ℕ × OpenB) :=
  ops.map fun op => (op.sh.tree, op.sh.W, ⟨op.sh.a, op.xs, op.out.cols, op.out.salts, op.out.given⟩)

theorem tblOf_lookup {ops : List OpAt} {t W : ℕ} {Ob : OpenB}
    (h : (tblOf ops).lookup t = some (W, Ob)) :
    ∃ op ∈ ops, op.sh.tree = t ∧ op.sh.W = W ∧ Ob =
        ⟨op.sh.a, op.xs, op.out.cols, op.out.salts, op.out.given⟩ := by
  obtain ⟨op, hop, e⟩ := List.mem_map.1 (mem_of_lookup _ _ _ h)
  cases e
  exact ⟨op, hop, rfl, rfl, rfl⟩

/-- the row of the i-th tree from k on -/
theorem rowsT_at (tbl : List (ℕ × ℕ × OpenB)) (sb : ℕ) (all : List _root_.Fmt.Shape)
    (isRead : PQ.PosT all → Bool) :
    ∀ (k : ℕ) (ts : List _root_.Fmt.Shape) (R : List ByteArray), RowsT tbl sb all isRead k ts R →
      ∀ i sh, ts[i]? = some sh →
        (∃ Ob, tbl.lookup sh.tree = some (sh.W, Ob) ∧ Ob.ok sb sh.W = true ∧
            ∀ x p, PQ.posAtT all (k + i) x = some p → isRead p = decide (x ∈ Ob.idx)) ∨
          ∀ x p, PQ.posAtT all (k + i) x = some p → isRead p = false
  | _, [], [], _, _, _, h => by simp at h
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
  | k, s :: ts, root :: R, h, 0, sh, hs => by
      obtain rfl : s = sh := by simpa using hs
      obtain ⟨-, hcase, -⟩ := h
      rcases hcase with ⟨Ob, hl, -, hok, -, hread⟩ | ⟨-, hno⟩
      · exact Or.inl ⟨Ob, hl, hok, hread⟩
      · exact Or.inr hno
  | k, _ :: ts, _ :: R, h, i + 1, sh, hs => by
      have := rowsT_at tbl sb all isRead (k + 1) ts R h.2.2 i sh (by simpa using hs)
      rw [show k + 1 + i = k + (i + 1) by omega] at this
      exact this

/-! ## The table of openings at a position -/

theorem opTS_isSome {lam : ℕ} (look : Look lam) : ∀ (ts : List _root_.Fmt.Shape) (n : ℕ)
    (p : PQ.PosT ts),
    ∃ (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)), ts[PQ.treeT ts p]? = some s ∧
        x.val = PQ.placeT ts p ∧
      (opTS look n ts p).isSome = (look (n + PQ.treeT ts p) s x).isSome
  | s :: _, _, .inl x => ⟨s, x, rfl, rfl, rfl⟩
  | _ :: ts, n, .inr p => by
      obtain ⟨s, x, h1, h2, h3⟩ := opTS_isSome look ts (n + 1) p
      refine ⟨s, x, by simpa [PQ.treeT] using h1, h2, ?_⟩
      rw [show n + PQ.treeT (_ :: ts) (.inr p) = n + 1 + PQ.treeT ts p by show n + (PQ.treeT ts p + 1) = _; omega]
      exact h3

theorem lookE_isSome {run : ByteArray} {tab : List ((ℕ × ℕ) × Row)} {n : ℕ} {s : _root_.Fmt.Shape}
    {x : Fin (2 ^ s.a)}
    {row : Row} (hl : tab.lookup (s.tree, x.val) = some row) (hw : row.1.length = s.W) :
    (lookE run tab n s x).isSome = true := by
  obtain ⟨col, salt, path⟩ := row
  unfold lookE lookF
  rw [hl]
  show (if h : col.length = s.W then _ else _ : Option _).isSome = true
  rw [dif_pos hw]
  rfl

/-- every column has its form's width; two openings of one number have one width -/
structure ColsFit (ops : List OpAt) : Prop where
  cols : ∀ op ∈ ops, ∀ c ∈ op.out.cols, c.length = op.sh.W
  one : ∀ op ∈ ops, ∀ op' ∈ ops, op.sh.tree = op'.sh.tree → op.sh.W = op'.sh.W

section
variable {ops : List OpAt} {tab : List ((ℕ × ℕ) × Row)}
    (ht : tabOf (fun op => op.sh.tree) ops = some tab)
  (hc : ColsFit ops) (run : ByteArray) (sb : ℕ)
include ht hc

/-- one round's trees -/
theorem round_opened (ts : List _root_.Fmt.Shape) (isRead : PQ.PosT ts → Bool) (R : List ByteArray)
    (h : RowsT (tblOf ops) sb ts isRead 0 ts R) (n : ℕ) (p : PQ.PosT ts) (hp : isRead p = true) :
    (opTS (lookE run tab) n ts p).isSome = true := by
  obtain ⟨s, x, h1, h2, h3⟩ := opTS_isSome (lookE run tab) ts n p
  rw [h3]
  have hpos := PQ.posAtT_place ts p
  rcases rowsT_at (tblOf ops) sb ts isRead 0 ts R h _ s h1 with ⟨Ob, hl, hok, hread⟩ | hno
  · rw [Nat.zero_add] at hread
    have hx : PQ.placeT ts p ∈ Ob.idx := of_decide_eq_true ((hread _ p hpos).symm.trans hp)
    obtain ⟨op, hop, e1, e2, rfl⟩ := tblOf_lookup hl
    simp only [OpenB.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨y, hy⟩ := zip_mem op.xs (op.out.cols.zip op.out.salts)
      (by rw [List.length_zip, hok.1.1.1.1.1.2, hok.1.1.1.1.2, Nat.min_self]) _ hx
    obtain ⟨path, hm⟩ := tabOf_mem ht hop hy
    obtain ⟨row, hrow⟩ := Option.isSome_iff_exists.1 (lookup_isSome _ _ _ hm)
    have hrow' : tab.lookup (s.tree, x.val) = some row := by rw [h2, ← e1]; exact hrow
    obtain ⟨op', hop', e3, hz', -⟩ := tabOf_lookup ht hrow'
    refine lookE_isSome hrow' ?_
    rw [hc.cols op' hop' _ (List.of_mem_zip (List.of_mem_zip hz').2).1,
        hc.one op' hop' op hop (e3.trans e1.symm), e2]
  · rw [Nat.zero_add] at hno
    rw [hno _ p hpos] at hp
    cases hp

/-- Every read position of the chain's own trees has an opening. -/
theorem own_opened (C : PQ.CK) : ∀ (ds : List PQ.RD) (ros : List _root_.Fmt.RoundOut)
    (isRead : OPos (PQ.uL C ds) → Bool),
    RowsL C (tblOf ops) sb ds ros isRead → ∀ (n : ℕ) (q : OPos (PQ.uL C ds)), isRead q = true →
      (opLS C (lookE run tab) n ds q).isSome = true
  | [], _, _, _, _, q, _ => q.elim
  | _ :: _, [], _, h, _, _, _ => h.elim
  | d :: _, _ :: _, isRead, h, n, .inl p, hq =>
      round_opened ht hc run sb d.trees (fun p => isRead (.inl p)) _ h.1 n p hq
  | d :: ds, _ :: ros, isRead, h, n, .inr q, hq =>
      own_opened C ds ros (fun p => isRead (.inr p)) h.2 (n + d.trees.length) q hq

end

/-! ## The two tables -/

/-- a read position is listed in a stored opening of its table, whose lists have one length -/
def ListedX (D : XD) (a : ℕ) (ops : List OpAt) (isReadE : Fin (2 ^ a) ⊕ Fin (2 ^ a) → Bool) :
    Prop :=
  ∀ p, isReadE p = true → ∃ op ∈ ops, whichOf D op = Sum.elim (fun _ => 0) (fun _ => 1) p ∧
    (Sum.elim id id p : Fin (2 ^ a)).val ∈ op.xs ∧ op.out.cols.length = op.xs.length ∧
    op.out.salts.length = op.xs.length

theorem ext_opened {D : XD} {a : ℕ} {ops : List OpAt} {tx : List ((ℕ × ℕ) × Row)}
    (ht : tabOf (whichOf D) ops = some tx)
    (cfg : ByteArray) {isReadE : Fin (2 ^ a) ⊕ Fin (2 ^ a) → Bool} (h : ListedX D a ops isReadE)
    (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) (hp : isReadE p = true) : (extE a cfg tx p).isSome = true := by
  obtain ⟨op, hop, hw, hx, l1, l2⟩ := h p hp
  obtain ⟨y, hy⟩ := zip_mem op.xs (op.out.cols.zip op.out.salts)
      (by rw [List.length_zip, l1, l2, Nat.min_self]) _ hx
  obtain ⟨path, hm⟩ := tabOf_mem ht hop hy
  have hs := lookup_isSome _ _ _ hm
  rw [hw] at hs
  cases p with
  | inl q =>
    show ((tx.lookup (0, q.val)).map _).isSome = true
    rw [Option.isSome_map]
    exact hs
  | inr q =>
    show ((tx.lookup (1, q.val)).map _).isSome = true
    rw [Option.isSome_map]
    exact hs

/-! ## At the typing's string -/

section
variable {X : Type} (D : XD) (dec : X → View → Bool) {I X' : Type} {L : BatchProtocolWithLeafBody I X'}

/-- "own". -/
theorem assembleS_own {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    (hπ : assembleS D dec o = some π)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
        OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds)))
        (isRead : OPos (_root_.Run.Twin.up (SOf D.C D.ds)) → Bool)
    (sb : ℕ) (ros : List _root_.Fmt.RoundOut)
    (hrows : RowsL D.C (tblOf ((opsOf 1 o).filter fun op => !op.sh.stored)) sb D.ds ros fun q =>
        isRead (.inr q))
    (hc : ColsFit ((opsOf 1 o).filter fun op => !op.sh.stored)) :
    ∃ a : List (Check 256 L), checksB (_root_.Run.Twin.up (SOf D.C D.ds))
        (_root_.Run.Twin.allLo (SOf D.C D.ds))
      (wqXE D dec).sh embS rts isRead π.opens = some a := by
  obtain ⟨run, pl, tab, tx, -, -, e3, -, -, -, -, hop, -⟩ := assembleS_some D dec hπ
  refine Option.isSome_iff_exists.1 (checksB_isSome _ _ _ embS rts isRead π.opens fun p hp => ?_)
  cases p with
  | inl e => exact e.elim
  | inr q =>
    rw [hop q]
    exact own_opened e3 hc run sb D.C D.ds ros (fun q => isRead (.inr q)) hrows 0 q hp

/-- "ext". -/
theorem assembleS_ext {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    (hπ : assembleS D dec o = some π)
    (embE : SgX → Body L) (cms : List (Dig 256)) (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool)
    (h : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) isReadE) :
    ∃ b : List (Check 256 L), TypedOracleCompiler.Compile.Batch.checksExt (wqXE D dec).ext embE
        cms isReadE π.ext
      (wqXE D dec).ext.all = some b := by
  obtain ⟨run, pl, tab, tx, -, -, -, e4, -, -, -, -, hext, -⟩ := assembleS_some D dec hπ
  refine Option.isSome_iff_exists.1 (checksExt_isSome _ embE cms isReadE π.ext (fun p hp => ?_) _)
  rw [hext]
  exact ext_opened e4 D.base.cfg h p hp

end

end TypedOracleCompiler.Slice
