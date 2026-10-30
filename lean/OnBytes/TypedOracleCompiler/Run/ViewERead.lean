-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ViewERead.lean: THE TYPED VIEW OF ONE CHAIN IS THE STRICT READER's VIEW, WITHOUT THE
LIMIT "EVERY TREE IS OPENED AT MOST ONCE": FROM "ONE COLUMN A POSITION". A piece of "the tie at H_b"
for an entry file (LinkE).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. The protocol's decision sees a chain as a view (Fmt/View.lean): the rounds' items and draws,
and the opened columns AS A LIST: order and repeats count. OnBytes/TypedOracleCompiler HAS the equation of the two
views: viewX_eq (Run/StoredView.lean), and the verdict: acceptX (Run/StoredTop.lean). BOTH STAND
UNDER TWO LIMITS OF THE OLDER DEFAULT: PQ.ok's fourth clause (every own tree is opened at most once:
used for the tree's form and for the look-up in the parser's table) and StoOK.once (each stored
table is opened at most once), AND AT THE PARSER's OWN TABLES OF OPENINGS. A typed string has ONE
symbol a position; a file may show a position in several openings.
  viewX_cols     viewX_eq's TEXT, WITH THREE THINGS AS LETTERS: (1) THE TRANSCRIPT τ IS ANY: asked
                 of it: hrv (its rounds' items and draws are the reader's), hdr (its verifier
                 messages draw what the reader drew); (2) IN THE PLACE OF "the table finds the
                 tree's one opening": hcol: EVERY (tree, place, column) THAT THE
                     READER LISTS IS WHAT colAtS FINDS IN τ; (3) in the place of PQ.ok: D.base.ok
                     and hg (every opening of the description is some own tree's, of that tree's
                     form: TabGood: the description's matter alone). The stored tables' half stood
                     general already: hy: at every listed place the string y holds the place and the
                     listed column. ⊢ PQ.viewX D.C D.ds D.a D.xs y τ = Fmt.viewX ⟨D.base, D.stored⟩
                     o
  viewX_cols_tr      the same at τ := trL … (rtSL …) pl ρ op, op ANY table of typed openings: hrv |
                     hdr are rvSL_tr | rhoSL_tr
  viewX_eq_again A GUARD AGAINST EMPTINESS: viewX_eq's statement, TO THE LETTER, follows from
  viewX_cols_tr: within the older limits the parser's table meets hcol and the description meets hg:
  the new contains the old
  accept_cols    skeletonOverBothExternalStrings's verdict at that transcript: passSL, everyOpeningHasItsDraws, symbolsCarryTheirPositions true and the view's
                 equation ⇒ accept = dec (Fmt.viewX ⟨D.base, D.stored⟩ o)
  Agree tab, lookup_agree      a table (key ↦ column …) in which two rows under one key have one
                               column: THEN THE FIRST ROW THAT A LOOK-UP FINDS HAS THE COLUMN OF
                               EVERY ROW UNDER THAT KEY: the step from "the first opening that shows
                               a place" (tabOf | lookF) to hcol | hy;
  lookup_or_clash    without Agree: the look-up's column is the row's, OR two rows of the table
                     under one key have different columns (THE CLASH, as a disjunct on the file's
                     openings)
WHAT IS NOT SAID. hcol | hy AT A TYPING's TABLES (E's pure map is not here; lookF | extF are F's):
from lookup_agree they want: colAtS at trL … op is op's symbol's column at the position that posAtS
names, where a root was sent. Agree FROM "NoClash σ and all lists that openingM wrote down lie in
σ": NOT SHOWN IN THIS LIBRARY. hg at
the default's description (an evaluation). everyOpeningHasItsDraws (drawn.poss.length: readX_trace has it), symbolsCarryTheirPositions.
The decision with the record.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.StoredView
import OnBytes.TypedOracleCompiler.Run.StoredTop

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open OnBytes.Tie (xsOf storedB_eq roundWithStoredOpenings StoredFact forall₂_zip storedKey_item tab_small
  offStored_rounds)

/-- The protocol's view is the strict reader's, from "every listed column is the transcript's". -/
theorem viewX_cols (h : HId) (D : XD) (hbase : D.base.ok = true)
    (hg : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, ∃ n, TabGood D.base x n)
    (ros : List _root_.Fmt.RoundOut) (o : _root_.Fmt.ChainOut) (c : _root_.Fmt.Chain)
    (htr : TraceL h D.base.plan D.base.rounds ros c #[])
    (τ : _root_.Iop.Tr (uL D.C D.ds))
    (hrv : rvSL D.C D.ds τ = ros.map fun r => ⟨_root_.Fmt.noRoots r.vals, r.drawn⟩)
    (hdr : drawnSL D.C D.ds (rhoSL D.C D.ds τ) = ros.map (·.drawn))
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (hoo : ros = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg D.base.statement p.1.drawn.poss) ts p.2) D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (y : (twoExternalStrings (2 ^ D.a) SgX).Str)
    (hy : ∀ tp ∈ D.stored.zip rc, ∀ tz ∈ tp.1.zip tp.2.2, ∀ xc ∈ tz.2.2.1.zip tz.2.2.2.cols,
      ∃ q, xPos (2 ^ D.a) (tz.1.item == 1, xc.1) = some q ∧
        (twoExternalStrings (2 ^ D.a) SgX).rd y q = (xc.1, xc.2))
    (hcol : ∀ ro ∈ ros, ∀ x ∈ ro.opens, ∀ zc ∈ x.2.1.zip x.2.2.cols,
      colAtS D.C D.ds τ (x.1.tree - D.base.firstTree) zc.1 = some zc.2) :
    PQ.viewX D.C D.ds D.a D.xs y τ = _root_.Fmt.viewX ⟨D.base, D.stored⟩ o := by
  have ht : TabTR D.base.rounds ros [] := tab_tr h _ _ _ _ _ htr
  have hlen : D.stored.length = ros.length := by
    rw [hoo, List.length_map]
    exact hS.length_eq
  have ht16 : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, x.1.tree < 2 ^ 16 := by
    have e := _root_.Fmt.ok_trees hbase
    simp only [List.all_eq_true, decide_eq_true_eq] at e
    exact e
  have hsm := tab_small _ _ _ ht ht16
  have hw := wantedX_eq D.base D.a D.stored ros hlen ht hg
  show (⟨rvSL D.C D.ds τ,
      (wantedX D.a (rds D.base) (xsOf D.stored) (drawnSL D.C D.ds (rhoSL D.C D.ds τ))).filterMap
        (lookX D.C D.ds D.a y τ)⟩ : _root_.Fmt.View) =
    ⟨o.rounds.toList.map fun r => ⟨_root_.Fmt.noRoots r.vals, r.drawn⟩,
      (D.stored.zip o.rounds.toList).flatMap fun u => _root_.Fmt.openedX D.base.firstTree u.1 u.2⟩
  rw [hrv, hdr, hw]
  have hR : (ros.map fun r => (⟨_root_.Fmt.noRoots r.vals, r.drawn⟩ : _root_.Fmt.RoundView)) =
      o.rounds.toList.map fun r => ⟨_root_.Fmt.noRoots r.vals, r.drawn⟩ := by
    rw [hoo, ho, List.map_map, List.map_map]
    rfl
  rw [hR]
  refine congrArg _ ?_
  rw [hoo, ho, List.zip_map_right, List.zip_map_right, List.flatMap_map, List.flatMap_map]
  refine filterMap_flatMap_of _ _ _ _ fun tp htp => ?_
  obtain ⟨ts, p⟩ := tp
  have f : List.Forall₂ (StoredFact h D.base.cfg D.base.statement p.1.drawn.poss) ts p.2 :=
    forall₂_zip hS (ts, p) htp
  have hts : ts ∈ D.stored := (List.of_mem_zip htp).1
  have hp : p ∈ rc := (List.of_mem_zip htp).2
  have hlen2 : ts.length = p.2.length := f.length_eq
  have hz : ts.zip (p.2 ++ p.1.opens) = ts.zip p.2 := by
    have e := List.zip_append (l₁ := ts) (r₁ := []) (l₂ := p.2) (r₂ := p.1.opens) hlen2
    rw [List.append_nil] at e
    rw [e, List.zip_nil_left, List.append_nil]
  show ((ts.flatMap fun t =>
        (_root_.Fmt.listOf ((_root_.Fmt.partOf t p.1.drawn.poss).map (· % 2 ^ D.a))).map fun x =>
          (PQ.storedKey (t.item == 1), x)) ++
      (stripR p.1).opens.flatMap fun x => x.2.1.map fun z =>
        (x.1.tree - D.base.firstTree, z)).filterMap _ =
    ((ts.zip (p.2 ++ p.1.opens)).flatMap fun u => (u.2.2.1.zip u.2.2.2.cols).map fun q =>
        (_root_.Fmt.storedKey u.1.item, q.1, q.2)) ++
      _root_.Fmt.openedOf D.base.firstTree
        { roundWithStoredOpenings p with opens := (p.2 ++ p.1.opens).drop ts.length }
  rw [List.filterMap_append,
    stored_share h _ _ _ D.C D.ds D.a y _ f
      (fun t ht => hD t (List.mem_flatten.2 ⟨ts, hts, ht⟩)) (hy (ts, p) htp),
    hz, List.drop_left' hlen2.symm]
  congr 1
  have e : _root_.Fmt.openedOf D.base.firstTree { roundWithStoredOpenings p with opens := p.1.opens } =
      (stripR p.1).opens.flatMap fun x => (x.2.1.zip x.2.2.cols).map fun q =>
        (x.1.tree - D.base.firstTree, q.1, q.2) := by
    show _ = (p.1.opens.map _).flatMap _
    rw [List.flatMap_map]
    rfl
  rw [e]
  refine filterMap_flatMap_of _ _ _ _ fun x hx => ?_
  have hro : stripR p.1 ∈ ros := by
    rw [hoo]
    exact List.mem_map_of_mem hp
  have hob := trace_okb h D.base.plan _ _ _ _ htr (stripR p.1) hro x hx
  have hn16 : x.1.tree - D.base.firstTree < 2 ^ 16 := by
    have := hsm _ hro x hx
    omega
  rw [List.filterMap_map]
  refine filterMap_zip_of _ (fun y c => (x.1.tree - D.base.firstTree, y, c)) x.2.1 x.2.2.cols
    (TieTree.ok_spec (obOf x) _ _ hob).1 fun y' c' hm => ?_
  show lookX D.C D.ds D.a y τ (x.1.tree - D.base.firstTree, y') = some
      (x.1.tree - D.base.firstTree, y', c')
  rw [lookX_small _ _ _ _ _ _ _ hn16, hcol _ hro x hx (y', c') hm]
  rfl

/-- the same at the transcript that the verifier makes of a typed string, at ANY table of typed
openings -/
theorem viewX_cols_tr (h : HId) (D : XD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)
    (hbase : D.base.ok = true) (hg : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, ∃ n, TabGood D.base x n)
    (ros : List _root_.Fmt.RoundOut) (o : _root_.Fmt.ChainOut) (c : _root_.Fmt.Chain)
    (htr : TraceL h D.base.plan D.base.rounds ros c #[])
    (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (op : (p : OPos (uL D.C D.ds)) → Option (Opening 256 (OSym (uL D.C D.ds) p)))
    (hpl : plainsSL D.C D.ds ros = some pl) (hd : drawnSL D.C D.ds ρ = ros.map (·.drawn))
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (hoo : ros = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg D.base.statement p.1.drawn.poss) ts p.2) D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (y : (twoExternalStrings (2 ^ D.a) SgX).Str)
    (hy : ∀ tp ∈ D.stored.zip rc, ∀ tz ∈ tp.1.zip tp.2.2, ∀ xc ∈ tz.2.2.1.zip tz.2.2.2.cols,
      ∃ q, xPos (2 ^ D.a) (tz.1.item == 1, xc.1) = some q ∧
        (twoExternalStrings (2 ^ D.a) SgX).rd y q = (xc.1, xc.2))
    (hcol : ∀ ro ∈ ros, ∀ x ∈ ro.opens, ∀ zc ∈ x.2.1.zip x.2.2.cols,
      colAtS D.C D.ds (trL D.C K chal D.ds (rtSL D.C D.ds ros) pl ρ op)
          (x.1.tree - D.base.firstTree) zc.1 =
        some zc.2) :
    PQ.viewX D.C D.ds D.a D.xs y (trL D.C K chal D.ds (rtSL D.C D.ds ros) pl ρ op) =
      _root_.Fmt.viewX ⟨D.base, D.stored⟩ o :=
  viewX_cols h D hbase hg ros o c htr _ (rvSL_tr D.C K chal D.ds ros pl ρ op hpl hd)
    (by rw [rhoSL_tr]; exact hd) rc hoo ho hS hD y hy hcol

/-- A GUARD AGAINST EMPTINESS: viewX_eq AGAIN, TO THE LETTER, FROM viewX_cols_tr: within the older
limits the parser's table meets hcol (pi_rowOf, colAtS_tr) and the description meets hg (tab_good):
so the new statement contains the old. -/
theorem viewX_eq_again (h : HId) (D : XD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)
    (hok : PQ.ok D.base = true) (oo o : _root_.Fmt.ChainOut) (run : ByteArray)
    (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (hL : LaxFacts h D.base oo) (hpl : plainsSL D.C D.ds oo.rounds.toList = some pl)
    (hd : drawnSL D.C D.ds ρ = oo.rounds.toList.map (·.drawn))
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (hoo : oo.rounds.toList = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg D.base.statement p.1.drawn.poss) ts p.2) D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (y : (twoExternalStrings (2 ^ D.a) SgX).Str)
    (hy : ∀ tp ∈ D.stored.zip rc, ∀ tz ∈ tp.1.zip tp.2.2, ∀ xc ∈ tz.2.2.1.zip tz.2.2.2.cols,
      ∃ q, xPos (2 ^ D.a) (tz.1.item == 1, xc.1) = some q ∧
        (twoExternalStrings (2 ^ D.a) SgX).rd y q = (xc.1, xc.2)) :
    PQ.viewX D.C D.ds D.a D.xs y
        (trL D.C K chal D.ds (rtSL D.C D.ds oo.rounds.toList) pl ρ
          (opL D.C (opensB oo) run D.ds))
      = _root_.Fmt.viewX ⟨D.base, D.stored⟩ o := by
  have hsent : List.Forall₂ SentR (rds D.base) oo.rounds.toList := pi_sent h D.base oo hok hL
  refine viewX_cols_tr h D K chal (base_ok D.base hok)
    (fun r hr x hx => tab_good D.base (tab_limits D.base hok) r hr x hx) oo.rounds.toList o
        _ hL.trace pl ρ
    (opL D.C (opensB oo) run D.ds) hpl hd rc hoo ho hS hD y hy ?_
  intro ro hro x hx zc hm
  obtain ⟨n, htn, row⟩ := pi_rowOf h D.base oo hok hL ro hro x hx
  have hn : x.1.tree - D.base.firstTree = n := by
    rw [row.no]
    omega
  have hob := trace_okb h D.base.plan _ _ _ _ hL.trace ro hro x hx
  rw [hn]
  exact colAtS_tr D.C K chal (opensB oo) run D.base.plan.salt (rds D.base) oo.rounds.toList pl ρ n
    x.1 (obOf x) hsent htn row.look rfl hob zc.1 zc.2 hm

/-- The protocol's own verdict, at that transcript behind the trivial round. -/
theorem accept_cols (D : XD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)
    (dec : View → Bool)
    (rts : RootsOfChain 256 (uL D.C D.ds)) (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (op : (p : OPos (uL D.C D.ds)) → Option (Opening 256 (OSym (uL D.C D.ds) p)))
    (y : (twoExternalStrings (2 ^ D.a) SgX).Str) (v : View) (m : (s0 D.C).up.Msg) (c0 : (s0 D.C).Chal)
    (hpass : passSL D.C D.ds ρ = true) (hfull : everyOpeningHasItsDraws D.xs (drawnSL D.C D.ds ρ) = true)
    (hcar : symbolsCarryTheirPositions D.a D.ds D.xs (drawnSL D.C D.ds ρ) y = true)
    (hview : PQ.viewX D.C D.ds D.a D.xs y (trL D.C K chal D.ds rts pl ρ op) = v) :
    (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).accept () y (m, c0, trL D.C K chal D.ds rts pl ρ op) = dec v := by
  show (passSL D.C D.ds (rhoSL D.C D.ds (trL D.C K chal D.ds rts pl ρ op)) &&
      everyOpeningHasItsDraws D.xs (drawnSL D.C D.ds (rhoSL D.C D.ds (trL D.C K chal D.ds rts pl ρ op))) &&
      symbolsCarryTheirPositions D.a D.ds D.xs (drawnSL D.C D.ds (rhoSL D.C D.ds (trL D.C K chal D.ds rts pl ρ op))) y
          &&
      dec (PQ.viewX D.C D.ds D.a D.xs y (trL D.C K chal D.ds rts pl ρ op))) = dec v
  rw [rhoSL_tr, hpass, hfull, hcar, hview]
  rfl

/-! ## The first row that a look-up finds -/

/-- two rows of a table under one key have one column -/
def Agree {κ γ ρ : Type} (tab : List (κ × γ × ρ)) : Prop :=
  ∀ k a b, (k, a) ∈ tab → (k, b) ∈ tab → a.1 = b.1

/-- a look-up finds a row of the table, if the key has one -/
theorem lookup_some_of_mem {κ β : Type} [BEq κ] [LawfulBEq κ] :
    ∀ (l : List (κ × β)) (k : κ) (v : β), (k, v) ∈ l → ∃ w, l.lookup k = some w ∧ (k, w) ∈ l
  | (k', v') :: l, k, v, h => by
    rw [List.lookup_cons]
    cases hk : k == k' with
    | true =>
      have e : k = k' := eq_of_beq hk
      exact ⟨v', rfl, by rw [e]; exact List.mem_cons_self⟩
    | false =>
      rcases List.mem_cons.1 h with e | h'
      · have e1 : k = k' := congrArg Prod.fst e
        rw [e1, beq_self_eq_true] at hk
        cases hk
      · obtain ⟨w, hw, hm⟩ := lookup_some_of_mem l k v h'
        exact ⟨w, hw, List.mem_cons_of_mem _ hm⟩

/-- the look-up's column is the row's, or the table shows a clash -/
theorem lookup_or_clash {κ γ ρ : Type} [BEq κ] [LawfulBEq κ] (tab : List (κ × γ × ρ))
    (k : κ) (a : γ × ρ)
    (h : (k, a) ∈ tab) :
    (∃ w, tab.lookup k = some w ∧ w.1 = a.1) ∨ ∃ b, (k, b) ∈ tab ∧ b.1 ≠ a.1 := by
  obtain ⟨w, hw, hm⟩ := lookup_some_of_mem tab k a h
  by_cases e : w.1 = a.1
  · exact Or.inl ⟨w, hw, e⟩
  · exact Or.inr ⟨w, hm, e⟩

/-- under Agree the first row has the column of every row under its key -/
theorem lookup_agree {κ γ ρ : Type} [BEq κ] [LawfulBEq κ] (tab : List (κ × γ × ρ))
    (hA : Agree tab) (k : κ)
    (a : γ × ρ) (h : (k, a) ∈ tab) : ∃ w, tab.lookup k = some w ∧ w.1 = a.1 := by
  obtain ⟨w, hw, hm⟩ := lookup_some_of_mem tab k a h
  exact ⟨w, hw, hA k w a hm h⟩

end TypedOracleCompiler.Run.PQ
