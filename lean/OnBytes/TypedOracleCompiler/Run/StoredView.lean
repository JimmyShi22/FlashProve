-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/StoredView.lean: the sibling's compiled verifier's view is the strict reader's view.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/StoredView.lean (7 declarations, 222 lines). CUT BY PROGRAM. A decision
sees a chain as a view: the rounds' items and draws, and the opened columns. The strict reader forms
a view from what it has read (`Fmt.viewX`). The protocol that the sibling makes from a description
forms one from its typed transcript and from two strings, which stand for the stored tables
(`viewX`). The two views are equal at the typed transcript made from what was read.

AS TEXT, but for `_root_.` before `Fmt.` and `Iop.`, and one line break (5). `lookX`,
`lookX_stored`, `lookX_small`, `stored_share`, `viewX_eq`. NOT SAID AGAIN, imported as they are (2):
`forall₂_zip`, `storedKey_item`. TURNED, NEW, NO COUNTERPART: none. That the text stands with a list
of trees a round rests on the sibling's `pi_want`, `pi_rowOf`, `pi_sent`, `rvSL_tr`, `rhoSL_tr`,
`colAtS_tr`.

WHAT IS NOT SAID. What a chain proves. Nothing on soundness; no probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.StoredGlue
import OnBytes.TypedOracleCompiler.Run.PageIsAfterTop
import OnBytes.Tie.StoredView

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open OnBytes.Tie (xsOf storedB_eq roundWithStoredOpenings StoredFact forall₂_zip storedKey_item tab_small
  offStored_rounds)

/-- How the protocol's view finds the column under a key at a place: in one of the two strings, or
in the transcript. This is the function inside `Run.PQ.viewX`. -/
def lookX (C : CK) (ds : List RD) (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str) (τ : _root_.Iop.Tr (uL C ds))
    (kx : ℕ × ℕ) : Option (ℕ × ℕ × List UInt64) :=
  if kx.1 = PQ.storedKey false then
    (xPos (2 ^ a) (false, kx.2)).map fun p => (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2)
  else if kx.1 = PQ.storedKey true then
    (xPos (2 ^ a) (true, kx.2)).map fun p => (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2)
  else (colAtS C ds τ kx.1 kx.2).map fun c => (kx.1, kx.2, c)

/-- Under a stored table's key the column is read in that table's string. -/
theorem lookX_stored (C : CK) (ds : List RD) (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (τ : _root_.Iop.Tr (uL C ds)) (b : Bool) (x : ℕ) :
    lookX C ds a y τ (PQ.storedKey b, x) =
      (xPos (2 ^ a) (b, x)).map fun p => (PQ.storedKey b, x, ((twoExternalStrings (2 ^ a) SgX).rd y p).2) := by
  cases b
  · exact if_pos rfl
  · have h0 : ¬ (PQ.storedKey true, x).1 = PQ.storedKey false := by
      show ¬ 2 ^ 16 + 1 = 2 ^ 16 + 0
      omega
    unfold lookX
    rw [if_neg h0, if_pos rfl]

/-- Under a key below 2 ^ 16 the column is read in the transcript. -/
theorem lookX_small (C : CK) (ds : List RD) (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (τ : _root_.Iop.Tr (uL C ds)) (k x : ℕ) (h : k < 2 ^ 16) :
    lookX C ds a y τ (k, x) = (colAtS C ds τ k x).map fun c => (k, x, c) := by
  have h0 : ¬ (k, x).1 = PQ.storedKey false := by
    show ¬ k = 2 ^ 16 + 0
    omega
  have h1 : ¬ (k, x).1 = PQ.storedKey true := by
    show ¬ k = 2 ^ 16 + 1
    omega
  unfold lookX
  rw [if_neg h0, if_neg h1]

/-- One round's stored tables: the protocol's view finds the columns that the reader lists. -/
theorem stored_share (h : HId) (cfg statement : ByteArray) (poss : List ℕ) (C : CK)
    (ds : List RD) (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str) (τ : _root_.Iop.Tr (uL C ds)) :
    ∀ {ts : List _root_.Fmt.Stored} {zs : List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)},
    List.Forall₂ (StoredFact h cfg statement poss) ts zs →
    (∀ t ∈ ts, t.sh.a = a ∧ t.item ≤ 1) →
    (∀ tz ∈ ts.zip zs, ∀ xc ∈ tz.2.2.1.zip tz.2.2.2.cols,
      ∃ q, xPos (2 ^ a) (tz.1.item == 1, xc.1) = some q ∧
        (twoExternalStrings (2 ^ a) SgX).rd y q = (xc.1, xc.2)) →
    (ts.flatMap fun t =>
      (_root_.Fmt.listOf ((_root_.Fmt.partOf t poss).map (· % 2 ^ a))).map fun x =>
        (PQ.storedKey (t.item == 1), x)).filterMap (lookX C ds a y τ) =
      (ts.zip zs).flatMap fun u => (u.2.2.1.zip u.2.2.2.cols).map fun q =>
        (_root_.Fmt.storedKey u.1.item, q.1, q.2)
  | _, _, .nil, _, _ => rfl
  | t :: ts, z :: zs, .cons f r, ha, hy => by
    have ih := stored_share h cfg statement poss C ds a y τ r
      (fun t' ht' => ha t' (List.mem_cons_of_mem _ ht'))
      (fun tz htz => hy tz (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ htz))
    have hy0 := hy (t, z) (by rw [List.zip_cons_cons]; exact List.mem_cons_self)
    obtain ⟨ha0, hi0⟩ := ha t List.mem_cons_self
    rw [List.flatMap_cons, List.filterMap_append, ih, List.zip_cons_cons, List.flatMap_cons]
    congr 1
    have hx : _root_.Fmt.listOf ((_root_.Fmt.partOf t poss).map (· % 2 ^ a)) = z.2.1 := by
      rw [f.xs, ha0]
    rw [hx, List.filterMap_map]
    refine filterMap_zip_of _ (fun x c => (_root_.Fmt.storedKey t.item, x, c)) z.2.1 z.2.2.cols
      (TieTree.ok_spec _ _ _ f.okb).1 fun x c hm => ?_
    obtain ⟨q, hq, hr⟩ := hy0 (x, c) hm
    show lookX C ds a y τ (PQ.storedKey (t.item == 1), x) = _
    rw [lookX_stored, hq, storedKey_item t.item hi0]
    show some (_root_.Fmt.storedKey t.item, x, ((twoExternalStrings (2 ^ a) SgX).rd y q).2) = _
    rw [hr]

/-- The view that the protocol forms is the view that the strict reader forms. `rc` holds, round by
round, the part without stored tables and the stored tables' openings. `oo` is the chain as read
without the stored tables' openings, `o` with them. y stands for the two strings that the verifier
builds; all that is asked of it is hy: at a listed place it holds the place and the listed column.
The other hypotheses: the
own part is within the sibling's limits; oo has `LaxFacts`; pl types its plain parts; ρ holds its
draws; each stored opening has `StoredFact`; all tables have the depth `D.a` and are
items 0 or 1. -/
theorem viewX_eq (h : HId) (D : XD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)
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
  have hbase : D.base.ok = true := base_ok D.base hok
  have ht : TabTR D.base.rounds oo.rounds.toList [] := tab_tr h _ _ _ _ _ hL.trace
  have hlen : D.stored.length = oo.rounds.toList.length := by
    rw [hoo, List.length_map]
    exact hS.length_eq
  have ht16 : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, x.1.tree < 2 ^ 16 := by
    have e := _root_.Fmt.ok_trees hbase
    simp only [List.all_eq_true, decide_eq_true_eq] at e
    exact e
  have hsm := tab_small _ _ _ ht ht16
  have hsent : List.Forall₂ SentR (rds D.base) oo.rounds.toList := pi_sent h D.base oo hok hL
  have hw := wantedX_eq D.base D.a D.stored oo.rounds.toList hlen ht
    fun r hr x hx => tab_good D.base (tab_limits D.base hok) r hr x hx
  show (⟨rvSL D.C D.ds (trL D.C K chal D.ds (rtSL D.C D.ds oo.rounds.toList) pl ρ
        (opL D.C (opensB oo) run D.ds)),
      (wantedX D.a (rds D.base) (xsOf D.stored) (drawnSL D.C D.ds (rhoSL D.C D.ds
        (trL D.C K chal D.ds (rtSL D.C D.ds oo.rounds.toList) pl ρ
          (opL D.C (opensB oo) run D.ds))))).filterMap
        (lookX D.C D.ds D.a y (trL D.C K chal D.ds (rtSL D.C D.ds oo.rounds.toList) pl ρ
          (opL D.C (opensB oo) run D.ds)))⟩ : _root_.Fmt.View) =
    ⟨o.rounds.toList.map fun r => ⟨_root_.Fmt.noRoots r.vals, r.drawn⟩,
      (D.stored.zip o.rounds.toList).flatMap fun u => _root_.Fmt.openedX D.base.firstTree u.1 u.2⟩
  rw [rvSL_tr D.C K chal D.ds oo.rounds.toList pl ρ _ hpl hd, rhoSL_tr, hd, hw]
  have hR : (oo.rounds.toList.map fun r => (⟨_root_.Fmt.noRoots r.vals, r.drawn⟩ : _root_.Fmt.RoundView)) =
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
  have hro : stripR p.1 ∈ oo.rounds.toList := by
    rw [hoo]
    exact List.mem_map_of_mem hp
  obtain ⟨n, htn, row⟩ := pi_rowOf h D.base oo hok hL (stripR p.1) hro x hx
  have hn : x.1.tree - D.base.firstTree = n := by
    rw [row.no]
    omega
  have hob := trace_okb h D.base.plan _ _ _ _ hL.trace (stripR p.1) hro x hx
  have hn16 : n < 2 ^ 16 := by
    have := hsm _ hro x hx
    omega
  rw [List.filterMap_map, hn]
  refine filterMap_zip_of _ (fun y c => (n, y, c)) x.2.1 x.2.2.cols
    (TieTree.ok_spec (obOf x) _ _ hob).1 fun y' c hm => ?_
  show lookX D.C D.ds D.a y _ (n, y') = some (n, y', c)
  rw [lookX_small _ _ _ _ _ _ _ hn16, ← hoo,
    colAtS_tr D.C K chal (opensB oo) run D.base.plan.salt (rds D.base) oo.rounds.toList pl ρ n
      x.1 (obOf x) hsent htn row.look rfl hob y' c hm]
  rfl


end TypedOracleCompiler.Run.PQ
