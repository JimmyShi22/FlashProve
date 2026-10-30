-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsViewProofs.lean: WHAT THE VIEW READS OFF THE TRANSCRIPT THAT THE VERIFIER
MAKES OF THE PARSER's ARGUMENT STRING. After the library's Run/PageIsViewProofs.lean: what the
entry's clause holds of it and stands on a declaration that the sibling says again.
  AS TEXT        trL, rhoSL_tr, rvSL_tr
  TURNED         trP_head (rootP reads the position's tree), SentR (as many trees as roots)
  WRITTEN ANEW   colAtS_tr: the library cases on "no tree | a tree" and on n = 0; here on n <
                 d.trees.length, and goes by the position of leaf y of tree n.
                 NO INNER INDUCTION WAS NEEDED: the lemmas "at the position of leaf x of tree k"
                 (Run/PageIsOp.lean; Slice/Plain3Pins.lean) carry it
  NEW            colT_symT (a list of words, made a symbol of a position's tree, is read back as
                 that list)

Terms: lean/GLOSSARY.md.

-/
import Run.PageIsViewProofs
import OnBytes.TypedOracleCompiler.Run.PageIsOp
import OnBytes.TypedOracleCompiler.Run.PageIsTabProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (gots_ofGots pv_old_mk lookup_of_mem mem_zip_ext at_listed filterMap_flatMap_of
    filterMap_zip_of pv_right trace_okb)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src Item ItemValue)

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- the transcript that the verifier makes of the rounds ds -/
abbrev trL (ds : List RD) (rts : RootsOfChain 256 (uL C ds)) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds))
    (f : (p : OPos (uL C ds)) → Option (Opening 256 (OSym (uL C ds) p))) : Iop.Tr (uL C ds) :=
  trP (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds) rts pl ρ f

/-- the verifier messages read off the transcript are those put in -/
theorem rhoSL_tr :
    ∀ (ds : List RD) (rts : RootsOfChain 256 (uL C ds)) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds))
        (f : (p : OPos (uL C ds)) → Option (Opening 256 (OSym (uL C ds) p))),
      rhoSL C ds (trL C K chal ds rts pl ρ f) = ρ
  | [], _, _, _, _ => rfl
  | d :: ds, (rt, rts), (p, pl), (c, ρ), f => by
      show (c, rhoSL C ds (trL C K chal ds rts pl ρ fun q => f (.inr q))) = (c, ρ)
      rw [rhoSL_tr ds]

/-- the rounds' values on the transcript -/
theorem rvSL_tr :
    ∀ (ds : List RD) (ros : List RoundOut) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds))
        (f : (p : OPos (uL C ds)) → Option (Opening 256 (OSym (uL C ds) p))),
      plainsSL C ds ros = some pl → drawnSL C ds ρ = ros.map (·.drawn) →
      rvSL C ds (trL C K chal ds (rtSL C ds ros) pl ρ f) =
        ros.map fun r => ⟨_root_.Fmt.noRoots r.vals, r.drawn⟩
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h, _ => by simp [plainsSL] at h
  | _ :: _, [], _, _, _, h, _ => by simp [plainsSL] at h
  | d :: ds, ro :: ros, (p, pl), (c, ρ), f, h, hd => by
      rcases h1 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, h1] at h
      rcases h2 : plainsSL C ds ros with _ | pl0
      · simp [plainsSL, h1, h2] at h
      simp only [plainsSL, h1, h2, Option.some.injEq] at h
      cases h
      have hd1 : C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) = ro.drawn :=
        (List.cons.inj hd).1
      have hd2 : drawnSL C ds ρ = ros.map (·.drawn) := (List.cons.inj hd).2
      show (⟨PlainOf.gots d.items
              (GPlain.old (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce)),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ : RV) ::
          rvSL C ds (trL C K chal ds (rtSL C ds ros) pl ρ fun q => f (.inr q)) = _
      rw [pv_old_mk, gots_ofGots _ _ _ h1, hd1, rvSL_tr ds ros pl ρ _ h2 hd2]
      rfl

end

/-! ### The head of the transcript -/

theorem trP_head {lam K : ℕ} (r : RS) (S : List RS) (a : RAnn r.up) (A : RoundSplits (up S))
    (w : WireRB lam K r.up a) (W : RoundsQueryLayout lam K (up S) A) (rt : RtC lam × RtC lam)
    (rts : RootsOfChain lam (up S)) (pl : r.Plain) (pls : Plains (up S)) (c : r.Chal) (ρ : Rho (up S))
    (f : (p : OPos (up (r :: S))) → Option (Opening lam (OSym (up (r :: S)) p))) (p : r.Pos)
    (op : Opening lam (r.Sym p)) (h1 : rootP r a w.tree rt p = true) (h2 : f (.inl p) = some op) :
    r.rd (trP (r :: S) (a, A) (w, W) (rt, rts) (pl, pls) (c, ρ) f).1.1 p = op.sym := by
  simp only [trP]
  rw [show r.rd = r.up.rd from rfl, w.pt.rd_ofSyms, h1, h2]

/-! ### A column read off the transcript -/

/-- a round and what was read in it go together: as many trees as roots, each root of 32 bytes -/
def SentR (d : RD) (ro : RoundOut) : Prop :=
  d.trees.length = (_root_.Fmt.rootsOf ro.vals).length ∧
      ∀ r ∈ _root_.Fmt.rootsOf ro.vals, r.size = 32

/-- TWO: a list of words, made a symbol of a position's tree, is read back as that list -/
theorem colT_symT : ∀ (ts : List _root_.Fmt.Shape) (p : PosT ts) (col : List UInt64)
    (y : SymT ts p),
    symT ts p col = some y → colT ts p y = col
  | s :: _, .inl _, col, y, h => by
      have h0 : (if h : col.length = s.W then
          some (fun i : Fin s.W => col[i.val]'(by rw [h]; exact i.isLt)) else none) = some y := h
      by_cases hw : col.length = s.W
      · rw [dif_pos hw] at h0
        cases Option.some.inj h0
        have e2 : (fun i : Fin s.W => col[i.val]'(by rw [hw]; exact i.isLt)) = colFn s.W col :=
          funext fun i => by
            simp [colFn, List.getElem?_eq_getElem (show i.val < col.length by rw [hw]; exact i.isLt)]
        show List.ofFn (fun i : Fin s.W => col[i.val]'(by rw [hw]; exact i.isLt)) = col
        rw [e2, ofFn_colFn s.W col hw]
      · rw [dif_neg hw] at h0
        cases h0
  | _ :: ts, .inr p, col, y, h => colT_symT ts p col y h

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (tbl : List (ℕ × ℕ × OpenB))
  (run : ByteArray) (sb : ℕ)

/-- at own tree n, whose opening the table finds, the transcript's column at a listed position is
the listed column -/
theorem colAtS_tr :
    ∀ (ds : List RD) (ros : List RoundOut) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds)) (n : ℕ)
        (sh : _root_.Fmt.Shape) (Ob : OpenB),
      List.Forall₂ SentR ds ros → treeSh ds n = some sh → tbl.lookup sh.tree = some (sh.W, Ob) →
      Ob.a = sh.a → Ob.ok sb sh.W = true →
      ∀ (y : ℕ) (c : List UInt64), (y, c) ∈ Ob.idx.zip Ob.cols →
        colAtS C ds (trL C K chal ds (rtSL C ds ros) pl ρ (opL C tbl run ds)) n y = some c
  | [], _, _, _, _, _, _, _, ht, _, _, _, _, _, _ => by cases ht
  | d :: ds, _, (p, pl), (c0, ρ), n, sh, Ob, hs, ht, hl, ha, hok, y, c, hm => by
      cases hs with
      | @cons _ ro _ ros h0 hs' =>
        have ht0 : (if n < d.trees.length then d.trees[n]? else treeSh ds (n - d.trees.length)) =
            some sh := ht
        by_cases hn : n < d.trees.length
        · rw [if_pos hn] at ht0
          have hy : y < 2 ^ sh.a := by
            rw [← ha]
            exact (TieTree.ok_list Ob sb sh.W hok).2.1 y (List.of_mem_zip hm).1
          have hw : c.length = sh.W := (TieTree.ok_list Ob sb sh.W hok).2.2 c (List.of_mem_zip hm).2
          obtain ⟨q, hq, -⟩ := TypedOracleCompiler.Slice.posAtT_some d.trees n y sh ht0 hy
          obtain ⟨v, hv, -⟩ := leafT_at 0 d.trees n y sh q c ht0 hq hw
          obtain ⟨sl, pt, hat⟩ := at_listed (symT d.trees q) run Ob sb sh.W hok y c hm
          have hop : opL C tbl run (d :: ds) (.inl q) = some ⟨v, leafSalt run sl, pt⟩ := by
            unfold opL
            show (match tbl.lookup (noT d.trees q).1 with
              | none => none
              | some x => x.2.at (symT d.trees q) run (noT d.trees q).2) = _
            rw [noT_at d.trees n y sh q ht0 hq, hl]
            show Ob.at _ run y = _
            rw [hat, hv]
            rfl
          have hroot : rootP (roundS C d) (roundS C d).lo (wireS C K chal d).tree
                ((none, some ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)) : RtC 256 × RtC 256)
                q = true := by
            show ((((_root_.Fmt.rootsOf ro.vals).map bytesToDig))[treeT d.trees q]?).isSome = true
            rw [(place_posAtT d.trees n y q hq).1, List.getElem?_map, Option.isSome_map,
              List.getElem?_eq_getElem (by rw [← h0.1]; exact hn)]
            rfl
          have key := trP_head (roundS C d) (SL C ds) (roundS C d).lo (allLo (SL C ds))
            (wireS C K chal d) (wiresSL C K chal ds)
            (none, some ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)) (rtSL C ds ros)
            p pl c0 ρ (opL C tbl run (d :: ds)) q _ hroot hop
          show (if n < d.trees.length then
              (posAtT d.trees n y).map fun p' => colT d.trees p'
                ((trL C K chal (d :: ds) (rtSL C (d :: ds) (ro :: ros)) (p, pl) (c0, ρ)
                  (opL C tbl run (d :: ds))).1.1 p')
            else _) = some c
          rw [if_pos hn, hq]
          refine congrArg some ?_
          refine Eq.trans (congrArg (colT d.trees q) key) ?_
          exact colT_symT d.trees q c v hv
        · rw [if_neg hn] at ht0
          have ih := colAtS_tr ds ros pl ρ (n - d.trees.length) sh Ob hs' ht0 hl ha hok y c hm
          show (if n < d.trees.length then _
              else
                colAtS C ds (trL C K chal ds (rtSL C ds ros) pl ρ (opL C tbl run ds))
                  (n - d.trees.length) y) = some c
          rw [if_neg hn]
          exact ih

end

end TypedOracleCompiler.Run.PQ
