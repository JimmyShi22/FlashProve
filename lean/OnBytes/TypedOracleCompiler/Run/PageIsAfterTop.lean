-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsAfterTop.lean: THE FORESTS' HALF's OWN STATEMENT: pi_after, WITH pi_view: THE
LEMMAS JOINED IN ONE PROOF. The half's own statement is said and proved here: pi_after :
Spec.pi_after, with no hypothesis beyond those in the statement: answers of 32 bytes, ok S = true,
the bodies' spelling (hi, below), LaxFacts, the run value, the typed plain parts, the draws.
After the library's Run/PageIsOp.lean:44-50 (opL_top, opL_tail), Run/PageIsView.lean (Spec.pi_view),
Run/PageIsViewProofs.lean:334-381 (pi_view_of, pi_view), Run/PageIs.lean:231-250 (Spec.pi_after),
Run/PageIsAfter.lean:101-214 (strict_top, after_top, pi_after): cut by program, then turned by hand.
NOT held by the entry's clause T1.
  AS TEXT       opL_top, opL_tail, Spec.pi_view_of, pi_view_of, pi_view
  TURNED BY FORM   Spec.pi_view, strict_top ("some []" for "some none"; the trivial round's strict
                   format is that of no tree)
  TURNED BY MATTER   Spec.pi_after, after_top, pi_after: THE STATEMENT CHANGES IN MORE THAN FORM:
                     bodies are a parameter: Bd, leaf, embS, embE (no body dflt is asked: trees_ind
                     takes it from the tree's own leaf 0); and what the library has by
                "fun s => rfl" IS A HYPOTHESIS NOW: hi: the page's reader of bodies spells every
                symbol's body as the format does:
                ∀ p a, leaf (embS (.inr p) a) = some (leafSL C S.plan.salt (rds S) ⟨p, a⟩).
                (rdOk_embTail' gives it for string bodies, under bounds on the trees: not checked
                here.) The bound on a check's depth goes through two folds (the tree in its round;
                the round in the list).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageIsAfter
import Run.PageIsAfter

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

theorem opL_top (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (run : ByteArray)
    (o : ChainOut) (q : OPos (uL C (rds S))) :
    opensAt (TYS S C dec).up run o (.inr q) = opL C (opensB o) run (rds S) q := rfl

theorem opL_tail (C : CK) (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray) (d : RD)
    (ds : List RD) (q : OPos (uL C ds)) :
    opL C tbl run (d :: ds) (.inr q) = opL C tbl run ds q := rfl

def Spec.pi_view : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
      (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool),
    ok S = true →
    ∀ (o : ChainOut) (run : ByteArray) (pl : Plains (uL C (rds S)))
        (ρ : Rho (uL C (rds S))) (ex : E0.Str),
      LaxFacts h S o → o.run = some run → plainsSL C (rds S) o.rounds.toList = some pl →
      drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn) →
      (PSof C (rds S) dec).accept () ex
          (trP (PSof C (rds S) dec).S (PSof C (rds S) dec).ann (wqS C K chal (rds S) dec).sh
            ((none, some []), rtSL C (rds S) o.rounds.toList) ((), pl) (default, ρ)
            (opensAt (TYS S C dec).up run o)) =
        (passSL C (rds S) ρ && dec (_root_.Fmt.viewOf S.firstTree o))

def Spec.pi_view_of : Prop := Spec.pi_want → Spec.pi_rowOf → Spec.pi_sent → Spec.pi_view

theorem pi_view_of : Spec.pi_view_of := by
  intro hw hr hs h S C K chal dec hok o run pl ρ ex hL hrun hpl hd
  have hsent : List.Forall₂ SentR (rds S) o.rounds.toList := hs h S o hok hL
  show (passSL C (rds S)
        (rhoSL C (rds S)
          (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList)
            pl ρ (opL C (opensB o) run (rds S)))) &&
      dec (viewSL C (rds S)
          (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList)
            pl ρ (opL C (opensB o) run (rds S))))) = _
  rw [rhoSL_tr]
  refine congrArg (fun v => passSL C (rds S) ρ && dec v) ?_
  show (⟨rvSL C (rds S)
        (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList) pl ρ (opL C (opensB o) run (rds S))),
      (wanted (rds S)
        (drawnSL C (rds S)
          (rhoSL C (rds S)
            (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList) pl ρ
              (opL C (opensB o) run (rds S)))))).filterMap fun nx =>
                (colAtS C (rds S)
                    (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList)
                      pl ρ (opL C (opensB o) run (rds S)))
                    nx.1 nx.2).map
                  fun c => (nx.1, nx.2, c)⟩ : View) =
    ⟨o.rounds.toList.map fun r => ⟨_root_.Fmt.noRoots r.vals, r.drawn⟩,
      o.rounds.toList.flatMap (_root_.Fmt.openedOf S.firstTree)⟩
  rw [rvSL_tr C K chal (rds S) o.rounds.toList pl ρ _ hpl hd, rhoSL_tr, hd, hw h S o hok hL]
  refine congrArg _ ?_
  refine filterMap_flatMap_of _ _ _ _ fun ro hro => ?_
  refine filterMap_flatMap_of _ _ _ _ fun x hx => ?_
  obtain ⟨n, ht, row⟩ := hr h S o hok hL ro hro x hx
  have hn : x.1.tree - S.firstTree = n := by rw [row.no]; omega
  have hob := trace_okb h S.plan _ _ _ _ hL.trace ro hro x hx
  rw [List.filterMap_map, hn]
  refine filterMap_zip_of _ (fun y c => (n, y, c)) x.2.1 x.2.2.cols
    (TieTree.ok_spec (obOf x) _ _ hob).1 fun y c hm => ?_
  show (colAtS C (rds S)
        (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList) pl ρ (opL C (opensB o) run (rds S)))
        n y).map
      (fun c => (n, y, c)) = some (n, y, c)
  rw [colAtS_tr C K chal (opensB o) run S.plan.salt (rds S) o.rounds.toList pl ρ n x.1 (obOf x)
      hsent ht row.look rfl hob y c hm]
  rfl

/-- THE DECISION'S PART, OUTRIGHT: the three statements on the book-keeping of trees are proved
(Run/PageIsTabProofs.lean). -/
theorem pi_view : Spec.pi_view := pi_view_of pi_want pi_rowOf pi_sent

namespace Spec

def pi_after : Prop :=
  ∀ (Bd : Type) (leaf : Bd → Option (Nat × Nat × ByteArray))
      (O : ByteArray → ByteArray), (∀ s, (O s).size = 32) →
    ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
        (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool),
      ok S = true →
      ∀ (embS : (p : OPos (Twin.up (SOf C (rds S)))) → OSym (Twin.up (SOf C (rds S))) p → Bd)
          (embE : E0.Sym → Bd),
        (∀ p a, leaf (embS (.inr p) a) = some (leafSL C S.plan.salt (rds S) ⟨p, a⟩)) →
      ∀ (o : ChainOut) (run : ByteArray) (pl : Plains (uL C (rds S)))
          (ρ : Rho (uL C (rds S))) (v : Bits),
        LaxFacts (_root_.Fmt.HO O) S o → o.run = some run →
        plainsSL C (rds S) o.rounds.toList = some pl →
        drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn) →
        strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec) (wqS C K chal (rds S) dec) 0 ()
            (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
            (default, ρ) ((none, some []), rtSL C (rds S) o.rounds.toList) (.loc v) = true ∧
        afterP (fun _ => LbS Bd C (rds S) dec) (famOf O (PDS Bd S C dec leaf) (K + 1))
            (PSof C (rds S) dec)
            (wqS C K chal (rds S) dec) embS
            embE 0 [bytesToDig o.pd] ()
            (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
            (default, ρ) ((none, some []), rtSL C (rds S) o.rounds.toList) (.loc v) =
          (rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList &&
            (passSL C (rds S) ρ && dec (_root_.Fmt.viewOf S.firstTree o)))

end Spec

section
variable (Bd : Type) (leaf : Bd → Option (Nat × Nat × ByteArray))
  (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)

/-- THE STRICT FORMAT HOLDS ON THE PARSER'S ARGUMENT STRING -/
theorem strict_top (hO : ∀ s, (O s).size = 32) (hok : ok S = true) (o : ChainOut) (run : ByteArray)
    (pl : Plains (uL C (rds S))) (ρ : Rho (uL C (rds S))) (v : Bits)
    (hf : LaxFacts (_root_.Fmt.HO O) S o) (hr : o.run = some run)
    (hd : drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn)) :
    strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec) (wqS C K chal (rds S) dec) 0 ()
        (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
        (default, ρ) ((none, some []), rtSL C (rds S) o.rounds.toList) (.loc v) = true := by
  have hrun := run_size O S hO o run hf hr
  unfold strictP
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show decide ((bytesToBits run).length = 256) = true
    rw [length_bytesToBits, hrun]
    rfl
  · show decide (((rootsB o).map bytesToDig).length ≤
          0 + 0 + cntP (SL C (rds S)) (rtSL C (rds S) o.rounds.toList)) = true
    rw [cntP_rt C (rds S) o.rounds.toList (pi_sent _ S o hok hf), List.length_map]
    exact decide_eq_true (Nat.le_of_eq (by simp only [Nat.zero_add]; rfl))
  · have := strict_ind C K chal (opensB o) run S.plan.salt hrun (rds S) o.rounds.toList _
      (rows_top (_root_.Fmt.HO O) S C dec o ρ
        (effsP (PSof C (rds S) dec).S (PSof C (rds S) dec).ann
          ((none, some []), rtSL C (rds S) o.rounds.toList) ((), pl))
        hok hf hd)
    show (sTreesP _ (s0 C) (fun _ _ => none) [] _ _ _ && sTreesP _ (s0 C)
        (fun _ _ => none) [] _ _ _ &&
        sSP (256 + 8 * S.plan.salt) (SL C (rds S)) (allLo (SL C (rds S))) (wiresSL C K chal (rds S))
          (rtSL C (rds S) o.rounds.toList) _ _) = true
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨rfl, rfl⟩, this⟩
  · rfl
  · rfl
  · rfl
  · rfl

/-- WHAT FOLLOWS THE CHAIN -/
theorem after_top (hO : ∀ s, (O s).size = 32) (hok : ok S = true)
    (embS : (p : OPos (Twin.up (SOf C (rds S)))) → OSym (Twin.up (SOf C (rds S))) p → Bd)
    (embE : E0.Sym → Bd)
    (hi : ∀ p a, leaf (embS (.inr p) a) = some (leafSL C S.plan.salt (rds S) ⟨p, a⟩))
    (o : ChainOut) (run : ByteArray)
    (pl : Plains (uL C (rds S))) (ρ : Rho (uL C (rds S))) (v : Bits)
    (hf : LaxFacts (_root_.Fmt.HO O) S o) (hr : o.run = some run)
    (hp : plainsSL C (rds S) o.rounds.toList = some pl)
    (hd : drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn)) :
    afterP (fun _ => LbS Bd C (rds S) dec) (famOf O (PDS Bd S C dec leaf) (K + 1))
        (PSof C (rds S) dec)
        (wqS C K chal (rds S) dec) embS
        embE 0 [bytesToDig o.pd] ()
        (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
        (default, ρ) ((none, some []), rtSL C (rds S) o.rounds.toList) (.loc v) =
      (rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList &&
        (passSL C (rds S) ρ && dec (_root_.Fmt.viewOf S.firstTree o))) := by
  have hrun := run_size O S hO o run hf hr
  obtain ⟨Fs, g1, g2, g3, g4⟩ :=
    forests_ind (L := LbS Bd C (rds S) dec) O (PDS Bd S C dec leaf) C K chal (opensB o) run
        S.plan.salt hO hrun
      (rds S) o.rounds.toList _ (fun p a => embS (.inr p) a)
      (rows_top (_root_.Fmt.HO O) S C dec o ρ
        (effsP (PSof C (rds S) dec).S (PSof C (rds S) dec).ann
          ((none, some []), rtSL C (rds S) o.rounds.toList) ((), pl))
        hok hf hd) hi
  have hFo : forestsOfP (fun _ => LbS Bd C (rds S) dec) (PSof C (rds S) dec)
      (wqS C K chal (rds S) dec)
        embS embE [bytesToDig o.pd] ()
        (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
        (default, ρ) ((none, some []), rtSL C (rds S) o.rounds.toList) =
      some (Fs ++ []) := by
    unfold forestsOfP
    dsimp only
    split
    · rename_i a b e1 e2
      have ea : a = Fs :=
        Option.some.inj (e1.symm.trans (forestsP_front C K chal (rds S) _ _ _ _ Fs g1))
      have eb : b = [] := Option.some.inj (e2.symm.trans rfl)
      rw [ea, eb]
    · rename_i hne
      exact (hne Fs [] (forestsP_front C K chal (rds S) _ _ _ _ Fs g1) rfl).elim
  unfold afterP
  rw [hFo]
  dsimp only
  rw [List.append_nil, if_pos ⟨by rw [g2]; exact cnt_le _ S o hok hf, List.all_eq_true.2 fun c hc => by
    obtain ⟨w, d, hdm, sh, hsh, hdd⟩ := g3 c hc
    rw [Bool.and_eq_true]
    exact ⟨w, decide_eq_true
        (by
          rw [hdd]
          exact le_trans (le_depthOf d.trees sh.a (List.mem_map_of_mem hsh))
            ((foldl_max_le (fun d : RD => depthOf d.trees) (rds S) 0).2 d hdm))⟩⟩]
  have h4 := g4 [] []
  rw [List.append_nil, List.append_nil] at h4
  rw [h4, tree_roots Bd leaf O S C dec o run hok hf]
  refine Eq.trans ?_
    (congrArg (fun b => rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList && b)
      (pi_view (_root_.Fmt.HO O) S C K chal dec hok o run pl ρ
        ((wqS C K chal (rds S) dec).ext.build fun _ => none) hf hr hp hd))
  show (rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList && true && true && _) = _
  rw [Bool.and_true, Bool.and_true]
  rfl

theorem pi_after : Spec.pi_after :=
  fun Bd leaf O hO S C K chal dec hok embS embE hi o run pl ρ v hf hr hp hd =>
  ⟨strict_top O S C K chal dec hO hok o run pl ρ v hf hr hd,
    after_top Bd leaf O S C K chal dec hO hok embS embE hi o run pl ρ v hf hr hp hd⟩

end

end TypedOracleCompiler.Run.PQ
