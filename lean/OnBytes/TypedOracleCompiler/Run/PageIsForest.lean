-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsForest.lean: THE VERIFIER's FORESTS AND THE STRICT FORMAT OF THE OPENINGS,
ROUND BY ROUND AND, IN A ROUND, TREE BY TREE, ON THE PARSER's ARGUMENT STRING. After the library's
Run/PageIsForest.lean. HERE IS PROOF WRITTEN, NOT TEXT SAID AGAIN: the library's two inductions case
on "this round has no tree | a tree with a record | a tree without"; here each has an INNER
INDUCTION over the round's trees.
  AS TEXT (but for bodies as a parameter, or a prefix)   walkOb, forest_tree (bodies),
                                                         runForests_cons, runForestP_nil
  LEFT TO THE LIBRARY   mem_of_lookup, at_some
  TURNED      RowsL, treeAll, cntO (each through its like on a round's trees), comp_unread (along
              posAt alone), forestsP_step, forests_ind, strict_ind
  NEW         RowsT, treeAllT, cntT (a round's trees, from tree k on); forestsTP_cons; trees_ind
              (the inner induction of forests_ind); RowsT_at,
              strict_tree (the inner step of strict_ind)

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageIsOp
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
import Run.PageIsForest

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (mem_of_lookup at_some)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (O : ByteArray → ByteArray) (D : PageD L .onl) (C : CK)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (tbl : List (ℕ × ℕ × OpenB))
  (run : ByteArray) (sb : ℕ)

/-- TWO: a round's trees from tree k on, each with its root: a root of 32 bytes; and its record in
the table, and "read" means "listed"; or no record in the table, and nothing is read -/
def RowsT (all : List _root_.Fmt.Shape) (isRead : PosT all → Bool) :
    ℕ → List _root_.Fmt.Shape → List ByteArray → Prop
  | _, [], [] => True
  | k, sh :: ts, root :: R =>
      root.size = 32 ∧
      ((∃ Ob,
          tbl.lookup sh.tree = some (sh.W, Ob) ∧
          Ob.a = sh.a ∧
          Ob.ok sb sh.W = true ∧
          Ob.idx ≠ [] ∧
          ∀ x p, posAtT all k x = some p → isRead p = decide (x ∈ Ob.idx)) ∨
        (tbl.lookup sh.tree = none ∧ ∀ x p, posAtT all k x = some p → isRead p = false)) ∧
      RowsT all isRead (k + 1) ts R
  | _, _, _ => False

/-- round by round: as many roots as trees, and tree by tree RowsT -/
def RowsL : (ds : List RD) → List RoundOut → (OPos (uL C ds) → Bool) → Prop
  | [], _, _ => True
  | _ :: _, [], _ => False
  | d :: ds, ro :: ros, isRead =>
      RowsT tbl sb d.trees (fun p => isRead (.inl p)) 0 d.trees (_root_.Fmt.rootsOf ro.vals) ∧
      RowsL ds ros (fun p => isRead (.inr p))

/-- the walk of one record of the table, on bytes -/
def walkOb (tree W : ℕ) (Ob : OpenB) : ByteArray :=
  (Octopus.octF (TieTree.vP O D) Ob.a Ob.idx
    (WalkTie.leafV (_root_.Fmt.HO O) ⟨Ob.a, W, false, tree⟩ run Ob.idx (Ob.cols.zip Ob.salts))
    Ob.given).headD default

/-- TWO: every tree of a round that has a record in the table walks to its root -/
def treeAllT : List _root_.Fmt.Shape → List ByteArray → Bool
  | sh :: ts, root :: R =>
      (match tbl.lookup sh.tree with
        | none => true
        | some x => decide (walkOb O D run sh.tree x.1 x.2 = root)) && treeAllT ts R
  | _, _ => true

/-- every tree that has a record in the table, in the order of sending, walks to its root -/
def treeAll : List RD → List RoundOut → Bool
  | d :: ds, ro :: ros => treeAllT O D tbl run d.trees (_root_.Fmt.rootsOf ro.vals) &&
      treeAll ds ros
  | _, _ => true

/-- TWO: the number of listed positions of a round's trees -/
def cntT : List _root_.Fmt.Shape → ℕ
  | [] => 0
  | sh :: ts => (match tbl.lookup sh.tree with
      | none => 0
      | some x => x.2.idx.length) + cntT ts

/-- the number of listed positions of all trees -/
def cntO : List RD → ℕ
  | [] => 0
  | d :: ds => cntT tbl d.trees + cntO ds

/-- one forest, walked on the digests read off its own paths -/
theorem forest_tree (hO : ∀ s, (O s).size = 32)
    (sy : ℕ → List UInt64 → L.Bd) (root : ByteArray)
    (hr : run.size = 32) (hroot : root.size = 32) (Ob : OpenB) (W tree : ℕ)
    (hok : Ob.ok sb W = true) (hne : Ob.idx ≠ [])
    (hleaf : ∀ x col, x < 2 ^ Ob.a → col.length = W →
      D.leaf (sy x col) =
        some (_root_.Fmt.leafPlace tree W (sb / 8),
          2 ^ Ob.a + x,
          _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen W sb))) :
    runForestP (fun _ => L) (famOf O D (K + 1))
        (⟨Ob.a, fun _ => bytesToDig root,
          (TieTree.checksOf sy run (bytesToDig root) Ob).map fun c => (0, c)⟩ : Forest 256 L)
        (readsOneP (fun _ => L)
          (⟨Ob.a, fun _ => bytesToDig root,
            (TieTree.checksOf sy run (bytesToDig root) Ob).map fun c => (0, c)⟩ : Forest 256 L)) =
      decide (walkOb O D run tree W Ob = root) := by
  have hlen : (readsOneP (fun _ => L)
        (⟨Ob.a, fun _ => bytesToDig root,
          (TieTree.checksOf sy run (bytesToDig root) Ob).map fun c =>
            (0, c)⟩ : Forest 256 L)).length =
      needP (fun _ => L)
        (⟨Ob.a, fun _ => bytesToDig root,
          (TieTree.checksOf sy run (bytesToDig root) Ob).map fun c => (0, c)⟩ : Forest 256 L) := by
    unfold readsOneP needP idxP
    rw [Octopus.length_reads]
    simp only [List.map_map]
    rfl
  unfold walkOb
  rw [← TieTree.forestV_checksOf O D (K + 1) hO sy run root hr hroot Ob sb W tree hok hne hleaf,
    ← TieTree.det_runForest, runForest_det]
  exact congrArg (runForestF (famOf O D (K + 1)) _)
    (List.take_of_length_le (Nat.le_of_eq hlen)).symm

theorem runForests_cons (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) (F : Forest 256 L)
    (Fs : List (Forest 256 L)) (s : List (Dig 256)) :
    runForestsP (fun _ => L) g (F :: Fs) (readsOneP (fun _ => L) F ++ s) =
      (runForestP (fun _ => L) g F (readsOneP (fun _ => L) F) &&
        runForestsP (fun _ => L) g Fs s) := by
  have hlen : (readsOneP (fun _ => L) F).length = needP (fun _ => L) F := by
    unfold readsOneP needP idxP
    rw [Octopus.length_reads]
    simp only [List.map_map]
    rfl
  show (runForestP (fun _ => L) g F ((readsOneP (fun _ => L) F ++ s).take (needP (fun _ => L) F)) &&
      runForestsP (fun _ => L) g Fs ((readsOneP (fun _ => L) F ++ s).drop (needP (fun _ => L) F))) =
    _
  rw [← hlen, List.take_left', List.drop_left']
  · rfl
  · rfl

/-- a forest without a check says yes -/
theorem runForestP_nil (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) (depth : ℕ)
    (rt : ℕ → Dig 256) (s : List (Dig 256)) :
    runForestP (fun _ => L) g (⟨depth, rt, []⟩ : Forest 256 L) s = true := by
  unfold runForestP
  show ((Octopus.upN depth []).zip _).all _ = true
  rw [_root_.Compile.Batch.upN_nil]
  rfl

/-- a tree of which no position is read calls for no check (TWO: asked along posAt alone) -/
theorem comp_unread (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig 256) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening 256 (r.Sym p)))
    (h : ∀ j p, posAt j = some p → isRead p = false) :
    ∀ js : List ℕ, compP (fun _ => L) r posAt depth emb rt isRead f js = some []
  | [] => rfl
  | j :: js => by
    have ih := comp_unread r posAt depth emb rt isRead f h js
    rw [compP]
    split
    · rename_i p hp
      rw [if_neg (by rw [h j p hp]; exact Bool.false_ne_true)]
      exact ih
    · exact ih

/-- TWO: whole trees: one forest a tree -/
theorem forestsTP_cons (z : ℕ × Dig 256 × List (Check 256 L))
    (l : List (ℕ × Dig 256 × List (Check 256 L))) :
    forestsTP (fun _ => L) true (z :: l) =
      (⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩ : Forest 256 L) ::
        forestsTP (fun _ => L) true l := rfl

/-- one step of forestsP on the road's rounds: no forest for the shared component; ONE forest FOR
EACH TREE of the round's own component, whatever its checks -/
theorem forestsP_step (d : RD) (ds : List RD) (rtJ : List (Dig 256)) (rts : RootsOfChain 256 (uL C ds))
    (isRead : OPos (uL C (d :: ds)) → Bool)
    (emb : (p : OPos (uL C (d :: ds))) → OSym (uL C (d :: ds)) p → L.Bd)
    (b : List (ℕ × Dig 256 × List (Check 256 L))) (c : List (Forest 256 L))
    (hb : treesP (fun _ => L) (roundS C d) (wireS C K chal d).posAtJ
        (fun p a => emb (.inl p) a) (fun p => isRead (.inl p))
        (fun p => opL C tbl run (d :: ds) (.inl p)) 0 (wireS C K chal d).depthJ rtJ = some b)
    (hc : forestsP (fun _ => L) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
        (fun p a => emb (.inr p) a) rts (fun p => isRead (.inr p))
        (fun p => opL C tbl run (d :: ds) (.inr p)) = some c) :
    forestsP (fun _ => L) (SL C (d :: ds)) (allLo (SL C (d :: ds)))
        (wiresSL C K chal (d :: ds)) emb
        ((none, some rtJ), rts) isRead (opL C tbl run (d :: ds)) =
      some (forestsTP (fun _ => L) true b ++ c) := by
  simp only [SL, wiresSL, forestsP]
  split
  · rename_i a b' c' e1 e2 e3
    have ea : a = [] := Option.some.inj (e1.symm.trans rfl)
    have eb : b' = b := Option.some.inj (e2.symm.trans hb)
    have ec : c' = c := Option.some.inj (e3.symm.trans hc)
    subst ea eb ec
    rfl
  · rename_i hne
    exact (hne [] b c rfl hb hc).elim

/-- TWO: THE FORESTS OF ONE ROUND, TREE BY TREE: the inner induction -/
theorem trees_ind (hO : ∀ s, (O s).size = 32) (hr : run.size = 32) (d : RD) (ds : List RD)
    (isRead : OPos (uL C (d :: ds)) → Bool)
    (emb : (p : PosT d.trees) → SymT d.trees p → L.Bd)
    (hi : ∀ p a, D.leaf (emb p a) = some (leafT sb d.trees p a)) :
    ∀ (k : ℕ) (ts : List _root_.Fmt.Shape) (R : List ByteArray),
      (∀ i, d.trees[k + i]? = ts[i]?) →
      RowsT tbl sb d.trees (fun p => isRead (.inl p)) k ts R →
      ∃ l,
        treesP (fun _ => L) (roundS C d) (wireS C K chal d).posAtJ emb (fun p => isRead (.inl p))
            (fun p => opL C tbl run (d :: ds) (.inl p)) k (ts.map (·.a)) (R.map bytesToDig) =
          some l ∧
        (flatP (fun _ => L) (forestsTP (fun _ => L) true l)).length = cntT tbl ts ∧
        (∀ c ∈ flatP (fun _ => L) (forestsTP (fun _ => L) true l),
          wellP (fun _ => L) c = true ∧ ∃ sh ∈ ts, c.depth = sh.a) ∧
        ∀ Fs' s', runForestsP (fun _ => L) (famOf O D (K + 1))
            (forestsTP (fun _ => L) true l ++ Fs')
            (readsP (fun _ => L) (forestsTP (fun _ => L) true l) ++ s') =
          (treeAllT O D tbl run ts R && runForestsP (fun _ => L) (famOf O D (K + 1)) Fs' s')
  | _, [], [], _, _ =>
    ⟨[], by simp only [List.map_nil, treesP], rfl, fun c hc => absurd hc (List.not_mem_nil),
      fun _ _ => rfl⟩
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim
  | k, sh :: ts, root :: R, hsuf, h => by
    obtain ⟨hroot, hcase, hrest⟩ := h
    have hk : d.trees[k]? = some sh := by simpa using hsuf 0
    -- the body that stands where a number is no leaf's: the tree's own leaf 0 with the fixed symbol
    -- (it shows in no conclusion)
    obtain ⟨p0, -, -⟩ := TypedOracleCompiler.Slice.posAtT_some d.trees k 0 sh hk
        (Nat.pos_of_ne_zero (by positivity))
    have dflt : L.Bd := emb p0 (zeroT d.trees p0)
    obtain ⟨l, t1, t2, t3, t4⟩ := trees_ind hO hr d ds isRead emb hi (k + 1) ts R
      (fun i => by
        have := hsuf (i + 1)
        rw [List.getElem?_cons_succ] at this
        rw [← this]
        congr 1
        omega) hrest
    rcases hcase with ⟨Ob, hl, ha, hok, hne, hread⟩ | ⟨hl, hread⟩
    · -- a tree with its record
      have hb := comp_tree (L := L) C K chal d ds k sh hk tbl run sb Ob hl ha hok emb dflt
        isRead hread (bytesToDig root)
      have hleaf : ∀ x col, x < 2 ^ Ob.a → col.length = sh.W →
          D.leaf (syOf d emb dflt k x col) =
            some (_root_.Fmt.leafPlace sh.tree sh.W (sb / 8),
              2 ^ Ob.a + x,
              _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen sh.W sb)) := by
        intro x col hx hc
        rw [ha] at hx
        obtain ⟨p, hp, -⟩ := TypedOracleCompiler.Slice.posAtT_some d.trees k x sh hk hx
        obtain ⟨y, hy, hly⟩ := leafT_at sb d.trees k x sh p col hk hp hc
        unfold syOf
        rw [hp]
        dsimp only
        rw [hy]
        dsimp only
        rw [hi, hly, ha]
      have hF := forest_tree O D K run sb hO (syOf d emb dflt k)
        root hr hroot Ob sh.W sh.tree hok hne hleaf
      rw [ha] at hF
      refine ⟨(sh.a, bytesToDig root,
          TieTree.checksOf (syOf d emb dflt k) run (bytesToDig root) Ob) :: l, ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, treesP, hb, t1]
      · obtain ⟨hc1, hs1, -, -, -⟩ := TieTree.ok_spec Ob sb sh.W hok
        have hpl : Ob.paths.length = Ob.idx.length := Octopus.length_fill _ _ _
        rw [forestsTP_cons]
        show ((((TieTree.checksOf (syOf d emb dflt k) run (bytesToDig root) Ob).map
                fun c => ((0 : ℕ), c)).map Prod.snd) ++
            flatP (fun _ => L) (forestsTP (fun _ => L) true l)).length = _
        simp only [cntT, hl, List.length_append, List.length_map, t2,
          TieTree.checksOf, List.length_zip]
        omega
      · intro c hc
        rw [forestsTP_cons] at hc
        have hc' : c ∈
            (((TieTree.checksOf (syOf d emb dflt k) run (bytesToDig root) Ob).map
                  fun c => ((0 : ℕ), c)).map Prod.snd) ++
              flatP (fun _ => L) (forestsTP (fun _ => L) true l) := hc
        rcases List.mem_append.1 hc' with hc1 | hc1
        · simp only [List.map_map, Function.comp_def, TieTree.checksOf, List.mem_map] at hc1
          obtain ⟨z, hz, rfl⟩ := hc1
          have hz1 : z.1 ∈ Ob.idx := (List.of_mem_zip hz).1
          have hz2 : z.2.2.2 ∈ Ob.paths :=
            (List.of_mem_zip (List.of_mem_zip (List.of_mem_zip hz).2).2).2
          refine ⟨?_, sh, List.mem_cons_self .., ha⟩
          unfold wellP
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨Octopus.length_of_mem_fill _ _ _ _ hz2, (TieTree.ok_list Ob sb sh.W hok).2.1 _ hz1⟩
        · obtain ⟨w, s', hs', hdd⟩ := t3 c hc1
          exact ⟨w, s', List.mem_cons_of_mem _ hs', hdd⟩
      · intro Fs' s'
        rw [forestsTP_cons]
        show runForestsP (fun _ => L) (famOf O D (K + 1))
            (_ :: (forestsTP (fun _ => L) true l ++ Fs'))
            (readsOneP (fun _ => L) _ ++ readsP (fun _ => L)
                (forestsTP (fun _ => L) true l) ++ s') = _
        rw [List.append_assoc, runForests_cons, t4, hF]
        simp only [treeAllT, hl, Bool.and_assoc]
    · -- a tree of which nothing is read
      have hb := comp_unread (L := L) (roundS C d) ((wireS C K chal d).posAtJ k) sh.a emb
        (bytesToDig root) (fun p => isRead (.inl p))
        (fun p => opL C tbl run (d :: ds) (.inl p)) hread (List.range (2 ^ sh.a))
      refine ⟨(sh.a, bytesToDig root, []) :: l, ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, treesP, hb, t1]
      · rw [forestsTP_cons]
        show (([] : List (Check 256 L)) ++
            flatP (fun _ => L) (forestsTP (fun _ => L) true l)).length = _
        simp only [cntT, hl, List.nil_append, t2, Nat.zero_add]
      · intro c hc
        rw [forestsTP_cons] at hc
        obtain ⟨w, s', hs', hdd⟩ := t3 c hc
        exact ⟨w, s', List.mem_cons_of_mem _ hs', hdd⟩
      · intro Fs' s'
        rw [forestsTP_cons]
        show runForestsP (fun _ => L) (famOf O D (K + 1))
            ((⟨sh.a, fun _ => bytesToDig root, []⟩ : Forest 256 L) ::
              (forestsTP (fun _ => L) true l ++ Fs'))
            (readsOneP (fun _ => L) (⟨sh.a, fun _ => bytesToDig root, []⟩ : Forest 256 L) ++
              readsP (fun _ => L) (forestsTP (fun _ => L) true l) ++ s') = _
        rw [List.append_assoc, runForests_cons, t4, runForestP_nil]
        simp only [treeAllT, hl, Bool.true_and]

theorem flatP_app (Fs Gs : List (Forest 256 L)) :
    flatP (fun _ => L) (Fs ++ Gs) = flatP (fun _ => L) Fs ++ flatP (fun _ => L) Gs :=
  List.flatMap_append

theorem readsP_app (Fs Gs : List (Forest 256 L)) :
    readsP (fun _ => L) (Fs ++ Gs) = readsP (fun _ => L) Fs ++ readsP (fun _ => L) Gs :=
  List.flatMap_append

/-- THE FORESTS, ROUND BY ROUND -/
theorem forests_ind (hO : ∀ s, (O s).size = 32) (hr : run.size = 32) :
    ∀ (ds : List RD) (ros : List RoundOut) (isRead : OPos (uL C ds) → Bool)
        (emb : (p : OPos (uL C ds)) → OSym (uL C ds) p → L.Bd),
      RowsL C tbl sb ds ros isRead → (∀ p a, D.leaf (emb p a) = some (leafSL C sb ds ⟨p, a⟩)) →
      ∃ Fs,
        forestsP (fun _ => L) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
            emb (rtSL C ds ros) isRead (opL C tbl run ds) =
          some Fs ∧
        (flatP (fun _ => L) Fs).length = cntO tbl ds ∧
        (∀ c ∈ flatP (fun _ => L) Fs,
          wellP (fun _ => L) c = true ∧ ∃ d ∈ ds, ∃ sh ∈ d.trees, c.depth = sh.a) ∧
        ∀ Fs' s', runForestsP (fun _ => L) (famOf O D (K + 1))
            (Fs ++ Fs') (readsP (fun _ => L) Fs ++ s') =
          (treeAll O D tbl run ds ros && runForestsP (fun _ => L) (famOf O D (K + 1)) Fs' s')
  | [], _, _, _, _, _ => ⟨[], rfl, rfl, fun c hc => absurd hc (List.not_mem_nil), fun _ _ => rfl⟩
  | _ :: _, [], _, _, h, _ => h.elim
  | d :: ds, ro :: ros, isRead, emb, h, hi => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨Fs, f1, f2, f3, f4⟩ :=
      forests_ind hO hr ds ros (fun p => isRead (.inr p)) (fun p a => emb (.inr p) a)
        h2 (fun p a => hi (.inr p) a)
    obtain ⟨l, t1, t2, t3, t4⟩ := trees_ind O D C K chal tbl run sb hO hr d ds isRead
      (fun p a => emb (.inl p) a) (fun p a => hi (.inl p) a) 0 d.trees
      (_root_.Fmt.rootsOf ro.vals) (fun i => by rw [Nat.zero_add]) h1
    refine ⟨forestsTP (fun _ => L) true l ++ Fs, ?_, ?_, ?_, ?_⟩
    · exact forestsP_step (L := L) C K chal tbl run d ds _ (rtSL C ds ros) isRead emb l Fs t1 f1
    · rw [flatP_app, List.length_append, t2, f2]
      rfl
    · intro c hc
      rw [flatP_app] at hc
      rcases List.mem_append.1 hc with hc1 | hc1
      · obtain ⟨w, sh, hs, hdd⟩ := t3 c hc1
        exact ⟨w, d, List.mem_cons_self .., sh, hs, hdd⟩
      · obtain ⟨w, d', hd, sh, hs, hdd⟩ := f3 c hc1
        exact ⟨w, d', List.mem_cons_of_mem _ hd, sh, hs, hdd⟩
    · intro Fs' s'
      rw [readsP_app, List.append_assoc, List.append_assoc, t4, f4]
      simp only [treeAll, Bool.and_assoc]

/-! ### The strict format -/

/-- TWO: the row of the i-th tree from k on -/
theorem RowsT_at (all : List _root_.Fmt.Shape) (isRead : PosT all → Bool) :
    ∀ (k : ℕ) (ts : List _root_.Fmt.Shape) (R : List ByteArray), RowsT tbl sb all isRead k ts R →
      ∀ i sh, ts[i]? = some sh →
        (R[i]?).isSome = true ∧
        ((∃ Ob,
            tbl.lookup sh.tree = some (sh.W, Ob) ∧ Ob.ok sb sh.W = true ∧
            ∀ x p, posAtT all (k + i) x = some p → isRead p = decide (x ∈ Ob.idx)) ∨
          tbl.lookup sh.tree = none)
  | _, [], [], _, _, _, h => by simp at h
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
  | k, s :: ts, root :: R, h, 0, sh, hs => by
      obtain rfl : s = sh := by simpa using hs
      obtain ⟨-, hcase, -⟩ := h
      refine ⟨rfl, ?_⟩
      rcases hcase with ⟨Ob, hl, -, hok, -, hread⟩ | ⟨hl, -⟩
      · exact Or.inl ⟨Ob, hl, hok, hread⟩
      · exact Or.inr hl
  | k, _ :: ts, _ :: R, h, i + 1, sh, hs => by
      have := RowsT_at all isRead (k + 1) ts R h.2.2 i sh (by simpa using hs)
      rw [show k + 1 + i = k + (i + 1) by omega] at this
      simpa using this

/-- TWO: the strict format of the openings of ONE tree of a round -/
theorem strict_tree (hr : run.size = 32) (d : RD) (ds : List RD)
    (isRead : OPos (uL C (d :: ds)) → Bool) (k : ℕ) (sh : _root_.Fmt.Shape)
    (hk : d.trees[k]? = some sh)
    (hrow : (∃ Ob,
        tbl.lookup sh.tree = some (sh.W, Ob) ∧ Ob.ok sb sh.W = true ∧
        ∀ x p, posAtT d.trees k x = some p → isRead (.inl p) = decide (x ∈ Ob.idx)) ∨
      tbl.lookup sh.tree = none) (depth : ℕ) :
    sCompP (256 + 8 * sb) (roundS C d) ((wireS C K chal d).posAtJ k) depth true
      (fun p => isRead (.inl p)) (fun p => opL C tbl run (d :: ds) (.inl p)) = true := by
  unfold sCompP
  rw [List.all_eq_true]
  intro j _
  cases hp : (wireS C K chal d).posAtJ k j with
  | none => rfl
  | some p =>
    have hp' : posAtT d.trees k j = some p := hp
    dsimp only
    have hno := noT_at d.trees k j sh p hk hp'
    rcases hrow with ⟨Ob, hl, hok, hread⟩ | hl
    · have ho : opL C tbl run (d :: ds) (.inl p) = Ob.at (symT d.trees p) run j := by
        unfold opL
        show (match tbl.lookup (noT d.trees p).1 with
          | none => none
          | some x => x.2.at (symT d.trees p) run (noT d.trees p).2) = _
        rw [hno, hl]
      rw [ho]
      cases hat : Ob.at (symT d.trees p) run j with
      | none => rfl
      | some op =>
        obtain ⟨hm, s, hs, hsalt⟩ := at_some run _ Ob j op hat
        dsimp only
        have hrd : isRead (.inl p) = true := (hread j p hp').trans (decide_eq_true hm)
        have hsl : op.salt.length = 256 + 8 * sb := by
          rw [hsalt]
          simp only [leafSalt, List.length_append, length_bytesToBits, hr,
            (TieTree.ok_spec Ob sb sh.W hok).2.2.1 s hs]
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨rfl, hrd⟩, decide_eq_true hsl⟩
    · have ho : opL C tbl run (d :: ds) (.inl p) = none := by
        unfold opL
        show (match tbl.lookup (noT d.trees p).1 with
          | none => none
          | some x => x.2.at (symT d.trees p) run (noT d.trees p).2) = _
        rw [hno]
        show (match tbl.lookup sh.tree with
          | none => none
          | some x => x.2.at (symT d.trees p) run j) = _
        rw [hl]
        rfl
      rw [ho]

/-- THE STRICT FORMAT OF THE OPENINGS, ROUND BY ROUND -/
theorem strict_ind (hr : run.size = 32) :
    ∀ (ds : List RD) (ros : List RoundOut) (isRead : OPos (uL C ds) → Bool),
      RowsL C tbl sb ds ros isRead →
      sSP (256 + 8 * sb) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds) (rtSL C ds ros)
          isRead (opL C tbl run ds) = true
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => h.elim
  | d :: ds, ro :: ros, isRead, h => by
    obtain ⟨h1, h2⟩ := h
    have ih := strict_ind hr ds ros (fun p => isRead (.inr p)) h2
    show (sTreesP (256 + 8 * sb) (roundS C d) (fun _ _ => none) [] _
          (fun p => isRead (.inl p)) (fun p => opL C tbl run (d :: ds) (.inl p)) &&
        sTreesP (256 + 8 * sb) (roundS C d) (wireS C K chal d).posAtJ (d.trees.map (·.a))
          ((_root_.Fmt.rootsOf ro.vals).map bytesToDig) (fun p => isRead (.inl p))
          (fun p => opL C tbl run (d :: ds) (.inl p)) &&
        sSP (256 + 8 * sb) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds) (rtSL C ds ros)
          (fun p => isRead (.inr p)) (opL C tbl run ds)) = true
    rw [ih, Bool.and_true, Bool.and_eq_true]
    refine ⟨rfl, ?_⟩
    unfold sTreesP
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range, List.length_map] at hk
    obtain ⟨hroot, hrow⟩ := RowsT_at tbl sb d.trees (fun p => isRead (.inl p)) 0 d.trees
      (_root_.Fmt.rootsOf ro.vals) h1 k d.trees[k] (List.getElem?_eq_getElem hk)
    rw [Nat.zero_add] at hrow
    have hsome : (((_root_.Fmt.rootsOf ro.vals).map bytesToDig)[k]?).isSome = true := by
      rw [List.getElem?_map, Option.isSome_map]
      exact hroot
    rw [hsome]
    exact strict_tree C K chal tbl run sb hr d ds isRead k d.trees[k]
      (List.getElem?_eq_getElem hk) hrow _

end

end TypedOracleCompiler.Run.PQ
