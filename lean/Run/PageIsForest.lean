-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsForest.lean: tools for Run/PageIs.lean: the verifier's forests and the strict format of
the openings, round by round, on the parser's argument string.

Definitions, lemmas with their proofs; no Spec. Run/PageIsAfter.lean applies `forests_ind` and
`strict_ind` in its proof of `Spec.pi_after` (Run/PageIs.lean).
A forest (`Forest`, Compile/Batch/Verifier.lean) holds the checks of Merkle openings in trees of one
depth. The compiled verifier, here in its evaluable form (Run/ThinDefs.lean), forms the forests of
an argument string (`forestsP`) and walks each from the opened leaves to the roots of its trees,
over a pruned set of sibling digests (`runForestsP`). The strict format of the openings (`sSP`, one
clause of `strictP`) is its test on the string's openings.
This file works out both by induction on a list ds of rounds of the generic construction (`SL`,
`wiresSL`, Run/PlanQS.lean). The openings are looked up in a table tbl of records (`opL`,
Run/PageIsOp.lean; a record is an `OpenB`, Run/ParseBS.lean). The roots are taken from a list ros of
rounds as read (`rtSL`, Run/PageIs.lean; `RoundOut`, Fmt/Rules8.lean).
Generic in the ambient interface L, its spellings D (`PageD`, Run/CodingFn.lean: what the format
hashes for a typed query), the oracle O, the choice of challenge types C (`CK`,
Run/PlanQTypes.lean), the table of openings.

Main names:
  `RowsL C tbl sb ds ros isRead`: the hypothesis, round by round. Each round of ds has its round in
    ros. A round has no tree and its items hold no root; or it has a tree of shape sh, its items
    hold one root of 32 bytes, the table finds (sh.W, Ob) under sh.tree, Ob.a = sh.a, Ob passes the
    parser's test (`OpenB.ok`), its list is not empty, and a position of the round is read exactly
    if its number is listed in Ob; or it has a tree of shape sh, its items hold one root of 32
    bytes, the table has no record under sh.tree, and no position of the round is read.
  `treeAll`: "every tree that has a record in the table, in the order of sending, walks to its
    root". Trees without a record, and rounds of ds beyond the end of ros, are not tested.
  `forests_ind`: the main statement on the forests. Suppose `RowsL` and "D spells inj's symbols as
    `leafSL` does", and suppose that the answers of O and the run's value `run` have 32 bytes. Then
    `forestsP` = some Fs; Fs holds `cntO` checks; and each is well formed, of the depth of a round's
    tree. And then walking Fs on the digests read off its own paths comes to `treeAll`: runForestsP
    g (Fs ++ Fs') (readsP Fs ++ s') = treeAll && runForestsP g Fs' s', for all Fs' and s', at the
    typed oracle functions g that O induces (`famOf`, Run/CodingFn.lean).
  `at_some`: an opening of a record stands only at a listed position; its typed salt is the run's
    value and a salt of the record.
  `strict_ind`: the main statement on the strict format of the openings. `RowsL`, the run's value of
    32 bytes ⇒ sSP (256 + 8 sb) .. = true: an opening stands only under a root, only where the
    verifier reads, with a salt of the right length.

Notation:
  `K`: the number of blocks from which a verifier message is made;
  `chal`: the samplers, from `K` 256-bit blocks to a verifier message;
  `sb`: a number; in `Ob.ok sb ..` (Run/ParseBS.lean), the bytes of one salt;
  `256 + 8 sb`: the length of the salt of a leaf (`sMT`, Compile/Batch/Verifier.lean).

Limits: both main statements have the hypothesis `RowsL`. This file does not say that `RowsL` holds
of what the lenient reader hands out (from Run/PageIsTab.lean's statements: elsewhere). It does not
say that `treeAll` is `rootsAll` of Run/PageIs.lean (the proof file's order). It says nothing on
soundness.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.PageIsOp
import Run.VerifyDetProofs
import Hash.OctopusFacts
import Run.CodingBitsLaws
import Compile.Batch.PrunedNil

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

section
variable {I X : Type} {L : BatchProtocol I X} (O : ByteArray → ByteArray) (D : PageD L .onl) (C : CK)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (tbl : List (ℕ × ℕ × OpenB))
  (run : ByteArray) (sb : ℕ)

/-- The hypothesis of `forests_ind` and `strict_ind`, round by round. The head tells each clause. -/
def RowsL : (ds : List RD) → List RoundOut → (OPos (uL C ds) → Bool) → Prop
  | [], _, _ => True
  | _ :: _, [], _ => False
  | d :: ds, ro :: ros, isRead =>
      ((d.tree = none ∧ _root_.Fmt.rootsOf ro.vals = []) ∨
        (∃ sh Ob root,
          d.tree = some sh ∧
          _root_.Fmt.rootsOf ro.vals = [root] ∧
          root.size = 32 ∧
          tbl.lookup sh.tree = some (sh.W, Ob) ∧
          Ob.a = sh.a ∧
          Ob.ok sb sh.W = true ∧
          Ob.idx ≠ [] ∧
          ∀ x : Fin (posN d.tree), isRead (.inl x) = decide (x.val ∈ Ob.idx)) ∨
        ∃ sh root,
          d.tree = some sh ∧
          _root_.Fmt.rootsOf ro.vals = [root] ∧
          root.size = 32 ∧
          tbl.lookup sh.tree = none ∧
          ∀ x : Fin (posN d.tree), isRead (.inl x) = false) ∧
      RowsL ds ros (fun p => isRead (.inr p))

/-- The walk of one record of the table, on bytes: the first digest that it leaves after the last
level, or the default value if it leaves none. -/
def walkOb (tree W : ℕ) (Ob : OpenB) : ByteArray :=
  (Octopus.octF (TieTree.vP O D) Ob.a Ob.idx
    (WalkTie.leafV (_root_.Fmt.HO O) ⟨Ob.a, W, false, tree⟩ run Ob.idx (Ob.cols.zip Ob.salts))
    Ob.given).headD default

/-- Every tree that has a record in the table, in the order of sending, walks to its root. Trees
without a record, and rounds of ds beyond the end of ros, are not tested. -/
def treeAll : List RD → List RoundOut → Bool
  | d :: ds, ro :: ros =>
      (match d.tree with
        | none => true
        | some sh => match tbl.lookup sh.tree with
          | none => true
          | some x => decide (walkOb O D run sh.tree x.1 x.2 = (_root_.Fmt.rootsOf ro.vals).headD default)) && treeAll ds ros
  | _, _ => true

/-- The number of listed positions of all trees. -/
def cntO : List RD → ℕ
  | [] => 0
  | d :: ds => (match d.tree with
      | none => 0
      | some sh => match tbl.lookup sh.tree with
        | none => 0
        | some x => x.2.idx.length) + cntO ds

/-- Under the hypotheses below, the forest of the checks that the record Ob calls for
(`TieTree.checksOf`), walked on the digests read off its own paths, says yes exactly if `walkOb`
ends in root. -/
theorem forest_tree (hO : ∀ s, (O s).size = 32)
    (sy : ℕ → List UInt64 → SymAny (Compile.Batch.shapeOf L .onl)) (root : ByteArray)
    (hr : run.size = 32) (hroot : root.size = 32) (Ob : OpenB) (W tree : ℕ)
    (hok : Ob.ok sb W = true) (hne : Ob.idx ≠ [])
    (hleaf : ∀ x col, x < 2 ^ Ob.a → col.length = W →
      D.leaf (sy x col) =
        (_root_.Fmt.leafPlace tree W (sb / 8),
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


theorem runForests_cons (g : Fam (Batch.spec 256 (K + 1) L)) (F : Forest 256 L)
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

/-- A forest without a check says yes. -/
theorem runForestP_nil (g : Fam (Batch.spec 256 (K + 1) L)) (depth : ℕ)
    (rt : ℕ → Dig 256) (s : List (Dig 256)) :
    runForestP (fun _ => L) g (⟨depth, rt, []⟩ : Forest 256 L) s = true := by
  unfold runForestP
  show ((Octopus.upN depth []).zip _).all _ = true
  rw [upN_nil]
  rfl

/-- A component of which no position is read calls for no check. -/
theorem comp_unread (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig 256) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening 256 (r.Sym p))) (h : ∀ p, isRead p = false) :
    ∀ js : List ℕ, compP (fun _ => L) r posAt depth emb rt isRead f js = some []
  | [] => rfl
  | j :: js => by
    have ih := comp_unread r posAt depth emb rt isRead f h js
    rw [compP]
    split
    · rename_i p _
      rw [if_neg (by rw [h p]; exact Bool.false_ne_true)]
      exact ih
    · exact ih

/-- One step of `forestsP` on the rounds of the generic construction (`roundS`, `wireS`,
Run/PlanQS.lean), where the shared component is not sent: if the round's own component gives the
checks b (`hb`) and the remaining rounds give the forests c (`hc`), the result is one forest with
the checks b, then c. So: no forest for the shared component; one forest for the round's own
component, whatever its checks (an empty one where the round has no tree, or a tree of which no
position is read). -/
theorem forestsP_step (d : RD) (ds : List RD) (rtJ : Option (Dig 256)) (rts : RootsOfChain 256 (uL C ds))
    (isRead : OPos (uL C (d :: ds)) → Bool)
    (inj : SymAny (uL C (d :: ds)) → SymAny (Compile.Batch.shapeOf L .onl))
    (b : List (Check 256 L)) (c : List (Forest 256 L))
    (hb : optP (fun _ => L) (roundS C d) (wireS C K chal d).posAtJ (wireS C K chal d).depthJ
        (fun p a => some (.inr ⟨.onl, inj ⟨.inl p, a⟩⟩)) (some rtJ).join (fun p => isRead (.inl p))
        (fun p => opL C tbl run (d :: ds) (.inl p)) = some b)
    (hc : forestsP (fun _ => L) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
        (fun p a => some (.inr ⟨.onl, inj ⟨.inr p, a⟩⟩)) rts (fun p => isRead (.inr p))
        (fun p => opL C tbl run (d :: ds) (.inr p)) = some c) :
    forestsP (fun _ => L) (SL C (d :: ds)) (allLo (SL C (d :: ds)))
        (wiresSL C K chal (d :: ds)) (fun p a => some (.inr ⟨.onl, inj ⟨p, a⟩⟩))
        ((none, some rtJ), rts) isRead (opL C tbl run (d :: ds)) =
      some ((⟨depthOf d.tree, fun _ => rtJ.getD default, b.map fun c => (0, c)⟩ : Forest 256 L) ::
          c) := by
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

/-- The forests, round by round. The head tells the statement in words, under `forests_ind`. -/
theorem forests_ind (hO : ∀ s, (O s).size = 32) (hr : run.size = 32) :
    ∀ (ds : List RD) (ros : List RoundOut) (isRead : OPos (uL C ds) → Bool)
        (inj : SymAny (uL C ds) → SymAny (Compile.Batch.shapeOf L .onl)),
      RowsL C tbl sb ds ros isRead → (∀ s, D.leaf (inj s) = leafSL C sb ds s) →
      ∃ Fs,
        forestsP (fun _ => L) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
            (fun p a => some (.inr ⟨.onl, inj ⟨p, a⟩⟩)) (rtSL C ds ros) isRead (opL C tbl run ds) =
          some Fs ∧
        (flatP (fun _ => L) Fs).length = cntO tbl ds ∧
        (∀ c ∈ flatP (fun _ => L) Fs,
          wellP (fun _ => L) c = true ∧ ∃ d ∈ ds, c.depth = depthOf d.tree) ∧
        ∀ Fs' s', runForestsP (fun _ => L) (famOf O D (K + 1))
            (Fs ++ Fs') (readsP (fun _ => L) Fs ++ s') =
          (treeAll O D tbl run ds ros && runForestsP (fun _ => L) (famOf O D (K + 1)) Fs' s')
  | [], _, _, _, _, _ => ⟨[], rfl, rfl, fun c hc => absurd hc (List.not_mem_nil), fun _ _ => rfl⟩
  | _ :: _, [], _, _, h, _ => h.elim
  | ⟨e, k, items, tree, opens⟩ :: ds, ro :: ros, isRead, inj, h, hi => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨Fs, f1, f2, f3, f4⟩ :=
      forests_ind hO hr ds ros (fun p => isRead (.inr p)) (fun s => inj ⟨.inr s.1, s.2⟩)
        h2 (fun s => hi ⟨.inr s.1, s.2⟩)
    rcases h1 with ⟨ht, hv⟩ | ⟨sh, Ob, root, ht, hv, hroot, hl, ha, hok, hne, hread⟩ | ⟨sh,
      root, ht, hv, -, hl, hread⟩
    · -- no tree
      dsimp only at ht
      subst ht
      refine ⟨(⟨0, fun _ => default, []⟩ : Forest 256 L) :: Fs, ?_, ?_, ?_, ?_⟩
      · have := forestsP_step (L := L) C K chal tbl run ⟨e, k, items, none, opens⟩ ds none
          (rtSL C ds ros) isRead inj [] Fs rfl f1
        simp only [rtSL, hv]
        exact this
      · show (([] : List (Check 256 L)) ++ flatP (fun _ => L) Fs).length = 0 + cntO tbl ds
        rw [List.nil_append, f2, Nat.zero_add]
      · intro c hc
        obtain ⟨w, d, hd, hdd⟩ := f3 c hc
        exact ⟨w, d, List.mem_cons_of_mem _ hd, hdd⟩
      · intro Fs' s'
        show runForestsP (fun _ => L) (famOf O D (K + 1))
            ((⟨0, fun _ => default, []⟩ : Forest 256 L) :: (Fs ++ Fs'))
            (readsOneP (fun _ => L) (⟨0, fun _ => default, []⟩ : Forest 256 L) ++
              (readsP (fun _ => L) Fs ++ s')) = _
        rw [runForests_cons, f4]
        rfl
    · -- a tree
      dsimp only at ht
      subst ht
      have hb := comp_tree (L := L) C K chal e k items sh opens ds tbl run sb Ob hl ha hok inj
        isRead hread (bytesToDig root)
      have hleaf : ∀ x col, x < 2 ^ Ob.a → col.length = sh.W →
          D.leaf (syOf C e k items sh opens ds inj x col) =
            (_root_.Fmt.leafPlace sh.tree sh.W (sb / 8),
              2 ^ Ob.a + x,
              _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen sh.W sb)) := by
        intro x col hx hc
        rw [ha] at hx
        unfold syOf
        rw [dif_pos hx, hi, ha]
        show (_root_.Fmt.leafPlace sh.tree sh.W (sb / 8),
            2 ^ sh.a + x,
            _root_.Fmt.colBytes (List.ofFn (colFn sh.W col)) ++ _) = _
        rw [ofFn_colFn sh.W col hc]
        rfl
      have hF := forest_tree O D K run sb hO (syOf C e k items sh opens ds inj)
        root hr hroot Ob sh.W sh.tree hok hne hleaf
      rw [ha] at hF
      refine ⟨(⟨sh.a,
            fun _ => bytesToDig root,
            (TieTree.checksOf (syOf C e k items sh opens ds inj) run (bytesToDig root) Ob).map
              fun c => (0, c)⟩ : Forest 256 L) :: Fs,
        ?_, ?_, ?_, ?_⟩
      · have := forestsP_step (L := L) C K chal tbl run ⟨e, k, items, some sh, opens⟩ ds
          (some (bytesToDig root)) (rtSL C ds ros) isRead inj _ Fs hb f1
        simp only [rtSL, hv]
        exact this
      · obtain ⟨hc1, hs1, -, -, -⟩ := TieTree.ok_spec Ob sb sh.W hok
        have hpl : Ob.paths.length = Ob.idx.length := Octopus.length_fill _ _ _
        show ((((TieTree.checksOf (syOf C e k items sh opens ds inj) run (bytesToDig root) Ob).map
                fun c => ((0 : ℕ), c)).map Prod.snd) ++
            flatP (fun _ => L) Fs).length = _
        simp only [cntO, hl, List.length_append, List.length_map, f2,
          TieTree.checksOf, List.length_zip]
        omega
      · intro c hc
        have hc' : c ∈
            (((TieTree.checksOf (syOf C e k items sh opens ds inj) run (bytesToDig root) Ob).map
                  fun c => ((0 : ℕ), c)).map Prod.snd) ++
              flatP (fun _ => L) Fs := hc
        rcases List.mem_append.1 hc' with hc1 | hc1
        · simp only [List.map_map, Function.comp_def, TieTree.checksOf, List.mem_map] at hc1
          obtain ⟨z, hz, rfl⟩ := hc1
          have hz1 : z.1 ∈ Ob.idx := (List.of_mem_zip hz).1
          have hz2 : z.2.2.2 ∈ Ob.paths :=
            (List.of_mem_zip (List.of_mem_zip (List.of_mem_zip hz).2).2).2
          refine ⟨?_, ⟨e, k, items, some sh, opens⟩, List.mem_cons_self .., ha⟩
          unfold wellP
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨Octopus.length_of_mem_fill _ _ _ _ hz2, (TieTree.ok_list Ob sb sh.W hok).2.1 _ hz1⟩
        · obtain ⟨w, d, hd, hdd⟩ := f3 c hc1
          exact ⟨w, d, List.mem_cons_of_mem _ hd, hdd⟩
      · intro Fs' s'
        show runForestsP (fun _ => L) (famOf O D (K + 1)) (_ :: (Fs ++ Fs'))
            (readsOneP (fun _ => L) _ ++ readsP (fun _ => L) Fs ++ s') = _
        rw [List.append_assoc, runForests_cons, f4, hF]
        simp only [treeAll, hl, hv, List.headD_cons, Bool.and_assoc]
    · -- a tree of which nothing is read
      dsimp only at ht
      subst ht
      have hb := comp_unread (L := L) (roundS C ⟨e, k, items, some sh, opens⟩)
        (wireS C K chal ⟨e, k, items, some sh, opens⟩).posAtJ
        (wireS C K chal ⟨e, k, items, some sh, opens⟩).depthJ
        (fun p a => some (.inr ⟨.onl, inj ⟨.inl p, a⟩⟩)) (bytesToDig root)
        (fun p => isRead (.inl p))
        (fun p => opL C tbl run (⟨e, k, items, some sh, opens⟩ :: ds) (.inl p)) hread
        (List.range (2 ^ (wireS C K chal ⟨e, k, items, some sh, opens⟩).depthJ))
      refine ⟨(⟨sh.a, fun _ => bytesToDig root, []⟩ : Forest 256 L) :: Fs, ?_, ?_, ?_, ?_⟩
      · have := forestsP_step (L := L) C K chal tbl run ⟨e, k, items, some sh, opens⟩ ds
          (some (bytesToDig root)) (rtSL C ds ros) isRead inj _ Fs hb f1
        simp only [rtSL, hv]
        exact this
      · show (([] : List (Check 256 L)) ++ flatP (fun _ => L) Fs).length = _
        simp only [cntO, hl, List.nil_append, f2, Nat.zero_add]
      · intro c hc
        obtain ⟨w, d, hd, hdd⟩ := f3 c hc
        exact ⟨w, d, List.mem_cons_of_mem _ hd, hdd⟩
      · intro Fs' s'
        show runForestsP (fun _ => L) (famOf O D (K + 1)) (_ :: (Fs ++ Fs'))
            (readsOneP (fun _ => L) _ ++ readsP (fun _ => L) Fs ++ s') = _
        rw [List.append_assoc, runForests_cons, f4, runForestP_nil]
        simp only [treeAll, hl, Bool.true_and]


/-! ### The strict format -/

theorem mem_of_lookup {β : Type} :
    ∀ (es : List (ℕ × β)) (x : ℕ) (v : β), es.lookup x = some v → (x, v) ∈ es
  | [], _, _, h => by cases h
  | (k, w) :: es, x, v, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i hk
      cases h
      rw [beq_iff_eq.1 hk]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookup es x v h)

/-- An opening stands only at a listed position, and its typed salt is the run's value and a salt of
the record (`leafSalt run s`, Run/ParseBS.lean). -/
theorem at_some {σ : Type} (sym : List UInt64 → Option σ) (Ob : OpenB) (x : ℕ)
    (op : Opening 256 σ) (h : Ob.at sym run x = some op) :
    x ∈ Ob.idx ∧ ∃ s ∈ Ob.salts, op.salt = leafSalt run s := by
  unfold OpenB.at OpenB.atP at h
  split at h
  · cases h
  · rename_i c s p hl
    have hm := mem_of_lookup _ _ _ hl
    obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h
    subst hy
    exact ⟨(List.of_mem_zip hm).1, s,
      (List.of_mem_zip (List.of_mem_zip (List.of_mem_zip hm).2).2).1, rfl⟩

/-- The strict format of the openings, round by round. The head tells the statement in words, under
`strict_ind`. -/
theorem strict_ind (hr : run.size = 32) :
    ∀ (ds : List RD) (ros : List RoundOut) (isRead : OPos (uL C ds) → Bool),
      RowsL C tbl sb ds ros isRead →
      sSP (256 + 8 * sb) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds) (rtSL C ds ros)
          isRead (opL C tbl run ds) = true
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => h.elim
  | ⟨e, k, items, tree, opens⟩ :: ds, ro :: ros, isRead, h => by
    obtain ⟨h1, h2⟩ := h
    have ih := strict_ind hr ds ros (fun p => isRead (.inr p)) h2
    show (sCompP (256 + 8 * sb) (roundS C ⟨e, k, items, tree, opens⟩) (fun _ => none) 0 _
          (fun p => isRead (.inl p))
          (fun p => opL C tbl run (⟨e, k, items, tree, opens⟩ :: ds) (.inl p)) &&
        sCompP (256 + 8 * sb) (roundS C ⟨e, k, items, tree, opens⟩)
          (wireS C K chal ⟨e, k, items, tree, opens⟩).posAtJ (depthOf tree)
          (((_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig).isSome) (fun p => isRead (.inl p))
          (fun p => opL C tbl run (⟨e, k, items, tree, opens⟩ :: ds) (.inl p)) &&
        sSP (256 + 8 * sb) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds) (rtSL C ds ros)
          (fun p => isRead (.inr p)) (opL C tbl run ds)) = true
    rw [ih, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · unfold sCompP
      exact List.all_eq_true.2 fun _ _ => rfl
    · unfold sCompP
      rw [List.all_eq_true]
      intro j _
      rcases h1 with ⟨ht, -⟩ | ⟨sh, Ob, root, ht, hv, -, hl, -, hok, -,
        hread⟩ | ⟨sh, root, ht, -, -, hl, -⟩
      · dsimp only at ht
        subst ht
        rfl
      · dsimp only at ht
        subst ht
        by_cases hj : j < 2 ^ sh.a
        · rw [show (wireS C K chal ⟨e, k, items, some sh, opens⟩).posAtJ j =
                some (⟨j, hj⟩ : Fin (2 ^ sh.a)) from dif_pos hj]
          dsimp only
          have ho : opL C tbl run (⟨e, k, items, some sh, opens⟩ :: ds)
                (.inl (⟨j, hj⟩ : Fin (2 ^ sh.a))) =
              Ob.at
                (symSL C (⟨e, k, items, some sh, opens⟩ :: ds) (.inl (⟨j, hj⟩ : Fin (2 ^ sh.a))))
                run j := by
            unfold opL
            show (match tbl.lookup sh.tree with | none => none | some x => x.2.at _ run j) = _
            rw [hl]
          rw [ho]
          cases hat : Ob.at
              (symSL C (⟨e, k, items, some sh, opens⟩ :: ds) (.inl (⟨j, hj⟩ : Fin (2 ^ sh.a))))
              run j with
          | none => rfl
          | some op =>
            obtain ⟨hm, s, hs, hsalt⟩ := at_some run _ Ob j op hat
            dsimp only
            have hrd : isRead (.inl (⟨j, hj⟩ : Fin (2 ^ sh.a))) = true :=
              (hread ⟨j, hj⟩).trans (decide_eq_true hm)
            have hsl : op.salt.length = 256 + 8 * sb := by
              rw [hsalt]
              simp only [leafSalt, List.length_append, length_bytesToBits, hr,
                (TieTree.ok_spec Ob sb sh.W hok).2.2.1 s hs]
            rw [hv, Bool.and_eq_true, Bool.and_eq_true]
            exact ⟨⟨rfl, hrd⟩, decide_eq_true hsl⟩
        · rw [show (wireS C K chal ⟨e, k, items, some sh, opens⟩).posAtJ j = none from dif_neg hj]
      · dsimp only at ht
        subst ht
        by_cases hj : j < 2 ^ sh.a
        · rw [show (wireS C K chal ⟨e, k, items, some sh, opens⟩).posAtJ j =
                some (⟨j, hj⟩ : Fin (2 ^ sh.a)) from dif_pos hj]
          dsimp only
          have ho : opL C tbl run (⟨e, k, items, some sh, opens⟩ :: ds)
                (.inl (⟨j, hj⟩ : Fin (2 ^ sh.a))) = none := by
            unfold opL
            show (match tbl.lookup sh.tree with | none => none | some x => x.2.at _ run j) = _
            rw [hl]
          rw [ho]
        · rw [show (wireS C K chal ⟨e, k, items, some sh, opens⟩).posAtJ j = none from dif_neg hj]

end

end Run.PQ
