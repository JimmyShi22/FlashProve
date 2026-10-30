-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/OwnForests.lean: the forests of the chain's own trees at the interface with stored
tables and at the family `famXPd`: the sibling's `forests_ind` carried over.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/ForestMap.lean (17 declarations, 237 lines) and `toLink`, `leaf_agree` of
OnBytes/Tie/StoredTop.lean. There the plain case's interface and the interface with stored tables
have two types of leaves' bodies, and forests are mapped from one to the other. Here both have one
type Bd, and the sibling's `forests_ind` (OnBytes/TypedOracleCompiler/Run/PageIsForest.lean) is general in the
interface: it is taken at the interface with stored tables, at spellings `pageOnl`, and nothing is
mapped. What is left: the plain family at these spellings and `famXPd` agree at all vertices and at
every leaf whose body is no stored symbol.

As text (3). `length_readsOneP`, `runForestsP_cons`, `runForestsP_append`.
Turned (3).
 `runForestP_congr`, `runForestsP_congr`  the original's `runForestP_map`, `runForestsP_map` at one
     interface and the identity on bodies.
 `famXPd_leaf_onl`  the original's `leaf_agree`: asked is that the body is no stored symbol, where
     the original goes by cases on the body's constructor.
New (6).
 `pageOnl B D dec`  spellings at the tag "onl" at the interface with stored tables: the spelling of
     a body is `B.own`, the vertices' start the configuration's digest; the other fields are read by
     nothing here.
 `famXPd_node_onl`  at all vertices the two families are one, by definition.
 `walkOb_onl`, `treeAllT_onl`, `treeAll_onl`  the test "every tree that has a record in the table
     walks to its root" at `pageOnl` is that at the plain case's spellings `PDS ..`, of which the
     sibling's laws speak.
 `forestsX_ind`  `forests_ind` with `famXPd` in the place of the plain family, at every pd.
No counterpart (13). `mapC`, `mapF`, `compP_map`, `optP_map`, `splitP_map`, `forestsP_map`,
`flatP_map`, `idxP_map`, `needP_map`, `readsOneP_map`, `readsP_map`, `wellP_map`, `toLink`: the maps
of checks and forests between two interfaces and their laws.

What is asked beside `forests_ind`'s hypotheses. `hns`: no body of an own symbol is a stored symbol
(`OwnFits.notStored`). `hs`: the strict format of the openings (`sSP .. = true`): from it
`forestsP_inp` reads that every leaf query of the forests is on the body of an own symbol. The
original needs no such hypothesis: its `leaf_agree` holds at every body.

What is not said. The forests of the two stored tables; the strict format itself; what follows the
forests. So no statement on `afterP` at the protocol with stored tables. Nothing on soundness; no
probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXFit
import OnBytes.TypedOracleCompiler.Run.PageIsForest
import OnBytes.TypedOracleCompiler.Run.ThinAskedMore

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (RoundOut)

/-! ## The walks of forests, at two families of one interface -/

section
variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g g' : Fam (typedOracleFamily lam K (Lf ())))

/-- The walk of one forest is the same at two families of oracle functions that agree on its leaves
and on all vertices. -/
theorem runForestP_congr (F : Forest lam (Lf ())) (s : List (Dig lam))
    (hleaf : ∀ e ∈ F.cs, (g' OracleName.leaf e.2.inp : Dig lam) = g OracleName.leaf e.2.inp)
    (hnode : ∀ q : Bits × Bits, (g' OracleName.node q : Dig lam) = g OracleName.node q) :
    runForestP Lf g' F s = runForestP Lf g F s := by
  have hn : nodeP Lf g' = nodeP Lf g := by
    funext a b
    exact hnode _
  have hl : (F.cs.map fun e => (g' OracleName.leaf e.2.inp : Dig lam)) =
      F.cs.map fun e => (g OracleName.leaf e.2.inp : Dig lam) := List.map_congr_left hleaf
  unfold runForestP
  rw [hn]
  erw [hl]
  rfl

/-- The walks of a list of forests are the same at two families of oracle functions that agree on
their leaves and on all vertices. -/
theorem runForestsP_congr (hnode : ∀ q : Bits × Bits, (g' OracleName.node q : Dig lam) = g OracleName.node q) :
    ∀ (Fs : List (Forest lam (Lf ()))) (s : List (Dig lam)),
    (∀ c ∈ flatP Lf Fs, (g' OracleName.leaf c.inp : Dig lam) = g OracleName.leaf c.inp) →
    runForestsP Lf g' Fs s = runForestsP Lf g Fs s
  | [], _, _ => rfl
  | F :: Fs, s, h => by
    have h1 : ∀ e ∈ F.cs, (g' OracleName.leaf e.2.inp : Dig lam) = g OracleName.leaf e.2.inp :=
      fun e he => h e.2 (List.mem_flatMap.2 ⟨F, List.mem_cons_self, List.mem_map_of_mem he⟩)
    have h2 : ∀ c ∈ flatP Lf Fs, (g' OracleName.leaf c.inp : Dig lam) = g OracleName.leaf c.inp := by
      intro c hc
      obtain ⟨F', hF', hc'⟩ := List.mem_flatMap.1 hc
      exact h c (List.mem_flatMap.2 ⟨F', List.mem_cons_of_mem _ hF', hc'⟩)
    rw [runForestsP, runForestsP, runForestP_congr Lf g g' F _ h1 hnode,
      runForestsP_congr hnode Fs _ h2]

/-- A forest's walk takes as many digests as are read off its checks' paths. -/
theorem length_readsOneP (F : Forest lam (Lf ())) : (readsOneP Lf F).length = needP Lf F := by
  unfold readsOneP needP idxP
  rw [Octopus.length_reads]
  simp only [List.map_map]
  rfl

/-- The walk of a forest and further ones, on the first one's digests and further ones, says yes
exactly if both walks do. -/
theorem runForestsP_cons (F : Forest lam (Lf ())) (Fs : List (Forest lam (Lf ())))
    (s : List (Dig lam)) :
    runForestsP Lf g (F :: Fs) (readsOneP Lf F ++ s) =
      (runForestP Lf g F (readsOneP Lf F) && runForestsP Lf g Fs s) := by
  rw [runForestsP, List.take_left' (length_readsOneP Lf F),
    List.drop_left' (length_readsOneP Lf F)]

/-- The walk of two lists of forests, on the first list's digests and further ones, says yes exactly
if both walks do. -/
theorem runForestsP_append : ∀ (Fs Fs' : List (Forest lam (Lf ()))) (s' : List (Dig lam)),
    runForestsP Lf g (Fs ++ Fs') (readsP Lf Fs ++ s') =
      (runForestsP Lf g Fs (readsP Lf Fs) && runForestsP Lf g Fs' s')
  | [], _, _ => rfl
  | F :: Fs, Fs', s' => by
    have ih := runForestsP_append Fs Fs' s'
    have e : readsP Lf (F :: Fs) = readsOneP Lf F ++ readsP Lf Fs := rfl
    rw [e, List.cons_append, List.append_assoc, runForestsP_cons, ih, runForestsP_cons,
      Bool.and_assoc]

end

/-! ## A page at the tag "onl", at the interface with stored tables -/

section
variable {Bd : Type} (B : BodyD Bd) (D : XD) (dec : View → Bool) (pd : ByteArray)
  (O : ByteArray → ByteArray)

/-- Spellings at the tag "onl", at the interface with stored tables, for the sibling's laws on
forests (OnBytes/TypedOracleCompiler/Run/PageIsForest.lean), which are general in the interface, ask spellings at
that tag, and read of them the spelling of a body and the vertices' start alone: these two are
`B.own` and the configuration's digest. The other fields are read by nothing here. -/
def pageOnl : PageD (D.L Bd dec) .onl where
  label := 0
  kind := fun _ => 0
  work := fun _ => 0
  stm := fun _ => ByteArray.empty
  msg := fun _ _ _ => ByteArray.empty
  nonce := fun _ _ => 0
  leaf := B.own
  cfg := D.base.cfg

/-- At every vertex `famXPd` is the plain family at these spellings, by definition. -/
theorem famXPd_node_onl (K : ℕ) (q : Bits × Bits) :
    (famXPd B D dec pd O K .node q : Dig 256) = famOf O (pageOnl B D dec) K .node q := rfl

/-- At a leaf whose body is no stored symbol `famXPd` is the plain family at these spellings. -/
theorem famXPd_leaf_onl (K : ℕ) (q : LeafIn (D.L Bd dec)) (h : B.getE q.body = none) :
    (famXPd B D dec pd O K .leaf q : Dig 256) = famOf O (pageOnl B D dec) K .leaf q := by
  show ansOf O (leafX B D dec q) = ansOf O (leafCall (pageOnl B D dec) q)
  rw [leafX_own D dec B q h]
  rfl

/-- The walk of one record of the table is that at the plain case's spellings: it reads of the
spellings the vertices' start alone. -/
theorem walkOb_onl (run : ByteArray) (tree W : ℕ) (Ob : OpenB) :
    walkOb O (pageOnl B D dec) run tree W Ob =
      walkOb O (PDS Bd D.base D.C dec B.own) run tree W Ob := rfl

/-- So is "every tree of a round that has a record in the table walks to its root". -/
theorem treeAllT_onl (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray) :
    ∀ (ts : List _root_.Fmt.Shape) (R : List ByteArray),
      treeAllT O (pageOnl B D dec) tbl run ts R =
        treeAllT O (PDS Bd D.base D.C dec B.own) tbl run ts R
  | [], _ => rfl
  | _ :: _, [] => rfl
  | sh :: ts, root :: R => by
    show ((match tbl.lookup sh.tree with
        | none => true
        | some x => decide (walkOb O (pageOnl B D dec) run sh.tree x.1 x.2 = root)) &&
      treeAllT O (pageOnl B D dec) tbl run ts R) = _
    rw [treeAllT_onl tbl run ts R]
    rfl

/-- And so is "every tree that has a record in the table walks to its root": the sibling's laws on
`treeAll` at the plain case's spellings (OnBytes/TypedOracleCompiler/Run/PageIsRows.lean) speak of the test in
`forestsX_ind`. -/
theorem treeAll_onl (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray) :
    ∀ (ds : List RD) (ros : List RoundOut),
      treeAll O (pageOnl B D dec) tbl run ds ros =
        treeAll O (PDS Bd D.base D.C dec B.own) tbl run ds ros
  | [], _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, ro :: ros => by
    show (treeAllT O (pageOnl B D dec) tbl run d.trees (_root_.Fmt.rootsOf ro.vals) &&
      treeAll O (pageOnl B D dec) tbl run ds ros) = _
    rw [treeAllT_onl B D dec O tbl run, treeAll_onl tbl run ds ros]
    rfl

/-- The forests of the chain's own trees, round by round, at famXPd. The sibling's `forests_ind`
carried to the interface with stored tables and to the wider family, at every pd. Asked beside its
hypotheses: no body of an own symbol is a stored symbol; the strict format of the openings (from
which it is read that every leaf query of the forests is on such a body). -/
theorem forestsX_ind (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray) (sb : ℕ) (hO : ∀ s, (O s).size = 32)
    (hr : run.size = 32) (ds : List RD) (ros : List RoundOut) (isRead : OPos (uL C ds) → Bool)
    (emb : (p : OPos (uL C ds)) → OSym (uL C ds) p → Bd)
    (hrows : RowsL C tbl sb ds ros isRead)
    (hi : ∀ p a, B.own (emb p a) = some (leafSL C sb ds ⟨p, a⟩))
    (hns : ∀ p a, B.getE (emb p a) = none) (sMT : ℕ)
    (hs : sSP sMT (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds) (rtSL C ds ros) isRead
      (opL C tbl run ds) = true) :
    ∃ Fs,
      forestsP (fun _ => D.L Bd dec) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
          emb (rtSL C ds ros) isRead (opL C tbl run ds) = some Fs ∧
      (flatP (fun _ => D.L Bd dec) Fs).length = cntO tbl ds ∧
      (∀ c ∈ flatP (fun _ => D.L Bd dec) Fs,
        wellP (fun _ => D.L Bd dec) c = true ∧ ∃ d ∈ ds, ∃ sh ∈ d.trees, c.depth = sh.a) ∧
      ∀ Fs' s', runForestsP (fun _ => D.L Bd dec) (famXPd B D dec pd O (K + 1))
          (Fs ++ Fs') (readsP (fun _ => D.L Bd dec) Fs ++ s') =
        (treeAll O (pageOnl B D dec) tbl run ds ros &&
          runForestsP (fun _ => D.L Bd dec) (famXPd B D dec pd O (K + 1)) Fs' s') := by
  obtain ⟨Fs, f1, f2, f3, f4⟩ := forests_ind (L := D.L Bd dec) O (pageOnl B D dec) C K chal tbl run
    sb hO hr ds ros isRead emb hrows hi
  refine ⟨Fs, f1, f2, f3, fun Fs' s' => ?_⟩
  have hin := forestsP_inp (fun _ => D.L Bd dec) sMT (SL C ds) (allLo (SL C ds))
    (wiresSL C K chal ds) emb (rtSL C ds ros) isRead (opL C tbl run ds) Fs f1 hs
  have hc : runForestsP (fun _ => D.L Bd dec) (famXPd B D dec pd O (K + 1)) Fs
      (readsP (fun _ => D.L Bd dec) Fs) =
      runForestsP (fun _ => D.L Bd dec) (famOf O (pageOnl B D dec) (K + 1)) Fs
        (readsP (fun _ => D.L Bd dec) Fs) :=
    runForestsP_congr (fun _ => D.L Bd dec) _ _ (fun q => famXPd_node_onl B D dec pd O (K + 1) q)
      Fs _ fun c hcm => by
        obtain ⟨p, a, salt, i1, -⟩ := hin c hcm
        exact famXPd_leaf_onl B D dec pd O (K + 1) c.inp (by rw [i1]; exact hns p a)
  have h4 := f4 [] []
  rw [List.append_nil, List.append_nil] at h4
  rw [runForestsP_append, hc, h4]
  show (treeAll O (pageOnl B D dec) tbl run ds ros && true && _) = _
  rw [Bool.and_true]

end

end TypedOracleCompiler.Run.PQ
