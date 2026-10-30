-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/StoredExt.lean: the forest of the two stored tables, at the sibling's interface with
stored tables and at the family `famXPd`.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/StoredExt.lean, from its section "The walk over all positions
of the two strings" on (line 436 to the end: 23 declarations). CUT AND TURNED BY PROGRAM. That part
of the original is written for any interface `Lf` and any embedding `emb : SgX → Body (Lf ())` of
stored symbols into leaves' bodies, up to its last section; so over the sibling's `Check`, `Forest`,
`extWP`, `forestExtP`, `runForestP` its text stands as it is.

WHAT IT IMPORTS FROM OUTSIDE THE SIBLING: OnBytes/Tie/StoredExt.lean itself, for its first 435
lines, which speak of lists, `OpenB`, `extOf` and walks on bytes, notions that the sibling takes
over from the library as they are (`Row`, `rowsOf`, `tabAt`, `tabsOf`, `readOf`, `StoOK`, `TabOK`
and their laws); with it OnBytes/Tie/StoredWalk.lean and TwoTrees.lean (`walk_two`). These three
stand under OnBytes/TypedOracleCompiler/Run/PageXRead.lean already. The second half of the original is imported with
the first and used by nothing here.

AS TEXT, but for `_root_.` before `Fmt.` and some line breaks (20). `checkFor`, `extWP_listed`,
`chk`, `twoF`, `one_string`, `two_strings`, `forest_two`, `flat_one`, `length_two`, `well_chk`,
`well_two`, `idx_part`, `path_part`, `leafD`, `leaf_part`, `run_mk`, `run_two`, `node_call`,
`ext_strict`, `ext_symbol`.
TURNED (3).
 `famXPd_leaf`      the original's `famX_leaf`: the body is `B.embE (x, col)`; that the leaf is
                    spelled as call 174 goes through `leafX_stored`, which rests on `B.get_e`.
 `famXPd_node`      the original's `famX_node`, at every pd.
 `ext_forest`       the embedding is `B.embE`, the family `famXPd B D dec pd O (D.K + 1)`.
NEW: none. NO COUNTERPART: none.

WHAT IS NOT SAID. That any list of openings has `StoOK` (of what the strict reader has read:
`stoOK_of`, OnBytes/TypedOracleCompiler/Run/StoredMain.lean). "Read" is what the openings themselves list
(`readOf`); that the protocol reads these positions is another file's. A table that is not opened is
not walked. TWO tables under two roots, as the entry has them; an interface with one stored table:
a file of this project that is not in this library. Nothing on soundness; no probability; nothing on
any hash: O is any
function on byte strings with answers of 32 bytes.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXFit
import OnBytes.TypedOracleCompiler.Run.ThinAskedMore
import OnBytes.Tie.StoredExt

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open OnBytes.Tie (Row rowsOf tabAt tabsOf readOf StoOK TabOK tabOK_of sum_two rows_fst rows_length
  rows_ends rows_three walkOK_of extOf_rows tabAt_ok tabAt_depth read_law extOf_found
  extOf_at_listed xPos_back xPos_at mem_readOf length_leafSalt walk_two)

/-! ### The walk over all positions of the two strings -/

section
variable {I X : Type} {lam : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) {E : ExtSpec} (we : WireE E)
  (emb : E.Sym → Body (Lf ())) (cms : List (Dig lam)) (isRead : E.Pos → Bool)
  (g : E.Pos → Option (Opening lam E.Sym))

/-- The tree's number and the check that the walk makes of the opening at a position, if one is
there. -/
def checkFor (p : E.Pos) : Option (ℕ × Check lam (Lf ())) :=
  (g p).map fun op => (we.which p, ⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
    cms.getD (we.which p) default, we.depth⟩)

/-- If there is an opening exactly at the positions that are read, the walk does not fail, and it
gives the checks of the openings in the order of the positions. -/
theorem extWP_listed : ∀ ps : List E.Pos, (∀ p ∈ ps, isRead p = (g p).isSome) →
    extWP Lf we emb cms isRead g ps = some (ps.filterMap (checkFor Lf we emb cms g))
  | [], _ => rfl
  | p :: ps, h => by
    have ih := extWP_listed ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp : isRead p = (g p).isSome := h p List.mem_cons_self
    cases hg : g p with
    | none =>
      have hr : isRead p = false := by rw [hp, hg]; rfl
      have hc : checkFor Lf we emb cms g p = none := by unfold checkFor; rw [hg]; rfl
      rw [List.filterMap_cons_none hc, extWP, hr, ← ih]
      rfl
    | some op =>
      have hr : isRead p = true := by rw [hp, hg]; rfl
      have hc : checkFor Lf we emb cms g p = some (we.which p, ⟨⟨emb op.sym, op.salt⟩, we.leaf p,
          op.path, cms.getD (we.which p) default, we.depth⟩) := by
        unfold checkFor
        rw [hg]
        rfl
      rw [List.filterMap_cons_some hc, extWP, hr, hg, ih]
      rfl

end

/-! ### The checks of the two tables, for any interface -/

section
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (emb : SgX → Body (Lf ()))

/-- The check that a row of tree number t calls for, with the tree's number. -/
def chk (cfg : ByteArray) (a t : ℕ) (rt : Dig 256) (e : Row) : ℕ × Check 256 (Lf ()) :=
  (t, ⟨⟨emb (e.1, e.2.1), leafSalt cfg e.2.2.1⟩, e.1, e.2.2.2, rt, a⟩)

/-- The forest of two trees of depth a with the checks that two openings call for. -/
def twoF (cfg : ByteArray) (a : ℕ) (R : ℕ → Dig 256) (A B : OpenB) : Forest 256 (Lf ()) :=
  ⟨a, R, (rowsOf A).map (chk Lf emb cfg a 0 (R 0)) ++ (rowsOf B).map (chk Lf emb cfg a 1 (R 1))⟩

/-- One of the two strings: the checks at its positions, in order, are the checks of its table's
rows. Here inj makes a position of the two strings of a place in string number t. -/
theorem one_string (cms : List (Dig 256)) (a salt : ℕ) (cfg : ByteArray)
    (sto : List (Bool × ℕ × OpenB)) (ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true)
    (depth : ∀ e ∈ sto, e.2.2.a = a) (b : Bool) (t : ℕ)
    (inj : Fin (2 ^ a) → Fin (2 ^ a) ⊕ Fin (2 ^ a))
    (h1 : ∀ i, (inj i).elim (fun _ => false) (fun _ => true) = b)
    (h2 : ∀ i, (inj i).elim (·.val) (·.val) = i.val) (h3 : ∀ i, (weX a).which (inj i) = t)
    (h4 : ∀ i, (weX a).leaf (inj i) = i.val) :
    ((List.finRange (2 ^ a)).map inj).filterMap
        (checkFor Lf (weX a) emb cms (extOf a cfg (tabsOf sto)))
      = (rowsOf (tabAt a sto b).2).map (chk Lf emb cfg a t (cms.getD t default)) := by
  have hok := tabAt_ok a salt sto ok b
  have hfst := rows_fst _ salt _ hok
  obtain ⟨hsorted, hbound, -⟩ := TieTree.ok_list _ salt _ hok
  rw [tabAt_depth a sto depth b] at hbound
  -- At the position of place i is the check of the row that is listed under i.
  have hat : checkFor Lf (weX a) emb cms (extOf a cfg (tabsOf sto)) ∘ inj
      = (fun j : ℕ => ((rowsOf (tabAt a sto b).2).lookup j).map
          fun r => chk Lf emb cfg a t (cms.getD t default) (j, r)) ∘ Fin.val := by
    funext i
    show checkFor Lf (weX a) emb cms (extOf a cfg (tabsOf sto)) (inj i)
      = ((rowsOf (tabAt a sto b).2).lookup i.val).map
          fun r => chk Lf emb cfg a t (cms.getD t default) (i.val, r)
    unfold checkFor
    rw [extOf_rows, h1, h2, h3, h4, Option.map_map]
    rfl
  -- The places in order are the numbers below 2 ^ a, and the rows' places increase.
  rw [List.filterMap_map, hat, ← List.filterMap_map, List.map_coe_finRange_eq_range,
    List.range_eq_range', TieTree.filterMap_lookup _ (2 ^ a) 0 _ (hfst.symm ▸ hsorted)]
  intro e he
  have hm : e.1 ∈ (rowsOf (tabAt a sto b).2).map Prod.fst := List.mem_map.2 ⟨e, he, rfl⟩
  rw [hfst] at hm
  exact ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact hbound e.1 hm⟩

/-- The compiled verifier walks all positions of both strings. If each table is opened at most once,
every opening has the right form and the depth a, and "read" is what the openings list (`readOf`),
it collects the checks of the first table's rows in order, then those of the second table's. -/
theorem two_strings (cms : List (Dig 256)) (a salt : ℕ) (cfg : ByteArray)
    (sto : List (Bool × ℕ × OpenB)) (once : (sto.map (·.1)).Nodup)
    (ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true) (depth : ∀ e ∈ sto, e.2.2.a = a) :
    extWP Lf (weX a) emb cms (fun p => decide (p ∈ readOf a sto)) (extOf a cfg (tabsOf sto))
        (weX a).all
      = some ((rowsOf (tabAt a sto false).2).map (chk Lf emb cfg a 0 (cms.getD 0 default)) ++
          (rowsOf (tabAt a sto true).2).map (chk Lf emb cfg a 1 (cms.getD 1 default))) := by
  rw [extWP_listed Lf (weX a) emb cms _ _ (weX a).all
    fun p _ => read_law a salt cfg sto once ok p]
  show some (((List.finRange (2 ^ a)).map Sum.inl ++ (List.finRange (2 ^ a)).map Sum.inr).filterMap
    (checkFor Lf (weX a) emb cms (extOf a cfg (tabsOf sto)))) = _
  rw [List.filterMap_append,
    one_string Lf emb cms a salt cfg sto ok depth false 0 Sum.inl (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl),
    one_string Lf emb cms a salt cfg sto ok depth true 1 Sum.inr (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)]

/-- Of the two tables' openings the compiled verifier forms one forest, `twoF`. -/
theorem forest_two (cms : List (Dig 256)) (a salt : ℕ) (cfg : ByteArray)
    (sto : List (Bool × ℕ × OpenB)) (once : (sto.map (·.1)).Nodup)
    (ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true) (depth : ∀ e ∈ sto, e.2.2.a = a) :
    forestExtP Lf (weX a) emb cms (fun p => decide (p ∈ readOf a sto)) (extOf a cfg (tabsOf sto))
      = some [twoF Lf emb cfg a (fun t => cms.getD t default) (tabAt a sto false).2
          (tabAt a sto true).2] := by
  unfold forestExtP
  rw [two_strings Lf emb cms a salt cfg sto once ok depth]
  rfl

/-- Flattening one forest gives its checks. -/
theorem flat_one (F : Forest 256 (Lf ())) : flatP Lf [F] = F.cs.map Prod.snd := by
  simp [flatP]

/-- The forest has as many checks as the two openings list places. -/
theorem length_two (cfg : ByteArray) (a salt : ℕ) (R : ℕ → Dig 256) (A B : ℕ × OpenB)
    (hA : A.2.ok salt A.1 = true) (hB : B.2.ok salt B.1 = true) :
    (flatP Lf [twoF Lf emb cfg a R A.2 B.2]).length = A.2.idx.length + B.2.idx.length := by
  rw [flat_one, List.length_map]
  show ((rowsOf A.2).map _ ++ (rowsOf B.2).map _).length = _
  rw [List.length_append, List.length_map, List.length_map, rows_length A.2 salt A.1 hA,
    rows_length B.2 salt B.1 hB]

/-- The check of a row is well formed and has the tables' depth. -/
theorem well_chk (cfg : ByteArray) (a salt t : ℕ) (rt : Dig 256) (T : ℕ × OpenB)
    (hok : T.2.ok salt T.1 = true) (ha : T.2.a = a) (e : Row) (he : e ∈ rowsOf T.2) :
    wellP Lf (chk Lf emb cfg a t rt e).2 = true ∧ (chk Lf emb cfg a t rt e).2.depth = a := by
  obtain ⟨-, hb, -⟩ := TieTree.ok_list T.2 salt T.1 hok
  have h1 : e.1 < 2 ^ a := ha ▸ hb e.1 (List.of_mem_zip he).1
  have hp : e.2.2.2 ∈ T.2.paths :=
    (List.of_mem_zip (List.of_mem_zip (List.of_mem_zip he).2).2).2
  have h2 : e.2.2.2.length = a := ha ▸ Octopus.length_of_mem_fill _ _ _ _ hp
  refine ⟨?_, rfl⟩
  show (decide (e.2.2.2.length = a) && decide (e.1 < 2 ^ a)) = true
  rw [decide_eq_true h2, decide_eq_true h1]
  rfl

/-- Each check of the forest is well formed and has the tables' depth. -/
theorem well_two (cfg : ByteArray) (a salt : ℕ) (R : ℕ → Dig 256) (A B : ℕ × OpenB)
    (hA : A.2.ok salt A.1 = true) (hB : B.2.ok salt B.1 = true) (aA : A.2.a = a)
    (aB : B.2.a = a) :
    ∀ c ∈ flatP Lf [twoF Lf emb cfg a R A.2 B.2], wellP Lf c = true ∧ c.depth = a := by
  intro c hc
  rw [flat_one] at hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact well_chk Lf emb cfg a salt 0 (R 0) A hA aA e he
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact well_chk Lf emb cfg a salt 1 (R 1) B hB aB e he

/-- In the forest, one tree's opened leaves have the listed places with t * 2 ^ a added. -/
theorem idx_part (cfg : ByteArray) (a salt t : ℕ) (rt : Dig 256) (T : ℕ × OpenB)
    (hok : T.2.ok salt T.1 = true) :
    ((rowsOf T.2).map (chk Lf emb cfg a t rt)).map (fun e => e.1 * 2 ^ a + e.2.j)
      = T.2.idx.map (t * 2 ^ a + ·) := by
  conv_rhs => rw [← rows_fst T.2 salt T.1 hok]
  rw [List.map_map, List.map_map]
  rfl

/-- The same with their paths, which `Octopus.fill` makes from the given digests. -/
theorem path_part (cfg : ByteArray) (a salt t : ℕ) (rt : Dig 256) (T : ℕ × OpenB)
    (hok : T.2.ok salt T.1 = true) (ha : T.2.a = a) :
    ((rowsOf T.2).map (chk Lf emb cfg a t rt)).map (fun e => (e.1 * 2 ^ a + e.2.j, e.2.path))
      = (T.2.idx.zip (Octopus.fill a T.2.idx (T.2.given.map bytesToDig))).map
          fun x => (t * 2 ^ a + x.1, x.2) := by
  have h := rows_ends T.2 salt T.1 hok
  unfold OpenB.paths at h
  rw [ha] at h
  rw [← h, List.map_map, List.map_map]
  rfl

variable {K : ℕ} (g : Fam (typedOracleFamily 256 K (Lf ())))

/-- The typed leaf function's answer at a check, as a digest. -/
def leafD (e : ℕ × Check 256 (Lf ())) : Dig 256 := g OracleName.leaf e.2.inp

/-- If the typed leaf function is the format's call 174, one tree's opened leaves have the digests
from which the reader's walk starts. -/
theorem leaf_part (O : ByteArray → ByteArray) (cfg : ByteArray) (a salt t : ℕ) (rt : Dig 256)
    (hleaf : ∀ (x : ℕ) (col : List UInt64) (s : ByteArray),
      (g OracleName.leaf (⟨emb (x, col), leafSalt cfg s⟩ : LeafIn (Lf ())) : Dig 256)
        = bytesToDig (_root_.Fmt.HO O 174 (_root_.Fmt.leafPlace 0 col.length (s.size / 8))
            (2 ^ a + x) cfg
            (_root_.Fmt.leafBytes col s)))
    (T : ℕ × OpenB) (hok : T.2.ok salt T.1 = true) :
    ((rowsOf T.2).map (chk Lf emb cfg a t rt)).map (leafD Lf g)
      = (WalkTie.leafV (_root_.Fmt.HO O) ⟨a, T.1, true, 0⟩ cfg T.2.idx
          (T.2.cols.zip T.2.salts)).map bytesToDig := by
  rw [TieTree.leafV_eq, ← rows_three T.2 salt T.1 hok, List.map_map, List.map_map, List.map_map]
  exact List.map_congr_left fun e _ => hleaf e.1 e.2.1 e.2.2.1

/-- The compiled verifier's walk through a forest, written out. -/
theorem run_mk (a : ℕ) (R : ℕ → Dig 256) (cs : List (ℕ × Check 256 (Lf ()))) :
    runForestP Lf g ⟨a, R, cs⟩ (readsOneP Lf ⟨a, R, cs⟩)
      = ((Octopus.upN a (cs.map fun e => e.1 * 2 ^ a + e.2.j)).zip
          (Octopus.octF (nodeP Lf g) a (cs.map fun e => e.1 * 2 ^ a + e.2.j)
            (cs.map (leafD Lf g))
            (Octopus.reads a (cs.map fun e => (e.1 * 2 ^ a + e.2.j, e.2.path))))).all
          fun m => decide (m.2 = R m.1) :=
  rfl

/-- The compiled verifier's walk through the forest of the two tables ends in the roots of the
tables that are opened, if both openings have `TabOK`, O's answers and the roots have 32 bytes, R
gives the roots at 0 and 1, and the typed node and leaf functions are the format's calls 166 and
174. A table that is not opened is not walked. -/
theorem run_two (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (cfg : ByteArray)
    (a salt : ℕ) (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hnode : nodeP Lf g = TieTree.digFn (fun l r => _root_.Fmt.HO O 166 0 0 cfg (l ++ r)))
    (hleaf : ∀ (x : ℕ) (col : List UInt64) (s : ByteArray),
      (g OracleName.leaf (⟨emb (x, col), leafSalt cfg s⟩ : LeafIn (Lf ())) : Dig 256)
        = bytesToDig (_root_.Fmt.HO O 174 (_root_.Fmt.leafPlace 0 col.length (s.size / 8))
            (2 ^ a + x) cfg
            (_root_.Fmt.leafBytes col s)))
    (R : ℕ → Dig 256) (hR0 : R 0 = bytesToDig r0) (hR1 : R 1 = bytesToDig r1) (A B : ℕ × OpenB)
    (kA : TabOK O cfg a salt r0 A) (kB : TabOK O cfg a salt r1 B) :
    runForestP Lf g (twoF Lf emb cfg a R A.2 B.2) (readsOneP Lf (twoF Lf emb cfg a R A.2 B.2))
      = true := by
  have i0 : ∀ l : List ℕ, l.map (0 * 2 ^ a + ·) = l := fun l => by simp
  have i1 : ∀ l : List ℕ, l.map (1 * 2 ^ a + ·) = l.map (2 ^ a + ·) := fun l => by
    simp only [Nat.one_mul]
  have p0 : ∀ l : List (ℕ × List (Dig 256)), l.map (fun x => (0 * 2 ^ a + x.1, x.2)) = l :=
    fun l => by simp
  have p1 : ∀ l : List (ℕ × List (Dig 256)),
      l.map (fun x => (1 * 2 ^ a + x.1, x.2)) = l.map fun x => (2 ^ a + x.1, x.2) := fun l => by
    simp only [Nat.one_mul]
  unfold twoF
  rw [run_mk]
  simp only [List.map_append]
  rw [idx_part Lf emb cfg a salt 0 (R 0) A kA.ok, idx_part Lf emb cfg a salt 1 (R 1) B kB.ok,
    path_part Lf emb cfg a salt 0 (R 0) A kA.ok kA.depth,
    path_part Lf emb cfg a salt 1 (R 1) B kB.ok kB.depth,
    leaf_part Lf emb g O cfg a salt 0 (R 0) hleaf A kA.ok,
    leaf_part Lf emb g O cfg a salt 1 (R 1) hleaf B kB.ok, i0, i1, p0, p1, hnode]
  exact walk_two (fun l r => _root_.Fmt.HO O 166 0 0 cfg (l ++ r)) (fun _ _ => hO _) a A.2.idx
    B.2.idx
    _ _ A.2.given B.2.given r0 r1 R hR0 hR1 (walkOK_of hO h0 kA) (walkOK_of hO h1 kB)

end

section
variable {Bd : Type} (B : BodyD Bd) (D : XD) (dec : View → Bool) (pd : ByteArray)
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)

/-- If the configuration's digest has 32 bytes, the typed leaf function at the body of a symbol of a
stored table, with the typed salt `leafSalt cfg s`, is the format's call 174. At every pd. Nothing
is said of another typed salt. -/
theorem famXPd_leaf (x : ℕ) (col : List UInt64) (s : ByteArray) (hc : D.base.cfg.size = 32) :
    (famXPd B D dec pd O (D.K + 1) .leaf
        (⟨B.embE (x, col), leafSalt D.base.cfg s⟩ : LeafIn (D.L Bd dec)) : Dig 256)
      = bytesToDig (_root_.Fmt.HO O 174 (_root_.Fmt.leafPlace 0 col.length (s.size / 8))
          (2 ^ D.a + x)
          D.base.cfg (_root_.Fmt.leafBytes col s)) := by
  -- The typed salt is the 256 bits of cfg and then the bits of s.
  have hl : (bytesToBits D.base.cfg).length = 256 := by rw [length_bytesToBits, hc]
  have hfront : bitsToBytes ((leafSalt D.base.cfg s).take 256) = D.base.cfg := by
    unfold leafSalt
    rw [List.take_left' hl, bitsToBytes_bytesToBits]
  have hback : bitsToBytes ((leafSalt D.base.cfg s).drop 256) = s := by
    unfold leafSalt
    rw [List.drop_left' hl, bitsToBytes_bytesToBits]
  -- The number of the salt's words of 64 bits is the number of its words of 8 bytes.
  have hwords : ((leafSalt D.base.cfg s).length - 256) / 64 = s.size / 8 := by
    unfold leafSalt
    rw [List.length_append, hl, length_bytesToBits]
    omega
  -- So the test on the salt's front holds, and the leaf is spelled as call 174.
  have hcall : leafX B D dec ⟨B.embE (x, col), leafSalt D.base.cfg s⟩
      = some ⟨0, 174, _root_.Fmt.leafPlace 0 col.length (s.size / 8), 2 ^ D.a + x, D.base.cfg,
          _root_.Fmt.leafBytes col s⟩ := by
    rw [leafX_stored D dec B (x, col) (leafSalt D.base.cfg s)]
    show (if bitsToBytes ((leafSalt D.base.cfg s).take 256) == D.base.cfg then
        some (⟨0, 174,
          _root_.Fmt.leafPlace 0 col.length (((leafSalt D.base.cfg s).length - 256) / 64),
          2 ^ D.a + x, D.base.cfg,
          _root_.Fmt.leafBytes col (bitsToBytes ((leafSalt D.base.cfg s).drop 256))⟩ :
            _root_.Fmt.OQ)
      else none) = _
    rw [hfront, hback, hwords, if_pos (bytes_beq_self D.base.cfg)]
  show ansOf O (leafX B D dec ⟨B.embE (x, col), leafSalt D.base.cfg s⟩) = _
  rw [hcall]
  -- `Fmt.HO` asks O once under every number but 162.
  rfl

/-- A typed node query on two bit strings is the format's call 166 on their bytes. -/
theorem node_call (cfg : ByteArray) (u v : Bits) :
    ansOf O (nodeCallC cfg (u, v))
      = bytesToDig (_root_.Fmt.HO O 166 0 0 cfg (bitsToBytes u ++ bitsToBytes v)) :=
  rfl

/-- The typed node function is the format's call 166. At every pd. -/
theorem famXPd_node :
    nodeP (fun _ => D.L Bd dec) (famXPd B D dec pd O (D.K + 1))
      = TieTree.digFn (fun l r => _root_.Fmt.HO O 166 0 0 D.base.cfg (l ++ r)) := by
  funext l r
  -- Both sides are the answer of O at the string of call 166 on the bytes of l and then of r.
  show ansOf O (nodeCallC D.base.cfg (List.ofFn l, List.ofFn r))
    = bytesToDig (_root_.Fmt.HO O 166 0 0 D.base.cfg (digToBytes l ++ digToBytes r))
  exact node_call O D.base.cfg (List.ofFn l) (List.ofFn r)

include hO in
/-- The forest of the two stored tables, given `StoOK`, with O's answers, the roots and the
configuration's digest of 32 bytes, and "read" taken to be what the openings list (`readOf`): there
is one; it has as many checks as places are listed; each check is well formed and of the tables'
depth; its walk ends in the roots of the tables that are opened. A table that is not opened is not
walked. -/
theorem ext_forest (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hc : D.base.cfg.size = 32) (sto : List (Bool × ℕ × OpenB))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto) :
    ∃ Fx : Forest 256 (D.L Bd dec),
      forestExtP (fun _ => D.L Bd dec) (weX D.a) B.embE
        [bytesToDig r0, bytesToDig r1] (fun p => decide (p ∈ readOf D.a sto))
        (extOf D.a D.base.cfg (tabsOf sto)) = some [Fx] ∧
      (flatP (fun _ => D.L Bd dec) [Fx]).length = (sto.map (·.2.2.idx.length)).sum ∧
      (∀ c ∈ flatP (fun _ => D.L Bd dec) [Fx],
        wellP (fun _ => D.L Bd dec) c = true ∧ c.depth = D.a) ∧
      runForestP (fun _ => D.L Bd dec) (famXPd B D dec pd O (D.K + 1)) Fx
        (readsOneP (fun _ => D.L Bd dec) Fx) = true := by
  have k0 : TabOK O D.base.cfg D.a D.base.plan.salt r0 (tabAt D.a sto false) := tabOK_of hs false
  have k1 : TabOK O D.base.cfg D.a D.base.plan.salt r1 (tabAt D.a sto true) := tabOK_of hs true
  refine ⟨twoF (fun _ => D.L Bd dec) B.embE D.base.cfg D.a
    (fun t => [bytesToDig r0, bytesToDig r1].getD t default) (tabAt D.a sto false).2
    (tabAt D.a sto true).2, ?_, ?_, ?_, ?_⟩
  · exact forest_two (fun _ => D.L Bd dec) B.embE [bytesToDig r0, bytesToDig r1]
      D.a D.base.plan.salt D.base.cfg sto hs.once hs.ok hs.depth
  · rw [length_two (fun _ => D.L Bd dec) B.embE D.base.cfg D.a D.base.plan.salt _
      (tabAt D.a sto false) (tabAt D.a sto true) k0.ok k1.ok]
    exact (sum_two D.a (fun T => T.2.idx.length) rfl sto hs.once).symm
  · exact well_two (fun _ => D.L Bd dec) B.embE D.base.cfg D.a D.base.plan.salt _
      (tabAt D.a sto false) (tabAt D.a sto true) k0.ok k1.ok k0.depth k1.depth
  · exact run_two (fun _ => D.L Bd dec) B.embE (famXPd B D dec pd O (D.K + 1)) O hO
      D.base.cfg D.a D.base.plan.salt r0 r1 h0 h1 (famXPd_node B D dec pd O)
      (fun x col s => famXPd_leaf B D dec pd O x col s hc) _ rfl rfl (tabAt D.a sto false)
      (tabAt D.a sto true) k0 k1

/-- The strict format of the stored tables' openings, given `StoOK` and a configuration's digest of
32 bytes. "Read" is taken here to be what the openings themselves list (`readOf`), so "an opening
is present only where the verifier reads" holds by construction. What the theorem adds is the salt's
length. -/
theorem ext_strict (r0 r1 : ByteArray) (hc : D.base.cfg.size = 32)
    (sto : List (Bool × ℕ × OpenB))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto) :
    sExtP (256 + 8 * D.base.plan.salt) (weX D.a) (fun p => decide (p ∈ readOf D.a sto))
      (extOf D.a D.base.cfg (tabsOf sto)) = true := by
  refine _root_.Compile.Cmpl.strictExt_of (weX D.a) fun p op hop => ?_
  obtain ⟨e, he, hw, c, s, pt, hm, rfl⟩ := extOf_found D.a D.base.cfg sto p op hop
  have hidx : p.elim (·.val) (·.val) ∈ e.2.2.idx := (List.of_mem_zip hm).1
  have hsalt : s ∈ e.2.2.salts :=
    (List.of_mem_zip (List.of_mem_zip (List.of_mem_zip hm).2).2).1
  have hsize : s.size = D.base.plan.salt :=
    (TieTree.ok_spec e.2.2 D.base.plan.salt e.2.1 (hs.ok e he)).2.2.1 s hsalt
  have hpos : xPos (2 ^ D.a) (e.1, p.elim (·.val) (·.val)) = some p := by
    rw [hw]
    exact xPos_back (2 ^ D.a) p
  refine ⟨decide_eq_true (mem_readOf D.a sto e he _ hidx p hpos), ?_⟩
  show (leafSalt D.base.cfg s).length = 256 + 8 * D.base.plan.salt
  rw [length_leafSalt, hc, hsize]

/-- Given `StoOK`: at a place that an opening of sto lists, the string that the verifier builds
holds the place and the listed column. -/
theorem ext_symbol (r0 r1 : ByteArray) (sto : List (Bool × ℕ × OpenB))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto) (e : Bool × ℕ × OpenB)
    (he : e ∈ sto) (x : ℕ) (col : List UInt64) (hx : (x, col) ∈ e.2.2.idx.zip e.2.2.cols) :
    ∃ p, xPos (2 ^ D.a) (e.1, x) = some p ∧
      (twoExternalStrings (2 ^ D.a) SgX).rd ((weX D.a).build fun p =>
                      (extOf D.a D.base.cfg (tabsOf sto) p).map Opening.sym) p = (x, col) := by
  have hlt : x < 2 ^ D.a := by
    rw [← hs.depth e he]
    exact (TieTree.ok_list e.2.2 D.base.plan.salt e.2.1 (hs.ok e he)).2.1 x (List.of_mem_zip hx).1
  obtain ⟨p, hp, hw, hv⟩ := xPos_at (2 ^ D.a) e.1 x hlt
  obtain ⟨s, pt, hat⟩ := extOf_at_listed D.a D.base.cfg D.base.plan.salt sto hs.once e he
    (hs.ok e he) x col hx p hw hv
  have hsym : (extOf D.a D.base.cfg (tabsOf sto) p).map Opening.sym = some (x, col) := by
    rw [hat]
    rfl
  exact ⟨p, hp, (WireE.two_ok (2 ^ D.a) SgX (0, [])).build_rd
    (fun p => (extOf D.a D.base.cfg (tabsOf sto) p).map Opening.sym) p (x, col) hsym⟩

end


end TypedOracleCompiler.Run.PQ
