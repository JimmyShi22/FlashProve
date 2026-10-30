-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/WholePaths.lean: THE FORESTS' HALF OF THE TIE, AT WHOLE PATHS: THE LAX VERIFIER's
CHECKS OF OPENINGS (afterB: checksB | checksExt, then runChecks: each opened position climbed alone
along its own path) SAY YES UNDER ORACLE FUNCTIONS g, IF g ANSWERS AT LEAVES AND VERTICES AS THE
FILE's HASH CALLS DO AND EACH PATH WAS LOOKED UP IN A RECORD OF THE VERTICES MET. Lemmas with
proofs. A piece of "the tie at H_b" for a proof file (LinkF) and a key (LinkK).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. OnBytes/TypedOracleCompiler's engine for forests is at pruned walks (checkPrunedOpenings). Said afresh here, for afterB.
I. ON BYTES (no typed thing):
  octF_one               the library's pruned walk at ONE leaf along a whole path is the climb along
                         that path: octF hN p.length [x] [c] p = [climbF hN p x c]
  pathFrom_zero | _succ the library's look-up of a whole path (Run/ParseFull.lean: pathFrom), level
  by level: the sibling's value at (a + 1, sibOf x), then the path of the parent (a, x / 2)
  SeenOk vert root seen   FACTS ON A RECORD OF VERTICES (depth, place, value), in terms of the
                          look-up seenAt (which gives ONE value a vertex: the first): the vertex (0,
                          0) has the value root; where both children of a vertex have values, the
                          vertex has vert of them ("closed under parents up to the root"); every
                          value has 32 bytes
  RowOk vert a root lf x path   WHAT IS ASKED OF ONE SHOWN PLACE: x < 2 ^ a; the leaf's digest lf
                                has 32 bytes; path is a list p of a strings of 32 bytes, as digests;
                                climbed alone along p ON BYTES, lf at x reaches root
  rowOk_of_seen      SeenOk, the leaf's value and the path both looked up in seen ⇒ RowOk
  rowOk_of_oct       the conclusion of THE LIBRARY's THEOREM Run/WalkPaths.lean: opening_paths (at a
                     yes of the format's reader of an opening, for every listed place) ⇒ RowOk: SO
                     WHERE THE READING IS readOpeningW's, SeenOk NEED NOT BE ASSUMED
II. TYPED, UNDER g:
  NodeLaw g vert         THE ROW LAW AT VERTICES, A HYPOTHESIS (no family, no page is named; as
                         Run/ReqClimb.lean's RowLaws.node): g at node (l, r), l and r of 256 bits,
                         is vert (l's bytes) (r's bytes) as a digest; vert gives 32 bytes
  nodeF_law, climbF_dig  the typed climb on digests is the climb on bytes
  runCheck_det, runChecks_true      one check's run under g; a list of checks each of which says yes
                                    says yes
  runCheck_row       NodeLaw, RowOk, THE ROW LAW AT THIS LEAF (g at leaf inp = lf as a digest) ⇒ the
                     check ⟨inp, x, path, root as a digest, a⟩ says yes, and is well formed
III. ONE TREE (local | shared alike: the place function is a parameter):
  TreeGood P …, tree_all        every check that checksComp makes comes from a read position with
                                its opening (OnBytes/TypedOracleCompiler's inv_checksComp): so a property of all
                                such holds of all checks
IV. THE FOREST: inv_checksTrees; CompGood, comp_all (all trees of a component); GoodAt, checksB_all
(all rounds); checksExt_all (the stored strings)
V.  checks_yes       GoodAt and the stored strings' like, at the property "says yes under g and is
                     well formed" ⇒ (runChecks (a ++ b)).det g = true and all of a ++ b are well
                     formed: afterB's two clauses on the openings' checks
WHAT IS NOT SAID. THAT ANY FAMILY HAS THE ROW LAWS. That a typing's string meets GoodAt (for
assembleF: Slice/…: not here). That every read position HAS an opening (checksB = some …): the
chain's half gives what is read. That the root in which a walk ends is the root SENT. THAT SeenOk
HOLDS OF A REAL OPENING's RECORD IS SHOWN NOWHERE (its second clause is by reading of the pruned
walk: a vertex both of whose children were met was computed); rowOk_of_oct does not lean on it.
afterB's other clauses (at most nOpen checks; depth ≤ maxDepth; the request tree; the decision).
Nothing on soundness: these are identities of computations.

Terms: lean/GLOSSARY.md.

-/
import Run.WalkPaths
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestFacts

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open Octopus (sibOf)

/-! ## I. On bytes -/

/-- the pruned walk at one leaf along a whole path is the climb along that path -/
theorem octF_one {D : Type} [Inhabited D] (hN : D → D → D) :
    ∀ (p : List D) (x : ℕ) (c : D), Octopus.octF hN p.length [x] [c] p = [climbF hN p x c]
  | [], _, _ => rfl
  | s :: p, x, c => by
      rw [climbF_cons]
      exact octF_one hN p (x / 2) (Octopus.loneF hN x c s)

theorem pathFrom_zero (seen : List (ℕ × ℕ × ByteArray)) (x : ℕ) : pathFrom 0 seen x = some [] := rfl

theorem pathFrom_succ (a : ℕ) (seen : List (ℕ × ℕ × ByteArray)) (x : ℕ) :
    pathFrom (a + 1) seen x =
      (seenAt seen (a + 1) (sibOf x)).bind fun s => (pathFrom a seen (x / 2)).map fun p =>
          bytesToDig s :: p := by
  unfold pathFrom
  rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
  have e2 : ((fun k => (seenAt seen (a + 1 - k) ((x / 2 ^ k) ^^^ 1)).map bytesToDig) ∘ Nat.succ) =
      fun k => (seenAt seen (a - k) (((x / 2) / 2 ^ k) ^^^ 1)).map bytesToDig := by
    funext t
    show (seenAt seen (a + 1 - (t + 1)) ((x / 2 ^ (t + 1)) ^^^ 1)).map bytesToDig = _
    rw [Nat.add_sub_add_right, Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
  show (do
      let y ← (seenAt seen (a + 1 - 0) ((x / 2 ^ 0) ^^^ 1)).map bytesToDig
      let ys ← (List.range a).mapM
        ((fun k => (seenAt seen (a + 1 - k) ((x / 2 ^ k) ^^^ 1)).map bytesToDig) ∘ Nat.succ)
      pure (y :: ys)) = _
  rw [e2, Nat.sub_zero, Nat.pow_zero, Nat.div_one, WalkTie.xor_one]
  cases seenAt seen (a + 1) (sibOf x) with
  | none => rfl
  | some s =>
    cases (List.range a).mapM fun k => (seenAt seen (a - k) (((x / 2) / 2 ^ k) ^^^ 1)).map
        bytesToDig with
    | none => rfl
    | some p => rfl

/-- Facts on a record of vertices. -/
structure SeenOk (vert : ByteArray → ByteArray → ByteArray) (root : ByteArray)
    (seen : List (ℕ × ℕ × ByteArray)) :
    Prop where
  /-- the root's own value -/
  top : seenAt seen 0 0 = some root
  /-- closed under parents -/
  up : ∀ (d q : ℕ) (l r : ByteArray), seenAt seen (d + 1) (2 * q) = some l →
      seenAt seen (d + 1) (2 * q + 1) = some r →
    seenAt seen d q = some (vert l r)
  /-- every value has 32 bytes -/
  size : ∀ (d p : ℕ) (v : ByteArray), seenAt seen d p = some v → v.size = 32

/-- What is asked of one shown place. -/
structure RowOk (vert : ByteArray → ByteArray → ByteArray) (a : ℕ) (root lf : ByteArray) (x : ℕ)
    (path : List (Dig 256)) : Prop where
  lt : x < 2 ^ a
  leaf32 : lf.size = 32
  climb : ∃ p : List ByteArray, path = p.map bytesToDig ∧ p.length = a ∧ (∀ q ∈ p, q.size = 32) ∧
    climbF vert p x lf = root

/-- From the facts on a record. -/
theorem rowOk_of_seen {vert : ByteArray → ByteArray → ByteArray} {root : ByteArray}
    {seen : List (ℕ × ℕ × ByteArray)} (S : SeenOk vert root seen) :
    ∀ (a x : ℕ) (lf : ByteArray) (path : List (Dig 256)), x < 2 ^ a → seenAt seen a x = some lf →
      pathFrom a seen x = some path → RowOk vert a root lf x path
  | 0, x, lf, path, hx, hl, hp => by
      have hx0 : x = 0 := by simpa using hx
      subst hx0
      obtain rfl : [] = path := Option.some.inj hp
      obtain rfl : root = lf := Option.some.inj (S.top.symm.trans hl)
      exact ⟨hx, S.size _ _ _ hl, [], rfl, rfl, fun _ h => absurd h List.not_mem_nil, rfl⟩
  | a + 1, x, lf, path, hx, hl, hp => by
      rw [pathFrom_succ] at hp
      obtain ⟨s, hs, hp⟩ := Option.bind_eq_some_iff.1 hp
      obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
      have hx2 : x / 2 < 2 ^ a := by
        rw [Nat.pow_succ] at hx
        omega
      have hpar : seenAt seen a (x / 2) = some (if x % 2 = 0 then vert lf s else vert s lf) := by
        by_cases h0 : x % 2 = 0
        · rw [if_pos h0]
          have e1 : 2 * (x / 2) = x := by omega
          have e2 : 2 * (x / 2) + 1 = sibOf x := by unfold sibOf; rw [if_pos h0]; omega
          exact S.up a (x / 2) lf s (by rw [e1]; exact hl) (by rw [e2]; exact hs)
        · rw [if_neg h0]
          have e1 : 2 * (x / 2) + 1 = x := by omega
          have e2 : 2 * (x / 2) = sibOf x := by unfold sibOf; rw [if_neg h0]; omega
          exact S.up a (x / 2) s lf (by rw [e2]; exact hs) (by rw [e1]; exact hl)
      obtain ⟨-, -, p, rfl, hlen, h32, hc⟩ := rowOk_of_seen S a (x / 2) _ p' hx2 hpar hp'
      refine ⟨hx, S.size _ _ _ hl, s :: p, rfl, by rw [List.length_cons, hlen], fun q hq => ?_, ?_⟩
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact S.size _ _ _ hs
        · exact h32 q hq
      · rw [climbF_cons]
        exact hc

/-- From the conclusion of the library's opening_paths. -/
theorem rowOk_of_oct {vert : ByteArray → ByteArray → ByteArray} {a x : ℕ} {root lf : ByteArray}
    (hx : x < 2 ^ a)
    (hl : lf.size = 32) {p : List ByteArray} (hlen : p.length = a) (h32 : ∀ q ∈ p, q.size = 32)
    (ho : Octopus.octF vert a [x] [lf] p = [root]) : RowOk vert a root lf x (p.map bytesToDig) := by
  subst hlen
  rw [octF_one] at ho
  exact ⟨hx, hl, p, rfl, rfl, h32, List.head_eq_of_cons_eq ho⟩

/-! ## II. Typed, under oracle functions -/

section
variable {I X : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L))

/-- The row law at vertices. -/
structure NodeLaw (vert : ByteArray → ByteArray → ByteArray) : Prop where
  node : ∀ l r : Bits, l.length = 256 → r.length = 256 →
    (g TypedOracleCompiler.Compile.Batch.OracleName.node ((l, r) : Bits × Bits) : Dig 256) =
      bytesToDig (vert (bitsToBytes l) (bitsToBytes r))
  size : ∀ l r : ByteArray, (vert l r).size = 32

variable {g} {vert : ByteArray → ByteArray → ByteArray}

theorem nodeF_law (N : NodeLaw g vert) (a c : ByteArray) (ha : a.size = 32) (hc : c.size = 32) :
    nodeF g (bytesToDig a) (bytesToDig c) = bytesToDig (vert a c) := by
  have e := N.node (List.ofFn (bytesToDig a)) (List.ofFn (bytesToDig c)) List.length_ofFn
      List.length_ofFn
  have ea : bitsToBytes (List.ofFn (bytesToDig a)) = a := _root_.Run.TieTree.dig_bytes a ha
  have ec : bitsToBytes (List.ofFn (bytesToDig c)) = c := _root_.Run.TieTree.dig_bytes c hc
  rw [ea, ec] at e
  exact e

/-- the typed climb on digests is the climb on bytes -/
theorem climbF_dig (N : NodeLaw g vert) :
    ∀ (p : List ByteArray) (x : ℕ) (c : ByteArray), c.size = 32 → (∀ q ∈ p, q.size = 32) →
      climbF (nodeF g) (p.map bytesToDig) x (bytesToDig c) = bytesToDig (climbF vert p x c)
  | [], _, _, _, _ => rfl
  | s :: p, x, c, hc, hp => by
      have hs : s.size = 32 := hp s List.mem_cons_self
      have hp' : ∀ q ∈ p, q.size = 32 := fun q h => hp q (List.mem_cons_of_mem _ h)
      rw [List.map_cons, climbF_cons, climbF_cons]
      by_cases h0 : x % 2 = 0
      · rw [if_pos h0, if_pos h0, nodeF_law N c s hc hs]
        exact climbF_dig N p _ _ (N.size _ _) hp'
      · rw [if_neg h0, if_neg h0, nodeF_law N s c hs hc]
        exact climbF_dig N p _ _ (N.size _ _) hp'

variable (g)

/-- one check's run under g -/
theorem runCheck_det (c : Check 256 L) :
    (runCheck (K := K) c).det g =
      decide (climbF (nodeF g) c.path c.j (g TypedOracleCompiler.Compile.Batch.OracleName.leaf c.inp : Dig 256)
          = c.root) := by
  simp only [TypedOracleCompiler.Compile.Batch.runCheck, det_bind', det_pure', det_askV]
  exact congrArg (fun r => decide (r = c.root))
    (Evaluates.climbM (_root_.Compile.Batch.Seed.evalO g) (qN := hashTreeNode (L := L) (K := K))
        (hN := nodeF g)
      (fun _ _ => rfl) c.path c.j _)

theorem runChecks_true : ∀ cs : List (Check 256 L), (∀ c ∈ cs, (runCheck (K := K) c).det g = true) →
    (runChecks (K := K) cs).det g = true
  | [], _ => rfl
  | c :: cs, h => by
      simp only [TypedOracleCompiler.Compile.Batch.runChecks, det_bind', det_pure', h c List.mem_cons_self,
        runChecks_true cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc'), Bool.and_self]

variable {g}

/-- says yes under g, and is well formed -/
def Yes (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L)) (c : Check 256 L) : Prop :=
  (runCheck (K := K) c).det g = true ∧ c.wellFormed = true

/-- One shown place. -/
theorem runCheck_row (N : NodeLaw g vert) {a x : ℕ} {root lf : ByteArray} {path : List (Dig 256)}
    (R : RowOk vert a root lf x path) (inp : LeafIn L)
    (hleaf : (g TypedOracleCompiler.Compile.Batch.OracleName.leaf inp : Dig 256) = bytesToDig lf) :
    Yes g (⟨inp, x, path, bytesToDig root, a⟩ : Check 256 L) := by
  obtain ⟨p, rfl, hlen, h32, hc⟩ := R.climb
  refine ⟨?_, ?_⟩
  · rw [runCheck_det]
    show decide (climbF (nodeF g) (p.map bytesToDig) x
        (g TypedOracleCompiler.Compile.Batch.OracleName.leaf inp : Dig 256) =
      bytesToDig root) = true
    rw [hleaf, climbF_dig N p x lf R.leaf32 h32, hc]
    exact decide_eq_true rfl
  · show (decide ((p.map bytesToDig).length = a) && decide (x < 2 ^ a)) = true
    rw [List.length_map, hlen, decide_eq_true rfl, decide_eq_true R.lt]
    rfl

end

/-! ## III. One tree -/

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (P : Check lam L → Prop)

/-- the property holds of the check of every read position of a tree that has an opening -/
def TreeGood {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : Dig lam) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
        Prop :=
  ∀ (j : ℕ) (p : r.Pos) (op : Opening lam (r.Sym p)), j < 2 ^ depth → posAt j = some p →
      isRead p = true →
    f p = some op → P ⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩

/-- One tree: it holds of all checks. -/
theorem tree_all {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : Dig lam) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : TreeGood P posAt depth emb rt isRead f) (cs : List (Check lam L))
    (e : checksComp posAt depth emb rt isRead f (List.range (2 ^ depth)) = some cs) : ∀ c ∈ cs,
        P c := fun c hc => by
  obtain ⟨p, op, hj, hp, hr, hf, hceq⟩ := inv_checksComp posAt depth emb rt isRead f _ cs e c hc
  rw [hceq]
  exact h c.j p op (List.mem_range.1 hj) hp hr hf

/-! ## IV. The forest -/

/-- what checksTrees yields: tree by tree, checksComp's value -/
theorem inv_checksTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds rt = some l →
      ∀ z ∈ l, ∃ i, ds[i]? = some z.1 ∧ rt[i]? = some z.2.1 ∧
        checksComp (posAt (k + i)) z.1 emb z.2.1 isRead f (List.range (2 ^ z.1)) = some z.2.2
  | _, [], _, l, h, z, hz => by
      simp only [checksTrees] at h
      obtain rfl := Option.some.inj h
      cases hz
  | _, _ :: _, [], l, h, z, hz => by
      simp only [checksTrees] at h
      obtain rfl := Option.some.inj h
      cases hz
  | k, d0 :: ds, c0 :: rt, l, h, z, hz => by
      simp only [checksTrees] at h
      cases h1 : checksComp (posAt k) d0 emb c0 isRead f (List.range (2 ^ d0)) with
      | none => rw [h1] at h; cases h
      | some a =>
        cases h2 : checksTrees posAt emb isRead f (k + 1) ds rt with
        | none => rw [h1, h2] at h; cases h
        | some b =>
          rw [h1, h2] at h
          obtain rfl := Option.some.inj h
          rcases List.mem_cons.1 hz with rfl | hz
          · exact ⟨0, rfl, rfl, h1⟩
          · obtain ⟨i, e1, e2, e3⟩ := inv_checksTrees posAt emb isRead f (k + 1) ds rt b h2 z hz
            exact ⟨i + 1, by simpa using e1, by simpa using e2, by rwa [show k + (i + 1) = k + 1 + i by omega]⟩

/-- the property holds at every tree of a component that has a depth and a root -/
def CompGood {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : List (Dig lam)) (isRead : r.Pos → Bool) (f : (p : r.Pos) →
        Option (Opening lam (r.Sym p))) : Prop :=
  ∀ (k d : ℕ) (c : Dig lam), depth[k]? = some d → rt[k]? = some c →
      TreeGood P (posAt k) d emb c isRead f

theorem comp_all {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : List (Dig lam)) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : CompGood P posAt depth emb rt isRead f) (cs : List (Check lam L))
    (e : checksOpt posAt depth emb rt isRead f = some cs) : ∀ c ∈ cs, P c := fun c hc => by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨z, hz, hcz⟩ := List.mem_flatMap.1 hc
  obtain ⟨i, e1, e2, e3⟩ := inv_checksTrees posAt emb isRead f 0 depth rt l hl z hz
  rw [Nat.zero_add] at e3
  exact tree_all P (posAt i) z.1 emb z.2.1 isRead f (h i z.1 z.2.1 e1 e2) z.2.2 e3 c hcz

/-- the property holds at every tree of every round -/
def GoodAt : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → OSym s p → Body L) → RootsOfChain lam s →
    (OPos s → Bool) → ((p : OPos s) → Option (Opening lam (OSym s p))) → Prop
  | [], _, _, _, _, _, _ => True
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f =>
      CompGood P w.posAt0 w.depth0 (fun p => emb (.inl p)) (rt.1.getD []) (fun p => isRead (.inl p))
        (fun p => f (.inl p)) ∧
      CompGood P w.posAtJ w.depthJ (fun p => emb (.inl p)) (rt.2.getD []) (fun p => isRead (.inl p))
        (fun p => f (.inl p)) ∧
      GoodAt s A W (fun p => emb (.inr p)) rts (fun p => isRead (.inr p)) (fun p => f (.inr p))

/-- All rounds. -/
theorem checksB_all : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (emb : (p : OPos s) → OSym s p → Body L)
    (rts : RootsOfChain lam s) (isRead : OPos s → Bool) (f : (p : OPos s) → Option (Opening lam (OSym s p))),
    GoodAt P s A W emb rts isRead f → ∀ cs, checksB s A W emb rts isRead f = some cs → ∀ c ∈ cs, P c
  | [], _, _, _, _, _, _, _, cs, e, c, hc => by
      obtain rfl : [] = cs := Option.some.inj e
      cases hc
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f, h, cs, e, c, hc => by
      simp only [checksB] at e
      split at e
      · rename_i a b c' ha hb hc'
        obtain rfl := Option.some.inj e
        rcases List.mem_append.1 hc with hc | hc
        · rcases List.mem_append.1 hc with hc | hc
          · exact comp_all P _ _ _ _ _ _ h.1 a ha c hc
          · exact comp_all P _ _ _ _ _ _ h.2.1 b hb c hc
        · exact checksB_all s A W _ rts _ _ h.2.2 c' hc' c hc
      · cases e

/-- The stored strings. -/
theorem checksExt_all {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym))
    (h : ∀ (p : E.Pos) (op : Opening lam E.Sym), isRead p = true → f p = some op →
      P ⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path, cms.getD (we.which p) default, we.depth⟩) :
    ∀ (ps : List E.Pos) (cs : List (Check lam L)), checksExt we emb cms isRead f ps = some
        cs → ∀ c ∈ cs, P c
  | [], cs, e, c, hc => by
      obtain rfl : [] = cs := Option.some.inj e
      cases hc
  | p :: ps, cs, e, c, hc => by
      simp only [TypedOracleCompiler.Compile.Batch.checksExt] at e
      split_ifs at e with hr
      · split at e
        · rename_i op cs' hop hcs
          obtain rfl := Option.some.inj e
          rcases List.mem_cons.1 hc with rfl | hc
          · exact h p op hr hop
          · exact checksExt_all we emb cms isRead f h ps cs' hcs c hc
        · cases e
      · exact checksExt_all we emb cms isRead f h ps cs e c hc

end

/-! ## V. afterB's two clauses on the openings' checks -/

/-- The checks of the openings say yes, and are well formed. -/
theorem checks_yes {I X : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X}
    (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L)) {E : ExtSpec}
    (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout 256 K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (rts : RootsOfChain 256 s)
    (isRead : OPos s → Bool) (f : (p : OPos s) → Option (Opening 256 (OSym s p)))
    (we : WireE E) (embE : E.Sym → Body L) (cms : List (Dig 256)) (isReadE : E.Pos → Bool)
    (fE : E.Pos → Option (Opening 256 E.Sym))
    (h : GoodAt (Yes g) s A W embS rts isRead f)
    (hE : ∀ (p : E.Pos) (op : Opening 256 E.Sym), isReadE p = true → fE p = some op →
      Yes g ⟨⟨embE op.sym, op.salt⟩, we.leaf p, op.path, cms.getD (we.which p) default, we.depth⟩)
    (a b : List (Check 256 L)) (ha : checksB s A W embS rts isRead f = some a)
    (hb : checksExt we embE cms isReadE fE we.all = some b) :
    (runChecks (K := K) (a ++ b)).det g = true ∧ (a ++ b).all (fun c => c.wellFormed) = true := by
  have hall : ∀ c ∈ a ++ b, Yes g c := fun c hc => by
    rcases List.mem_append.1 hc with hc | hc
    · exact checksB_all (Yes g) s A W embS rts isRead f h a ha c hc
    · exact checksExt_all (Yes g) we embE cms isReadE fE hE we.all b hb c hc
  exact ⟨runChecks_true g _ fun c hc => (hall c hc).1, List.all_eq_true.2 fun c hc => (hall c hc).2⟩

end TypedOracleCompiler.Run
