-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ForestSound.lean: a form of Compile/Batch/ForestSound.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Compile/Batch/ForestSound.lean, comments apart: statements:
`repath_opt`; proofs alone: `mkTr_reP`, `repath_B`; only here: `repath_comp`, `repath_trees`; not
here: `checksOpt_reP`. Every other declaration has that file's text.

Where the head below explains the fields of a `WireRB`: here `depth0`, `depthJ` are the lists of the
depths of the trees over the shared component and over a slot's component; `tree` and `place` say in
which tree of its component a position is, and where among that tree's leaves. One flag (`pr0`,
`prJ`) serves all trees of a component.

The rest of this head is the head of Compile/Batch/ForestSound.lean, to be read with these changes;
the files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that
name, this folder's.

Compile/Batch/ForestSound.lean: for a well-formed wire record, what the verifier with pruned Merkle
paths accepts, the verifier with full paths accepts with other paths, from the same trace (words of
this library: lean/GLOSSARY.md).

The last part `checkPrunedOpenings` of the strict verifier `verifyOneProtocol` (Compile/Batch/Verifier.lean) verifies the
opened leaves of a tree together where the tree's flag in the wire record is set, and then uses only
some digests of the paths in its proof string; soundness (Compile/Batch/Sound.lean) is proved for
`verifyB`, whose last part `afterB` verifies every path.
  `repath_opt`, `repath_B`, `repath_Ext`
      if every check has some good path (`GoodPath`), there is one assignment of paths to positions
      under which all checks are good. Here the conditions on the wire record are used: a position
      is at one leaf of one tree. For the external strings: the list holds every position (`hps`).
  `runsIn_afterB_of_afterBO`, `runsIn_verifyB_of_strict`
      the two theorems. No query is added, so no soundness bound changes.

Notation: `π`: a `OneProtocolProof lam Q` (Compile/Batch/Verifier.lean), the proof string of a slot;
`π.withPaths P1 P2`: the proof string π with other paths in its openings (P1: in `opens`, P2: in
`ext`); `reP f P`: the openings f with their paths replaced by those of P; in
`afterB … depthReq cms x π ρ rts ph` (Compile/Batch/Verifier.lean): ρ: the verifier messages, rts:
the roots round by round, ph: the last phase; in a `WireRB` (Iop/BatchWire.lean): `depth0`,
`depthJ`: the depth of the tree over the shared component m_0, over a slot's component m_j; so 0 and
J in `posAt0`, `posAtJ`; `place`: where a position is among the leaves of the tree of its component;
`a.own` (`RAnn`, Iop/Batch.lean): to which part an oracle position belongs; `depthReq` (`QueryLayout`,
Iop/BatchWire.lean): depth of a request tree.

Limits: the paths are not computed; they are shown to exist (the proof of `octSound`,
Compile/OctopusRom.lean, reads them off the trace). Nothing is said on a wire record that is not
well-formed.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestFacts
import OnBytes.TypedOracleCompiler.Compile.Batch.Runs

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Openings with other paths -/

/-- the path of P at the position of leaf j -/
def pathJ {ι : Type} (posAt : ℕ → Option ι) (P : ι → List (Dig lam)) (j : ℕ) : List (Dig lam) :=
  match posAt j with
  | some p => P p
  | none => []

theorem checksComp_reP {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    ∀ js : List ℕ, checksComp posAt depth emb rt isRead (reP f P) js =
      (checksComp posAt depth emb rt isRead f js).map
        (List.map fun c => c.withPath (pathJ posAt P c.j))
  | [] => rfl
  | j :: js => by
      have ih := checksComp_reP posAt depth emb rt isRead f P js
      simp only [checksComp]
      cases hp : posAt j with
      | none => exact ih
      | some p =>
        simp only []
        split_ifs
        · rw [ih]
          unfold reP
          cases f p with
          | none => rfl
          | some op =>
            cases checksComp posAt depth emb rt isRead f js with
            | none => rfl
            | some cs =>
              simp only [Option.map_some, List.map_cons, Check.withPath, pathJ, hp]
        · exact ih

/-! Here: checksOpt_reP of the library is not said: repath_comp below uses checksComp_reP tree by
tree. -/

theorem mkTr_reP :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s) (pls : Plains s) (ρ : Rho s)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))) (P : OPos s → List (Dig lam)),
      mkTr s A W rts pls ρ (reP f P) = mkTr s A W rts pls ρ f
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), (rt, rts), (pl, pls), (c, ρ), f, P => by
      have ih := mkTr_reP s A W rts pls ρ (fun p => f (.inr p)) (fun p => P (.inr p))
      show ((w.pt.ofSyms _, effPlain a rt pl),
          c,
          mkTr s A W rts pls ρ (reP (fun p => f (.inr p)) fun p => P (.inr p))) =
        ((w.pt.ofSyms _, effPlain a rt pl), c, mkTr s A W rts pls ρ fun p => f (.inr p))
      rw [ih]
      refine congrArg
        (fun o => ((w.pt.ofSyms o, effPlain a rt pl), c, mkTr s A W rts pls ρ fun p => f (.inr p)))
        (funext fun p => ?_)
      unfold reP
      generalize f (Sum.inl p) = o
      generalize rootAt w rt p = b
      cases b <;> cases o <;> rfl

/-! ## One assignment of paths for all checks -/

section Repath
variable {tr : Trace (typedOracleFamily lam K L)}

/-- the path has the length of the tree's depth, and the check with this path accepts from the trace
-/
def GoodPath (tr : Trace (typedOracleFamily lam K L)) (c : Check lam L) (path : List (Dig lam)) : Prop :=
  path.length = c.depth ∧ RunsIn tr (runCheck (K := K) (c.withPath path)) true

/-- cs' has the length of cs; each of its checks is one of cs with a good path -/
def Repathed (tr : Trace (typedOracleFamily lam K L)) (cs cs' : List (Check lam L)) : Prop :=
  cs'.length = cs.length ∧ ∀ c' ∈ cs', ∃ c ∈ cs, ∃ path, c' = c.withPath path ∧ GoodPath tr c path

theorem Repathed.append {a a' b b' : List (Check lam L)}
    (h1 : Repathed tr a a') (h2 : Repathed tr b b') :
    Repathed tr (a ++ b) (a' ++ b') := by
  refine ⟨by rw [List.length_append, List.length_append, h1.1, h2.1], fun c' hc' => ?_⟩
  rcases List.mem_append.1 hc' with h | h
  · obtain ⟨c, hc, path, e, g⟩ := h1.2 c' h
    exact ⟨c, List.mem_append_left _ hc, path, e, g⟩
  · obtain ⟨c, hc, path, e, g⟩ := h2.2 c' h
    exact ⟨c, List.mem_append_right _ hc, path, e, g⟩

/-- Here: one tree (the library's repath_opt, in the case that there is a root) -/
theorem repath_comp {r : Round} (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (depth : ℕ) (emb : (p : r.Pos) → r.Sym p → Body L)
    (x : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (cs : List (Check lam L))
    (h : checksComp posAt depth emb x isRead f (List.range (2 ^ depth)) = some cs)
    (hall : ∀ c ∈ cs, ∃ path, GoodPath tr c path) :
    ∃ P : r.Pos → List (Dig lam), ∀ P' : r.Pos → List (Dig lam),
      (∀ j p, posAt j = some p → P' p = P p) →
      ∃ cs', checksComp posAt depth emb x isRead (reP f P') (List.range (2 ^ depth)) = some cs' ∧
        Repathed tr cs cs' := by
    have hinv := inv_checksComp posAt depth emb x isRead f _ cs h
    have huniq : ∀ c ∈ cs, ∀ c' ∈ cs, c.j = c'.j → c = c' := by
      intro c hc c' hc' hj
      obtain ⟨p, op, -, h1, -, h2, h3⟩ := hinv c hc
      obtain ⟨p', op', -, h1', -, h2', h3'⟩ := hinv c' hc'
      rw [hj, h1'] at h1
      obtain rfl := Option.some.inj h1
      rw [h2'] at h2
      obtain rfl := Option.some.inj h2
      rw [h3, h3', hj]
    have hex : ∀ p, ∃ path, ∀ c ∈ cs, c.j = place p → GoodPath tr c path := by
      intro p
      by_cases hp : ∃ c ∈ cs, c.j = place p
      · obtain ⟨c, hc, hj⟩ := hp
        obtain ⟨path, hg⟩ := hall c hc
        exact ⟨path, fun c' hc' hj' => by rw [huniq c' hc' c hc (hj'.trans hj.symm)]; exact hg⟩
      · exact ⟨[], fun c hc hj => absurd ⟨c, hc, hj⟩ hp⟩
    choose P hP using hex
    refine ⟨P, fun P' hP' => ⟨_, by rw [checksComp_reP, h]; rfl, by simp, fun c' hc' => ?_⟩⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨p, op, -, h1, -, -, -⟩ := hinv c hc
    refine ⟨c, hc, _, rfl, ?_⟩
    have e : pathJ posAt P' c.j = P p := by
      unfold pathJ
      rw [h1]
      exact hP' _ p h1
    rw [e]
    exact hP p c hc (hpl _ p h1).symm

/-- Here: the trees of a component from number k on. A position stands in one tree (hpl): so the
assignments of paths, tree by tree, are one assignment. -/
theorem repath_trees {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (tree place : r.Pos → ℕ)
    (hpl : ∀ k j p, posAt k j = some p → tree p = k ∧ place p = j)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds rt = some l →
      (∀ c ∈ l.flatMap (fun z => z.2.2), ∃ path, GoodPath tr c path) →
      ∃ P : r.Pos → List (Dig lam), ∀ P' : r.Pos → List (Dig lam),
        (∀ k' j p, k ≤ k' → posAt k' j = some p → P' p = P p) →
        ∃ l', checksTrees posAt emb isRead (reP f P') k ds rt = some l' ∧
          Repathed tr (l.flatMap fun z => z.2.2) (l'.flatMap fun z => z.2.2)
  | _, [], _, l, h, _ => by
      simp only [checksTrees] at h
      cases h
      exact ⟨fun _ => [], fun P' _ => ⟨[], by simp only [checksTrees], rfl, fun _ h => by cases h⟩⟩
  | _, _ :: _, [], l, h, _ => by
      simp only [checksTrees] at h
      cases h
      exact ⟨fun _ => [], fun P' _ => ⟨[], by simp only [checksTrees], rfl, fun _ h => by cases h⟩⟩
  | k, d :: ds, x :: rt, l, h, hall => by
      simp only [checksTrees] at h
      split at h
      · rename_i a b ha hb
        obtain rfl := Option.some.inj h
        obtain ⟨Pk, hPk⟩ := repath_comp (tr := tr) (posAt k) place
          (fun j p hp => (hpl k j p hp).2) d emb x isRead f a ha
          fun c hc => hall c (by rw [List.flatMap_cons]; exact List.mem_append_left _ hc)
        obtain ⟨Pr, hPr⟩ := repath_trees posAt tree place hpl emb isRead f (k + 1) ds rt b hb
          fun c hc => hall c (by rw [List.flatMap_cons]; exact List.mem_append_right _ hc)
        refine ⟨fun p => if tree p = k then Pk p else Pr p, fun P' hP' => ?_⟩
        obtain ⟨a', ha', ra⟩ := hPk P' fun j p hp =>
          (hP' k j p le_rfl hp).trans (if_pos (hpl k j p hp).1)
        obtain ⟨b', hb', rb⟩ := hPr P' fun k' j p hk hp =>
          (hP' k' j p (by omega) hp).trans (if_neg (by rw [(hpl k' j p hp).1]; omega))
        refine ⟨(d, x, a') :: b', by simp only [checksTrees, ha', hb'], ?_⟩
        rw [List.flatMap_cons, List.flatMap_cons]
        exact ra.append rb
      · cases h

theorem repath_opt {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (tree place : r.Pos → ℕ)
    (hpl : ∀ k j p, posAt k j = some p → tree p = k ∧ place p = j) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (cs : List (Check lam L))
    (h : checksOpt posAt depth emb rt isRead f = some cs)
    (hall : ∀ c ∈ cs, ∃ path, GoodPath tr c path) :
    ∃ P : r.Pos → List (Dig lam), ∀ P' : r.Pos → List (Dig lam),
      (∀ k j p, posAt k j = some p → P' p = P p) →
      ∃ cs', checksOpt posAt depth emb rt isRead (reP f P') = some cs' ∧ Repathed tr cs cs' := by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨P, hP⟩ := repath_trees posAt tree place hpl emb isRead f 0 depth rt l hl hall
  refine ⟨P, fun P' hP' => ?_⟩
  obtain ⟨l', hl', r⟩ := hP P' fun k j p _ hp => hP' k j p hp
  exact ⟨_, by unfold checksOpt; rw [hl']; rfl, r⟩

theorem repath_B :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (emb : (p : OPos s) → OSym s p → Body L) (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
          (f : (p : OPos s) → Option (Opening lam (OSym s p))) (cs : List (Check lam L)),
        checksB s A W emb rts isRead f = some cs → (∀ c ∈ cs, ∃ path, GoodPath tr c path) →
        ∃ (P : OPos s → List (Dig lam)) (cs' : List (Check lam L)),
          checksB s A W emb rts isRead (reP f P) = some cs' ∧ Repathed tr cs cs'
  | [], _, _, _, _, _, _, _, cs, h, _ => by
      obtain rfl : [] = cs := Option.some.inj h
      exact ⟨fun _ => [], [], rfl, rfl, fun _ h => by cases h⟩
  | r :: s, (a, A), (w, W), hW, emb, (rt, rts), isRead, f, cs, h, hall => by
      simp only [checksB] at h
      split at h
      · rename_i c0 cJ c2 h0 hJ h2
        obtain rfl := Option.some.inj h
        obtain ⟨P0, hP0⟩ := repath_opt (tr := tr) w.posAt0 w.tree w.place
          (fun k j p h => (hW.1.place_posAt0 k j p h).2) w.depth0 _ _ _ _ c0 h0
          fun c hc => hall c (List.mem_append_left _ (List.mem_append_left _ hc))
        obtain ⟨PJ, hPJ⟩ := repath_opt (tr := tr) w.posAtJ w.tree w.place
          (fun k j p h => (hW.1.place_posAtJ k j p h).2) w.depthJ _ _ _ _ cJ hJ
          fun c hc => hall c (List.mem_append_left _ (List.mem_append_right _ hc))
        obtain ⟨P2, c2', h2', r2⟩ :=
          repath_B s A W hW.2 _ rts _ _ c2 h2 fun c hc => hall c (List.mem_append_right _ hc)
        let Pl : r.Pos → List (Dig lam) := fun p => if a.own p then PJ p else P0 p
        obtain ⟨c0', h0', r0⟩ := hP0 Pl fun k j p hp => by
          show (if a.own p then PJ p else P0 p) = P0 p
          rw [(hW.1.place_posAt0 k j p hp).1]; rfl
        obtain ⟨cJ', hJ', rJ⟩ := hPJ Pl fun k j p hp => by
          show (if a.own p then PJ p else P0 p) = PJ p
          rw [(hW.1.place_posAtJ k j p hp).1]; rfl
        refine ⟨fun p => match p with | .inl q => Pl q | .inr q => P2 q, c0' ++ cJ' ++ c2',
          ?_, (r0.append rJ).append r2⟩
        have key : ∀ o0 oJ o2 : Option (List (Check lam L)),
            o0 = some c0' → oJ = some cJ' → o2 = some c2' →
            (match o0, oJ, o2 with
              | some a, some b, some c => some (a ++ b ++ c)
              | _, _, _ => none) = some (c0' ++ cJ' ++ c2') := by
          rintro _ _ _ rfl rfl rfl; rfl
        exact key _ _ _ h0' hJ' h2'
      · cases h

theorem checksExt_reP {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) (P : E.Pos → List (Dig lam))
    (hg : ∀ p, isRead p = true →
      ∀ op, g p = some op →
        GoodPath tr
          (⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
            cms.getD (we.which p) default, we.depth⟩ : Check lam L) (P p)) :
    ∀ (ps : List E.Pos) (cs : List (Check lam L)), checksExt we emb cms isRead g ps = some cs →
      ∃ cs', checksExt we emb cms isRead (reP g P) ps = some cs' ∧ Repathed tr cs cs'
  | [], cs, h => by
      obtain rfl : [] = cs := Option.some.inj h
      exact ⟨[], rfl, rfl, fun _ h => by cases h⟩
  | p :: ps, cs, h => by
      simp only [checksExt] at h ⊢
      split_ifs at h ⊢ with hr
      · split at h
        · rename_i op cs0 hop hcs
          obtain rfl := Option.some.inj h
          obtain ⟨cs', h1, h2, h3⟩ := checksExt_reP we emb cms isRead g P hg ps cs0 hcs
          refine ⟨(⟨⟨emb op.sym, op.salt⟩, we.leaf p, P p,
                cms.getD (we.which p) default, we.depth⟩ : Check lam L) :: cs',
            ?_, by simp [h2], fun c' hc' => ?_⟩
          · rw [h1]
            unfold reP
            rw [hop]
            rfl
          · rcases List.mem_cons.1 hc' with rfl | hc'
            · exact ⟨_, List.mem_cons_self, P p, rfl, hg p hr op hop⟩
            · obtain ⟨c, hc, path, e, gd⟩ := h3 c' hc'
              exact ⟨c, List.mem_cons_of_mem _ hc, path, e, gd⟩
        · cases h
      · exact checksExt_reP we emb cms isRead g P hg ps cs h

theorem repath_Ext {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) (ps : List E.Pos)
    (hps : ∀ p, p ∈ ps) (cs : List (Check lam L)) (h : checksExt we emb cms isRead g ps = some cs)
    (hall : ∀ c ∈ cs, ∃ path, GoodPath tr c path) :
    ∃ (P : E.Pos → List (Dig lam)) (cs' : List (Check lam L)),
      checksExt we emb cms isRead (reP g P) ps = some cs' ∧ Repathed tr cs cs' := by
  have hex : ∀ p, ∃ path, isRead p = true →
      ∀ op, g p = some op →
        GoodPath tr
          (⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
            cms.getD (we.which p) default, we.depth⟩ : Check lam L) path := by
    intro p
    by_cases hr : isRead p = true
    · obtain ⟨op, hop, hmem⟩ := mem_checksExt we emb cms isRead g ps cs h p (hps p) hr
      obtain ⟨path, hg⟩ := hall _ hmem
      exact ⟨path,
        fun _ op' hop' => by rw [hop] at hop'; obtain rfl := Option.some.inj hop'; exact hg⟩
    · exact ⟨[], fun h => absurd h hr⟩
  choose P hP using hex
  obtain ⟨cs', h1, h2⟩ := checksExt_reP we emb cms isRead g P hP ps cs h
  exact ⟨P, cs', h1, h2⟩

theorem runsIn_runChecks_of_all :
    ∀ cs : List (Check lam L),
      (∀ c ∈ cs, RunsIn tr (runCheck (K := K) c) true) → RunsIn tr (runChecks (K := K) cs) true
  | [], _ => RunsIn.pure _
  | c :: cs, h =>
      (runsIn_bind_iff _ _ _).2
        ⟨true, h c List.mem_cons_self,
          (runsIn_bind_iff _ _ _).2
            ⟨true, runsIn_runChecks_of_all cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc'),
              RunsIn.pure _⟩⟩

end Repath

/-! ## The theorem -/

/-- For `wq.OKG`: what `checkPrunedOpenings` accepts, `afterB` accepts with other paths, from the same trace. -/
theorem runsIn_afterB_of_afterBO {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q}
    (hwq : wq.OKG) {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
    {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam Q}
    {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam} {tr : Trace (typedOracleFamily lam K L)}
    (h : RunsIn tr (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) true) :
    ∃ P1 P2,
      RunsIn tr (afterB Q wq embS embE depthReq cms x (π.withPaths P1 P2) ρ rts ph) true := by
  unfold checkPrunedOpenings at h
  split at h
  · rename_i Fs hFs
    split_ifs at h with hc
    · obtain ⟨hok, a, b, ha, hb, hflat⟩ := forestsOf_spec hFs
      have h' : RunsIn tr
          ((runForests (K := K) Fs (readsF Fs)).bind fun ok =>
            (reqPart depthReq π ph).bind fun okr =>
              OComp.pure
                (ok && okr &&
                  Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
                    (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens))) true := h
      obtain ⟨ok, hrun, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      have hok1 : ok = true := by
        obtain ⟨okr, -, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
        exact (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h3)).1).1
      subst hok1
      have hwf : ∀ c ∈ flatF Fs,
          c.path.length = c.depth ∧ c.j < 2 ^ c.depth ∧ c.depth ≤ wq.maxDepth := by
        intro c hmem
        have := List.all_eq_true.1 hc.2 c hmem
        simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
        exact ⟨this.1.1, this.1.2, this.2⟩
      have hgood := runForests_sound Fs _ hok (fun c hmem => (hwf c hmem).2.1) hrun
      rw [hflat] at hgood hwf hc
      obtain ⟨P1, a', ha', ra⟩ :=
        repath_B (tr := tr) Q.loc.shape Q.ann wq.sh hwq.sh embS rts _ π.opens a ha
          fun c hmem => hgood c (List.mem_append_left _ hmem)
      obtain ⟨P2, b', hb', rb⟩ :=
        repath_Ext (tr := tr) wq.ext embE cms _ π.ext wq.ext.all hwq.ext.complete b hb
          fun c hmem => hgood c (List.mem_append_right _ hmem)
      have rab := ra.append rb
      refine ⟨P1, P2, ?_⟩
      unfold afterB OneProtocolProof.withPaths
      dsimp only
      rw [ha', hb']
      have hcond : (a' ++ b').length ≤ wq.nOpen ∧
          (a' ++ b').all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) = true := by
        refine ⟨by rw [rab.1]; exact hc.1, List.all_eq_true.2 fun c' hc' => ?_⟩
        obtain ⟨c, hmem, path, rfl, hg⟩ := rab.2 c' hc'
        obtain ⟨-, w2, w3⟩ := hwf c hmem
        simp only [Check.wellFormed, Check.withPath, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hg.1, w2⟩, w3⟩
      dsimp only
      rw [if_pos hcond]
      refine (runsIn_bind_iff _ _ _).2 ⟨true, runsIn_runChecks_of_all _ fun c' hc' => ?_, ?_⟩
      · obtain ⟨c, -, path, rfl, hg⟩ := rab.2 c' hc'
        exact hg.2
      · have e1 : (fun p => (reP π.ext P2 p).map Opening.sym) =
            fun p => (π.ext p).map Opening.sym := by
          funext p
          show ((π.ext p).map _).map _ = _
          cases π.ext p <;> rfl
        rw [e1, mkTr_reP]
        unfold reqPart at h2
        cases hsv : ph.slotVal with
        | none => rw [hsv] at h2; exact h2
        | some c => rw [hsv] at h2; exact h2
    · cases runsIn_pure_iff.1 h
  · cases runsIn_pure_iff.1 h

/-- For `wq.OKG`: what the strict verifier `verifyOneProtocol` accepts, `verifyB` accepts with other paths,
from the same trace. Where a tree's flag is set, `verifyOneProtocol` verifies its opened leaves together and
uses only some digests of the paths; the other proof string is π with full paths that verify from
the trace. -/
theorem runsIn_verifyB_of_strict {sMT sFS : ℕ} {t : Tag} {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q} (hwq : wq.OKG)
    {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
    {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
    {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam Q}
    {tr : Trace (typedOracleFamily lam K L)}
    (h : RunsIn tr (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) true) :
    ∃ P1 P2,
      RunsIn tr (verifyB t Q wq embS embP xin embE depthReq cms x (π.withPaths P1 P2)) true := by
  unfold verifyOneProtocol at h
  obtain ⟨r, hr, h⟩ := (runsIn_bind_iff _ _ _).1 h
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact absurd (runsIn_pure_iff.1 h) (by simp)
  · dsimp only at h
    split_ifs at h
    · obtain ⟨P1, P2, h'⟩ := runsIn_afterB_of_afterBO hwq h
      exact ⟨P1, P2, (runsIn_bind_iff _ _ _).2 ⟨some (ρ, rts, ph), hr, h'⟩⟩
    · exact absurd (runsIn_pure_iff.1 h) (by simp)

end TypedOracleCompiler.Compile.Batch
