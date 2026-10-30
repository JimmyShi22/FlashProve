-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
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
import Compile.Batch.ForestFacts
import Compile.Batch.Runs

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

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

theorem checksOpt_reP {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    checksOpt posAt depth emb rt isRead (reP f P) =
      (checksOpt posAt depth emb rt isRead f).map
        (List.map fun c => c.withPath (pathJ posAt P c.j)) := by
  cases rt with
  | none => rfl
  | some c => exact checksComp_reP posAt depth emb c isRead f P _

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
      generalize rootAt a rt p = b
      cases b <;> cases o <;> rfl

/-! ## One assignment of paths for all checks -/

section Repath
variable {tr : Trace (spec lam K L)}

/-- the path has the length of the tree's depth, and the check with this path accepts from the trace
-/
def GoodPath (tr : Trace (spec lam K L)) (c : Check lam L) (path : List (Dig lam)) : Prop :=
  path.length = c.depth ∧ RunsIn tr (runCheck (K := K) (c.withPath path)) true

/-- cs' has the length of cs; each of its checks is one of cs with a good path -/
def Repathed (tr : Trace (spec lam K L)) (cs cs' : List (Check lam L)) : Prop :=
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

theorem repath_opt {r : Round} (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (depth : ℕ) (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (cs : List (Check lam L))
    (h : checksOpt posAt depth emb rt isRead f = some cs)
    (hall : ∀ c ∈ cs, ∃ path, GoodPath tr c path) :
    ∃ P : r.Pos → List (Dig lam), ∀ P' : r.Pos → List (Dig lam),
      (∀ j p, posAt j = some p → P' p = P p) →
      ∃ cs', checksOpt posAt depth emb rt isRead (reP f P') = some cs' ∧ Repathed tr cs cs' := by
  cases rt with
  | none =>
    obtain rfl : [] = cs := Option.some.inj h
    exact ⟨fun _ => [], fun P' _ => ⟨[], rfl, rfl, fun _ h => by cases h⟩⟩
  | some x =>
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
    refine ⟨P, fun P' hP' => ⟨_, by rw [checksOpt_reP, h]; rfl, by simp, fun c' hc' => ?_⟩⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨p, op, -, h1, -, -, -⟩ := hinv c hc
    refine ⟨c, hc, _, rfl, ?_⟩
    have e : pathJ posAt P' c.j = P p := by
      unfold pathJ
      rw [h1]
      exact hP' _ p h1
    rw [e]
    exact hP p c hc (hpl _ p h1).symm

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
        obtain ⟨P0, hP0⟩ := repath_opt (tr := tr) w.posAt0 w.place
          (fun j p h => (hW.1.place_posAt0 j p h).2) w.depth0 _ _ _ _ c0 h0
          fun c hc => hall c (List.mem_append_left _ (List.mem_append_left _ hc))
        obtain ⟨PJ, hPJ⟩ := repath_opt (tr := tr) w.posAtJ w.place
          (fun j p h => (hW.1.place_posAtJ j p h).2) w.depthJ _ _ _ _ cJ hJ
          fun c hc => hall c (List.mem_append_left _ (List.mem_append_right _ hc))
        obtain ⟨P2, c2', h2', r2⟩ :=
          repath_B s A W hW.2 _ rts _ _ c2 h2 fun c hc => hall c (List.mem_append_right _ hc)
        let Pl : r.Pos → List (Dig lam) := fun p => if a.own p then PJ p else P0 p
        obtain ⟨c0', h0', r0⟩ := hP0 Pl fun j p hp => by
          show (if a.own p then PJ p else P0 p) = P0 p
          rw [(hW.1.place_posAt0 j p hp).1]; rfl
        obtain ⟨cJ', hJ', rJ⟩ := hPJ Pl fun j p hp => by
          show (if a.own p then PJ p else P0 p) = PJ p
          rw [(hW.1.place_posAtJ j p hp).1]; rfl
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

/-! ## The two theorems -/

/-- For `wq.OKG`: what `checkPrunedOpenings` accepts, `afterB` accepts with other paths, from the same trace. -/
theorem runsIn_afterB_of_afterBO {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q}
    (hwq : wq.OKG) {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
    {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam Q}
    {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam} {tr : Trace (spec lam K L)}
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
    {tr : Trace (spec lam K L)}
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

end Compile.Batch
