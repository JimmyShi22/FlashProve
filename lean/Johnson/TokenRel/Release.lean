-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Release.lean: THE RULE OF RELEASE: the proof of Spec.release
(Johnson/TokenRules/ReleaseSpec.lean).

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

The end of a run (endC, Johnson/TokenRules/Chunks.lean) is a list of reveals, so in the mode in
which marked evaluations are deferred its run is one outcome, the state after these reveals in turn
(revAll, Johnson/TokenRel/Reveal.lean). What each writes:
  relL_first   The first, of the first salt and the chain's tokens: the evaluations that are not
               released and are charged to these are the evaluations that the hashing has added and
               that are no leaves (Cls, Johnson/TokenRel/Inv.lean), in their order.
  chunk_tree, chunk_trees, chunk_kept, chunk_ext   The lists of the leaves' tokens (shownK,
               shownExt) and the lists of entries that the plain rule writes (laidK, extLaid,
               Johnson/WholeKey/Sim.lean) go together term by term, and each pair is a LeafChunk: so
               the reveals write these entries in turn (revAll_chunks).
  the last     All its tokens are shown: it writes nothing (relL_shown).
Beside the rule, with no premise on the state: finishC_run and endC_run (the one outcome, written
out) and endC_leafAt (the end of a run keeps LeafAt of every tree, whatever its outcome).
Note on sources. forall₂_map and forall₂_append are two facts on lists that go together term by
term, proved here by recursion on the lists. forall₂_append repeats the library's lemma of that name
(Compile/Batch/DisciplineChain.lean), its premises in another order.

-/
import Johnson.TokenRel.Hash
import Johnson.TokenRules.Marks

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Lists that go together -/

theorem forall₂_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ l : List α, (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | x :: l, h => .cons (h x List.mem_cons_self)
      (forall₂_map l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem forall₂_append {β γ : Type} {R : β → γ → Prop} : ∀ {a : List β} {b : List γ}
    {a' : List β} {b' : List γ}, List.Forall₂ R a b → List.Forall₂ R a' b' →
    List.Forall₂ R (a ++ a') (b ++ b')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (forall₂_append t h')

/-! ## The chunks of the leaves -/

theorem leafChunk_of {d : DSt (typedOracleFamily lam K L)} {us : List Tok} {T : TreeT lam L} {pv : Bits}
    (hT : TreeOKT d us T) (hus : ∀ u ∈ us, u ∈ d.shown) (hL : LeafAt d T pv) {j : ℕ}
    (hj : j < T.tok.length) : LeafChunk d (T.toksAt j) (entryK (T.toK d.val pv) j) := by
  have e : T.tok[j]? = some T.tok[j] := List.getElem?_eq_getElem hj
  obtain ⟨h1, h2, h3, h4⟩ := hT _ (List.getElem_mem hj)
  rw [toksAt_some e]
  refine ⟨ClosedO.of_deps ?_ ?_, _, _, rfl, (hL.2 j _ e).1, (hL.2 j _ e).2⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h1
    · rw [List.mem_singleton.mp ht]
      exact h2
  · intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨_, h3, fun v hv => (List.mem_cons.mp hv).elim
        (fun h => Or.inl (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)) fun h => Or.inr (hus v h)⟩
    · rw [List.mem_singleton.mp hu]
      exact ⟨[], h4, fun _ h => absurd h List.not_mem_nil⟩

theorem chunk_tree {r : Round} (posAt : ℕ → Option r.Pos) (rd : r.Pos → Bool)
    {d : DSt (typedOracleFamily lam K L)} {us : List Tok} {T : TreeT lam L} {pv : Bits} (hT : TreeOKT d us T)
    (hus : ∀ u ∈ us, u ∈ d.shown) (hL : LeafAt d T pv) :
    List.Forall₂ (LeafChunk d) (shownTree posAt rd T) (laidTree posAt rd (T.toK d.val pv)) := by
  unfold shownTree laidTree
  exact forall₂_map _ fun j hj => leafChunk_of hT hus hL (by
    rw [hL.1]
    exact List.mem_range.mp (List.mem_filter.mp hj).1)

theorem chunk_trees {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (rd : r.Pos → Bool)
    {d : DSt (typedOracleFamily lam K L)} {us : List Tok} {pv : Bits} (hus : ∀ u ∈ us, u ∈ d.shown) :
    ∀ (Ts : List (TreeT lam L)) (k : ℕ), (∀ T ∈ Ts, TreeOKT d us T ∧ LeafAt d T pv) →
      List.Forall₂ (LeafChunk d) (shownTrees posAt rd k Ts)
        (laidTrees posAt rd k (Ts.map (TreeT.toK d.val pv)))
  | [], _, _ => .nil
  | T :: Ts, k, h => by
      rw [shownTrees, List.map_cons, laidTrees]
      exact forall₂_append
        (chunk_tree (posAt k) rd (h T List.mem_cons_self).1 hus (h T List.mem_cons_self).2)
        (chunk_trees posAt rd hus Ts (k + 1) fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))

theorem chunk_kept {n : ℕ} {d : DSt (typedOracleFamily lam K L)} {salt : Tok} {st : ℕ → Bool → Bits}
    (hs : salt ∈ d.shown) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (kept : KeptT lam L s) (rd : OPos s → Bool) (i : ℕ),
      KeptOK n d salt s kept → KeptAt d st s i kept →
      List.Forall₂ (LeafChunk d) (shownK s A W kept rd) (laidK s A W (keptK d.val st s i kept) rd)
  | [], _, _, _, _, _, _, _ => .nil
  | _ :: s, (_, A), (w, W), (kp, ks), rd, i, h1, h2 => by
      have hus : ∀ u ∈ [salt], u ∈ d.shown := fun u hu => by
        rw [List.mem_singleton.mp hu]
        exact hs
      rw [shownK, keptK, laidK]
      exact forall₂_append
        (chunk_trees w.posAtJ _ hus kp.2.2 0 fun T hT =>
          ⟨(h1.1 T (List.mem_append_right _ hT)).1, h2.2.1 T hT⟩)
        (forall₂_append
          (chunk_trees w.posAt0 _ hus kp.2.1 0 fun T hT =>
            ⟨(h1.1 T (List.mem_append_left _ hT)).1, h2.1 T hT⟩)
          (chunk_kept hs s A W ks _ (i + 1) h1.2 h2.2.2))

theorem chunk_ext {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y)
    (xt : ℕ → TreeT lam L) (preX : Bits) {d : DSt (typedOracleFamily lam K L)}
    (hx : ∀ k, TreeOKT d [] (xt k)) (hL : ∀ k, LeafAt d (xt k) preX)
    (hlt : ∀ p, wq.ext.leaf p < (xt (wq.ext.which p)).tok.length) (ρ : Rho Q.loc.shape) :
    List.Forall₂ (LeafChunk d) (shownExt Q wq x xt ρ)
      (extLaid Q wq x (fun k => (xt k).toK d.val preX) ρ) := by
  unfold shownExt extLaid
  exact forall₂_map _ fun p _ =>
    leafChunk_of (hx _) (fun _ h => absurd h List.not_mem_nil) (hL _) (hlt p)

/-! ## A reveal keeps what is known of trees -/

theorem TreeOKT.revI {d : DSt (typedOracleFamily lam K L)} {us : List Tok} {T : TreeT lam L}
    (h : TreeOKT d us T) (ts : List Tok) : TreeOKT (revI d ts) us T :=
  TreeOKT.keeps h (GrowsO.ofReveal (Ch := noTok) (e := zr) (M := zr) d ts _).charges
    fun _ _ h => h

theorem KeptOK.revI {n : ℕ} {d : DSt (typedOracleFamily lam K L)} {salt : Tok} (ts : List Tok) :
    ∀ (s : Shape) (kept : KeptT lam L s), KeptOK n d salt s kept →
      KeptOK n (revI d ts) salt s kept
  | [], _, _ => trivial
  | _ :: s, (_, ks), h =>
      ⟨fun T hT => ⟨TreeOKT.revI (h.1 T hT).1 ts, (h.1 T hT).2⟩, KeptOK.revI ts s ks h.2⟩

theorem KeptAt.revI {d : DSt (typedOracleFamily lam K L)} {st : ℕ → Bool → Bits} (ts : List Tok) :
    ∀ (s : Shape) (i : ℕ) (kept : KeptT lam L s), KeptAt d st s i kept →
      KeptAt (revI d ts) st s i kept
  | [], _, _, _ => trivial
  | _ :: s, i, (_, ks), h =>
      ⟨fun T hT => LeafAt.revAll [ts] (h.1 T hT), fun T hT => LeafAt.revAll [ts] (h.2.1 T hT),
        KeptAt.revI ts s (i + 1) ks h.2.2⟩

/-! ## The first reveal -/

theorem notLeaf_qa (e : Ev (typedOracleFamily lam K L)) : notLeaf (qa e) = true ↔ e.o ≠ OracleName.leaf := by
  obtain ⟨o, pt, ans, c, os, tl, rl⟩ := e
  cases o <;> simp [notLeaf, qa]

theorem relL_first {Rl : Rules (typedOracleFamily lam K L)} {D D₁ : DSt (typedOracleFamily lam K L)}
    {new : List (Ev (typedOracleFamily lam K L))} {c₁ : List Tok} (hD : TidyO Rl D) (hd₁ : TidyO Rl D₁)
    (hev : D₁.evs = D.evs ++ new) (hun : ∀ e ∈ new, e.released = false)
    (hcls : ∀ e ∈ new, Cls D.vals.length c₁ e) (hnew : ∀ u ∈ c₁, D.vals.length ≤ u) :
    relL D₁ c₁ = ((D₁.evs.drop D.evs.length).map qa).filter notLeaf := by
  have hold : (D.evs.filter fun e => !e.released && c₁.contains e.charged) = [] :=
    List.filter_eq_nil_iff.mpr fun e he hc => by
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      exact absurd (hnew _ hc.2) (Nat.not_le.mpr (hD.charged_lt e he))
  rw [relL_eq hd₁, hev, List.drop_left, List.filter_append, hold, List.nil_append, List.filter_map]
  congr 1
  refine List.filter_congr fun e he => ?_
  rw [hun e he]
  show (true && c₁.contains e.charged) = notLeaf (qa e)
  rw [Bool.true_and]
  rcases hcls e he with ⟨h1, _, h3⟩ | ⟨h1, h2⟩
  · have e1 : notLeaf (qa e) = false := Bool.eq_false_iff.mpr fun h => (notLeaf_qa e).mp h h1
    rw [e1]
    exact Bool.eq_false_iff.mpr fun h => h3 (List.contains_iff_mem.mp h)
  · rw [(notLeaf_qa e).mpr h1]
    exact List.contains_iff_mem.mpr h2

/-! ## The end of a run is one outcome -/

section Run
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y) (y : E.Str)
  (xt : ℕ → TreeT lam L) (preX : Bits) (pre : ℕ → Bool → Bits → Bits)
  (stop : Rho Q.loc.shape → Bool)

theorem revAll_val (l : List (List Tok)) (d : DSt (typedOracleFamily lam K L)) : (revAll l d).val = d.val := by
  funext u
  unfold DSt.val
  rw [revAll_vals]

/-- The reveals with the string, in mode I: the string at the store's values; the state after the
reveals in turn. -/
theorem finishC_run (salt : Tok) (cd : CoinsD lam L) (z : OutT lam L Q.loc.shape)
    (D₁ : DSt (typedOracleFamily lam K L)) :
    (finishC Q wq x y xt preX pre salt cd z).run true D₁ =
      PMF.pure (finish Q wq x y
          (fun k => (xt k).toK
            (valOf (showC Q wq x xt salt z) ((showC Q wq x xt salt z).map D₁.val)) preX)
          (coinsK (valOf (showC Q wq x xt salt z) ((showC Q wq x xt salt z).map D₁.val) salt) cd)
          (outK (valOf (showC Q wq x xt salt z) ((showC Q wq x xt salt z).map D₁.val))
            (fun i b => pre i b
              (valOf (showC Q wq x xt salt z) ((showC Q wq x xt salt z).map D₁.val) salt)) z),
        revI (revAll (chunksT Q wq x xt salt z) D₁) (showC Q wq x xt salt z)) := by
  unfold finishC
  rw [Life2.run_bind, run_revealsT, PMF.pure_bind, run_reveal, revAll_val]
  rfl

theorem endC_run (salt : Tok) (cd : CoinsD lam L) (z : OutT lam L Q.loc.shape)
    (hstop : stop z.rho = false) (D₁ : DSt (typedOracleFamily lam K L)) :
    (endC Q wq x y xt preX pre stop (salt, cd, Res.ok z)).run true D₁ =
      PMF.pure (some (finish Q wq x y
          (fun k => (xt k).toK
            (valOf (showC Q wq x xt salt z) ((showC Q wq x xt salt z).map D₁.val)) preX)
          (coinsK (valOf (showC Q wq x xt salt z) ((showC Q wq x xt salt z).map D₁.val) salt) cd)
          (outK (valOf (showC Q wq x xt salt z) ((showC Q wq x xt salt z).map D₁.val))
            (fun i b => pre i b
              (valOf (showC Q wq x xt salt z) ((showC Q wq x xt salt z).map D₁.val) salt)) z)),
        revI (revAll (chunksT Q wq x xt salt z) D₁) (showC Q wq x xt salt z)) := by
  show (if stop z.rho = true then Step.pure none
    else (finishC Q wq x y xt preX pre salt cd z).bind fun π => Step.pure (some π) :
      StT lam K L (Option (OneProtocolProof lam Q))).run true D₁ = _
  rw [if_neg (by rw [hstop]; exact Bool.false_ne_true), Life2.run_bind, finishC_run, PMF.pure_bind]
  rfl

/-- The end of a run keeps LeafAt of every tree, whatever its outcome. -/
theorem endC_leafAt (a : Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape))
    (D₁ : DSt (typedOracleFamily lam K L)) (v : Option (OneProtocolProof lam Q) × DSt (typedOracleFamily lam K L))
    (hv : v ∈ ((endC Q wq x y xt preX pre stop a).run true D₁).support) {T : TreeT lam L}
    {pr : Bits} (h : LeafAt D₁ T pr) : LeafAt v.2 T pr := by
  by_cases hn : ∀ z, a.2.2 = Res.ok z → stop z.rho = true
  · rw [releaseNone I X lam K L Y E Q wq x y xt preX pre stop true D₁ a hn, PMF.support_pure,
      Set.mem_singleton_iff] at hv
    rw [hv]
    exact h
  · obtain ⟨salt, cd, r⟩ := a
    simp only [not_forall] at hn
    obtain ⟨z, hz, hs⟩ := hn
    have hz' : r = Res.ok z := hz
    subst hz'
    rw [endC_run Q wq x y xt preX pre stop salt cd z (by simpa using hs), PMF.support_pure,
      Set.mem_singleton_iff] at hv
    rw [hv]
    exact LeafAt.revAll [showC Q wq x xt salt z] (LeafAt.revAll _ h)

end Run

/-! ## The rule of release -/

/-- **The rule of release.** -/
theorem release : TokenRules.Spec.release := by
  intro I X lam K L bl bf sd t Y E Q wq embS embP xin cms x y xt preX σ ln pre cap stop D D₁ a z hbl
    hbf hlam hext hD hLaid hx hLx hmem hz hstop
  obtain ⟨hd₁, hg, hsalt, hadd, hok⟩ := safeRunO _ _ _ _ _ _ _ true
    (safe_hashT t Q wq embS embP xin cms x σ ln pre cap D hbl hbf hlam hD) (a, D₁) hmem
  obtain ⟨hE, ⟨new', hev', hcls⟩, hK⟩ := hok z hz
  obtain ⟨_, new, hev, hun⟩ := DeferRun.modeI_frame _ _ _ mkHash _ D
    (marksHash I X lam K L t Y E Q wq embS embP xin cms x σ ln pre cap D.vals) (a, D₁) hmem
  have hnn : new' = new := List.append_cancel_left (hev'.symm.trans hev)
  subst hnn
  have hLaid₁ : Laid D₁ := laid_run _ D hLaid (a, D₁) hmem
  obtain ⟨salt, cd, r⟩ := a
  have hz' : r = Res.ok z := hz
  subst hz'
  have hsalt' : salt = D.vals.length := hsalt
  have hE' : ChainEnd D.vals.length D₁ salt [salt] z := hE
  have hK' : KeptAt D₁ (fun i b => pre i b (D₁.val salt)) Q.loc.shape 0 z.kept := hK
  have hcls' : ∀ e ∈ new', Cls D.vals.length (salt :: z.toks) e := hcls
  have hx₁ : ∀ k, TreeOKT D₁ [] (xt k) := fun k => TreeOKT.keeps (hx k) hg.charges fun _ _ h => h
  have hLx₁ : ∀ k, LeafAt D₁ (xt k) preX := fun k =>
    LeafAt.adds (hLx k) (fun u hu => TreeOKT.lt (hx k) hu) hg.vals hadd fun e he hc =>
      absurd (TreeOKT.lt (hx k) hc) (Nat.not_lt.mpr he)
  have hc₁ : ClosedO D₁ (salt :: z.toks) :=
    ClosedO.of_deps (fun u hu => (hE'.deps u hu).1) fun u hu =>
      ⟨_, (hE'.deps u hu).2, fun v hv => Or.inl hv⟩
  have hd' : TidyO (rulesT K L lam bl bf sd) (revI D₁ (salt :: z.toks)) := hd₁.reveal hc₁ _
  have hs' : salt ∈ (revI D₁ (salt :: z.toks)).shown :=
    List.mem_append_right _ List.mem_cons_self
  have F := forall₂_append
    (chunk_kept hs' Q.loc.shape Q.ann wq.sh z.kept (fun p =>
        haveI := wq.decO
        decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains)) 0
      (KeptOK.revI _ _ _ hE'.kept) (KeptAt.revI _ _ _ _ hK'))
    (chunk_ext Q wq x xt preX (fun k => TreeOKT.revI (hx₁ k) _)
      (fun k => LeafAt.revAll [salt :: z.toks] (hLx₁ k)) hext z.rho)
  obtain ⟨htab, hdc⟩ := revAll_chunks _ _ _ hd' (Laid.revI hLaid₁ _) F
  have htab' : (revAll (chunksT Q wq x xt salt z) D₁).table = _ := htab
  have hdc' : TidyO (rulesT K L lam bl bf sd) (revAll (chunksT Q wq x xt salt z) D₁) := hdc
  refine ⟨revI (revAll (chunksT Q wq x xt salt z) D₁) (showC Q wq x xt salt z), ?_, ?_,
    revAll_vals _ _, (revI_evs_qa _ _).trans (revAll_evs_qa _ _), revAll_nPlain _ _,
    Laid.revI (Laid.revAll _ hLaid₁) _,
    fun T pr h => LeafAt.revAll [showC Q wq x xt salt z] (LeafAt.revAll _ h)⟩
  · exact endC_run Q wq x y xt preX pre stop salt cd z hstop D₁
  · show (revAll (chunksT Q wq x xt salt z) D₁).table.lay
      (relL (revAll (chunksT Q wq x xt salt z) D₁) (showC Q wq x xt salt z)) = _
    have hsh : ∀ u ∈ showC Q wq x xt salt z, u ∈ (revAll (chunksT Q wq x xt salt z) D₁).shown :=
      fun u hu => by
        rw [revAll_shown]
        exact List.mem_append_right _ hu
    rw [relL_shown (Rl := rulesT K L lam bl bf sd) hdc' hsh, Table.lay_nil]
    refine htab'.trans ?_
    rw [Table.lay_append]
    show ((D₁.table.lay (relL D₁ (salt :: z.toks))).lay _).lay _ = _
    rw [relL_first hD hd₁ hev hun hcls' fun u hu => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact le_of_eq hsalt'.symm
      · exact hE'.new u hu]
    rfl

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.release
#print axioms OnBytes.TokenRel.endC_run
