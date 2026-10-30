-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/EndC.lean: A COMPILED RUN THAT SHOWS ITS TOKENS IN SEVERAL REVEALS (proveC,
Johnson/TokenRules/Chunks.lean) KEEPS THE RULES, GIVEN THAT ITS CHAIN DOES: the proof of
Spec.safeProveC (Johnson/TokenRules/Spec.lean) from Spec.safeChain (Johnson/TokenRel/Rules.lean),
which is a hypothesis here; it is proved in that file.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

All hashing of a run (hashT, Johnson/TokenSide/Finish.lean) is: the first salt, a new token; coins
that are values, which leave the state alone (safe_drawD, Johnson/TokenRules/End.lean); the chain.
Just after the first salt has been drawn the chain's invariant holds with the salt as the only token
so far (ci_start), so the statement on the chain applies, and what it says at the end (ChainEnd) is
handed on (safe_hashC). The end of a run asks no oracle. It shows nothing, or it shows the tokens
chunk by chunk:
  the first salt and the chain's tokens   closed in themselves (ChainEnd.deps);
  the two tokens of a leaf of the run     closed but for the first salt, which is shown by then;
  the two tokens of an external leaf      closed in themselves.
What is known of a token (Deps) stays along a reveal, which charges nothing.
  safe_revealsT     reveals in turn, each of a list that is closed in itself or by what is shown.
  closed_of_shown   in a well-formed state every list of tokens that are ALL SHOWN ALREADY can be
                    revealed: so the last reveal, which reads the values, asks nothing more.
  ChunkOK           each token of a list exists, and what it depends on is in the list or is shown.
  mem_shownTrees, mem_shownK   a chunk of the run's own leaves is the list of the two tokens of a
                    leaf of a kept tree. (For an external string's tree that is read off the
                    definition within the proof of safeProveC.)
  safeProveC        THE RUN.
Limits. Rules and counts alone: that the run is the compiled prover's is not shown here.

-/
import Johnson.TokenRules.End
import Johnson.TokenRules.Chunks

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRel
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

/-! ## Reveals in turn -/

section Generic
variable {S : OSpec} {Rl : Rules S}

/-- In a well-formed state tokens that are all shown can be revealed again. -/
theorem closed_of_shown {d : DSt S} (hd : TidyO Rl d) {ts : List Tok} (h : ∀ u ∈ ts, u ∈ d.shown) :
    ClosedO d ts where
  lt := fun t ht => hd.shown_lt t (h t ht)
  tail := fun e he hc => Or.inr (hd.closed_tail e he (hd.released e he (h _ hc)))
  others := fun e he hc u hu => Or.inr (hd.closed_others e he (hd.released e he (h _ hc)) u hu)

/-- Each token of ts exists, and what it depends on is in ts or is shown. -/
def ChunkOK (d : DSt S) (ts : List Tok) : Prop :=
  ∀ u ∈ ts, u < d.vals.length ∧ ∃ l, Deps d u l ∧ ∀ v ∈ l, v ∈ ts ∨ v ∈ d.shown

theorem ChunkOK.closed {d : DSt S} {ts : List Tok} (h : ChunkOK d ts) : ClosedO d ts :=
  ClosedO.of_deps (fun u hu => (h u hu).1) fun u hu => (h u hu).2

theorem ChunkOK.keeps {d d' : DSt S} {ts : List Tok} (h : ChunkOK d ts)
    (hc : Charges noTok d d') : ChunkOK d' ts := fun u hu => by
  obtain ⟨h1, l, h2, h3⟩ := h u hu
  exact ⟨lt_of_lt_of_le h1 hc.vals.length_le, l, h2.keeps h1 hc fun e => e,
    fun v hv => (h3 v hv).imp_right (hc.shown_old v)⟩

end Generic

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- Reveals in turn, each of a list that is closed in itself or by what is shown. -/
theorem safe_revealsT {Rl : Rules (typedOracleFamily lam K L)} :
    ∀ (l : List (List Tok)) (d : DSt (typedOracleFamily lam K L)),
    TidyO Rl d → (∀ ts ∈ l, ChunkOK d ts) →
    SafeO Rl (revealsT (K := K) (L := L) l) d fun _ d' =>
      TidyO Rl d' ∧ GrowsO noTok (fun u => u ∈ l.flatten) zr zr d d' ∧ ∀ u ∈ l.flatten, u ∈ d'.shown
  | [], d, hd, _ => ⟨hd, GrowsO.refl d, fun _ e => absurd e List.not_mem_nil⟩
  | ts :: l, d, hd, h => by
      rw [revealsT]
      have hc := (h ts List.mem_cons_self).closed
      refine ⟨hc, fun T => ?_⟩
      have hg : GrowsO noTok (fun u => u ∈ ts) zr zr d (afterReveal d ts T) :=
        GrowsO.ofReveal d ts T
      refine SafeO.mono ?_ _ _ (safe_revealsT l _ (hd.reveal hc T) fun ts' hts' =>
        (h ts' (List.mem_cons_of_mem _ hts')).keeps hg.charges)
      rintro _ d₂ ⟨hd₂, hg₂, hs₂⟩
      refine ⟨hd₂, (hg.mono (Ch := noTok) (R := fun u => u ∈ (ts :: l).flatten)
        (fun _ e => Or.inl e) (fun u hu => Or.inl ?_) (fun _ => le_rfl) (fun _ => le_rfl)).trans hg₂
        (fun _ e => Or.inl e) (fun u hu => Or.inl ?_) (fun _ => le_rfl) (fun _ => le_rfl), ?_⟩
      · rw [List.flatten_cons]
        exact List.mem_append_left _ hu
      · rw [List.flatten_cons]
        exact List.mem_append_right _ hu
      · intro u hu
        rw [List.flatten_cons] at hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hg₂.shown_old u (List.mem_append_right _ hu)
        · exact hs₂ u hu

/-! ## What a chunk is -/

theorem mem_shownTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (rd : r.Pos → Bool)
    {ts : List Tok} : ∀ (Ts : List (TreeT lam L)) (k : ℕ), ts ∈ shownTrees posAt rd k Ts →
      ∃ T ∈ Ts, ∃ j, ts = T.toksAt j
  | [], _, h => absurd h List.not_mem_nil
  | T :: Ts, k, h => by
      rw [shownTrees] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨j, _, e⟩ := List.mem_map.mp h
        exact ⟨T, List.mem_cons_self, j, e.symm⟩
      · obtain ⟨T', hT', j, e⟩ := mem_shownTrees posAt rd Ts (k + 1) h
        exact ⟨T', List.mem_cons_of_mem _ hT', j, e⟩

/-- A chunk of the run's own leaves: the two tokens of a leaf of a kept tree. -/
theorem mem_shownK {n : ℕ} {d : DSt (typedOracleFamily lam K L)} {salt : Tok} {ts : List Tok} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (ks : KeptT lam L s) (rd : OPos s → Bool),
      KeptOK n d salt s ks → ts ∈ shownK s A W ks rd →
      ∃ T j, (TreeOKT d [salt] T ∧ TreeNewT n T) ∧ ts = T.toksAt j
  | [], _, _, _, _, _, h => absurd h List.not_mem_nil
  | _ :: s, (_, A), (w, W), (kp, ks), rd, hk, h => by
      have hk' : ∀ T ∈ kp.2.1 ++ kp.2.2, TreeOKT d [salt] T ∧ TreeNewT n T := hk.1
      rw [shownK] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨T, hT, j, e⟩ := mem_shownTrees _ _ _ _ h
        exact ⟨T, j, hk' T (List.mem_append_right _ hT), e⟩
      rcases List.mem_append.mp h with h | h
      · obtain ⟨T, hT, j, e⟩ := mem_shownTrees _ _ _ _ h
        exact ⟨T, j, hk' T (List.mem_append_left _ hT), e⟩
      · exact mem_shownK s A W ks _ hk.2 h

/-- The two tokens of a leaf are closed but for us. -/
theorem chunkOK_toksAt {d : DSt (typedOracleFamily lam K L)} {us : List Tok} {T : TreeT lam L}
    (h : TreeOKT d us T) (hus : ∀ u ∈ us, u ∈ d.shown) (j : ℕ) : ChunkOK d (T.toksAt j) :=
  fun _ hu => ⟨(toksAt_ok h j hu).2.1, _, (toksAt_ok h j hu).2.2, fun v hv =>
    (List.mem_append.mp hv).imp_right (hus v)⟩

/-! ## All hashing, with what the end needs -/

/-- All hashing of a compiled run keeps the rules and shows nothing; what holds at the end of the
chain is handed on as it is. -/
theorem safe_hashC (hC : Spec.safeChain) {bl bf : ℕ} {sd : (t : Tag) → FbIn lam L t → Prop}
    (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (xt : ℕ → TreeT lam L) (σ : Strat Q.loc.shape Unit)
    (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ) (d : DSt (typedOracleFamily lam K L))
    (hbl : bl ≤ ln.fr) (hbf : bf ≤ ln.sFS) (hlam : bf ≤ lam)
    (hd : TidyO (rulesT K L lam bl bf sd) d) (hx : ∀ k, TreeOKT d [] (xt k)) :
    SafeO (rulesT K L lam bl bf sd) (hashT t Q wq embS embP xin cms x σ ln pre cap) d fun a d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      GrowsO noTok noTok (eRun Q.loc.shape Q.ann wq.sh) (mRun t Q.loc.shape Q.ann wq.sh cap ln.dq)
        d d' ∧ d.vals.length ≤ a.1 ∧ (∀ k, TreeOKT d' [] (xt k)) ∧
      ∀ z, a.2.2 = Res.ok z → ChainEnd d.vals.length d' a.1 [a.1] z := by
  unfold hashT
  intro u
  have h1 := hd.fresh (List.ofFn u)
  have hci := ci_start hd t u
  have hn : d.vals.length ≤ (afterFresh d (List.ofFn u)).vals.length := by
    rw [length_afterFresh]
    exact Nat.le_succ _
  refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (safe_drawD ln _))
  rintro cd _ ⟨rfl, hl⟩
  refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (hC I X lam K L bl bf sd t cms (xin x) ln.fr pre
    d.vals.length cd cap ln.sFS Q.loc.shape Q.ann wq.sh embS embP 0 .first σ [d.vals.length]
    d.vals.length _ hbl hbf hlam hn h1 hci))
  rintro r d₂ ⟨hd₂, hr, hE⟩
  rw [mChain_first, hl] at hr
  have hg : GrowsO noTok noTok (eRun Q.loc.shape Q.ann wq.sh)
      (mRun t Q.loc.shape Q.ann wq.sh cap ln.dq) d d₂ :=
    (GrowsO.ofFresh (Ch := noTok) (R := noTok) (e := zr) (M := zr) d (List.ofFn u)).trans hr.grows
      (fun _ hv => hv.elim (fun e => Or.inr (le_of_eq e.symm)) fun e => absurd e List.not_mem_nil)
      (fun _ hv => Or.inl hv) (fun _ => (Nat.zero_add _).le) (fun _ => (Nat.zero_add _).le)
  exact ⟨hd₂, hg, le_rfl, fun k => (hx k).keeps hg.charges fun _ _ e => e, hE⟩

/-! ## The whole run -/

/-- **A compiled run that shows its tokens in several reveals**, given the chain. -/
theorem safeProveC (hC : Spec.safeChain) : Spec.safeProveC := by
  intro I X lam K L bl bf sd t Y E Q wq embS embP xin cms x y xt preX σ ln pre cap stop d hbl hbf
    hlam hd hx
  unfold proveC
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d
    (safe_hashC hC t Q wq embS embP xin cms x xt σ ln pre cap d hbl hbf hlam hd hx))
  rintro ⟨salt, cd, r⟩ d₁ ⟨hd₁, hg, hsalt, hx₁, hz⟩
  have hg' : GrowsO noTok (fun u => ∃ k, TreeTokT (xt k) u) (eRun Q.loc.shape Q.ann wq.sh)
      (mRun t Q.loc.shape Q.ann wq.sh cap ln.dq) d d₁ :=
    hg.mono (fun _ e => Or.inl e) (fun _ e => e.elim) (fun _ => le_rfl) (fun _ => le_rfl)
  cases r with
  | noFormat => exact ⟨hd₁, hg'⟩
  | ranOut _ => exact ⟨hd₁, hg'⟩
  | ok z =>
      have hE : ChainEnd d.vals.length d₁ salt [salt] z := hz z rfl
      have hsalt' : d.vals.length ≤ salt := hsalt
      show SafeO _ (if stop z.rho = true then Step.pure none
        else (finishC Q wq x y xt preX pre salt cd z).bind fun π => Step.pure (some π)) d₁ _
      by_cases hs : stop z.rho = true
      · rw [if_pos hs]
        exact ⟨hd₁, hg'⟩
      rw [if_neg hs]
      refine SafeO.bind _ _ d₁ ?_
      unfold finishC
      refine SafeO.bind _ _ d₁ ?_
      -- the first chunk
      have h1 : ChunkOK d₁ (salt :: z.toks) := fun u hu =>
        ⟨(hE.deps u hu).1, _, (hE.deps u hu).2, fun v hv => Or.inl hv⟩
      show SafeO _ (Step.reveal (salt :: z.toks) fun _ => revealsT _) d₁ _
      refine ⟨h1.closed, fun T => ?_⟩
      have hg₁ : GrowsO noTok (fun u => u ∈ salt :: z.toks) zr zr d₁
          (afterReveal d₁ (salt :: z.toks) T) := GrowsO.ofReveal d₁ _ T
      have hsh : ∀ u ∈ [salt], u ∈ (afterReveal d₁ (salt :: z.toks) T).shown := fun u hu => by
        rw [List.mem_singleton.mp hu]
        exact List.mem_append_right _ List.mem_cons_self
      -- where the tokens of the other chunks come from
      have hsrc : ∀ ts ∈ shownK Q.loc.shape Q.ann wq.sh z.kept (fun p =>
            haveI := wq.decO
            decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains)) ++
          shownExt Q wq x xt z.rho,
          ChunkOK (afterReveal d₁ (salt :: z.toks) T) ts ∧
            ∀ u ∈ ts, (∃ k, TreeTokT (xt k) u) ∨ d.vals.length ≤ u := by
        intro ts hts
        rcases List.mem_append.mp hts with hts | hts
        · obtain ⟨T', j, ⟨hT, hN⟩, rfl⟩ := mem_shownK _ _ _ _ _ hE.kept hts
          exact ⟨chunkOK_toksAt (hT.keeps hg₁.charges fun _ _ e => e) hsh j,
            fun u hu => Or.inr (hN u (toksAt_ok hT j hu).1)⟩
        · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hts
          exact ⟨chunkOK_toksAt ((hx₁ _).keeps hg₁.charges fun _ _ e => e)
              (fun _ e => absurd e List.not_mem_nil) _,
            fun u hu => Or.inl ⟨_, (toksAt_ok (hx₁ _) _ hu).1⟩⟩
      refine SafeO.mono ?_ _ _ (safe_revealsT _ _ (hd₁.reveal h1.closed T) fun ts hts =>
        (hsrc ts hts).1)
      rintro _ d₃ ⟨hd₃, hg₃, hs₃⟩
      -- the last reveal: all is shown
      have hall : ∀ u ∈ showC Q wq x xt salt z, u ∈ d₃.shown := fun u hu => by
        have hu' : u ∈ (salt :: z.toks) ++ (shownK Q.loc.shape Q.ann wq.sh z.kept (fun p =>
            haveI := wq.decO
            decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains)) ++
          shownExt Q wq x xt z.rho).flatten := hu
        rcases List.mem_append.mp hu' with hu' | hu'
        · exact hg₃.shown_old u (List.mem_append_right _ hu')
        · exact hs₃ u hu'
      have hnew : ∀ u ∈ showC Q wq x xt salt z, (∃ k, TreeTokT (xt k) u) ∨ d.vals.length ≤ u :=
        fun u hu => by
        have hu' : u ∈ (salt :: z.toks) ++ (shownK Q.loc.shape Q.ann wq.sh z.kept (fun p =>
            haveI := wq.decO
            decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains)) ++
          shownExt Q wq x xt z.rho).flatten := hu
        rcases List.mem_append.mp hu' with hu' | hu'
        · rcases List.mem_cons.mp hu' with e | hu'
          · exact Or.inr (e ▸ hsalt')
          · exact Or.inr (hE.new u hu')
        · obtain ⟨ts, hts, hu''⟩ := List.mem_flatten.mp hu'
          exact (hsrc ts hts).2 u hu''
      have hc₃ := closed_of_shown hd₃ hall
      refine ⟨hc₃, fun T' => ⟨hd₃.reveal hc₃ T', ?_⟩⟩
      refine ((hg'.trans hg₁ (fun _ e => Or.inl e) (fun u hu => hnew u (List.mem_append_left _ hu))
        (fun _ => le_rfl) (fun _ => le_rfl)).trans hg₃ (fun _ e => Or.inl e)
        (fun u hu => hnew u (List.mem_append_right _ hu)) (fun _ => le_rfl)
        (fun _ => le_rfl)).trans (GrowsO.ofReveal (Ch := noTok) (e := zr) (M := zr) d₃ _ T')
        (fun _ e => Or.inl e) (fun u hu => hnew u hu) (fun _ => le_rfl) (fun _ => le_rfl)

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.safeProveC
