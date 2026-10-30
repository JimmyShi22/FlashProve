-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Hash.lean: ALL HASHING OF A COMPILED RUN AS A TOKEN PROGRAM: the rules, the counts,
and what it adds to the list of evaluations; and that every run in the mode in which marked
evaluations are deferred keeps "the point of each released evaluation has an entry in the table".

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

  laid_run     Laid (Johnson/TokenRules/ReleaseSpec.lean) stays along the run in mode I of ANY token
               program, and along a query of the adversary (laid_answer): tables only grow, a marked
               evaluation is not released when it is made, and a release writes. General in the
               family of oracles.
  safe_hashT   hashT (Johnson/TokenSide/Finish.lean): the first salt is a new token; then the chain
               (Johnson/TokenRel/Chain.lean) from the invariant's first member (ci_start).

-/
import Johnson.TokenRel.Chain
import Johnson.TokenRel.Reveal
import Johnson.TokenRules.End

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

/-! ## Laid along runs -/

section Generic
variable {S : OSpec} {sp : Split S} {α : Type}

theorem lazyAnswer_keeps {T : Table S} {o : S.ι} {q : S.Dom o} {p : S.Rng o × Table S}
    (hp : p ∈ (lazyAnswer T o q).support) {o' : S.ι} {q' : S.Dom o'} (h : T o' q' ≠ none) :
    p.2 o' q' ≠ none := by
  unfold lazyAnswer at hp
  cases hT : T o q with
  | some r =>
      simp only [hT, PMF.support_pure, Set.mem_singleton_iff] at hp
      rw [hp]
      exact h
  | none =>
      simp only [hT] at hp
      obtain ⟨r, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      have e : T.set o q r = T.lay1 o q r := (Table.lay1_of_none hT r).symm
      show T.set o q r o' q' ≠ none
      rw [e]
      exact lay_ne_none (l := [⟨o, q, r⟩]) h

theorem Laid.table {d : DSt S} (h : Laid d) {d' : DSt S} (he : d'.evs = d.evs)
    (ht : ∀ o q, d.table o q ≠ none → d'.table o q ≠ none) : Laid d' := fun e hm hr =>
  ht _ _ (h e (he ▸ hm) hr)

/-- A query of the adversary keeps Laid. -/
theorem laid_answer {d : DSt S} (h : Laid d) {o : S.ι} {q : S.Dom o} {p : S.Rng o × Table S}
    (hp : p ∈ (lazyAnswer d.table o q).support) : Laid { d with table := p.2 } :=
  Laid.table h rfl fun _ _ h' => lazyAnswer_keeps hp h'

/-- **Every run in mode I keeps Laid.** -/
theorem laid_run (c : Step S sp α) : ∀ d : DSt S, Laid d →
    ∀ x ∈ (c.run true d).support, Laid x.2 := by
  induction c with
  | pure a =>
      intro d h x hx
      rw [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
      exact h
  | sample n k ih =>
      intro d h x hx
      rw [Step.run, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, _, hr⟩ := hx
      exact ih r d h x hr
  | plain o q k ih =>
      intro d h x hx
      rw [Step.run, PMF.mem_support_bind_iff] at hx
      obtain ⟨p, hp, hr⟩ := hx
      refine ih p.1 _ ?_ x hr
      exact Laid.table h rfl fun _ _ h' => lazyAnswer_keeps hp h'
  | fresh ℓ k ih =>
      intro d h x hx
      rw [Step.run, PMF.mem_support_bind_iff] at hx
      obtain ⟨u, _, hr⟩ := hx
      refine ih _ _ ?_ x hr
      exact Laid.table h rfl fun _ _ h' => h'
  | marked o t us pt inj k ih =>
      intro d h x hx
      rw [Step.run] at hx
      simp only [if_true] at hx
      rw [PMF.mem_support_bind_iff] at hx
      obtain ⟨r, _, hr⟩ := hx
      refine ih _ _ _ (fun e he hre => ?_) x hr
      rcases List.mem_append.mp he with he | he
      · exact h e he hre
      · rw [List.mem_singleton.mp he] at hre
        exact nomatch hre
  | reveal ts k ih =>
      intro d h x hx
      rw [run_reveal] at hx
      exact ih _ _ (Laid.revI h ts) x hx

end Generic

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## All hashing -/

theorem safe_hashT {bl bf : ℕ} {sd : (t : Tag) → FbIn lam L t → Prop}
    (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (σ : Strat Q.loc.shape Unit)
    (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ) (d : DSt (typedOracleFamily lam K L))
    (hbl : bl ≤ ln.fr) (hbf : bf ≤ ln.sFS) (hlam : bf ≤ lam)
    (hd : TidyO (rulesT K L lam bl bf sd) d) :
    SafeO (rulesT K L lam bl bf sd) (hashT t Q wq embS embP xin cms x σ ln pre cap) d fun a d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      GrowsO noTok noTok (eRun Q.loc.shape Q.ann wq.sh) (mRun t Q.loc.shape Q.ann wq.sh cap ln.dq)
        d d' ∧
      a.1 = d.vals.length ∧ Adds (fun e => d.vals.length ≤ e.charged) d d' ∧
      ∀ z, a.2.2 = Res.ok z → ChainEnd d.vals.length d' a.1 [a.1] z ∧
        Adds (Cls d.vals.length (a.1 :: z.toks)) d d' ∧
        KeptAt d' (fun i b => pre i b (d'.val a.1)) Q.loc.shape 0 z.kept := by
  unfold hashT
  intro u
  have h1 := hd.fresh (List.ofFn u)
  have hci := ci_start hd t u
  have hn : d.vals.length ≤ (afterFresh d (List.ofFn u)).vals.length := by
    rw [length_afterFresh]
    exact Nat.le_succ _
  refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (safe_drawD ln _))
  rintro cd _ ⟨rfl, hl⟩
  refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (safe_chainT t cms (xin x) ln.fr pre
    d.vals.length cd cap ln.sFS _ hbl hbf hlam Q.loc.shape Q.ann wq.sh embS embP 0 .first σ
    [d.vals.length] d.vals.length _ hn h1 hci rfl))
  rintro r d₂ ⟨hd₂, hr, ha, hz⟩
  rw [mChain_first, hl] at hr
  have hg : GrowsO noTok noTok (eRun Q.loc.shape Q.ann wq.sh)
      (mRun t Q.loc.shape Q.ann wq.sh cap ln.dq) d d₂ :=
    (GrowsO.ofFresh (Ch := noTok) (R := noTok) (e := zr) (M := zr) d (List.ofFn u)).trans hr.grows
      (fun _ hv => hv.elim (fun e => Or.inr (le_of_eq e.symm)) fun e => absurd e List.not_mem_nil)
      (fun _ hv => Or.inl hv) (fun _ => (Nat.zero_add _).le) (fun _ => (Nat.zero_add _).le)
  have hsv : d₂.val d.vals.length = (afterFresh d (List.ofFn u)).val d.vals.length :=
    val_of_prefix hr.grows.vals (Untouched.of_fresh hd _).lt
  refine ⟨hd₂, hg, rfl, (Adds.ofFresh _ d (List.ofFn u)).trans (ha.mono fun e _ h => ?_),
    fun z hz' => ?_⟩
  · rcases h with h | h | h
    · exact hn.trans h
    · exact le_of_eq h.symm
    · exact absurd h List.not_mem_nil
  · obtain ⟨hE, _, hcls, hK⟩ := hz z hz'
    refine ⟨hE, (Adds.ofFresh _ d (List.ofFn u)).trans (hcls.mono fun e _ h =>
      h.imp_left fun h => ⟨h.1, hn.trans h.2.1, h.2.2⟩), ?_⟩
    show KeptAt d₂ (fun i b => pre i b (d₂.val d.vals.length)) Q.loc.shape 0 z.kept
    rw [hsv]
    exact hK

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.laid_run
#print axioms OnBytes.TokenRel.safe_hashT
