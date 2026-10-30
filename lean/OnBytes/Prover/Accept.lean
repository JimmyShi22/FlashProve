-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Accept.lean: the transcript that the compiled verifier builds from the compiled
prover's openings (`mkTr`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) shows, wherever the decision
reads, what the prover has kept (OnBytes/Prover/Inv.lean); so a local decision that says yes at the
prover's transcript says yes at the verifier's.

Main names:
  `rho_trK`        the verifier messages of the transcript as it was hashed
  `effPlain_eq`    one round: where a component that is not sent is empty, the plain part that the
                   verifier uses is the prover's
  `effPlains_at`   the same for all rounds, from the invariant
  `rootAt_of_treeOf`   a position whose tree has a depth and a root has a root
  `read_mkTr_at`   at a read position the verifier's transcript shows the symbol that is kept
  `mkTr_at`        both: the plain parts, and the symbols at the read positions
  `rdS_at`         which positions are read: those that are read at the prover's plain parts
  `accept_at`      the decision at the verifier's transcript and the external string that it builds

Limits: one direction only. Nothing says that a prover's run meets the invariant (that is
OnBytes/Prover/Chain.lean), nor that the decision says yes at the prover's transcript: that is a
premise. Nothing on probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Inv

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The verifier messages and the plain parts -/

theorem rho_trK : ∀ (s : Shape) (kp : Kept lam L s) (ρ : Rho s), (trK s kp ρ).rho = ρ
  | [], _, () => rfl
  | _ :: s, (_, ks), (c, ρ) => congrArg (Prod.mk c) (rho_trK s ks ρ)

/-- Under `a.Coherent`: where a component that is not sent is empty, the plain part that the
verifier uses is the prover's. -/
theorem effPlain_eq {r : Round} {a : RAnn r} (hC : a.Coherent) (rt : RtC lam × RtC lam)
    (h1 : rt.1 = none → a.NoShared) (h2 : rt.2 = none → a.NoSlot) (m : r.Msg) :
    effPlain a rt m.2 = m.2 := by
  have hm := hC.plain_join (a.split m).1 (a.split m).2
  rw [join_split] at hm
  have hd := hC.plain_join (a.split (r.dOrc, r.dPlain)).1 (a.split (r.dOrc, r.dPlain)).2
  rw [join_split] at hd
  have e1 : (if rt.1.isSome then (a.plain m.2).1 else (a.plain r.dPlain).1) = (a.plain m.2).1 := by
    cases h : rt.1 with
    | some c => rfl
    | none =>
      haveI := (h1 h).2
      show (a.plain r.dPlain).1 = _
      rw [hm, hd, Subsingleton.elim (a.split (r.dOrc, r.dPlain)).1 (a.split m).1]
  have e2 : (if rt.2.isSome then (a.plain m.2).2 else (a.plain r.dPlain).2) = (a.plain m.2).2 := by
    cases h : rt.2 with
    | some c => rfl
    | none =>
      haveI := (h2 h).2
      show (a.plain r.dPlain).2 = _
      rw [hm, hd, Subsingleton.elim (a.split (r.dOrc, r.dPlain)).2 (a.split m).2]
  unfold effPlain
  rw [e1, e2, Prod.mk.eta, Equiv.symm_apply_apply]

theorem effPlains_at {g : Fam (typedOracleFamily lam K L)} {sMT : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (kp : Kept lam L s) (R : RootsOfChain lam s) (ρ : Rho s),
      RoundsAt g sMT s A W embS kp R → A.Coherent →
      effPlains s A R (trK s kp ρ).plains = (trK s kp ρ).plains
  | [], _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (_, W), embS, (kp, ks), (rt, R), (_, ρ), hR, hC => by
    obtain ⟨h0, hJ, hr⟩ := hR
    show (effPlain a rt kp.1.2, effPlains s A R (trK s ks ρ).plains) =
      (kp.1.2, (trK s ks ρ).plains)
    rw [effPlain_eq hC.1 rt
        (fun e => h0.elim (fun z => z.2.2) fun z => by rw [z.1] at e; cases e)
        (fun e => hJ.elim (fun z => z.2.2) fun z => by rw [z.1] at e; cases e) kp.1,
      effPlains_at s A W (fun p => embS (.inr p)) ks R ρ hr hC.2]

/-! ## The symbols at the read positions -/

/-- a position of the first round whose tree has a depth and a root has a root -/
theorem rootAt_of_treeOf {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam K r a}
    {W : RoundsQueryLayout lam K s A} {rt : RtC lam × RtC lam} {R : RootsOfChain lam s} {p : r.Pos} {d : ℕ}
    {c : Dig lam} (h : treeOf (r :: s) (a, A) (w, W) (rt, R) (.inl p) = some (d, c)) :
    rootAt w rt p = true := by
  unfold rootAt
  simp only [treeOf] at h
  by_cases ho : a.own p = true
  · rw [if_pos ho] at h
    rw [if_pos ho, (treeAt_eq_some h).2, Option.isSome_some]
  · rw [if_neg ho] at h
    rw [if_neg ho, (treeAt_eq_some h).2, Option.isSome_some]

/-- At a read position the transcript that the verifier builds from the prover's openings shows the
symbol that the prover has kept. -/
theorem read_mkTr_at {g : Fam (typedOracleFamily lam K L)} {sMT : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (kp : Kept lam L s) (R : RootsOfChain lam s) (rd : OPos s → Bool),
      RoundsAt g sMT s A W embS kp R → RoundsQueryLayout.OKG s A W →
      ∀ (pls : Plains s) (ρ : Rho s) (p : OPos s), rd p = true →
        (mkTr s A W R pls ρ (opensK s A W kp rd)).read p = symK s kp p
  | [], _, _, _, _, _, _, _, _, _, _, p, _ => nomatch p
  | r :: s, (a, A), (w, W), embS, (kp, ks), (rt, R), rd, hR, hW, (_, _), (_, _), .inl p, hp => by
    obtain ⟨T, d, ht, -, -, ho, -, -⟩ :=
      look (r :: s) (a, A) (w, W) embS (kp, ks) (rt, R) rd hR hW (.inl p) hp
    show Round.rd _ (w.pt.ofSyms _) p = _
    rw [w.pt.rd_ofSyms]
    simp only [rootAt_of_treeOf ht, ho]
    rfl
  | _ :: s, (_, A), (_, W), embS, (_, ks), (_, R), rd, hR, hW, (_, pls), (_, ρ), .inr q, hp =>
    read_mkTr_at s A W (fun p => embS (.inr p)) ks R (fun p => rd (.inr p)) hR.2.2 hW.2 pls ρ q hp

/-- **The verifier's transcript against the prover's.** The plain parts that the verifier uses are
the prover's; at each read position the verifier's transcript shows the prover's symbol. -/
theorem mkTr_at :
  ∀ (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L) (kp : Kept lam L s)
    (R : RootsOfChain lam s) (ρ : Rho s) (rd : OPos s → Bool),
  RoundsAt g sMT s A W embS kp R → A.Coherent → RoundsQueryLayout.OKG s A W →
  effPlains s A R (trK s kp ρ).plains = (trK s kp ρ).plains ∧
    ∀ p, rd p = true →
      (mkTr s A W R (trK s kp ρ).plains ρ (opensK s A W kp rd)).read p = (trK s kp ρ).read p :=
  fun _ _ s A W embS kp R ρ rd hR hC hW =>
    ⟨effPlains_at s A W embS kp R ρ hR hC, fun p hp => by
      rw [read_trK]
      exact read_mkTr_at s A W embS kp R rd hR hW _ ρ p hp⟩

section
variable (sMT : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)

variable {sMT Q embS} in
/-- Which positions are read, given the roots: under the invariant the plain parts that the verifier
uses are the prover's, so these are the positions that are read at the prover's plain parts. -/
theorem rdS_at {g : Fam (typedOracleFamily lam K L)} {kp : Kept lam L Q.loc.shape} {R : RootsOfChain lam Q.loc.shape}
    (ρ : Rho Q.loc.shape) (hR : RoundsAt g sMT Q.loc.shape Q.ann wq.sh embS kp R)
    (hC : Q.ann.Coherent) :
    rdS Q wq x (trK Q.loc.shape kp ρ).plains ρ R =
      haveI := wq.decO
      fun p => decide (p ∈ Q.loc.reads x ρ (trK Q.loc.shape kp ρ).plains) := by
  unfold rdS
  rw [effPlains_at Q.loc.shape Q.ann wq.sh embS kp R ρ hR hC]

/-- **The decision.** If the decision is local and says yes at the external strings y and the
transcript as the prover has hashed it, it says yes at what the verifier builds from the prover's
openings. -/
theorem accept_at :
  ∀ (g : Fam (typedOracleFamily lam K L)) (kp : Kept lam L Q.loc.shape) (R : RootsOfChain lam Q.loc.shape)
    (ρ : Rho Q.loc.shape),
  RoundsAt g sMT Q.loc.shape Q.ann wq.sh embS kp R → Q.ann.Coherent → wq.OKG → Q.loc.IsLocal →
  Q.loc.accept x y (trK Q.loc.shape kp ρ) = true →
  Q.loc.accept x
    (wq.ext.build fun p => ((extK wq.ext y xt (rdE Q wq x ρ)) p).map Opening.sym)
    (mkTr Q.loc.shape Q.ann wq.sh R (trK Q.loc.shape kp ρ).plains ρ
      (opensK Q.loc.shape Q.ann wq.sh kp
        (rdS Q wq x (trK Q.loc.shape kp ρ).plains ρ R))) = true := by
  intro g kp R ρ hR hC hw hloc hacc
  obtain ⟨he, hrd⟩ := mkTr_at g sMT Q.loc.shape Q.ann wq.sh embS kp R ρ
    (rdS Q wq x (trK Q.loc.shape kp ρ).plains ρ R) hR hC hw.sh
  have hρ : (trK Q.loc.shape kp ρ).rho = ρ := rho_trK _ kp ρ
  refine (hloc x y _ _ _ ?_ ?_ ?_ ?_).symm.trans hacc
  · rw [hρ, mkTr_rho]
  · rw [mkTr_plains, he]
  · intro p hp
    rw [hρ] at hp
    have hr : rdE Q wq x ρ p = true := by
      letI := wq.ext.dec
      exact decide_eq_true hp
    have e : extK wq.ext y xt (rdE Q wq x ρ) p =
        some ((xt (wq.ext.which p)).opening (wq.ext.leaf p) (E.rd y p)) := if_pos hr
    refine (hw.ext.build_rd _ p _ ?_).symm
    exact congrArg (Option.map Opening.sym) e
  · intro p hp
    rw [hρ] at hp
    refine (hrd p ?_).symm
    have hp' : p ∈ Q.loc.reads x ρ
        (effPlains Q.loc.shape Q.ann R (trK Q.loc.shape kp ρ).plains) := by
      rw [he]
      exact hp
    letI := wq.decO
    exact decide_eq_true hp'

end

end OnBytes.Prover
