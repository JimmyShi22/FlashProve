-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/Bcs.lean: a proof of the statement
Compile.Batch.Spec.rec_bcs of CompileK/RecBindSpec.lean, by the generic lemmas of
Compile/Batch/Sound.lean and the one-line forms of Hiop/RecLine.lean.
What it is about: the verifier VR of CompileK/RecScheme.lean, whose design, by that file's head,
does not render the technical report's compilation.

-/
import CompileK.RecBindSpec
import Compile.Batch.Sound
import Ior.KnowWide

set_option autoImplicit false

noncomputable section

namespace Iop
open Prob

open Classical in
/-- The led verifier is local if Q's is. -/
theorem led_isLocal {Seed Ans Y : Type} [Fintype Seed] [Nonempty Seed] {E : ExtSpec} (Q : InteractiveOracleProof Y E)
    (rc : Y → Seed × Ans) (a0 : Ans) (h : Q.IsLocal) : (Q.led rc a0).IsLocal := by
  intro x y y' τ τ' hρ hpl hext hrd
  obtain ⟨m1, c1, m2, c2, t⟩ := τ
  obtain ⟨m1', c1', m2', c2', t'⟩ := τ'
  have hρ' : ((c1, c2, Tr.rho t) : Seed × Unit × Rho Q.shape) = (c1', c2', Tr.rho t') := hρ
  have hpl' : ((m1.2, m2.2, Tr.plains t) : Unit × Ans × Plains Q.shape) =
      (m1'.2, m2'.2, Tr.plains t') := hpl
  have e1 : c1 = c1' := congrArg Prod.fst hρ'
  have e2 : Tr.rho t = Tr.rho t' := congrArg (fun z => z.2.2) hρ'
  have e3 : m2.2 = m2'.2 := congrArg (fun z => z.2.1) hpl'
  have e4 : Tr.plains t = Tr.plains t' := congrArg (fun z => z.2.2) hpl'
  have ea : Q.accept x y t = Q.accept x y' t' :=
    h x y y' t t' e2 e4 hext fun p hp => hrd (.inr (.inr p)) (Finset.mem_image.2 ⟨p, hp, rfl⟩)
  have er : recTr (s := Q.shape) (a0 := a0) (m1, c1, m2, c2, t) =
      recTr (s := Q.shape) (a0 := a0) (m1', c1', m2', c2', t') := Prod.ext e1 e3
  rw [Bool.eq_iff_iff, led_accept, led_accept, er]
  exact and_congr_right fun _ => by
    show Q.accept x y t = true ↔ Q.accept x y' t' = true
    rw [ea]

end Iop

namespace Compile.Batch
open Iop Rom Prob
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

/-! ## The state function of a goal -/

section StG
variable {s : Shape} (ε : Err s) (goal : Tr s → Prop)

open Classical in
/-- 0 where the prover has lost towards the goal (Iop/State.lean). -/
def stG : PTr s → Bool := fun τ => decide (¬ Lost s ε goal τ)

variable {ε goal}

theorem stG_eq_false {τ : PTr s} : stG ε goal τ = false ↔ Lost s ε goal τ := by simp [stG]

theorem stG_eq_true {τ : PTr s} : stG ε goal τ = true ↔ ¬ Lost s ε goal τ := by simp [stG]

theorem stG_start (h : Doomed s ε goal) : stG ε goal (PTr.empty s) = false :=
  stG_eq_false.2 ((lost_empty _ _ _).2 h)

theorem stG_prover : ProverLaw s (stG ε goal) :=
  fun τ m h => stG_eq_false.2 (Lost.prover _ _ _ τ m (stG_eq_false.1 h))

theorem stG_full (τ : Tr s) (h : stG ε goal (.full τ) = false) : goal τ :=
  (lost_full _ _ _ τ).1 (stG_eq_false.1 h)

theorem stG_ver : VerLaw s ε (stG ε goal) :=
  fun τ h =>
    le_trans (cnt_mono fun _ hc => stG_eq_true.1 hc) (Lost.verifier _ _ _ τ (stG_eq_false.1 h))

theorem stG_joint {Y : Type} (ε : Err s) (g : Y → Tr s → Prop) (N : ℕ) (x : Fin N → Option Y) :
    JointLaw N s (RoundSplits.allLocal s) ε fun j => (x j).map fun a => stG ε (g a) := by
  have h := BatchH4.jointLaw_of_verLaw N s (RoundSplits.allLocal s) ε
    (fun j => (x j).map fun a => stG ε (g a)) (fun j S hS => by
      obtain ⟨xj, -, rfl⟩ := Option.map_eq_some_iff.1 hS
      exact stG_ver)
  rwa [timesShared_allLocal] at h

end StG

theorem instX_of_late_none {I X : Type} {L : BatchProtocol I X} (h : L.late = none) (xo : Option X) (i : ℕ) :
    instX L xo i = xo.map L.early := by
  unfold instX
  rw [h]

/-- A determined leaf under one of a link's two roots gives the symbol of the extracted string (the
last step of the link's clause in Compile/Batch/Sound.lean, as a lemma). -/
theorem agreeLk {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} (hW : W.OKG) {tr : Tc W}
    {cm cm' : Dig lam} (p : (twoExternalStrings L.wordLength L.Symbol).Pos) (a : (twoExternalStrings L.wordLength L.Symbol).Sym) (sl : Bits)
    (h : extLeaf tr W.Lk.ext.depth ([cm, cm'].getD (W.Lk.ext.which p) default) (W.Lk.ext.leaf p) =
      some ⟨some (.inl a), sl⟩) :
    (twoExternalStrings L.wordLength L.Symbol).rd (extEnc W tr cm, extEnc W tr cm') p = a := by
  rw [hW.extDepth.2.1] at h
  cases p with
  | inl p =>
    rw [(hW.extL.1 p).1, (hW.extL.1 p).2] at h
    exact extEnc_apply hW h
  | inr p =>
    rw [(hW.extL.2 p).1, (hW.extL.2 p).2] at h
    exact extEnc_apply hW h

/-! ## The three lanes -/

variable {I X Wn : Type} {lam : ℕ} {L : HolographicProtocol I X} {a0 : L.OutOfDomainAnswer}

/-- the goal of the offline chain: whatever record is claimed at the end -/
def goalOff (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (y : (oneExternalString L.wordLength L.Symbol).Str) :
    Tr (BatchInteractiveOracleProof.ofProto (L.offR a0)).loc.shape → Prop :=
  fun τ => ∀ rec : L.Rec, (L.offR a0).accept rec y τ = true → L.decodeIndex y rec ≠ none

/-- the goal of a link's chain, at the first record -/
def goalLink (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (y : (twoExternalStrings L.wordLength L.Symbol).Str) (rec0 : L.Rec) :
    Tr (BatchInteractiveOracleProof.ofProto (L.linkR a0)).loc.shape → Prop :=
  fun τ => ∀ rec : L.Rec,
    (L.linkR a0).accept (rec0, rec) y τ = true → L.decodeIndex y.2 rec = L.decodeIndex y.1 rec0

def errOff (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (eR : ℕ) (εT : Err L.offline.shape) :
    Err (BatchInteractiveOracleProof.ofProto (L.offR a0)).loc.shape :=
  show Err (recShape L.OutOfDomainSeed L.OutOfDomainAnswer a0 ++ L.offline.shape) from (eR, 0, εT)

def errLink (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (eR : ℕ) (εL : Err L.link.shape) :
    Err (BatchInteractiveOracleProof.ofProto (L.linkR a0)).loc.shape :=
  show Err (recShape L.OutOfDomainSeed L.OutOfDomainAnswer a0 ++ L.link.shape) from (eR, 0, εL)

/-- a record, for the places where none is read -/
def rec0 (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) : L.Rec := (Classical.arbitrary L.OutOfDomainSeed, a0)

def stOffR (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (eR : ℕ) (εT : Err L.offline.shape) :
    (oneExternalString L.wordLength L.Symbol).Str → L.Rec → PTr (BatchInteractiveOracleProof.ofProto (L.offR a0)).loc.shape → Bool :=
  fun y _ => stG (errOff L a0 eR εT) (goalOff L a0 y)

def stLinkR (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (eR : ℕ) (εL : Err L.link.shape) :
    (twoExternalStrings L.wordLength L.Symbol).Str → L.Rec × L.Rec → PTr (BatchInteractiveOracleProof.ofProto (L.linkR a0)).loc.shape → Bool :=
  fun y rr => stG (errLink L a0 eR εL) (goalLink L a0 y rr.1)

def xoutL (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) : Option L.XH → Option (L.Rec × L.Rec) :=
  fun xo => xo.map fun a => (a.2, rec0 L a0)

def xoutB (L : HolographicProtocol I X) : Option L.XH → Option (X × L.Rec) :=
  fun xo => xo.bind fun a => a.1.map fun x => (x, a.2)

variable (W : QueryLayout lam (L.carrier a0))

def laneTR (eR : ℕ) (εT : Err L.offline.shape) : Lane W :=
  laneOf W Tag.test (BatchInteractiveOracleProof.ofProto (L.offR a0)) (wOff W).sh (prjSym (L := L.carrier a0) Tag.test) some
    (errOff L a0 eR εT) (stOffR L a0 eR εT) (fun _ => some (rec0 L a0))
    fun tr cms => extEnc W tr (cms.getD 0 default)

def laneLR (eR : ℕ) (εL : Err L.link.shape) : Lane W :=
  laneOf W Tag.link (BatchInteractiveOracleProof.ofProto (L.linkR a0)) (wLink W).sh (prjSym (L := L.carrier a0) Tag.link) some
    (errLink L a0 eR εL) (stLinkR L a0 eR εL) (xoutL L a0)
    fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default))

def laneBR (εB : Err L.onlineBatch.loc.shape)
    (State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool) : Lane W :=
  laneOf W Tag.onl L.onlineBatch (wBat W).sh (prjSym (L := L.carrier a0) Tag.onl) some εB State (xoutB L)
    fun tr cms => extEnc W tr (cms.getD 0 default)

end Compile.Batch

namespace Compile.Batch
open Iop Rom Prob
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

theorem rec_bcs : Spec.rec_bcs := by
  intro I X Wn lam L a0 W Rno wit eR εT εL εB εs hS hmix heR hbT hbL hbB hl hlT hlL hlB hco hW
  obtain ⟨-, State, hB1, hB2, -, hB3, hB4⟩ :=
    (Iop.sndBKT_laws _ _ _ L.onlineBatch L.maxBatchSize (fun a => (L.early a.1, a.2)) L.late
      (fun a y w => L.relB Rno a.2 a.1 y w) wit εB).1 hmix
  have hl' : (L.carrier a0).late = none := hl
  have oT : (laneTR W eR εT).OK L.maxBatchSize :=
    laneOf_ok hW.T.sh fun y x => stG_joint (errOff L a0 eR εT) (fun _ => goalOff L a0 y) L.maxBatchSize x
  have oL : (laneLR W eR εL).OK L.maxBatchSize :=
    laneOf_ok hW.Lk.sh fun y x =>
      stG_joint (errLink L a0 eR εL) (fun rr : L.Rec × L.Rec => goalLink L a0 y rr.1) L.maxBatchSize x
  have oB : (laneBR W εB State).OK L.maxBatchSize := laneOf_ok hW.B.sh hB4
  have bT : Err.Below (laneTR W eR εT).ε εs := ⟨heR, by simp, hbT⟩
  have bL : Err.Below (laneLR W eR εL).ε εs := ⟨heR, by simp, hbL⟩
  refine ⟨fun tr =>
      (EM tr ∨ EF tr) ∨ StepEvent (stepS W (laneTR W eR εT) (laneLR W eR εL) (laneBR W εB State)) tr,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β A t hA
    have h := pr_stepEvent_le (S := spec lam W.K (L.carrier a0))
      (stepS W (laneTR W eR εT) (laneLR W eR εL) (laneBR W εB State)) (fun _ => εs)
      (fun pre e he hs =>
        hs.elim (fun h1 => h1.1 he) fun h1 => h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
      (fun pre o q _ => pr_stepS_le rfl rfl rfl hW.base.slots oT oL oB bT bL hbB pre o q) A t hA
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    calc
      pr A.withTrace.law
            {o | (EM o.2 ∨ EF o.2) ∨
              StepEvent (stepS W (laneTR W eR εT) (laneLR W eR εL) (laneBR W εB State)) o.2} ≤
          pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
            pr A.withTrace.law
              {o | StepEvent (stepS W (laneTR W eR εT) (laneLR W eR εL) (laneBR W εB State)) o.2} :=
        pr_union_le _ _ _
      _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
      _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
          rw [add_comm]
          gcongr
          exact Nat.le_succ t
  · rintro tr tr' ((h | h) | h)
    · exact Or.inl (Or.inl (h.append tr'))
    · exact Or.inl (Or.inr (h.append tr'))
    · exact Or.inr (StepEvent.append h tr')
  · intro tr cm rec π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.test (BatchInteractiveOracleProof.ofProto (L.offR a0)) (wOff W) _ id (fun _ => none)
      (fun s => some (.inl s)) hW.T (led_isLocal L.offline id a0 hlT)
      (Iop.BatchOne.BAnn.allLocal_coherent _) (Lg := fun rec y => L.decodeIndex y rec ≠ none)
      (stOffR L a0 eR εT)
      (prjSym (L := L.carrier a0) Tag.test) (fun p a => prjSym_emb (L := L.carrier a0) Tag.test p a) some (fun _ => rfl)
      (fun _ => some (rec0 L a0))
      (fun tr cms => extEnc W tr (cms.getD 0 default)) (errOff L a0 eR εT) hM
      (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inl h2⟩)) [cm] rec π
      (fun _ => rec0 L a0) (fun _ => rfl) (fun _ _ h => absurd rfl h)
      (fun y _ => stG_start (Iop.rec_line_test I X Wn L Rno wit eR εT εL εB a0 hS y))
      (fun y τ m _ h => stG_prover τ m h)
      (fun y τ hL h => Bool.eq_false_iff.2 fun hacc => hL (stG_full τ h rec hacc)) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp)))
      (fun p a sl h => by
        change extLeaf tr W.T.ext.depth ([cm].getD (W.T.ext.which p) default) (W.T.ext.leaf p) = _
          at h
        rw [hW.base.extDepth.1, (hW.base.extT p).1, (hW.base.extT p).2] at h
        exact extEnc_apply hW.base h)
  · intro tr cm cm' rec rec' π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.link (BatchInteractiveOracleProof.ofProto (L.linkR a0)) (wLink W) _ id
      (fun rr => some (none, rr.1))
      (fun s => some (.inl s)) hW.Lk (led_isLocal L.link Prod.snd a0 hlL)
      (Iop.BatchOne.BAnn.allLocal_coherent _)
      (Lg := fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1)
      (stLinkR L a0 eR εL)
      (prjSym (L := L.carrier a0) Tag.link) (fun p a => prjSym_emb (L := L.carrier a0) Tag.link p a) some (fun _ => rfl) (xoutL L a0)
      (fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default)))
      (errLink L a0 eR εL) hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inr (Or.inl h2)⟩))
      [cm, cm'] (rec, rec') π
      (fun _ => (rec, rec0 L a0)) (fun i => by rw [instX_of_late_none hl']; rfl)
      (fun n hn _ => by cases hl'.symm.trans hn)
      (fun y hL => stG_start
        (Iop.rec_line_link I X Wn L Rno wit eR εT εL εB a0 hS y rec fun h0 => hL (Or.inl h0)))
      (fun y τ m _ h => stG_prover τ m h)
      (fun y τ hL h => Bool.eq_false_iff.2 fun hacc => hL (Or.inr (stG_full τ h rec' hacc))) hrun
      (fun pre q a post htr hocc =>
        Prod.ext (extEnc_before htr hM (hocc _ (by simp)))
          (extEnc_before htr hM (hocc _ (by simp))))
      (fun p a sl h => agreeLk hW.base p a sl h)
  · intro tr cm x rec π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.onl L.onlineBatch (wBat W) _ id xinR (fun s => some (.inl s)) hW.B hlB hco
      (Lg := fun a y => L.decodeIndex y a.2 = none ∨ ∃ i, L.decodeIndex y a.2 = some i ∧ ∃ w, Rno i a.1 w) State
      (prjSym (L := L.carrier a0) Tag.onl) (fun p a => prjSym_emb (L := L.carrier a0) Tag.onl p a) some (fun _ => rfl) (xoutB L)
      (fun tr cms => extEnc W tr (cms.getD 0 default)) εB hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inr (Or.inr h2)⟩)) [cm]
      (x, rec) π
      (fun _ => (L.early x, rec)) (fun i => by rw [instX_of_late_none hl']; rfl)
      (fun n hn _ => by cases hl'.symm.trans hn)
      (fun y _ => hB1 y (x, rec))
      (fun y τ m _ h => hB2 y _ τ m h)
      (fun y τ hL h => Bool.eq_false_iff.2 fun hacc => hL (by
        have h3 := hB3 y (x, rec) τ
        rw [hl] at h3
        rcases h3 h hacc with h4 | ⟨i, hi, hr⟩
        · exact Or.inl h4
        · exact Or.inr ⟨i, hi, _, hr⟩)) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp)))
      (fun p a sl h => by
        change extLeaf tr W.B.ext.depth ([cm].getD (W.B.ext.which p) default) (W.B.ext.leaf p) = _
          at h
        rw [hW.base.extDepth.2.2, (hW.base.extB p).1, (hW.base.extB p).2] at h
        exact extEnc_apply hW.base h)
  · intro tr tr' cm hB hann
    exact extEnc_stable (fun h => hB (Or.inl (Or.inl h)))
      (List.prefix_append _ _) (occursIn_of_announced hann)

end Compile.Batch

#print axioms Compile.Batch.rec_bcs
