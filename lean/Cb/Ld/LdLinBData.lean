-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinBData.lean: the data of the test for linear constraints as a batch IOP: the annotation
is coherent; the positions read in the encoded index are a function of the shared verifier
messages, and at most t; with any closing chain whose annotations are coherent.

Definitions, statements (in `Iop.Spec` and `Cb.Spec`) and proofs. For the test on chains
(`P.linCA`, Cb/Ld/LdLinChainB.lean).
In standard terms: an annotation splits every prover message into a shared part and a slot's part;
it is coherent (`RoundSplits.Coherent`, Iop/Batch.lean) if in every round the plain string is the pair of
the two parts' plain strings and each oracle position is answered from one of the two parts alone.

Main names:
Generic (no protocol). e : ι → positions names the positions of one oracle (the encoded index) in
the implicit instance at a joint.
  `R.KeepsAt e e'`: R does not read that oracle and hands it on: the position e j is a source of the
    new position q if and only if q = e' j. `Spec.idx_keeps_seq`: two in a row.
  `a.Idx e t`, of a link with an annotation (`IOR.LinkA`): the annotation is coherent; nothing of
    that oracle survives (no e j is a source of a new position); which e j are read is a function of
    the shared verifier messages; every set of positions e j that are read has at most t elements.
  `Spec.idx_seq`: a link with `a.Idx e t`, then any link with a coherent annotation, has it: what
    follows cannot reach the oracle.
  `c.Coh`: every annotation of the chain is coherent. `Spec.idx_append`: as `Spec.idx_seq`, for
    chains: if the link of a chain c has `Idx e t` and c' has `Coh`, the link of `c.append c'` has
    `Idx e t`.
The test (in all four statements ι, the set of positions of the encoded index, is nonempty):
  `Spec.ldLinD_core`: the core has `Idx` at the encoded index, with t = `P.t` (how: its doc
    comment).
  `Spec.ldLinD_coherent`, `Spec.ldLinD_idxShared`, `Spec.ldLinD_idxReads`: for a closing chain with
    `cZ.Coh`: the items `coherent`, `idxShared`, `idxReads` of the parameter list `LinBListR`
    (Hiop/RecSubs.lean), in its notation (filter by "is a position of the first oracle").

Limits: this file says nothing on the honest side.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinChainB
import Ior.BatchSeqZkProofs
import Ior.BatchSeqZkRules
import Blocks.Batch.Kit

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR

/-- R does not read the oracle and hands it on. -/
structure KeepsAt {Xi Xo ι : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo)
    (e : ι → Ei.Pos) (e' : ι → Eo.Pos) : Prop where
  quiet : ∀ ρ j, e j ∉ R.extReads ρ
  src   : ∀ ρ q j, e j ∈ R.srcE ρ q ↔ q = e' j

/-- The oracle is read at few positions, which the shared verifier messages name, and does not
survive. -/
structure LinkA.Idx {K ι : Type} {A B : Joint K} (a : LinkA K A B) (e : ι → A.E.Pos) (t : ℕ) :
    Prop where
  coh    : a.ann.Coherent
  drop   : ∀ ρ q j, e j ∉ a.l.R.srcE ρ q
  shared : ∀ ρ ρ' j,
    Rho.sh a.ann ρ = Rho.sh a.ann ρ' → (e j ∈ a.l.R.extReads ρ ↔ e j ∈ a.l.R.extReads ρ')
  few    : ∀ ρ (S : Finset ι), (∀ j ∈ S, e j ∈ a.l.R.extReads ρ) → S.card ≤ t

/-- every annotation of the chain is coherent -/
def ChainA.Coh {K : Type} : {A B : Joint K} → ChainA K A B → Prop
  | _, _, .one a => a.ann.Coherent
  | _, _, .snoc c a => c.Coh ∧ a.ann.Coherent

theorem ChainA.coh_one {K : Type} {A B : Joint K} (a : LinkA K A B) :
    (ChainA.one a).Coh ↔ a.ann.Coherent := by rw [ChainA.Coh]
theorem ChainA.coh_snoc {K : Type} {A B C : Joint K} (c : ChainA K A B) (a : LinkA K B C) :
    (c.snoc a).Coh ↔ c.Coh ∧ a.ann.Coherent := by rw [ChainA.Coh]

end IOR

namespace Spec
open IOR

def idx_keeps_seq : Prop :=
  ∀ (X₁ X₂ X₃ ι : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (e₁ : ι → E₁.Pos) (e₂ : ι → E₂.Pos) (e₃ : ι → E₃.Pos),
    R₁.KeepsAt e₁ e₂ → R₂.KeepsAt e₂ e₃ → (R₁.seq R₂).KeepsAt e₁ e₃

/-- What follows cannot reach the oracle: a link with `Idx`, then a link with a coherent annotation,
has `Idx`. -/
def idx_seq : Prop :=
  ∀ (K ι : Type) (A B C : Joint K) (a : LinkA K A B) (a' : LinkA K B C) (d : A.W)
      (e : ι → A.E.Pos) (t : ℕ),
    a.Idx e t → a'.ann.Coherent → (a.seq a' d).Idx e t

def idx_append : Prop :=
  ∀ (K ι : Type) (A B C : Joint K) (c : ChainA K A B) (c' : ChainA K B C) (d : A.W)
      (e : ι → A.E.Pos) (t : ℕ),
    (c.linkA d).Idx e t → c'.Coh → ((c.append c').linkA d).Idx e t

end Spec

open IOR

theorem idx_keeps_seq : Spec.idx_keeps_seq := by
  intro X₁ X₂ X₃ ι E₁ E₂ E₃ R₁ R₂ e₁ e₂ e₃ h₁ h₂
  refine ⟨fun ρ j hj => ?_, fun ρ q j => ?_⟩
  · rcases (mem_seq_extReads R₁ R₂ ρ (e₁ j)).1 hj with h | ⟨q, hq, hs⟩
    · exact h₁.quiet _ j h
    · rw [(h₁.src _ q j).1 hs] at hq
      exact h₂.quiet _ j hq
  · rw [mem_seq_srcE]
    constructor
    · rintro ⟨q', hq', hs⟩
      rw [(h₁.src _ q' j).1 hs] at hq'
      exact (h₂.src _ q j).1 hq'
    · exact fun h => ⟨e₂ j, (h₂.src _ q j).2 h, (h₁.src _ _ j).2 rfl⟩

/-- if no e j is a source of a new position of the first link (`hd`), the positions of the oracle
that two links in a row read are those that the first reads -/
theorem ldk_idx_reads {K ι : Type} {A B C : Joint K} (a : LinkA K A B) (a' : LinkA K B C)
    (d : A.W) (e : ι → A.E.Pos) (hd : ∀ ρ q j, e j ∉ a.l.R.srcE ρ q)
    (ρ : Rho (a.l.R.shape ++ a'.l.R.shape)) (j : ι) :
    e j ∈ (a.seq a' d).l.R.extReads ρ ↔ e j ∈ a.l.R.extReads (Rho.fst ρ) := by
  show e j ∈ (a.l.R.seq a'.l.R).extReads ρ ↔ _
  rw [mem_seq_extReads]
  exact ⟨fun h => h.elim id fun ⟨q, _, hs⟩ => absurd hs (hd _ q j), Or.inl⟩

theorem idx_seq : Spec.idx_seq := by
  intro K ι A B C a a' d e t h hc
  refine ⟨RoundSplits.app_coherent h.coh hc, fun ρ q j hj => ?_, fun ρ ρ' j hρ => ?_, fun ρ S hS => ?_⟩
  · obtain ⟨q', _, hs⟩ := (mem_seq_srcE a.l.R a'.l.R ρ q (e j)).1 hj
    exact h.drop _ q' j hs
  · rw [ldk_idx_reads a a' d e h.drop, ldk_idx_reads a a' d e h.drop]
    refine h.shared _ _ j ?_
    rw [← RhoSh.fstA_sh a.ann a'.ann ρ, ← RhoSh.fstA_sh a.ann a'.ann ρ']
    exact congrArg _ hρ
  · exact h.few (Rho.fst ρ) S fun j hj => (ldk_idx_reads a a' d e h.drop ρ j).1 (hS j hj)

theorem idx_append : Spec.idx_append := by
  intro K ι A B C c c' d e t h
  induction c' with
  | one a =>
      intro hc
      rw [ChainA.append_one, ChainA.linkA_snoc]
      exact idx_seq K ι _ _ _ _ a d e t h ((ChainA.coh_one a).1 hc)
  | snoc c' a ih =>
      intro hc
      rw [ChainA.append_snoc, ChainA.linkA_snoc]
      exact idx_seq K ι _ _ _ _ a d e t (ih ((ChainA.coh_snoc c' a).1 hc).1)
        ((ChainA.coh_snoc c' a).1 hc).2

/-- `KeepsAt` for a step without rounds that copies the oracles. -/
theorem ldk_keeps_pure {X ι : Type} {Ex : ExtSpec} (e : ι → Ex.Pos) :
    (IOR.pure (Xi := X) some (ExtMap.id Ex)).KeepsAt e e :=
  ⟨fun _ _ h => absurd h (Finset.notMem_empty _),
    fun _ _ _ => ⟨fun h => (Finset.mem_singleton.1 h).symm, fun h => Finset.mem_singleton.2 h.symm⟩⟩

/-- after any rounds: shared rounds in which only the shared part speaks have all their verifier
messages among the shared ones -/
theorem ldk_snd_of_sh {s t : Shape} (A : RoundSplits s) {ρ ρ' : Rho (s ++ t)}
    (h : Rho.sh (RoundSplits.app A (RoundSplits.const (RAnn.ofShared .sh) t)) ρ =
      Rho.sh (RoundSplits.app A (RoundSplits.const (RAnn.ofShared .sh) t)) ρ') :
    Rho.snd (s := s) ρ = Rho.snd (s := s) ρ' := by
  rw [← RhoSh.all_sh t (Rho.snd (s := s) ρ), ← RhoSh.all_sh t (Rho.snd (s := s) ρ'),
    ← RhoSh.sndA_sh A _ ρ, ← RhoSh.sndA_sh A _ ρ', h]

theorem ldk_snd_of_shA {K : Type} {A B C : Joint K} (a : LinkA K A B) (a' : LinkA K B C) (d : A.W)
    (h' : a'.ann = RoundSplits.const (RAnn.ofShared .sh) a'.l.R.shape)
    {ρ ρ' : Rho (a.l.R.shape ++ a'.l.R.shape)}
    (h : Rho.sh (a.seq a' d).ann ρ = Rho.sh (a.seq a' d).ann ρ') :
    Rho.snd (s := a.l.R.shape) ρ = Rho.snd (s := a.l.R.shape) ρ' := by
  have h2 : Rho.sh (RoundSplits.app a.ann a'.ann) ρ = Rho.sh (RoundSplits.app a.ann a'.ann) ρ' := h
  rw [h'] at h2
  exact ldk_snd_of_sh a.ann h2

/-- the positions on the left, counted in two ways -/
theorem ldk_card_filter_isLeft
    {α β : Type} {inst : DecidablePred fun p : α ⊕ β => p.isLeft = true} (S : Finset (α ⊕ β)) :
    (@Finset.filter _ (fun p => p.isLeft = true) inst S).card = S.toLeft.card := by
  have e : @Finset.filter _ (fun p => p.isLeft = true) inst S =
      S.toLeft.map Function.Embedding.inl := by
    ext p
    rcases p with a | b
    · simp [Finset.mem_toLeft]
    · simp
  rw [e, Finset.card_map]

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldk_keeps_send {E ι : Type} [Field E] (N : Sig E) (Sd : N.Seeds) (X : Type)
    (E₀ : ExtSpec) (e : ι → E₀.Pos) :
    (ldSendFam N Sd X E₀).KeepsAt e fun j => Sum.inl (e j) := by
  refine ⟨fun _ _ h => absurd h (Finset.notMem_empty _), fun _ q j => ?_⟩
  rcases q with q | q
  · exact ⟨fun h => congrArg Sum.inl (Finset.mem_singleton.1 h).symm,
      fun h => Finset.mem_singleton.2 (Sum.inl.inj h).symm⟩
  · exact ⟨fun h => absurd h (Finset.notMem_empty _), fun h => by cases h⟩

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- For a nonempty ι the core has `Idx` at the encoded index, with t = `P.t`: the encoded index is
read at the t drawn locations alone, which are a shared verifier message, and is dropped there. -/
def ldLinD_core : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
      (εf N : ℕ) (S : P.Snd) (d : P.W0),
    ((P.chainA on0 S εf N).linkA d).Idx (fun j : ι => (Sum.inl j : P.E0.Pos)) P.t

def ldLinD_coherent : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (cZ : ChainA Unit P.J6 LdLinP.JT) (d : P.W0),
    cZ.Coh → (P.linCA on0 S εf N cZ d).ann.Coherent

open Classical in
def ldLinD_idxShared : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (cZ : ChainA Unit P.J6 LdLinP.JT) (d : P.W0),
    cZ.Coh →
    ∀ ρ ρ', Rho.sh (P.linCA on0 S εf N cZ d).ann ρ = Rho.sh (P.linCA on0 S εf N cZ d).ann ρ' →
      (((P.linCA on0 S εf N cZ d).l.R.extReads ρ : Finset P.E0.Pos)).filter (fun p => p.isLeft) =
        (((P.linCA on0 S εf N cZ d).l.R.extReads ρ' : Finset P.E0.Pos)).filter (fun p => p.isLeft)

open Classical in
def ldLinD_idxReads : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (cZ : ChainA Unit P.J6 LdLinP.JT) (d : P.W0),
    cZ.Coh →
    ∀ ρ, ((((P.linCA on0 S εf N cZ d).l.R.extReads ρ : Finset P.E0.Pos)).filter
        (fun p => p.isLeft)).card ≤ P.t

end
end Spec

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- up to the locations the encoded index is kept -/
theorem LdLinP.keeps4 (P : LdLinP E ι κ J Y) :
    (((P.step0.seq P.sW).seq P.pt).seq P.sU).KeepsAt (fun j : ι => (Sum.inl j : P.E0.Pos))
      (fun j => (Sum.inl (Sum.inl (Sum.inl j)) : P.E3.Pos)) := by
  have h0 : P.step0.KeepsAt (fun j : ι => (Sum.inl j : P.E0.Pos))
      (fun j : ι => (Sum.inl j : P.E0.Pos)) := ldk_keeps_pure _
  have hW : P.sW.KeepsAt (fun j : ι => (Sum.inl j : P.E0.Pos))
      (fun j => (Sum.inl (Sum.inl j) : P.E1.Pos)) :=
    ldk_keeps_send P.NW P.SdW P.X0 P.E0 _
  have hP : P.pt.KeepsAt (fun j : ι => (Sum.inl (Sum.inl j) : P.E1.Pos))
      (fun j => (Sum.inl (Sum.inl j) : P.E1.Pos)) :=
    ⟨fun _ _ h => absurd h (Finset.notMem_empty _),
      fun _ q j =>
        ⟨fun h => (Finset.mem_singleton.1 h).symm, fun h => Finset.mem_singleton.2 h.symm⟩⟩
  have hU : P.sU.KeepsAt (fun j : ι => (Sum.inl (Sum.inl j) : P.E1.Pos))
      (fun j => (Sum.inl (Sum.inl (Sum.inl j)) : P.E3.Pos)) :=
    ldk_keeps_send P.NU P.SdU P.X2 P.E1 _
  exact idx_keeps_seq _ _ _ _ _ _ _ _ _ _ _ _
    (idx_keeps_seq _ _ _ _ _ _ _ _ _ _ _ _ (idx_keeps_seq _ _ _ _ _ _ _ _ _ _ _ _ h0 hW) hP) hU

theorem ldLinD_core : Spec.ldLinD_core E ι κ J Y := by
  classical
  intro P on0 εf N S d
  unfold LdLinP.chainA
  simp only [ChainA.linkA_snoc, ChainA.linkA_one]
  have cs : ∀ s : Shape, (LdLinP.shAnn s).Coherent :=
    RoundSplits.const_coherent fun r => RAnn.ofShared_coherent .sh r
  have cl : ∀ s : Shape, (RoundSplits.allLocal s).Coherent :=
    RoundSplits.const_coherent (f := RAnn.allLocal) fun r => RAnn.ofSlot_coherent .lo r
  refine idx_seq _ _ _ _ _ _ _ d _ _ (idx_seq _ _ _ _ _ _ _ d _ _ ?_ (cs _)) (cs _)
  have hk := P.keeps4
  have hread : ∀ (ρ : Rho ((((P.step0.seq P.sW).seq P.pt).seq P.sU).shape ++ P.loc.shape)) (j : ι),
      (Sum.inl j : P.E0.Pos) ∈ ((((P.step0.seq P.sW).seq P.pt).seq P.sU).seq P.loc).extReads ρ ↔
      ∃ i, (show (Fin P.t → ι) × Unit
          from Rho.snd (s := (((P.step0.seq P.sW).seq P.pt).seq P.sU).shape) ρ).1 i = j := by
    intro ρ j
    rw [mem_seq_extReads]
    constructor
    · rintro (h | ⟨q, hq, hs⟩)
      · exact absurd h (hk.quiet _ j)
      · rw [(hk.src _ q j).1 hs] at hq
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hq
        exact ⟨i, Sum.inl.inj (Sum.inl.inj (Sum.inl.inj hi))⟩
    · rintro ⟨i, rfl⟩
      exact Or.inr ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, (hk.src _ _ _).2 rfl⟩
  refine ⟨RoundSplits.app_coherent
      (RoundSplits.app_coherent (RoundSplits.app_coherent (RoundSplits.app_coherent (cl _) (cl _)) (cs _)) (cs _))
      (cs _),
    fun ρ q j hj => ?_, fun ρ ρ' j hρ => ?_, fun ρ T hT => ?_⟩
  · obtain ⟨q', hq', hs⟩ :=
      (mem_seq_srcE (((P.step0.seq P.sW).seq P.pt).seq P.sU) P.loc ρ q (Sum.inl j)).1 hj
    rw [(hk.src _ q' j).1 hs] at hq'
    rcases q with (q | q) | q
    · exact absurd (Finset.mem_singleton.1 hq') (by simp)
    · exact absurd (Finset.mem_singleton.1 hq') (by simp)
    · exact absurd (Finset.mem_singleton.1 hq') (by simp)
  · have e3 : Rho.snd (s := (((P.step0.seq P.sW).seq P.pt).seq P.sU).shape) ρ =
        Rho.snd (s := (((P.step0.seq P.sW).seq P.pt).seq P.sU).shape) ρ' :=
      ldk_snd_of_shA _ _ d rfl hρ
    have eQ : (show (Fin P.t → ι) × Unit
          from Rho.snd (s := (((P.step0.seq P.sW).seq P.pt).seq P.sU).shape) ρ).1 =
        (show (Fin P.t → ι) × Unit
          from Rho.snd (s := (((P.step0.seq P.sW).seq P.pt).seq P.sU).shape) ρ').1 :=
      congrArg (fun z : Rho P.loc.shape => (show (Fin P.t → ι) × Unit from z).1) e3
    exact (hread ρ j).trans
      (Iff.trans
        ⟨fun ⟨i, hi⟩ => ⟨i, (congrFun eQ i).symm.trans hi⟩,
          fun ⟨i, hi⟩ => ⟨i, (congrFun eQ i).trans hi⟩⟩
        (hread ρ' j).symm)
  · have hsub : T ⊆
        Finset.univ.image
          (show (Fin P.t → ι) × Unit
            from Rho.snd (s := (((P.step0.seq P.sW).seq P.pt).seq P.sU).shape)
              ρ).1 := fun j hj => by
      obtain ⟨i, hi⟩ := (hread ρ j).1 (hT j hj)
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_univ, Fintype.card_fin]

theorem LdLinP.idxAll (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (εf N : ℕ) (S : P.Snd) (cZ : ChainA Unit P.J6 LdLinP.JT) (d : P.W0) (hc : cZ.Coh) :
    (P.linCA on0 S εf N cZ d).Idx (fun j : ι => (Sum.inl j : P.E0.Pos)) P.t :=
  idx_append Unit ι (P.J0 on0) P.J6 LdLinP.JT (P.chainA on0 S εf N) cZ d
    (fun j : ι => (Sum.inl j : P.E0.Pos)) P.t (ldLinD_core P on0 εf N S d) hc

theorem ldLinD_coherent : Spec.ldLinD_coherent E ι κ J Y := fun P on0 εf N S cZ d hc =>
  (P.idxAll on0 εf N S cZ d hc).coh

theorem ldLinD_idxShared : Spec.ldLinD_idxShared E ι κ J Y := by
  classical
  intro P on0 εf N S cZ d hc ρ ρ' hρ
  have h := P.idxAll on0 εf N S cZ d hc
  ext p
  rw [Finset.mem_filter, Finset.mem_filter]
  rcases p with j | p
  · exact and_congr_left fun _ => h.shared ρ ρ' j hρ
  · exact ⟨fun hp => absurd hp.2 (by simp), fun hp => absurd hp.2 (by simp)⟩

theorem ldLinD_idxReads : Spec.ldLinD_idxReads E ι κ J Y := by
  classical
  intro P on0 εf N S cZ d hc ρ
  have h := P.idxAll on0 εf N S cZ d hc
  refine le_of_eq_of_le (ldk_card_filter_isLeft (α := ι) (β := P.Ea.Pos) _) ?_
  exact h.few ρ _ fun j hj => Finset.mem_toLeft.1 hj

end
end Cb
