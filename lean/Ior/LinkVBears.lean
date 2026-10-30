-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVBears.lean: what a chain of batch links needs of its oracles, for families of slots.
Pieces of such a chain, and what a whole chain has at the end.

In standard terms: for the sequential composition of interactive oracle reductions that run on a
batch of instances, an invariant on sets of oracle positions that each reduction carries back from
what follows it to what comes before it.

Definitions, statements and proofs. No protocol occurs here. The analogue, for sets of slots, of
Ior/Bears.lean and of the honest half of Cb/Ld/LdTowerKit.lean.

A batch link is an IOR with an annotation of its shape (`RoundSplits`, Iop/Batch.lean) and an honest side
(`IOR.HonestV`, Ior/LinkV.lean). A slot is one of the N places of a batch; the statements here
speak of a set J of slots, each with one instance.

Notions of other files, for an IOR R (`given`: Ior/Honest.lean; `need`, `Bears`: Ior/Bears.lean):
  `R.srcO ρ q`, `R.srcE ρ q` (Ior/Ior.lean), the sources of q: the positions of the prover's
    oracles, and of the old implicit instance, from whose symbols the symbol at q of the new
    implicit instance is computed (data; the condition: `IOR.IsLocal`, Ior/Ior.lean).
  `R.given ρ T` is the set of positions of the implicit instance that the verifier reads at ρ,
    together with `R.tie ρ p` for every p that the verifier reads in the prover's oracles or that
    is in T.
  `R.need ρ U`, for a set U of positions of the new implicit instance: `R.given ρ` of the
    positions `R.srcO ρ q` for q in U, together with the positions `R.srcE ρ q` for q in U.
  `R.Bears bud qi qo`: for every ρ and every set U of positions of the new implicit instance for
    which qo holds, `bud ρ` holds of the positions `R.srcO ρ q` for q in U, and qi holds of
    `R.need ρ U`. Here it is a premise, of `Spec.bearsV_local` and `Spec.bearsV_shared`, written
    `R.Bears bud q₁ q₂`: these three speak of one set of positions, not of a family as bud, qi, qo
    do in the rows below.
  `R.IsLocal` (Ior/Ior.lean), "local" below: the verifier's output and the symbols of the new
    implicit instance depend on the oracles only at the positions declared.
  `H.AccV` (Ior/LinkV.lean), "complete" below: see its row in that file's head.

Why: the budget of "a link, then a link" (Ior/LinkV.lean: `budSeqV`) is nested: the first link
bears, as a family over the slots of J, the sources of all that the second simulator is given. For
a chain of many links one wants one invariant for each link. An oracle of one slot is read through
that slot alone. An oracle of the shared part is read through all slots of J, and its encoding has
to bear the union. So the invariants are predicates on families of sets of positions.

Main names (each row of a `Spec` name: under the hypotheses of its statement):
  `QFam E N`: a predicate on (J, a set of positions of the oracles of kind E for each slot of J).
    `q.Her`: it is kept by subsets of J.
  `R.BearsV A bud qi qo`: whenever the family (U_j) is within qo,
      (i) R's budget bears the family of the sources of the U_j in R's oracles, and
      (ii) the family of what is then needed of the old implicit instances (`IOR.need`, slot by
        slot) is within qi.
    Asked at the verifier messages of an execution of the batch (so in a shared round all slots
    have the same).
  `Spec.bearsV_seq`: it composes, at the composed budget; asked: the last predicate is kept by
    subsets of J.
  `Spec.bearsV_local`: for the budget of a run in every slot ("each slot's budget"): from
    `IOR.Bears` for one instance, if a family within qo has each member within the one-instance
    predicate; what is needed is left to the user.
  `Spec.bearsV_shared`: for the budget of a run by the shared part alone ("at the union"): from
    `IOR.Bears` for one instance, if a family within qo has its union within the one-instance
    predicate.
  `Spec.exactV_mono`: a smaller relation; a smaller budget (compared at executions of the batch
    only).
  `PieceV R A H N Ri Ro bud qi qo`:
      local;
      complete;
      honest-verifier exactly zero knowledge for sets of slots at bud (`PieceV.exact`:
        `HonestV.ExactV`, Ior/LinkV.lean);
      bears what follows.
  `Spec.pieceV_seq`: a piece, then a piece, is a piece.
  `Spec.pieceV_end`: what a whole chain has at the end, if nothing follows: qo is true of the
    empty family (for a link to a statement without oracles there is no other family):
      complete;
      honest-verifier exactly zero knowledge at no further reads (the budget "every T_j is empty",
        which holds of the empty family whatever the verifier messages are: the form that a
        parameter list asks);
      and the family of what the simulator is given is within qi.

Limits: this file says nothing on soundness; nothing on links whose masks were sent earlier
(Ior/LinkVMasked.lean). Further reads by a distinguisher, beside what follows in the chain, are
not in `BearsV`.

Terms: lean/GLOSSARY.md.
-/
import Ior.LinkVSeq
import Ior.LinkVRules
import Ior.BearsProofs
import Ior.SeqProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- A predicate on families of sets of positions, one set for each slot of J. -/
abbrev QFam (E : ExtSpec) (N : ℕ) : Type := (J : Finset (Fin N)) → (J → Finset E.Pos) → Prop

/-- q is kept by subsets of J. -/
def QFam.Her {E : ExtSpec} {N : ℕ} (q : QFam E N) : Prop :=
  ∀ (J J' : Finset (Fin N)) (h : J' ⊆ J) (Us : J → Finset E.Pos),
    q J Us → q J' fun j => Us ⟨j.1, h j.2⟩

namespace IOR
variable {X X' X'' : Type} {Ei Eo Eo' : ExtSpec}

open Classical in
/-- R bears what follows, for families of slots. -/
def BearsV (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) {N : ℕ} (bud : BudB R.shape N)
    (qi : QFam Ei N) (qo : QFam Eo N) : Prop :=
  ∀ (J : Finset (Fin N)) (ρ : BRho N R.shape A) (Us : J → Finset Eo.Pos), qo J Us →
    bud J (fun j => ρ.slot j.1) (fun j => (Us j).biUnion (R.srcO (ρ.slot j.1))) ∧
    qi J fun j => R.need (ρ.slot j.1) (Us j)

/-- A piece of a chain of batch links: the honest half. -/
structure PieceV (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) {W0 Wj W0' Wj' : Type}
    (H : R.HonestV A W0 Wj W0' Wj') (N : ℕ) (Ri : X → Ei.Str → W0 × Wj → Prop)
    (Ro : X' → Eo.Str → W0' × Wj' → Prop) (bud : BudB R.shape N) (qi : QFam Ei N) (qo : QFam Eo N) :
    Prop where
  isLocal : R.IsLocal
  acc     : H.AccV Ri Ro
  exact   : H.ExactV N Ri bud
  bears   : R.BearsV A bud qi qo

end IOR

namespace Spec
open IOR

/-- States, under the hypotheses below: bearing composes, at the composed budget. -/
def bearsV_seq : Prop :=
  ∀ (X X' X'' : Type) (Ei Eo Eo' : ExtSpec) (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo')
      (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (N : ℕ) (b₁ : BudB R₁.shape N)
      (b₂ : BudB R₂.shape N) (qa : QFam Ei N) (qb : QFam Eo N) (qc : QFam Eo' N),
    R₁.BearsV A₁ b₁ qa qb → R₂.BearsV A₂ b₂ qb qc → qc.Her →
    (R₁.seq R₂).BearsV (RoundSplits.app A₁ A₂) (budSeqV R₁ R₂ b₁ b₂) qa qc

/-- The budget of a run in every slot. In words: the row of `Spec.bearsV_local` in the head. -/
def bearsV_local : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (N : ℕ)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (q₁ : Finset Ei.Pos → Prop)
      (q₂ : Finset Eo.Pos → Prop) (qi : QFam Ei N) (qo : QFam Eo N),
    R.Bears bud q₁ q₂ → (∀ J Us, qo J Us → ∀ j, q₂ (Us j)) →
    (∀ J (ρ : BRho N R.shape A) Us, qo J Us → qi J fun j => R.need (ρ.slot j.1) (Us j)) →
    R.BearsV A (fun J ρs Ts => ∀ j : J, bud (ρs j) (Ts j)) qi qo

open Classical in
/-- The budget of a run by the shared part alone. In words: the row of `Spec.bearsV_shared` in the
head. -/
def bearsV_shared : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (N : ℕ)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (q₁ : Finset Ei.Pos → Prop)
      (q₂ : Finset Eo.Pos → Prop) (qi : QFam Ei N) (qo : QFam Eo N),
    R.Bears bud q₁ q₂ → (∀ J Us, qo J Us → q₂ (Finset.univ.biUnion Us)) →
    (∀ J (ρ : BRho N R.shape (RoundSplits.const (RAnn.ofShared .sh) R.shape)) Us,
      qo J Us → qi J fun j => R.need (ρ.slot j.1) (Us j)) →
    R.BearsV (RoundSplits.const (RAnn.ofShared .sh) R.shape)
      (fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts)) qi qo

/-- A smaller relation, a smaller budget. -/
def exactV_mono : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape)
      (W0 Wj W0' Wj' : Type) (H : R.HonestV A W0 Wj W0' Wj') (N : ℕ)
      (Ri Ri' : X → Ei.Str → W0 × Wj → Prop) (bud bud' : BudB R.shape N),
    (∀ x y w, Ri' x y w → Ri x y w) →
    (∀ J (ρ : BRho N R.shape A) Ts,
      bud' J (fun j => ρ.slot j.1) Ts → bud J (fun j => ρ.slot j.1) Ts) →
    H.ExactV N Ri bud → H.ExactV N Ri' bud'

/-- States, under the hypotheses below: a piece, then a piece, is a piece. -/
def pieceV_seq : Prop :=
  ∀ (X X' X'' : Type) (Ei Eo Eo' : ExtSpec) (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo')
      (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (W0 Wj W0' Wj' W0'' Wj'' : Type)
      (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'') (N : ℕ)
      (Ra : X → Ei.Str → W0 × Wj → Prop) (Rb : X' → Eo.Str → W0' × Wj' → Prop)
      (Rc : X'' → Eo'.Str → W0'' × Wj'' → Prop) (b₁ : BudB R₁.shape N) (b₂ : BudB R₂.shape N)
      (qa : QFam Ei N) (qb : QFam Eo N) (qc : QFam Eo' N),
    PieceV R₁ A₁ H₁ N Ra Rb b₁ qa qb → PieceV R₂ A₂ H₂ N Rb Rc b₂ qb qc → qc.Her →
    PieceV (R₁.seq R₂) (RoundSplits.app A₁ A₂) (H₁.seqV H₂) N Ra Rc (budSeqV R₁ R₂ b₁ b₂) qa qc

/-- What a whole chain has at the end. -/
def pieceV_end : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape)
      (W0 Wj W0' Wj' : Type) (H : R.HonestV A W0 Wj W0' Wj') (N : ℕ)
      (Ri : X → Ei.Str → W0 × Wj → Prop) (Ro : X' → Eo.Str → W0' × Wj' → Prop)
      (bud : BudB R.shape N) (qi : QFam Ei N) (qo : QFam Eo N),
    PieceV R A H N Ri Ro bud qi qo → (∀ J, qo J fun _ => ∅) →
    R.IsLocal ∧ H.AccV Ri Ro ∧
    H.ExactV N Ri (fun _ _ Ts => ∀ j, Ts j = ∅) ∧
    ∀ (J : Finset (Fin N)) (ρ : BRho N R.shape A), qi J fun j => R.given (ρ.slot j.1) ∅

end Spec

open IOR

theorem bearsV_seq : Spec.bearsV_seq := by
  classical
  intro X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ N b₁ b₂ qa qb qc h₁ h₂ hH J
    (ρ : BRho N (R₁.shape ++ R₂.shape) (RoundSplits.app A₁ A₂)) Us hU
  obtain ⟨-, hq₂⟩ := h₂ J (BRho.sndA A₁ A₂ ρ) Us hU
  obtain ⟨hb₁, hq₁⟩ := h₁ J (BRho.fstA A₁ A₂ ρ) _ hq₂
  simp only [BRho.slot_fstA, BRho.slot_sndA] at hb₁ hq₁
  refine ⟨⟨?_, fun J' hJ => ?_⟩, ?_⟩
  · have e : (fun j : J =>
          firstT R₁ R₂ (ρ.slot j.1) ((Us j).biUnion ((R₁.seq R₂).srcO (ρ.slot j.1)))) =
        fun j : J =>
          (R₂.need (Rho.snd (s := R₁.shape) (ρ.slot j.1)) (Us j)).biUnion
              (R₁.srcO (Rho.fst (ρ.slot j.1))) :=
      funext fun j => firstT_src R₁ R₂ (ρ.slot j.1) (Us j)
    exact (congrArg (fun T => b₁ J (fun j => Rho.fst (ρ.slot j.1)) T) e).mpr hb₁
  · have h := (h₂ J' (BRho.sndA A₁ A₂ ρ) _ (hH J J' hJ Us hU)).1
    simp only [BRho.slot_sndA] at h
    have e : (fun j : J' =>
          partR R₁.shape ((Us ⟨j.1, hJ j.2⟩).biUnion ((R₁.seq R₂).srcO (ρ.slot j.1)))) =
        fun j : J' => (Us ⟨j.1, hJ j.2⟩).biUnion (R₂.srcO (Rho.snd (s := R₁.shape) (ρ.slot j.1))) :=
      funext fun j => partR_src R₁ R₂ (ρ.slot j.1) (Us ⟨j.1, hJ j.2⟩)
    exact (congrArg (fun T => b₂ J' (fun j => Rho.snd (s := R₁.shape) (ρ.slot j.1)) T) e).mpr h
  · have e : (fun j : J => (R₁.seq R₂).need (ρ.slot j.1) (Us j)) =
        fun j : J =>
          R₁.need (Rho.fst (ρ.slot j.1)) (R₂.need (Rho.snd (s := R₁.shape) (ρ.slot j.1)) (Us j)) :=
      funext fun j => need_seq _ _ _ _ _ _ R₁ R₂ (ρ.slot j.1) (Us j)
    exact (congrArg (fun T => qa J T) e).mpr hq₁

theorem bearsV_local : Spec.bearsV_local := fun _ _ _ _ _ _ _ _ _ _ _ _ hB h1 h2 J ρ Us hU =>
  ⟨fun j => (hB (ρ.slot j.1) (Us j) (h1 J Us hU j)).1, h2 J ρ Us hU⟩

theorem bearsV_shared : Spec.bearsV_shared := by
  classical
  intro X X' Ei Eo R N bud q₁ q₂ qi qo hB h1 h2 J ρ Us hU
  refine ⟨fun j => ?_, h2 J ρ Us hU⟩
  have e : (Finset.univ.biUnion fun j' : J => (Us j').biUnion (R.srcO (ρ.slot j'.1))) =
      (Finset.univ.biUnion Us).biUnion (R.srcO (ρ.slot j.1)) := by
    rw [Finset.biUnion_biUnion]
    refine Finset.biUnion_congr rfl fun j' _ => ?_
    rw [BatchSeqZk.slot_eq ρ j'.1, BatchSeqZk.slot_eq ρ j.1]
  rw [e]
  exact (hB (ρ.slot j.1) _ (h1 J Us hU)).1

theorem exactV_mono : Spec.exactV_mono := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hb ⟨S, hS⟩ =>
  ⟨S, fun w0 J as ha ρ Ts hT => hS w0 J as (fun j => hR _ _ _ (ha j)) ρ Ts (hb J ρ Ts hT)⟩

theorem pieceV_seq : Spec.pieceV_seq := fun X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ W0 Wj W0' Wj' W0'' Wj'' H₁ H₂ N Ra Rb Rc b₁ b₂ qa qb qc h₁ h₂ hH =>
  { isLocal := isLocal_seq _ _ _ _ _ _ _ _ h₁.isLocal h₂.isLocal
    acc :=
      acc_seqV X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ W0 Wj W0' Wj' W0'' Wj'' H₁ H₂ Ra Rb Rc h₁.acc h₂.acc
    exact := exact_seqV X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ W0 Wj W0' Wj' W0'' Wj'' H₁ H₂ Ra Rb N b₁ b₂
      h₁.isLocal h₁.acc h₁.exact h₂.exact
    bears := bearsV_seq X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ N b₁ b₂ qa qb qc h₁.bears h₂.bears hH }

theorem pieceV_end : Spec.pieceV_end := by
  classical
  intro X X' Ei Eo R A W0 Wj W0' Wj' H N Ri Ro bud qi qo h h0
  have hb : ∀ (J : Finset (Fin N)) (ρ : BRho N R.shape A),
      bud J (fun j => ρ.slot j.1) (fun _ => ∅) ∧ qi J fun j => R.given (ρ.slot j.1) ∅ := by
    intro J ρ
    have := h.bears J ρ (fun _ => ∅) (h0 J)
    simpa [IOR.need] using this
  refine ⟨h.isLocal, h.acc,
    exactV_mono _ _ _ _ R A _ _ _ _ H N Ri Ri bud _ (fun _ _ _ hw => hw)
      (fun J ρ Ts hT => ?_) h.exact,
    fun J ρ => (hb J ρ).2⟩
  have e : Ts = fun _ => ∅ := funext hT
  rw [e]
  exact (hb J ρ).1

end Iop
