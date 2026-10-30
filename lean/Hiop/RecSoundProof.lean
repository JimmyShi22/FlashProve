-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecSoundProof.lean: this file proves the soundness part of the composition theorems of the
holographic interactive oracle proof (Hiop/RecMain.lean).
In this library's words: index binding of the holographic IOP with records.

Statements and proofs; among them the proof of `Hiop.Spec.rec_soundAt` (Hiop/RecMain.lean).

What is used. Of the parameter lists: the five items on knowledge soundness (`SubsR.HypK`) and two
items on formats of the preamble of a request: it hands the record on (`passes`) and copies the
encoded index (`copy`). Of the configuration: the record binds (`ConfigurationWithOutOfDomainSample.Props.rcd`). No item on the
honest side.

Main names:
  `Spec.rec_offline_know`: under `S.HypK P`: the offline IOP, on statements (record, word) without a
    collision: knowledge soundness with the relaxation "the index decoder answers"; errors: the
    preamble's, then the IOPP's.
  `Spec.rec_online_know`: under `S.HypK P`, `passes` and `copy` of the preamble of a request: a
    session, for each record, with that record in all slots: (Snd-B) with a witness, wide
    (Ior/KnowWide.lean), for "the index decoder says none, or the extracted cells are valid for the
    decoded index"; errors: the preamble's, then the IOPP's.
  `Spec.rec_sndT`, `Spec.rec_sndL`: under `S.HypK P`: the offline IOP and the link as IOPs:
    round-by-round soundness for the languages of Hiop/RecInterface.lean.
  `rec_soundAt : Spec.rec_soundAt`: under `C.Props b eR`, `S.Hyp P`: the five clauses together. "The
    index decoder says none at a collision" holds by the definition of `ConfigurationWithOutOfDomainSample.D`; the record clause
    is the configuration's law.

Why, offline: the preamble is sound into the collision-free statements of the constraint relation,
the IOPP on them: Ior/KnowColl.lean: `knowInto_seq_ext`. A collision of an oracle that the preamble
sends is counted in the preamble's list.
Why, a session: where the index decoder answers, the word decodes with the record; so the IOPP's
item, which is asked on such statements only, applies; outside the collision-free statements the
preamble's item has counted the collision.

Limits: the list of a session here is this: (Snd-B) takes, in a round that belongs to one instance,
the error for one instance, and joint errors in shared rounds only; so the preamble's errors stand
here once. The notion that is joint over all N instances in every round has N times the preamble's
errors (the union bound; for `SndBK`: Ior/Batch.lean: `Spec.jointAll_of_sndBK`). The list here is
the one for a single instance, which is the list that the compilation uses.
What the head of Hiop/RecMain.lean lists as not said is not said here either. This file says nothing
on the honest side (Hiop/RecMainProof.lean).

Terms: lean/GLOSSARY.md: record, collision, index decoder, offline IOP, preamble, parameter list,
  session, slot, wide, constraint relation, shared round, (Snd-B).
-/
import Hiop.RecMain
import Hiop.RecKitSound
import Ior.ToProtoProofs

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

namespace Spec

/-- the offline phase: knowledge soundness -/
def rec_offline_know : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), S.HypK P →
    S.offline.red.Know C.free C.RwfR (fun _ _ => True)
      (fun _ _ (_ : Unit) => ()) (Err.app P.wf.err P.linOff.err)

/-- the online phase: knowledge soundness for the instances of a batch, for each record -/
def rec_online_know : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), S.HypK P →
    (∀ x y τ b, S.req.out x y τ = some b → b.2 = x.2) → (∀ y τ, (S.req.imp y τ).1 = y) →
    ∀ rec : C.Rec, (S.session.toBatch.comap fun x => (x, rec)).SndBKT S.N id none
      (fun x y w => C.D y rec = none ∨ ∃ i, C.D y rec = some i ∧ C.Rno i x w)
      (fun x y τ => S.wit (x, rec) y τ) (Err.app P.req.err P.linOn.err)

/-- the offline IOP as an IOP -/
def rec_sndT : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), S.HypK P →
    S.lhr.offline.Sound (fun rec y => S.lhr.hasCollisionAt y rec.1 ∨ S.lhr.decodeIndex y rec ≠ none)
      (Err.app P.wf.err P.linOff.err : Err (S.wf.shape ++ S.linOff.shape))

/-- the link as an IOP -/
def rec_sndL : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), S.HypK P →
    S.lhr.link.Sound
      (fun rr y =>
        S.lhr.decodeIndex y.1 rr.1 = none ∨ S.lhr.hasCollisionAt y.2 rr.2.1 ∨ S.lhr.decodeIndex y.2 rr.2 = S.lhr.decodeIndex y.1 rr.1)
      P.link.err

end Spec

/-- where the index decoder answers, there is no collision and the word decodes with the record -/
theorem ConfigurationWithOutOfDomainSample.of_D_isSome {C : ConfigurationWithOutOfDomainSample} {y : C.E0.Str} {rec : C.Rec} (h : (C.D y rec).isSome) :
    ¬ C.coll y rec.1 ∧ (C.dcd y rec).isSome := by
  classical
  unfold ConfigurationWithOutOfDomainSample.D at h
  by_cases hc : C.coll y rec.1
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    refine ⟨hc, ?_⟩
    cases hd : C.dcd y rec with
    | none => rw [hd] at h; cases h
    | some m => rfl

theorem ConfigurationWithOutOfDomainSample.D_of_coll {C : ConfigurationWithOutOfDomainSample} {y : C.E0.Str} {rec : C.Rec} (h : C.coll y rec.1) :
    C.D y rec = none := by
  classical
  unfold ConfigurationWithOutOfDomainSample.D
  rw [if_pos h]

theorem rec_offline_know : Spec.rec_offline_know := by
  intro C S P hK
  have h₂ := (know_of_knowInto _ _ _ _ S.linOff.red S.off.cond S.off.RlinR
    (fun _ (_ : Unit) => True)
    (fun a _ (_ : Unit) => S.off.decA S.dOff a.1.1 a.2.2) P.linOff.err).2 hK.linOff
  have h := knowInto_seq_ext _ _ _ _ _ _ S.wf.red S.linOff.red C.free S.off.cond (fun _ => True)
    C.RwfR S.off.RlinR (fun _ (_ : Unit) => True) (fun _ _ _ => ())
    (fun a _ (_ : Unit) => S.off.decA S.dOff a.1.1 a.2.2) P.wf.err P.linOff.err (fun _ _ _ => ())
    hK.wf h₂ (fun _ _ _ _ _ _ => rfl)
  have h' := (know_of_knowInto _ _ _ _ (S.wf.red.seq S.linOff.red) C.free C.RwfR
    (fun _ (_ : Unit) => True) (fun _ _ _ => ()) (Err.app P.wf.err P.linOff.err)).1 h
  intro a ha
  refine Doomed.mono _ _ ?_ (h' a ha)
  intro τ hτ b w hb hw
  exact hτ b w ((IOR.red_seq_out S.wf S.linOff a τ).symm.trans hb) hw

theorem rec_sndT : Spec.rec_sndT := by
  classical
  intro C S P hK
  have sT := Iop.sound_toProto C.Rec Unit C.E0 S.offline C.free C.RwfR (fun _ _ _ => ())
    (Err.app P.wf.err P.linOff.err) (rec_offline_know C S P hK)
  refine fun rec y hy => sT rec y fun h => hy ?_
  rcases h with h | ⟨_, hw⟩
  · exact Or.inl (not_not.1 h)
  · refine Or.inr fun h0 => ?_
    have hw' : (C.D y rec).isSome = true := hw
    have h0' : C.D y rec = none := h0
    rw [h0'] at hw'
    cases hw'

theorem rec_sndL : Spec.rec_sndL := by
  classical
  intro C S P hK
  have sL := Iop.sound_toProto
    (C.Rec × C.Rec) Unit (twoExternalStrings C.n C.Sg) S.link C.onEq C.ReqR (fun _ _ _ => ()) P.link.err hK.link
  refine fun rr y hy => sL rr y fun h => hy ?_
  rcases h with h | ⟨_, hw⟩
  · show C.D y.1 rr.1 = none ∨ C.coll y.2 rr.2.1 ∨ C.D y.2 rr.2 = C.D y.1 rr.1
    by_cases h1 : (C.D y.1 rr.1).isSome
    · by_cases h2 : C.coll y.2 rr.2.1
      · exact Or.inr (Or.inl h2)
      · exact absurd ⟨h1, h2⟩ h
    · left
      cases hd : C.D y.1 rr.1 with
      | none => rfl
      | some i => rw [hd] at h1; exact absurd rfl h1
  · exact Or.inr (Or.inr hw)

theorem rec_online_know : Spec.rec_online_know := by
  classical
  intro C S P hK hpass hcopy rec
  -- the two parts with the record fixed
  let F' : IOR C.X C.E0 S.on.Xl S.on.El := (S.req.comapX fun x : C.X => (x, rec)).mapOut Prod.fst
  let Q' : BIOP S.on.Xl S.on.El := S.linOn.comapX fun xl : S.on.Xl => (xl, rec)
  have h₁ : F'.red.Know (fun a => (C.D a.2 rec).isSome) (fun a c => C.RreqR ((a.1, rec), a.2) c)
      (fun b m => Reduction.orOff S.on.cond S.on.RlinR ((b.1, rec), b.2) m)
      (fun a τ m => S.cellsOf ((a.1, rec), a.2) τ m) P.req.err :=
    know_fix C.X S.on.Xl C.Rec C.E0 S.on.El C.Cells S.on.AMsg S.req rec
      (fun a => (C.D a.2 a.1.2).isSome) C.RreqR (Reduction.orOff S.on.cond S.on.RlinR)
      S.cellsOf P.req.err hpass hK.req
  have h := sndBKT_online_ext C.X S.on.Xl C.Cells S.on.AMsg C.E0 S.on.Ej F' Q' S.N
    (fun a => (C.D a.2 rec).isSome) (fun a c => C.RreqR ((a.1, rec), a.2) c)
    (fun b m => Reduction.orOff S.on.cond S.on.RlinR ((b.1, rec), b.2) m)
    (fun b w =>
      (C.dcd b.2.1 rec).isSome → S.on.cond ((b.1, rec), b.2) → S.on.RlinR ((b.1, rec), b.2) w)
    (fun a τ m => S.cellsOf ((a.1, rec), a.2) τ m) (fun a _ _ => S.on.decA S.dOn a.1 a.2)
    (fun x y τ => S.wit (x, rec) y τ) P.req.err P.linOn.err h₁ (hK.linOn rec) hcopy ?_ ?_
  · -- the session's verifier on (x, record) accepts no more than the verifier with the record fixed in both parts
    have h2 := sndBP_withAccept C.X C.E0 (Iop.online F' Q').toBatch
      (fun x y τ => S.session.toBatch.loc.accept (x, rec) y τ) S.N id none _
      (Err.app P.req.err P.linOn.err) ?_ h
    · refine sndBP_mono C.X C.E0 (S.session.toBatch.comap fun x => (x, rec)) S.N id none _ _
        (Err.app P.req.err P.linOn.err) ?_ h2
      intro x y τ _ hw
      cases hD : C.D y rec with
      | none => exact Or.inl hD
      | some i =>
        obtain ⟨i', hi', hR⟩ := hw (by show (C.D y rec).isSome = true; rw [hD]; rfl)
        have e : C.D y rec = some i' := hi'
        rw [hD] at e
        cases e
        exact Or.inr ⟨i, hD, hR⟩
    · intro x y (τ : Tr (S.req.shape ++ S.linOn.ior.shape)) hacc
      have hacc' : ((S.req.out (x, rec) y (Tr.fst τ)).bind fun b =>
            S.linOn.ior.out b (S.req.imp y (Tr.fst τ)) (Tr.snd (s := S.req.shape) τ)).isSome =
          true := hacc
      show (((S.req.out (x, rec) y (Tr.fst τ)).map Prod.fst).bind fun xl =>
          S.linOn.ior.out (xl, rec) (S.req.imp y (Tr.fst τ)) (Tr.snd (s := S.req.shape) τ)).isSome =
        true
      cases ho : S.req.out (x, rec) y (Tr.fst τ) with
      | none =>
        rw [ho] at hacc'
        cases hacc'
      | some b =>
        rw [ho] at hacc'
        have e : b = (b.1, rec) := Prod.ext rfl (hpass (x, rec) y (Tr.fst τ) b ho)
        rw [e] at hacc'
        exact hacc'
  · intro x y τ xl w hon _ hw
    by_cases hc : S.on.cond ((xl, rec), F'.imp y τ)
    · refine Or.inl (hw ?_ hc)
      have e : (F'.imp y τ).1 = y := hcopy y τ
      rw [e]
      exact (ConfigurationWithOutOfDomainSample.of_D_isSome hon).2
    · exact Or.inr hc
  · intro x y τ xl hout
    have hout' : (S.req.out (x, rec) y (Tr.fst τ)).map Prod.fst = some xl := hout
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hout'
    show witSeqT S.req S.cellsOf (fun a _ _ => S.on.decA S.dOn a.1.1 a.2) C.cells0 (x, rec) y τ = _
    simp only [witSeqT, hb]
    rfl

theorem rec_soundAt : Spec.rec_soundAt := fun C S P _ _ hC hS =>
  { noneColl := fun _ _ h => ConfigurationWithOutOfDomainSample.D_of_coll h
    rcd := hC.rcd
    sndT := rec_sndT C S P hS.know
    sndL := rec_sndL C S P hS.know
    sndB := rec_online_know C S P hS.know hS.honest.req.passes hS.honest.req.copy }

end Hiop
