-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/Cond/TargetSoundOnly.lean.
Small twins: the soundness statements of Hiop/RecSoundProof.lean
under the fields that their proofs read, and no others. THE FOUR LONG PROOFS ARE MADE BY PROGRAM
from the library's own text: each is the library's proof, cut out of
Hiop/RecSoundProof.lean, in which only the names of hypotheses turn. THE STATEMENTS (def …_ofK) AND
THE ONE SHORT TERM ARE TYPED BY HAND after the library's; that each conclusion is the library's
is held twice: by a program on the text, and by Lean: the library's FIVE statements are proved
again from the twins (…_again).

-/
import Cond.ObjBitsProof

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

namespace Spec

/-- `rec_offline_know` under the two items that its proof reads. -/
def rec_offline_know_ofK : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums),
    PreKnowR S.off S.wf C.free C.RwfR (fun _ _ _ => ()) P.wf.err →
    LinKnowR S.off S.linOff S.dOff P.linOff.err →
    S.offline.red.Know C.free C.RwfR (fun _ _ => True)
      (fun _ _ (_ : Unit) => ()) (Err.app P.wf.err P.linOff.err)

/-- THE KEY FILE's SHARE: `rec_sndT` under the same two. -/
def rec_sndT_ofK : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums),
    PreKnowR S.off S.wf C.free C.RwfR (fun _ _ _ => ()) P.wf.err →
    LinKnowR S.off S.linOff S.dOff P.linOff.err →
    S.lhr.offline.Sound (fun rec y => S.lhr.hasCollisionAt y rec.1 ∨ S.lhr.decodeIndex y rec ≠ none)
      (Err.app P.wf.err P.linOff.err : Err (S.wf.shape ++ S.linOff.shape))

/-- THE ENTRY FILE's SHARE: `rec_sndL` under the one item that its proof reads. -/
def rec_sndL_ofK : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), LinkKnowR S.link P.link.err →
    S.lhr.link.Sound
      (fun rr y =>
        S.lhr.decodeIndex y.1 rr.1 = none ∨ S.lhr.hasCollisionAt y.2 rr.2.1 ∨ S.lhr.decodeIndex y.2 rr.2 = S.lhr.decodeIndex y.1 rr.1)
      P.link.err

/-- THE PROOF FILE's SHARE: `rec_online_know` under the two items that its proof reads, with its two
premises. -/
def rec_online_know_ofK : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums),
    PreKnowR S.on S.req (fun a => (C.D a.2 a.1.2).isSome) C.RreqR S.cellsOf P.req.err →
    LinBKnowR S.on S.linOn S.N S.dOn P.linOn.err →
    (∀ x y τ b, S.req.out x y τ = some b → b.2 = x.2) → (∀ y τ, (S.req.imp y τ).1 = y) →
    ∀ rec : C.Rec, (S.session.toBatch.comap fun x => (x, rec)).SndBKT S.N id none
      (fun x y w => C.D y rec = none ∨ ∃ i, C.D y rec = some i ∧ C.Rno i x w)
      (fun x y τ => S.wit (x, rec) y τ) (Err.app P.req.err P.linOn.err)

/-- `rec_soundAt` without `C.Props b eR` and without `S.HypH P`. -/
def rec_soundAt_ofK : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (eR : ℕ), (∀ y, cnt (fun s => C.coll y s) ≤ eR) →
    S.HypK P →
    (∀ x y τ b, S.req.out x y τ = some b → b.2 = x.2) → (∀ y τ, (S.req.imp y τ).1 = y) →
    S.lhr.SoundAtR C.Rno S.wit eR
      (Err.app P.wf.err P.linOff.err : Err (S.wf.shape ++ S.linOff.shape)) P.link.err
      (Err.app P.req.err P.linOn.err : Err (S.req.shape ++ S.linOn.ior.shape))

end Spec

theorem rec_offline_know_ofK : Spec.rec_offline_know_ofK := by
  intro C S P hwf hlin
  have h₂ := (know_of_knowInto _ _ _ _ S.linOff.red S.off.cond S.off.RlinR
    (fun _ (_ : Unit) => True)
    (fun a _ (_ : Unit) => S.off.decA S.dOff a.1.1 a.2.2) P.linOff.err).2 hlin
  have h := knowInto_seq_ext _ _ _ _ _ _ S.wf.red S.linOff.red C.free S.off.cond (fun _ => True)
    C.RwfR S.off.RlinR (fun _ (_ : Unit) => True) (fun _ _ _ => ())
    (fun a _ (_ : Unit) => S.off.decA S.dOff a.1.1 a.2.2) P.wf.err P.linOff.err (fun _ _ _ => ())
    hwf h₂ (fun _ _ _ _ _ _ => rfl)
  have h' := (know_of_knowInto _ _ _ _ (S.wf.red.seq S.linOff.red) C.free C.RwfR
    (fun _ (_ : Unit) => True) (fun _ _ _ => ()) (Err.app P.wf.err P.linOff.err)).1 h
  intro a ha
  refine Doomed.mono _ _ ?_ (h' a ha)
  intro τ hτ b w hb hw
  exact hτ b w ((IOR.red_seq_out S.wf S.linOff a τ).symm.trans hb) hw

theorem rec_sndT_ofK : Spec.rec_sndT_ofK := by
  classical
  intro C S P hwf hlin
  have sT := Iop.sound_toProto C.Rec Unit C.E0 S.offline C.free C.RwfR (fun _ _ _ => ())
    (Err.app P.wf.err P.linOff.err) (rec_offline_know_ofK C S P hwf hlin)
  refine fun rec y hy => sT rec y fun h => hy ?_
  rcases h with h | ⟨_, hw⟩
  · exact Or.inl (not_not.1 h)
  · refine Or.inr fun h0 => ?_
    have hw' : (C.D y rec).isSome = true := hw
    have h0' : C.D y rec = none := h0
    rw [h0'] at hw'
    cases hw'

theorem rec_sndL_ofK : Spec.rec_sndL_ofK := by
  classical
  intro C S P hlk
  have sL := Iop.sound_toProto
    (C.Rec × C.Rec) Unit (twoExternalStrings C.n C.Sg) S.link C.onEq C.ReqR (fun _ _ _ => ()) P.link.err hlk
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

theorem rec_online_know_ofK : Spec.rec_online_know_ofK := by
  classical
  intro C S P hreq hlinOn hpass hcopy rec
  -- the two parts with the record fixed
  let F' : IOR C.X C.E0 S.on.Xl S.on.El := (S.req.comapX fun x : C.X => (x, rec)).mapOut Prod.fst
  let Q' : BIOP S.on.Xl S.on.El := S.linOn.comapX fun xl : S.on.Xl => (xl, rec)
  have h₁ : F'.red.Know (fun a => (C.D a.2 rec).isSome) (fun a c => C.RreqR ((a.1, rec), a.2) c)
      (fun b m => Reduction.orOff S.on.cond S.on.RlinR ((b.1, rec), b.2) m)
      (fun a τ m => S.cellsOf ((a.1, rec), a.2) τ m) P.req.err :=
    know_fix C.X S.on.Xl C.Rec C.E0 S.on.El C.Cells S.on.AMsg S.req rec
      (fun a => (C.D a.2 a.1.2).isSome) C.RreqR (Reduction.orOff S.on.cond S.on.RlinR)
      S.cellsOf P.req.err hpass hreq
  have h := sndBKT_online_ext C.X S.on.Xl C.Cells S.on.AMsg C.E0 S.on.Ej F' Q' S.N
    (fun a => (C.D a.2 rec).isSome) (fun a c => C.RreqR ((a.1, rec), a.2) c)
    (fun b m => Reduction.orOff S.on.cond S.on.RlinR ((b.1, rec), b.2) m)
    (fun b w =>
      (C.dcd b.2.1 rec).isSome → S.on.cond ((b.1, rec), b.2) → S.on.RlinR ((b.1, rec), b.2) w)
    (fun a τ m => S.cellsOf ((a.1, rec), a.2) τ m) (fun a _ _ => S.on.decA S.dOn a.1 a.2)
    (fun x y τ => S.wit (x, rec) y τ) P.req.err P.linOn.err h₁ (hlinOn rec) hcopy ?_ ?_
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

theorem rec_soundAt_ofK : Spec.rec_soundAt_ofK := fun C S P _ hr hK hpass hcopy =>
  { noneColl := fun _ _ h => ConfigurationWithOutOfDomainSample.D_of_coll h
    rcd := hr
    sndT := rec_sndT_ofK C S P hK.wf hK.linOff
    sndL := rec_sndL_ofK C S P hK.link
    sndB := rec_online_know_ofK C S P hK.req hK.linOn hpass hcopy }

/-- THE CONTROLS: the library's own statements from the twins: so each twin's conclusion IS the
library's (Lean holds them together). -/
theorem rec_offline_know_again : Spec.rec_offline_know := fun C S P hK =>
  rec_offline_know_ofK C S P hK.wf hK.linOff

theorem rec_sndT_again : Spec.rec_sndT := fun C S P hK => rec_sndT_ofK C S P hK.wf hK.linOff

theorem rec_sndL_again : Spec.rec_sndL := fun C S P hK => rec_sndL_ofK C S P hK.link

theorem rec_online_know_again : Spec.rec_online_know := fun C S P hK hpass hcopy =>
  rec_online_know_ofK C S P hK.req hK.linOn hpass hcopy

theorem rec_soundAt_again : Spec.rec_soundAt := fun C S P _ eR hC hS =>
  rec_soundAt_ofK C S P eR hC.rcd hS.know hS.honest.req.passes hS.honest.req.copy

end Hiop

noncomputable section
