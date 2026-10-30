-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDKitAt.lean: pending blocks (`LdPend`, Cb/Ld/LdMia.lean) with the parameters of a coming
block: its own type of masks, its own places; and the own condition (`LdPend.StepD`,
Cb/Ld/LdLayDKit.lean) of a step that hands the messages on and computes a further witness.

In standard terms: two helper lemmas on sets of entries of oracle messages with their values: one
rewrites such a set in the form in which a later step names it; the other is on a step that sends
nothing and hands the messages on.

Theorems, for whoever builds an instance of the records that use the definitions of
Cb/Ld/LdLayDKit.lean (Cb/Ld/LdLayD.lean: `LdReqRefLayD`): the analogues, on data, of `baseMany_at`
and `stepW_wide` (Cb/Req1/LdReqStdLayAt.lean).

Main names:
  `ldLayD_manyAt`: behind a standard sending d (`hStd`, with `hY : Q d.N d.t F Y`), for an injective
    fr and a nonempty Mk: the block with the coming block's mask values Mk, ve : Mk ≃ (Ix → E), own
    entries `plOwn at'`, values `plVal at' ve`, at the reading of `d.pendMany`
    (`a.S.sumP d.N RdOld Y.NoPad`, `a.S.sumO d.N RrOld fun _ => False`), for at' x = the free entry
    fr x among all open entries, lies in the closure of `d.LaysD Q` (`LdPend.JD`,
    Cb/Ld/LdLayDKit.lean; here by its rules `base` ; `reMk`: another type of masks ; `same`: written
    otherwise).
  `ldLayD_stepW`: the step of Cb/Ld/LdStepW.lean (explicit part mapped; messages handed on; further
    witness computed by "up") has its own condition between a block and the block with the same
    fields (Mk nonempty), if "up" is the same at messages that agree on the entries of the reading
    that are not own.

Limits: This file says nothing on any instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayDKit
import Cb.Req1.LdReqStdLayAt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldLayD_manyAt (a : LdStage E Kc) (d : LdSendD a) (Y : d.N.StdL F)
    (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
    (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (Q : LdLayQ E)
    (hStd : d.StdAt F Y dat rst bk₀ w0) (hY : Q d.N d.t F Y) (Ix : Type) [Fintype Ix]
    (fr : Ix → Σ a, Y.Fr a) (hfr : Function.Injective fr) (RdOld : a.S.Ent → Prop)
    (RrOld : a.S.O → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (ve : Mk ≃ (Ix → E))
    (at' : Ix → (a.S.sum d.N).Ent)
    (hat : ∀ x, at' x = ⟨.inr (Y.entF (fr x)).1, (Y.entF (fr x)).2⟩) :
    LdPend.JD (d.LaysD Q)
      (⟨a.S.sumP d.N RdOld Y.NoPad, a.S.sumO d.N RrOld fun _ => False, plOwn at', Mk,
        plVal at' fun M => ve M⟩ : LdPend d.tgt) := by
  classical
  have b0 : LdPend.JD (d.LaysD Q) (d.pendMany Y fr RdOld RrOld) :=
    .base _ ⟨F, inferInstance, inferInstance, inferInstance, Y, dat, rst, bk₀, w0, hStd, hY,
        Or.inl ⟨Ix, inferInstance, inferInstance, inferInstance, fr, RdOld, RrOld, hfr, rfl⟩⟩
  have b1 := LdPend.JD.reMk _ Mk ve.symm b0
  have hinj : Function.Injective fun x => Y.entF (fr x) := fun x x' e => hfr (Y.entF_injective e)
  have hinj' : Function.Injective at' := fun x x' e => by
    rw [hat, hat] at e
    have e1 : (Y.entF (fr x)).1 = (Y.entF (fr x')).1 := Sum.inr_injective (congrArg Sigma.fst e)
    exact hinj (Sigma.ext e1 (Sigma.mk.inj e).2)
  refine LdPend.JD.same _ (plOwn at') (plVal at' fun M => ve M) (fun n => ?_) (fun M n hn => ?_) b1
  · obtain ⟨o, j⟩ := n
    rcases o with o | o
    · exact ⟨fun h => h.elim,
        fun ⟨x, hx⟩ => by rw [hat] at hx; exact absurd (congrArg Sigma.fst hx) Sum.inr_ne_inl⟩
    · constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [hat, ← hx]⟩
      · rintro ⟨x, hx⟩
        rw [hat] at hx
        have e1 : (Y.entF (fr x)).1 = o := Sum.inr_injective (congrArg Sigma.fst hx)
        exact ⟨x, (Sigma.ext e1 (Sigma.mk.inj hx).2).symm⟩
  · obtain ⟨o, j⟩ := n
    rcases o with o | o
    · exact hn.elim
    · obtain ⟨x, hx⟩ := hn
      have hx' : (⟨o, j⟩ : d.N.Ent) = Y.entF (fr x) := hx
      have e2 : (⟨.inr o, j⟩ : (a.S.sum d.N).Ent) = at' x := by rw [hat, ← hx']
      show Function.extend (fun i => Y.entF (fr i)) (ve M) (fun _ => 0) ⟨o, j⟩ =
        Function.extend at' (ve M) (fun _ => 0) ⟨.inr o, j⟩
      rw [hx', e2, hinj.extend_apply, hinj'.extend_apply]

end

section
variable {E Kc : Type} [Field E] [Fintype E] (S : Sig E) {St St' Wp Wp' : Type}
  {E₀ : ExtSpec} (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc St' E₀ (S.Msg × Wp'))
  (f : St → St') (up : St → S.Msg × Wp → Wp')

omit [Fintype E] in
theorem ldLayD_stepW (Rd : S.Ent → Prop) (Rr : S.O → Prop) (own : S.Ent → Prop) (Mk : Type)
    [Fintype Mk] [Nonempty Mk] (val : Mk → S.Ent → E)
    (hu : ∀ st (m m' : S.Msg) wp, S.Alike Rd own m m' → up st (m', wp) = up st (m, wp)) :
    LdPend.StepD (sideM S f up)
      (⟨Rd, Rr, own, Mk, val⟩ : LdPend (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc))
      (⟨Rd, Rr, own, Mk, val⟩ : LdPend (⟨S, St', E₀, Wp', A'⟩ : LdStage E Kc)) := by
  refine ⟨Equiv.refl _, fun x w w' M e => ⟨rfl, ?_⟩⟩
  obtain ⟨h1, -, h3⟩ := segWide_alike (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) Rd Rr own Mk val w w' M e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg (fun z => z.2.1) e
  refine Prod.ext e1 (Prod.ext e2 ?_)
  show up x.1 (S.msgs w'.1, w'.2) = up x.1 (S.msgs w.1, w.2)
  rw [h3]
  exact hu x.1 _ _ _ h1

end
end Cb
