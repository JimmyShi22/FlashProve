-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Rider/Model/AttLook.lean: the lookup of an attention sub-proof, with identity
at3 tested on its challenges, ending at the claim with which the chain of the sub-proof's own rounds
starts.

Two statements and their proofs. No protocol of its own. The term forB and its counts are those of
OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean; the rule at at3 is `den_forB_in`
(OnBytes/Tie/Pv/Lookup/Rider/Model/Denom.lean); the joint `jt` and the chain `Ch` with its claim
`Ch.Todo` are those of Cb/Pv/Att/Chain.lean.
Main names:
  `att_look`: `KnowAt` of forB, with the identity as extractor and forB's own counts, from forB's
    in-joint, with "`idnVal` is 0 at every valid `Idn.at3 b g i`" laid inside the relation R0 that
    rides along, at the input alone, to `jt A0 pr fun x m => Dn x m ∧ c.Todo x m`: the joint in
    front of the chain c. Premises: hK, forB's own `KnowAt` at R0 without the identity; `AttFits h D
    C`; hon: the condition on statements behind forB gives that of A0; hrel: the relaxed relation of
    A0, Dn and the chain's claim give the relaxed relation behind forB and `denOut` = 0 at the point
    of the claim on the keys.
  `att_look_own`: `att_look` at R0 := Base with a clause Own, A0 := Base, pr := the caller's state.
    Its two premises: Dn gives the lookup's own claim behind forB; Dn and the chain's claim give Own
    and `denOut` = 0. So the equation may stand in Dn or come out of the chain's claim.
Limits: R0, A0, pr, Dn, c and `cells` are free letters. If R0 gives the identity at every valid
index, the statement follows from hK alone (`forB_hollow`). If A0, Dn or the chain's claim `c.Todo`
gives it, at the caller's state, which forB hands on (`forB_passes`), the statement follows from hK
and `knowAt_hollow_out` (Cb/G6/Rider/KnowAt.lean), without `AttFits` and without `denOut`. In both
cases it says nothing of the test: the identity may stand in forB's in-joint and in nothing that is
read behind forB. hrel is a premise: that a chain's claim gives `denOut` = 0 is not proved here for
any chain. Nothing on whether the programs test this equation, or on an honest prover.
-/
import Cb.G6.Join
import Cb.Pv.Att.Chain
import OnBytes.Tie.Pv.Lookup.Rider.Model.Denom

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks Cb.LdLkp Cb.LdLkp.Kn TWhole Cb.Fo Inst.Model Inst.Model.AttSeg Cb.Pv.Att

variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  {h : Sh} {L : Lay E St₀ J₀} {Ex : ExtSpec} {Kc M Wp : Type}
  {R0 : IOR.Rels Kc St₀ Ex (M × Wp)} {msg₀ : M → J₀ → E}

/-- The lookup of an attention sub-proof into the claim at the start of the chain of its own rounds.
Warning: R0, A0, Dn and c are free; R0, A0, Dn and the chain's claim have to be without at3
(forB_hollow, knowAt_hollow_out). -/
theorem att_look
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {D : Dim} {C : Calls} (F : AttFits h D C) (cells : St₀ → M → Raw → E)
    {X0 : Type} (A0 : IOR.Rels Kc X0 Ex (M × Wp)) (pr : TX (St₀ × E) E (Option J₀) → X0)
    (Dn : TX (St₀ × E) E (Option J₀) → M → Prop) (c : Ch E M (TX (St₀ × E) E (Option J₀)))
    (hon : ∀ b, (forOut E h L R0 msg₀).on b → A0.on (pr b.1, b.2))
    (hrel : ∀ b w, (forOut E h L R0 msg₀).on b → A0.relR (pr b.1, b.2) w → Dn b.1 w.1 →
      c.Todo b.1 w.1 →
        (forOut E h L R0 msg₀).relR b w ∧ denOut D C b.1.2.1.pt (cells b.1.1.1 w.1) = 0) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a =>
        ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D (cells a.1 m) (.at3 b g i) = 0) msg₀)
      (jt A0 pr fun x m => Dn x m ∧ c.Todo x m)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  knowAt_mono (den_forB_in hK F cells) (fun _ ha => ha) (fun _ _ _ hw => hw)
    (fun b w hb hw => hrel b w hb hw.1 hw.2.1 hw.2.2) hon

/-- `att_look` where two relations ride: Base with Own through the lookup, Base alone through the
chain. Dn gives the lookup's own claim behind forB; Dn and the chain's claim give Own and the
equation. Warning: Base, Own, Dn and c are free; they and the chain's claim have to be without
at3. -/
theorem att_look_own (Base : IOR.Rels Kc St₀ Ex (M × Wp)) (Own : St₀ → M → Prop)
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider Base fun m a => Own a.1 m) msg₀)
      (forOut E h L (withRider Base fun m a => Own a.1 m) msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {D : Dim} {C : Calls} (F : AttFits h D C) (cells : St₀ → M → Raw → E)
    (Dn : TX (St₀ × E) E (Option J₀) → M → Prop) (c : Ch E M (TX (St₀ × E) E (Option J₀)))
    (hout : ∀ x m, Dn x m → ((forA E h L).lk.out id id) x (zext (msg₀ m)))
    (hown : ∀ x m, Dn x m → c.Todo x m →
      Own x.1.1 m ∧ denOut D C x.2.1.pt (cells x.1.1 m) = 0) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider (withRider Base fun m a => Own a.1 m) fun m a =>
        ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D (cells a.1 m) (.at3 b g i) = 0) msg₀)
      (jt Base (fun x => x.1.1) fun x m => Dn x m ∧ c.Todo x m)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  att_look hK F cells Base (fun x => x.1.1) Dn c (fun _ hb => hb)
    (fun b w _ h1 h2 h3 =>
      ⟨⟨⟨h1, (hown b.1 w.1 h2 h3).1⟩, hout b.1 w.1 h2⟩, (hown b.1 w.1 h2 h3).2⟩)

end Cb.Rider

#print axioms Cb.Rider.att_look
#print axioms Cb.Rider.att_look_own
