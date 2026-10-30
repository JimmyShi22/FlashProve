-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GuestLink.lean: the identities at1, at2 and at3 of an attention segment
from one statement of knowledge soundness over "the lookup, then the segment's own rounds".

Statements and proofs. No protocol of its own. The lookup of a sub-proof (`forB` at V₀, V₀C and the
challenge field) has `KnowAt` from one test on public numbers
(OnBytes/Tie/Pv/Lookup/Forest/FoAt.lean: `holeCgl`), and the rule for at3 on its challenges
(OnBytes/Tie/Pv/Lookup/Rider/Model/Denom.lean: `den_forB`) leads from "at3 at every valid index" in
front to "`denOut` = 0 at the point of the claim on the keys" behind. The chain of the own rounds
(Cb/Pv/Att/OwnAt.lean: `ownAt_knowAt`) is laid behind it: its first statements are the lookup's
output statements, and its base joint is the lookup's own out-joint `forOut`.
Main names:
  `Three P m`: at1, at2 and at3 vanish at every valid index, at D := P.D and t := P.tOf m: the
    premises own1, own2 and ridden of `att_ord_base` (Johnson/Road/Rows/AttStartBase.lean).
  `Two`, `two_of_todo`: Todo gives at1 and at2 (where kap variables number all bits of a position).
  `three_fails_bad`, `three_holds_good`: `Three` at the two cells of
    Johnson/Desc/First/Att/K05Guest.lean.
  `guest_mid`: the lookup alone, from (`forIn` and `Three`) to (`forOut`, Dn and Todo).
  `guest_seam`: `att_look` (OnBytes/Tie/Pv/Lookup/Rider/Model/AttLook.lean) at this chain; its
    premise hrel is `guest_at_point`.
  `guest_link`: the lookup, then the own rounds, from (`forIn` and `Three`) to (`forOut` at the
    first statement inside the last, and the chain's `Last`). The errors are the lookup's, then the
    chain's: no count is added for at3.
Premises: the lookup's test `FoNums.ok c.h`; `AttFits c.h P.D P.C` (arithmetic between the lookup's
record and the segment's sizes and calls); hz: the chain's point is the lookup's pt; `ZCRead P`
(Johnson/Desc/First/Att/K05Guest.lean); P.D.lT ≤ 2 ^ P.kap.
Used: typed reductions and joints and theorems on them; no routine in a context and no
run of a verifier on bytes: `forB`, `forIn`, `forOut`, `holeCgl`, `den_forB`, `att_look`, `AttFits`,
`knowAt_carry`, `knowAt_mono`, `knowAt_seq`, `ownAt_knowAt`, `att_todo`, `jt`, `withRider`,
`LookupCCaller`.
Limits: c and P are free letters; no value of them is given. `KnowAt` speaks for each fixed tuple of
messages m: all of m, the committed cells and the mask entries that the hidden scalars read, is
fixed before the lookup's first round. The joint R0 that rides through the lookup, and Dn, have to
be without at3: if either gives it, the statements follow from the lookup's own `KnowAt` and say
nothing of the test (`forB_hollow`, `knowAt_hollow_out`). The two sentences that a use of the rule
should prove (at `hollow_own`, Cb/G6/Rider/Both.lean) want a value of c and are not proved.
`two_of_todo` is `att_todo` (Cb/Pv/Att/End/Seam.lean), and `Two` is its `OwnM`, clause for clause.
Nothing on whether the programs test these equations, on an honest prover or on hiding.

-/
import Johnson.Top.H.LookupCRModel
import OnBytes.Tie.Pv.Lookup.Rider.Model.AttLook
import Cb.G6.Join
import Cb.Pv.Att.End.Seam
import Johnson.Desc.First.Att.K05Guest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.Rider Cb.LdLkp Cb.LdLkp.Kn Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open VerifiableInference.OnPublicFiles (LookupCCaller)

section Three
variable {K M X : Type} [Field K] [Fintype K]

/-- The three premises of `att_ord_base` on identities, at the chain's letters. -/
def Three (P : OwnPar K M X) (m : M) : Prop :=
  (∀ k b g i, (Idn.at1 k b g i).Valid P.D → idnVal P.D (P.tOf m) (.at1 k b g i) = 0) ∧
  (∀ b g i, (Idn.at2 b g i).Valid P.D → idnVal P.D (P.tOf m) (.at2 b g i) = 0) ∧
  ∀ b g i, (Idn.at3 b g i).Valid P.D → idnVal P.D (P.tOf m) (.at3 b g i) = 0

/-- own1 and own2. -/
def Two (P : OwnPar K M X) (m : M) : Prop :=
  (∀ k b g i, (Idn.at1 k b g i).Valid P.D → idnVal P.D (P.tOf m) (.at1 k b g i) = 0) ∧
  ∀ b g i, (Idn.at2 b g i).Valid P.D → idnVal P.D (P.tOf m) (.at2 b g i) = 0

theorem two_of_todo (P : OwnPar K M X) (hk : P.D.lT ≤ 2 ^ P.kap) (x : X) (m : M)
    (h : (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m) : Two P m :=
  Cb.Pv.Att.End.att_todo P hk x m h

theorem three_fails_bad (P : OwnPar K M X) (hb : 1 ≤ P.D.nb) (m : M) (ht : P.tOf m = cellsAt true) :
    ¬ Three P m := by
  intro h
  have h0 := h.2.2 0 0 0 ⟨hb, Nat.two_pow_pos _, by rw [P.D.T_eq]; exact Nat.two_pow_pos _⟩
  rw [ht, cells_at3] at h0
  simp at h0

theorem three_holds_good (P : OwnPar K M X) (m : M) (ht : P.tOf m = cellsAt false) : Three P m := by
  refine ⟨fun k b g i _ => ?_, fun b g i _ => ?_, fun b g i _ => ?_⟩
  · rw [ht]; exact cells_own1 _ _ _ _ _ _
  · rw [ht]; exact cells_own2 _ _ _ _ _
  · rw [ht, cells_at3]; simp

end Three

section Link
variable (c : LookupCCaller)
  (P : OwnPar Cb.Gl.E c.Sg.Msg (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)))

/-- **The host alone: the first joint of the own rounds takes the host's target up.** -/
theorem guest_mid (ok : FoNums.ok c.h = true) (F : AttFits c.h P.D P.C) (hz : ∀ b, P.zOf b = b.2.1.pt)
    (hZ : ZCRead P) (hk : P.D.lT ≤ 2 ^ P.kap)
    (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) :
    KnowAt (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R
      (withRider (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀) fun m _ => Three P m)
      (jt (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) id
        fun x m => Dn x m ∧ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.Todo x m)
      (fun _ _ _ wp => wp) (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e := by
  have g0 := holeCgl c.St₀ c.J₀ c.h c.L c.Ex c.Kc c.Sg.Msg c.Wp c.R0 c.msg₀ ok
  have g1 := den_forB g0 F (fun _ m => P.tOf m)
  have g2 := knowAt_carry g1 (fun _ => ()) (fun _ => ()) (fun _ _ _ _ _ => rfl) (fun m _ => Two P m)
  refine knowAt_mono g2 (fun _ h => h) (fun a w _ h => ⟨h.1.1, h.2.1, h.2.2, h.1.2⟩)
    (fun b w _ h => ⟨⟨h.1, ?_⟩, two_of_todo P hk b.1 w.1 h.2.2⟩) (fun _ h => h)
  show denOut P.D P.C b.1.2.1.pt (P.tOf w.1) = 0
  rw [← hz]
  exact guest_at_point P hZ b.1 w.1 h.2.2

/-- **`att_look` at the own rounds' chain**, with A0 := the host's out-joint and pr := id. -/
theorem guest_seam (ok : FoNums.ok c.h = true) (F : AttFits c.h P.D P.C) (hz : ∀ b, P.zOf b = b.2.1.pt)
    (hZ : ZCRead P) (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) :
    KnowAt (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R
      (forIn Cb.Gl.E c.h c.L (withRider c.R0 fun m _ =>
        ∀ b g i, Idn.Valid P.D (.at3 b g i) → idnVal P.D (P.tOf m) (.at3 b g i) = 0) c.msg₀)
      (jt (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) id
        fun x m => Dn x m ∧ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.Todo x m)
      (fun _ _ _ wp => wp) (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e :=
  att_look (holeCgl c.St₀ c.J₀ c.h c.L c.Ex c.Kc c.Sg.Msg c.Wp c.R0 c.msg₀ ok) F (fun _ m => P.tOf m)
    (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) id Dn (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch
    (fun _ hb => hb)
    (fun b w _ h1 _ h3 => ⟨h1, by rw [← hz]; exact guest_at_point P hZ b.1 w.1 h3⟩)

/-- **Host and guest composed**: the lookup, then attention's own rounds. -/
theorem guest_link (ok : FoNums.ok c.h = true) (F : AttFits c.h P.D P.C) (hz : ∀ b, P.zOf b = b.2.1.pt)
    (hZ : ZCRead P) (hk : P.D.lT ≤ 2 ^ P.kap)
    (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) :
    KnowAt ((forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.seq
        ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.R c.Ex))
      (withRider (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀) fun m _ => Three P m)
      (jt (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀)
        (fun e => id ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.back e))
        ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.Last Dn))
      (fun _ _ _ wp => wp)
      (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e
        ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.eps c.Ex)) :=
  knowAt_seq (guest_mid c P ok F hz hZ hk Dn)
    (ownAt_knowAt P c.Ex (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) id Dn)

end Link

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.two_of_todo
#print axioms VerifiableInference.Desc.First.Att.P.three_fails_bad
#print axioms VerifiableInference.Desc.First.Att.P.three_holds_good
#print axioms VerifiableInference.Desc.First.Att.P.guest_mid
#print axioms VerifiableInference.Desc.First.Att.P.guest_seam
#print axioms VerifiableInference.Desc.First.Att.P.guest_link
