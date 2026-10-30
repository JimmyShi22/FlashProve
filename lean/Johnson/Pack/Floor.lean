-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/Floor.lean: the sending of any family of oracle messages, and what a preamble leaves
behind it, from three conditions on the members.

Definitions, statements and proofs; each proof is a call of the library. The library builds its own
families of oracle messages by records that fix a layout. This file shows that the road from a
family to the interface of `rec_main` does not need them: for every signature N (`Sig`,
Cb/Ld/LdSig.lean) the sending `ldSendFam` (Cb/Ld/LdSendFam.lean) is knowledge sound, and, closed, it
is a preamble in the sense of Hiop/RecSubs.lean, if the joint seed is fair, the members' lists are
short and their sample maps evade.
Main names:
  `HFair`, `HList`, `HEvades`, `HLaws`: the conditions, with the members bound inside.
  `send_knowInto`: knowledge soundness of the sending into collision-free statements
    (`ldSendFam_into`).
  `send_pl`: its verifier is local and its oracles are point oracles.
  `floor_preKnow`: `PreKnowR (sigLeft C N Cl holds) (closeF (ldSendFam ..))` (`ldClose_know`).
  `fair_indep`: independent seeds are fair.
  `MemOK`, `holes_of_members`: a member within unique decoding, below the Johnson radius, or below
    it over a subfield has short lists, an evading sample and the laws.
Limits: in `floor_preKnow` the claims `holds`, the joint A, the relation RiR and the way back are
parameters under three conditions that tie them; the statement shows that the types meet for every
signature, and it can be met by trivial choices. Nothing on the honest prover or on hiding.
-/
import Cb.Ld.LdWfCloseProofs
import Cb.Ld.LdSendFamProofs
import Cb.Req1.LdReqJohn
import Cb.Req1.LdReqJohnSub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pack
open Iop Prob Hiop IOR Cb.Ood

section
variable {E : Type} [Field E]

/-- The joint seed is fair: no member's seed is hit by more than its multiplicity. -/
def HFair (N : Sig E) (Sd : N.Seeds) : Prop := Sd.Fair

/-- Every member's lists have at most `L a` messages. -/
def HList (N : Sig E) (L : N.O → ℕ) : Prop := ∀ a, (N.om a).ListLE (L a)

/-- Every member's sample map evades: two different messages of one list have the same answers at
few seeds. -/
def HEvades (N : Sig E) : Prop := ∀ a, (N.om a).Evades

/-- Every member's code has its laws. (Used for locality alone.) -/
def HLaws (N : Sig E) : Prop := ∀ a, (N.om a).C.Laws

/-- The sending's errors. -/
def sendErr (N : Sig E) (Sd : N.Seeds) (L : N.O → ℕ) (X : Type) (E₀ : ExtSpec) :
    Err (ldSendFam N Sd X E₀).shape := (ldSendFamErr N Sd L, (0, ()))

/-- The sending of any signature: knowledge soundness into collision-free statements. -/
theorem send_knowInto (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec)
    (A : Rels Kc X E₀ W) (back : N.Msg → W' → W) (L : N.O → ℕ) (hF : HFair N Sd)
    (hL : HList N L) (hE : HEvades N) :
    (ldSendFam N Sd X E₀).red.KnowInto A.on (N.over (N.pull A back)).on A.relR
      (N.over (N.pull A back)).relR (fun _ _ w => back (N.msgs w.1) w.2) (sendErr N Sd L X E₀) :=
  ldSendFam_into E N Sd Kc X W W' E₀ A back L hF hL hE

/-- The sending of any signature: a local verifier, point oracles. -/
theorem send_pl (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec) (h : HLaws N) :
    (ldSendFam N Sd X E₀).IsLocal ∧ Nonempty (ldSendFam N Sd X E₀).shape.IsPoint :=
  ⟨ldSendFam_isLocal N Sd X E₀ h, ⟨N.pt Sd⟩⟩

/-- One sending of N, closed: the item on knowledge soundness of a preamble, at what the preamble
leaves for N. -/
theorem floor_preKnow (C : ConfigurationWithOutOfDomainSample) (N : Sig E) (Sd : N.Seeds) (Kc Wi Wr Cl Wp : Type)
    (holds : Cl → C.Rec → C.Msg → N.Msg → Prop) (A : Rels Kc (Cl × C.Rec) C.E0 Wi)
    (back : N.Msg → Wp → Wi) (L : N.O → ℕ) (RiR : (Cl × C.Rec) × C.E0.Str → Wr → Prop)
    (fr : Wi → Wr) (z0 : Wp) (r0 : N.Rnd) (hF : HFair N Sd) (hL : HList N L) (hE : HEvades N)
    (h1 : ∀ a m U, C.dcd a.2 a.1.2 = some U → holds a.1.1 a.1.2 U m → A.relR a (back m z0))
    (h2 : ∀ a, A.on a → ¬ C.coll a.2 a.1.2.1)
    (h3 : ∀ a w, A.on a → A.relR a w → RiR a (fr w)) :
    PreKnowR (sigLeft C N Cl holds) (closeF (ldSendFam N Sd (Cl × C.Rec) C.E0)) A.on RiR
      (fun _ _ m => fr (back (N.msgs (N.pair m r0)) z0)) (sendErr N Sd L (Cl × C.Rec) C.E0) :=
  ldClose_know E C N Kc (Cl × C.Rec) Wi Wr Cl Wp holds (ldSendFam N Sd (Cl × C.Rec) C.E0) A.on
    A.relR (N.pull A back) (fun _ _ w => back (N.msgs w.1) w.2) (sendErr N Sd L (Cl × C.Rec) C.E0)
    RiR fr z0 r0 (send_knowInto N Sd Kc (Cl × C.Rec) Wi Wp C.E0 A back L hF hL hE) h1 h2 h3

omit [Field E] in
/-- Independent seeds are fair, for every signature. -/
theorem fair_indep (N : Sig E) : HFair N (Sig.Seeds.indep N) := (ldSendFam_fair_indep E N).1

end

section
variable (K : Type) {E : Type} [Field K] [Field E] [Fintype E] [Algebra K E]

/-- What is asked of one member: within unique decoding, or below the Johnson radius, or below it
with all rows over the subfield K. -/
def MemOK (o : OMsg E) (d L : ℕ) : Prop := o.NearJ d L ∨ o.JohnF K d L

/-- Member by member: lists, evasion and laws. -/
theorem holes_of_members (N : Sig E) (d L : N.O → ℕ)
    (h : ∀ a, MemOK K (N.om a) (d a) (L a)) : HList N L ∧ HEvades N ∧ HLaws N :=
  ⟨fun a => (h a).elim (fun g => (ldReqJohn_msg E _ _ _ g).2.1) (ld_subfield_list K E _ _ _),
    fun a => (h a).elim (fun g => (ldReqJohn_msg E _ _ _ g).2.2) (ld_subfield_evades K E _ _ _),
    fun a => (h a).elim (fun g => (ldReqJohn_msg E _ _ _ g).1) fun g => g.laws⟩

end
end Cb.Pack

#print axioms Cb.Pack.send_knowInto
#print axioms Cb.Pack.send_pl
#print axioms Cb.Pack.floor_preKnow
#print axioms Cb.Pack.fair_indep
#print axioms Cb.Pack.holes_of_members
