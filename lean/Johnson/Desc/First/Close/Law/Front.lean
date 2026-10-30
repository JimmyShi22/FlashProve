-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Front.lean: THE END OF K10's LAW OVER ITS WRITTEN ROUNDS, SAID AT THE
DECODED MESSAGES. A definition, statements and proofs.

`k10_leads` (Leads.lean, beside this file) ends in "the relaxed relation of the typed joint in front
of the batching has a witness". That relation (the library's `Sig.over`, Cb/Ld/LdSig.lean) says of a
witness's messages first of all that each IS what its word decodes to with its sample: a function of
the statement and the oracles. So "there is a witness" says something of ONE object.
  `front_relR`: the relation, taken apart, by definition: (1) every member's message is what its
    word decodes to with its sample; (2) all typed rows of the claim hold of the group's messages;
    (3) the joint on the kept messages holds of the kept ones among them.
  `front_at`: so, if it has a witness: at EVERY family m of messages that are the decodings, (2)
    holds of m, and (3) of m with some further witness.
  `FrontAt s A₀ F x`, `frontAt_of`: both together: the decodings are there; and (2), (3) at whatever
    family is the decodings.
  `leads_front`: a law (Johnson/Desc/Plain/Leads.lean) that ends in "the joint in front has a
    witness" ends in `FrontAt`: by the frame rule `Leads.conseq`; the errors do not turn.
  `k10_front`: so of the end of `k10_leads` and `k10_leads_good`, as they stand.

What it is for [a thought; no statement here says it]. The table of joints wants a kind's law for
every world w (the one committed object). A world whose messages are pinned at the statement in
front should be such an m. If so, no extractor of the typed block need be named or opened, and that
"the message under the 'there is' behind, at the kept slots, is the kept joint's own" need not be
shown apart: the pins in front are functional.
Limits. Those of Leads.lean. Typed rows, typed decoding: no item of a table is named here. The
converse of `frontAt_of` is not shown (a witness also holds randomness).

-/
import Johnson.Desc.First.Close.Law.Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj OnBytes.Flat
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)

section Front
variable {K : Type} [Field K] [Fintype K] (s : Cb.Pv.Bat.Size K) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) (F : ExtSpec)

/-- The relaxed relation of the joint in front of the batching, taken apart. -/
theorem front_relR
    (x : ((((s.B → K) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod F).Str)
    (w : s.S.Wit × Wp) :
    ((Cb.Pv.Bat.inJ s A₀).keepE F).relR x w ↔
      (∀ i, s.S.decs x.1.2 x.2.1.2 i = some (w.1 i).1) ∧
        Slf.All s.sl x.1.1.1 (s.G.msg (s.S.msgs w.1)) ∧
        A₀.relR (x.1.1.2, x.2.1.1) (s.S.res (T := OMsg.Msg) s.kp (s.S.msgs w.1), w.2) := Iff.rfl

/-- If it has a witness, it holds at the decoded messages. -/
theorem front_at
    (x : ((((s.B → K) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod F).Str)
    (h : ∃ w, ((Cb.Pv.Bat.inJ s A₀).keepE F).relR x w) (m : s.S.Msg)
    (hm : ∀ i, s.S.decs x.1.2 x.2.1.2 i = some (m i)) :
    Slf.All s.sl x.1.1.1 (s.G.msg m) ∧
      ∃ wp, A₀.relR (x.1.1.2, x.2.1.1) (s.S.res (T := OMsg.Msg) s.kp m, wp) := by
  obtain ⟨w, h1, h2, h3⟩ := h
  have e : s.S.msgs w.1 = m := funext fun i => Option.some.inj ((h1 i).symm.trans (hm i))
  rw [e] at h2 h3
  exact ⟨h2, w.2, h3⟩

/-- **The joint in front, at the decoded messages**: every member's word decodes with its sample;
and of the messages that they decode to, all typed rows of the claim hold, and the joint on the kept
messages, with some further witness. -/
def FrontAt
    (x : ((((s.B → K) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod F).Str) : Prop :=
  (∃ m : s.S.Msg, ∀ i, s.S.decs x.1.2 x.2.1.2 i = some (m i)) ∧
    ∀ m : s.S.Msg, (∀ i, s.S.decs x.1.2 x.2.1.2 i = some (m i)) →
      Slf.All s.sl x.1.1.1 (s.G.msg m) ∧
        ∃ wp, A₀.relR (x.1.1.2, x.2.1.1) (s.S.res (T := OMsg.Msg) s.kp m, wp)

theorem frontAt_of
    (x : ((((s.B → K) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod F).Str)
    (h : ∃ w, ((Cb.Pv.Bat.inJ s A₀).keepE F).relR x w) : FrontAt s A₀ F x :=
  ⟨h.elim fun w hw => ⟨s.S.msgs w.1, hw.1⟩, fun m hm => front_at s A₀ F x h m hm⟩

/-- A law that ends in "the joint in front has a witness" ends in `FrontAt`. -/
theorem leads_front {A B : Type} (Kr : Reduction A B) (on : A → Prop) (P1 C : A → B → Prop)
    (fa : A → ((((s.B → K) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod F).Str)
    (ε : Err Kr.shape)
    (h : Kr.Leads on (fun a b => P1 a b ∧
      (C a b → ∃ w, ((Cb.Pv.Bat.inJ s A₀).keepE F).relR (fa a) w)) ε) :
    Kr.Leads on (fun a b => P1 a b ∧ (C a b → FrontAt s A₀ F (fa a))) ε :=
  h.conseq (fun _ k => k) fun a _ _ _ _ hq => ⟨hq.1, fun hc => frontAt_of s A₀ F (fa a) (hq.2 hc)⟩

end Front

section Caller
variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **K10's law over its written rounds, with its end at the decoded messages**: from the end of
`k10_leads` | `k10_leads_good`, as they stand. -/
theorem k10_front (L : List (BatFoldCaller GE)) (rB rE rR : Round)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR)
    (P : Plan) (g : Nat) (mask : Option Nat) {A : Type} (stOf : A → Statement)
    (fa : A → ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (on : A → Prop)
    (ε' : Err (rB :: rE ::
      List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR))
    (h : (closeRed ρ P g mask stOf).Leads on
      (fun a b => b.1 = a ∧ (CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (fa a) b.2.1 →
        ∃ w, ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).relR (fa a) w))
      ε') :
    (closeRed ρ P g mask stOf).Leads on
      (fun a b => b.1 = a ∧ (CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (fa a) b.2.1 →
        FrontAt (R.sizeB keep Sb sl Z) A₀ R.Sh.par.Cw.nat (fa a))) ε' :=
  leads_front (R.sizeB keep Sb sl Z) A₀ R.Sh.par.Cw.nat (closeRed ρ P g mask stOf) on
    (fun a b => b.1 = a)
    (fun a b => CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (fa a) b.2.1) fa ε' h

end Caller

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.front_relR
#print axioms VerifiableInference.Desc.First.Close.front_at
#print axioms VerifiableInference.Desc.First.Close.frontAt_of
#print axioms VerifiableInference.Desc.First.Close.leads_front
#print axioms VerifiableInference.Desc.First.Close.k10_front
