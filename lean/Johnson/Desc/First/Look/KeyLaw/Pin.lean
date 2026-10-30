-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/Pin.lean: FROM "KNOWLEDGE SOUND FOR EACH FIXED TUPLE OF MESSAGES" TO
"KNOWLEDGE SOUND": a rule, and the typed lookup with parts as a bare block with a block's property.

The typed lookup's lemma (Lk6.lamS_know, Cb/Pv/KeyLookup/Lam1Short.lean) is stated for each fixed
tuple m of messages (TWhole.KnowAt, Cb/G6/Cut.lean). A bare block's property (KObj.BK.Good,
Johnson/E/KObj/Blocks.lean) speaks of all witnesses (m, wp) at once. The second follows from the
first where the statement PINS the messages: two witnesses of the riding joint's relation at one
statement in its condition have the same messages (so it is where the relation says "the messages
are what a decoder, a function of the samples and the oracles, gives": Sig.over, Cb/Ld/LdSig.lean).

Main names:
  know_of_pin: the rule, for any reduction.
  Pins R0: the riding joint's relation pins the messages by the statement.
  jIn, jOut, bkLam: the typed lookup's two joints and the lookup itself, as a bare block.
  bkLam_good: under Adm and Pins: the block's property.

Limits. Pins is a premise. No riding joint is given here.

-/
import Cb.Pv.KeyLookup.HKey
import Johnson.E.KObj.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open Iop IOR Iop.Reduction KObj Cb Cb.LdLkp
open Lk6 (Dat Pl)

/-- **The rule.** A reduction that is knowledge sound for each fixed m, with the identity as
extractor; whatever it puts out from a statement in the condition is in the condition behind; and
any two witnesses of what it puts out from one statement have the same m. Then it is knowledge sound
into the condition behind, over all witnesses. -/
theorem know_of_pin {X Y M Wp : Type} (K : Reduction X Y) (on : X → Prop) (on' : Y → Prop)
    (RA : X → M × Wp → Prop) (RB : Y → M × Wp → Prop) (ε : Err K.shape)
    (h : ∀ m, K.Know on (fun a wp => RA a (m, wp)) (fun b wp => RB b (m, wp)) (fun _ _ wp => wp) ε)
    (ho : ∀ a τ b, on a → K.out a τ = some b → on' b)
    (pin : ∀ a τ τ' b b' m m' wp wp', on a → K.out a τ = some b → K.out a τ' = some b' →
      RB b (m, wp) → RB b' (m', wp') → m = m') :
    K.KnowInto on on' RA RB (fun _ _ w => w) ε := by
  intro a ha
  by_cases hex : ∃ τ b m wp, K.out a τ = some b ∧ RB b (m, wp)
  · obtain ⟨τ0, b0, m0, wp0, o0, r0⟩ := hex
    refine Doomed.mono _ _ (fun τ hτ b w hb hw => ?_) (h m0 a ha)
    rcases hw with hw | hn
    · obtain ⟨m, wp⟩ := w
      obtain rfl : m = m0 := pin a τ τ0 b b0 m m0 wp wp0 ha hb o0 hw r0
      exact hτ b wp hb hw
    · exact absurd (ho a τ b ha hb) hn
  · refine Doomed.of_forall _ _ fun τ b w hb hw => ?_
    rcases hw with hw | hn
    · exact absurd ⟨τ, b, w.1, w.2, hb, hw⟩ hex
    · exact absurd (ho a τ b ha hb) hn

variable (A : Dat Cb.Gl.E) (P : Pl A) (Ex : ExtSpec) {Kc M Wp : Type}
  (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → Cb.Gl.E)

/-- The riding joint's relation pins the messages by the statement, where its condition holds. -/
def Pins : Prop :=
  ∀ (x : A.St) (y : Ex.Str) (m m' : M) (wp wp' : Wp), R0.on (x, y) →
    R0.relR (x, y) (m, wp) → R0.relR (x, y) (m', wp') → m = m'

/-- The joint in front: beside R0, every key of every part is a row of the table. -/
def jIn : JK :=
  ⟨A.St, Ex, M × Wp, (A.jtIn R0 msg fun _ _ => True).on, (A.jtIn R0 msg fun _ _ => True).relR⟩

/-- The joint behind: beside R0, each part's claim on its keys and all rows hold. -/
def jOut : JK := ⟨A.Out, Ex, M × Wp, (A.jtOut R0 msg).on, (A.jtOut R0 msg).relR⟩

/-- The typed lookup with parts as a bare block. -/
noncomputable def bkLam : BK (jIn A Ex R0 msg) (jOut A Ex R0 msg) :=
  ⟨(A.lamS P Ex).R, fun _ _ w => w, (A.lamS P Ex).e⟩

/-- **The block's property.** -/
theorem bkLam_good (hadm : A.toPub.Adm Cb.Gl.p) (hpin : Pins A Ex R0) :
    (bkLam A P Ex R0 msg).Good := by
  have g := Lk6.lamS_know Cb.Gl.p A P Ex Kc M Wp R0 msg (fun _ _ => True) hadm
  refine ⟨g.point, g.isLocal, ?_⟩
  refine know_of_pin (A.lamS P Ex).R.red _ _ _ _ _ g.know g.onOut ?_
  intro a τ τ' b b' m m' wp wp' ha hb hb' hr hr'
  have e1 := (red_out_eq_some.1 hb).2
  have e2 := (red_out_eq_some.1 hb').2
  rw [(Lk6.lamS_copies A P Ex).copy] at e1 e2
  have p1 : b.1.1 = a.1 := Lk6.lamS_passes A P Ex _ _ _ _ (red_out_eq_some.1 hb).1
  have p2 : b'.1.1 = a.1 := Lk6.lamS_passes A P Ex _ _ _ _ (red_out_eq_some.1 hb').1
  have r1 : R0.relR (b.1.1, b.2) (m, wp) := hr.1
  have r2 : R0.relR (b'.1.1, b'.2) (m', wp') := hr'.1
  rw [e1, p1] at r1
  rw [e2, p2] at r2
  exact hpin _ _ _ _ _ _ ha r1 r2

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.know_of_pin
#print axioms VerifiableInference.Desc.K3.KeyLaw.bkLam_good
