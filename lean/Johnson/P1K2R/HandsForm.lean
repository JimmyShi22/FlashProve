-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HandsForm.lean: code switching
(K2): FROM «THE SEATED SUB-PROTOCOL IS THE WAY IN, THE SWITCH's OWN STEP, THE WAY OUT» TO THE FORM
«Hands» (IM.Hands, Johnson/IMR/HandsDef.lean). NO BLOCK IMPORTS THIS FILE.
  MarkDoor · NoMarkDoor.mark   the door's share of «a mark stays a mark»: the way in leaves the
                               mark; the way out hands no marked state on as unmarked. (A guarded
                               door, NoMarkDoor, has it; so has the lot's bare sub-protocol's.)
  hands_of_never  a sub-protocol that never accepts owes nothing
  hands_of_sitsR  the same at HandsR:
                  each field is asked at fenced states alone (Fk k s); the
                  proof stands here; hands_of_sits is its case «no fence»
  hands_of_sits   Sits b (K2.codeSwitchKind p) enter leave · MarkDoor · for every way through the three (s to
                  t by the way in, t to t' by the switch's step, t' to s' by the way out), with no
                  mark: X k s hands on X (k + 1) s': then Hands N links ps E ft k b
The field «mark» is paid here outright: the switch's own step leaves the mark (k2_step_mark).
LIMITS. A form: its last premise is the whole of shape · rows · members · book · more. No
soundness is claimed.
-/
import Johnson.IMR.HandsFence
import Johnson.P1K2R.SitsMark

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (Hands HandsR XK Yes xk_parts)

/-- The door's share of «a mark stays a mark». -/
structure MarkDoor (enter : S → Except String S) (leave : S → S → Except String S) : Prop where
  into : ∀ s t, enter s = .ok t → t.failed = s.failed
  out : ∀ s t' s', leave s t' = .ok s' → t'.failed ≠ none → s'.failed ≠ none

theorem NoMarkDoor.mark {enter : S → Except String S} {leave : S → S → Except String S}
    (h : NoMarkDoor enter leave) : MarkDoor enter leave :=
  ⟨h.into, fun s t' s' e hm => absurd (h.out s t' s' e).1 hm⟩

/-- A sub-protocol that never accepts owes nothing. -/
theorem hands_of_never {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft k : Nat} {b : Block S Cl} (h : ∀ s s', ¬ Yes ft b s s') : Hands N links ps E ft k b :=
  ⟨fun s s' hy => absurd hy (h s s'), fun s s' hy => absurd hy (h s s'),
    fun s s' hy => absurd hy (h s s'), fun s s' hy => absurd hy (h s s'),
    fun s s' hy => absurd hy (h s s'), fun s s' hy => absurd hy (h s s')⟩

theorem hands_of_sitsR {Fk : Nat → S → Prop} {N : Numbers} {links : List ModelPart} {ps : List Place}
    {E : Nat → S → Bool} {ft k : Nat} {b : Block S Cl} {p : P2} {enter : S → Except String S}
    {leave : S → S → Except String S} (hs : Sits b (codeSwitchKind p : Block S Unit) enter leave)
    (hd : MarkDoor enter leave)
    (H : ∀ (s t t' s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat), Fk k s →
      Yes ft b s s' → enter s = .ok t →
      (codeSwitchKind p : Block S Unit).step ft t rs cols = .ok (t', n) → leave s t' = .ok s' →
      s.failed = none → s'.failed = none → XK N links ps E k s = true →
      XK N links ps E (k + 1) s' = true) : HandsR Fk N links ps E ft k b := by
  have key : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps E k s = true → XK N links ps E (k + 1) s' = true := by
    intro s s' hf hy h0 h1 hx
    obtain ⟨rs, cols, n, e⟩ := hy
    obtain ⟨t, t', e1, e2, e3⟩ := hs.step ft s s' rs cols n e
    exact H s t t' s' rs cols n hf ⟨rs, cols, n, e⟩ e1 e2 e3 h0 h1 hx
  refine ⟨fun s s' _ hy hm => ?_,
    fun s s' hf hy h0 h1 hx => (xk_parts (key s s' hf hy h0 h1 hx)).1,
    fun s s' hf hy h0 h1 hx => (xk_parts (key s s' hf hy h0 h1 hx)).2.1,
    fun s s' hf hy h0 h1 hx => (xk_parts (key s s' hf hy h0 h1 hx)).2.2.1,
    fun s s' hf hy h0 h1 hx => (xk_parts (key s s' hf hy h0 h1 hx)).2.2.2.1,
    fun s s' hf hy h0 h1 hx => (xk_parts (key s s' hf hy h0 h1 hx)).2.2.2.2⟩
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨t, t', e1, e2, e3⟩ := hs.step ft s s' rs cols n e
  refine hd.out s t' s' e3 ?_
  rw [k2_step_mark e2, hd.into s t e1]
  exact hm

theorem hands_of_sits {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft k : Nat} {b : Block S Cl} {p : P2} {enter : S → Except String S}
    {leave : S → S → Except String S} (hs : Sits b (codeSwitchKind p : Block S Unit) enter leave)
    (hd : MarkDoor enter leave)
    (H : ∀ (s t t' s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat), Yes ft b s s' →
      enter s = .ok t →
      (codeSwitchKind p : Block S Unit).step ft t rs cols = .ok (t', n) → leave s t' = .ok s' →
      s.failed = none → s'.failed = none → XK N links ps E k s = true →
      XK N links ps E (k + 1) s' = true) : Hands N links ps E ft k b :=
  (hands_of_sitsR (Fk := fun _ _ => True) hs hd
    fun s t t' s' rs cols n _ => H s t t' s' rs cols n).free

end P1K2

#print axioms P1K2.hands_of_never
#print axioms P1K2.hands_of_sitsR
#print axioms P1K2.hands_of_sits
