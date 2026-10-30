-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyEvalIn.lean: THE KEY FILE's SHARED CHAIN: THE PREMISE «evalIn» OF THE RIDE LAWS (Common.evalIn: RunOne/Law/KeyRide23.lean:220) FROM THE TABLES' OWN PROMISE: the row (Eval), as it lies in what the first chain handed on, lies on the tables of a group whose members the first chain's plan sends to riders.
OBJECT: Common.evalIn at rows 2.9 | 2.10 · USER: whoever calls ride_29 | ride_210 · LETTERS: one · ks.
  evalIn_of_last     PROVED: on the handed state alone: the first chain's last book-keeping (last₁At one s) · OpenIn at the last group · 1 ≤ stages · 0 ∈ ks · 2 ∈ ks ⟹ evalIn's text at s
  evalIn_of_free₂    PROVED: from Free₂ … k z y at K₁ := plan₁ one · last₁ := last₁At one (its fields last · in₁)
BY THREE CALLS: firstOutFrom_spec (what the last chain's start reads is the handed statement and the claim's own group's number) · ownB inside the last book-keeping (core₁_own: the own group is the last; its members are just I and V) · OpenIn at «size − 1».
Nothing on soundness.
-/
import Johnson.RunOne.KeySeam1
import Johnson.RunOne.KeySeams23
import Johnson.RunOne.KeyAtFkMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ n₁ slots₁ ties₁ tiesA)

theorem evalIn_of_last (S : LinShape) (one : OneTime) (ks : List Nat) (h0 : 0 ∈ ks) (h2 : 2 ∈ ks) (hst : 1 ≤ one.ranges.stages.length)
    (s : FirstState) (hl : last₁At one s = true) (hin : OpenIn s.d.st (s.d.st.groups.size - 1)) (r : OnBytes.Row) (hr : evalAt S s = some r) :
    ∃ Gr, Means.RowIn (firstOf s).1 Gr r ∧ ∀ o ∈ Gr.members.toList, ∀ j, (plan₁ one).num o = some j → j ∈ ks := by
  -- what evalAt reads
  unfold evalAt firstAt at hr
  obtain ⟨f, hf, hr⟩ := Option.bind_eq_some_iff.1 hr
  obtain ⟨L, hL, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨e1, -, -, -, e5, -, -⟩ := firstOutFrom_spec S _ _ _ _ _ _ _ f hf
  rw [e1, e5] at hr
  obtain ⟨Gr, hG, hr0⟩ := Option.bind_eq_some_iff.1 hr
  -- the own group is the last; its members are I and V
  unfold last₁At at hl
  have hc := ((shape₁_iff _ _ _ _ _ _ _).1 hl).2
  have ho := core₁_own (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) 5 s (by decide) hc
  obtain ⟨v, hv, hnv⟩ := planOk₁ one hst 2 (by simp)
  have hown : (book₁ one).own s = some L.own := by show s.lin.map (·.own) = some L.own; rw [hL]; rfl
  have h00 : (plan₁ one).orc 0 = some 0 := rfl
  unfold ownB at ho
  rw [h00, hv, hown] at ho
  simp only [Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨⟨-, hlast⟩, hany⟩ := ho
  have hG' : s.d.st.groups[L.own]? = some Gr := hG
  have hG'' : ((readers₁ one).st s).groups[L.own]? = some Gr := hG
  rw [hG''] at hany
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hany
  have hmem : Gr.members.toList = [0, v] := hany.1.1
  have hsz : L.own = s.d.st.groups.size - 1 := by
    have : L.own + 1 = s.d.st.groups.size := hlast
    omega
  refine ⟨Gr, hin Gr (hsz ▸ hG') r ?_, fun o ho' j hj => ?_⟩
  · exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hr0)
  · rw [hmem] at ho'
    rcases (by simpa using ho' : o = 0 ∨ o = v) with rfl | rfl
    · obtain rfl : (0 : Nat) = j := Option.some.inj hj
      exact h0
    · obtain rfl : (2 : Nat) = j := Option.some.inj (hnv.symm.trans hj)
      exact h2

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop) (off₂ : Nat → Nat)

theorem evalIn_of_free₂ (ks : List Nat) (h0 : 0 ∈ ks) (h2 : 2 ∈ ks) (hst : 1 ≤ one.ranges.stages.length) (k : Nat) (z : P₂ × St₂) (y : Strs)
    (hf : Free₂ F G₂ at_ S (plan₁ one) R coll (last₁At one) off₂ k z y) :
    ∀ r, (readers₂ S).eval z.1 = some r → ∃ Gr, Means.RowIn ((readers₂ S).st₁ z.1) Gr r ∧
      ∀ o ∈ Gr.members.toList, ∀ j, (plan₁ one).num o = some j → j ∈ ks :=
  fun r hr => evalIn_of_last S one ks h0 h2 hst z.1.2 hf.last hf.in₁.2 r hr

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.evalIn_of_last
#print axioms Johnson.RunOne.KeyRows23.evalIn_of_free₂
