-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/OnlineK.lean: knowledge soundness of "an IOR in every slot, then a batch IOP": the proof of
`Iop.Spec.sndBK_online` (stated in Ior/Batch.lean).

An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction. A batch IOP (`BatchInteractiveOracleProof`,
Iop/Batch.lean) is one IOP, for the local transcript of a slot, with an annotation of its shape
(`RoundSplits`): which verifier messages the slots share, and how each prover message splits into a shared
part and a slot's part. A slot is one of the N places of a batch, each with one instance or empty,
with its own local transcript.

Main names (statements and hypotheses: Ior/Batch.lean):
  `sndBK_online`: knowledge soundness of "an IOR in every slot, then a batch IOP"

The proof is by sets of bad values (Blocks/Batch/Kit.lean; Ior/BatchKProofsBad.lean shows that for
batches they say the same as state functions, with the same errors, at early = id, late = none). The
rounds of the IOR are local, so each slot pays for itself. In the rounds of the batch IOP the joint
law is that of the batch IOP on the vector of the middle statements (`mid` in the proof); these
share their first implicit component because the IOR copies it.

Limits: this file says nothing on the honest side (completeness, zero knowledge), on queries, or on
running times. The bad sets of the proof (`lostFam` among them) are chosen, not computed; they occur
in no statement, but for the two lemmas on `lostFam`.
Terms: lean/GLOSSARY.md.
-/
import Ior.BatchKProofsBad
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

/-! ## 1. Raising flags, filling empty slots -/

/-- The laws on bad sets are kept if each slot of G' has the bad sets of the same slot of G, with a
flag that is 1 where that of G is, or has no bad value at all. -/
theorem JWithin.weaken (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (G G' : Fin N → Option (Bool × BadFam s)),
      JWithin N s A ε G →
      (∀ j p', G' j = some p' →
        (∃ p, G j = some p ∧ p'.2 = p.2 ∧ (p.1 = true → p'.1 = true)) ∨ p'.2 = BadFam.empty s) →
      JWithin N s A ε G'
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), G, G', hJ, hG => by
      intro m0 m
      obtain ⟨h1, h2⟩ := hJ m0 m
      refine ⟨?_, fun v => JWithin.weaken N s A ε _ _ (h2 v) fun j q hq => ?_⟩
      · obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
        cases k
        · refine le_trans (cnt_mono ?_) h1
          rintro c ⟨j, p', hp', h0, hc⟩
          rcases hG j p' hp' with ⟨p, hp, hB, hf⟩ | hB
          · rw [hB] at hc
            exact ⟨j, p, hp,
              Bool.eq_false_iff.2 fun h => Bool.false_ne_true (h0.symm.trans (hf h)), hc⟩
          · rw [hB] at hc
            exact absurd hc (Set.notMem_empty c)
        · intro j p' hp' h0
          rcases hG j p' hp' with ⟨p, hp, hB, hf⟩ | hB
          · rw [hB]
            exact h1 j p hp (Bool.eq_false_iff.2 fun h => Bool.false_ne_true (h0.symm.trans (hf h)))
          · rw [hB]
            exact (cnt_false fun c => Set.notMem_empty c).le.trans (Nat.zero_le _)
      · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hq
        rcases hG j p' hp' with ⟨p, hp, hB, hf⟩ | hB
        · refine Or.inl ⟨_, by rw [hp]; rfl, ?_, ?_⟩
          · show p'.2.2 _ _ = p.2.2 _ _
            rw [hB]
          · show (p.1 || _) = true → (p'.1 || _) = true
            rw [hB]
            intro h
            rcases Bool.or_eq_true_iff.1 h with h | h
            · rw [hf h, Bool.true_or]
            · rw [h, Bool.or_true]
        · right
          show p'.2.2 _ _ = _
          rw [hB]
          rfl

/-! ## 2. Bad values from "the prover has lost" -/

open Classical in
/-- Bad sets within the errors ε such that every full transcript without a bad value has the
property "lost", if there are such sets; else empty sets. -/
def lostFam (s : Shape) (ε : Err s) (lost : Tr s → Prop) : BadFam s :=
  if h : ∃ B : BadFam s, B.Within ε ∧ ∀ τ, B.Clean τ → lost τ then h.choose else BadFam.empty s

theorem lostFam_within (s : Shape) (ε : Err s) (lost : Tr s → Prop) :
    (lostFam s ε lost).Within ε := by
  unfold lostFam
  split_ifs with h
  · exact h.choose_spec.1
  · exact BadFam.empty_within s ε

theorem lostFam_clean {s : Shape} {ε : Err s} {lost : Tr s → Prop} (h : Doomed s ε lost)
    {τ : Tr s} (hτ : (lostFam s ε lost).Clean τ) : lost τ := by
  have h' := Doomed.exists_badFam s ε lost h
  unfold lostFam at hτ
  rw [dif_pos h'] at hτ
  exact h'.choose_spec.2 τ hτ

/-! ## 3. The theorem -/

/-- The oracles of the first part of a transcript, of the second part. -/
theorem Orcs.fst_read {s t : Shape} (τ : Tr (s ++ t)) : Orcs.fst τ.read = (Tr.fst τ).read :=
  funext fun p => Tr.read_left τ p
theorem Orcs.snd_read {s t : Shape} (τ : Tr (s ++ t)) :
    Orcs.snd (s := s) τ.read = (Tr.snd (s := s) τ).read :=
  funext fun p => Tr.read_right τ p

theorem sndBK_online : Spec.sndBK_online := by
  intro X Xl WA WB E0 Ej F Q N aux on RA RB RB' e₁ e₂ ε₁ ε₂ hF hQ himp hRB
  obtain ⟨(bad₂ : Xl × Ej.Str → E0.Str → BadFam Q.ior.shape), c₂, J₂⟩ := hQ.exists_badFam
  -- the bad values of the first part; the statement between the parts; the bad values of the second
  -- part
  let B₁ : X → E0.Str → BadFam F.shape := fun x y =>
    lostFam F.shape ε₁ fun τ =>
      ∀ b w, F.red.out (x, y) τ = some b → RB b w → RA (x, y) (e₁ x τ.read w)
  let mid : X → E0.Str → Tr F.shape → Option (Xl × Ej.Str) := fun x y τ =>
    (F.out x y τ).map fun xl => (xl, aux τ.read)
  let g : X → E0.Str → Tr F.shape → BadFam Q.ior.shape := fun x y τ =>
    ((mid x y τ).map fun a => bad₂ a y).getD (BadFam.empty Q.ior.shape)
  refine BatchInteractiveOracleProof.sndBK_of_badFam _ N _ _ _ (fun x y => BadFam.app (B₁ x y) (g x y)) ?_ ?_
  · intro x y (τ : Tr (F.shape ++ Q.ior.shape)) hτ hacc hon
    have hτ' : (B₁ x y).Clean (Tr.fst τ) ∧ (g x y (Tr.fst τ)).Clean (Tr.snd (s := F.shape) τ) := by
      rw [← BadFam.clean_app, Tr.app_fst_snd]
      exact hτ
    have hacc' : ((F.out x y (Tr.fst τ)).bind fun x₂ =>
          Q.ior.out x₂ (F.imp y (Tr.fst τ)) (Tr.snd (s := F.shape) τ)).isSome = true := hacc
    cases hout : F.out x y (Tr.fst τ) with
    | none =>
      rw [hout] at hacc'
      cases hacc'
    | some xl =>
      rw [hout, Option.bind_some, himp] at hacc'
      have hg : g x y (Tr.fst τ) = bad₂ (xl, aux (Tr.fst τ).read) y := by
        show (((F.out x y (Tr.fst τ)).map fun xl => (xl, aux (Tr.fst τ).read)).map
            fun a => bad₂ a y).getD _ = _
        rw [hout]
        rfl
      have h0 : RB' (xl, (y, aux (Tr.fst τ).read))
          (e₂ (aux (Tr.fst τ).read) (Tr.snd (s := F.shape) τ).read) :=
        c₂ (xl, aux (Tr.fst τ).read) y (Tr.snd (s := F.shape) τ) (hg ▸ hτ'.2) hacc'
      have h1 := hRB x y (Tr.fst τ) xl _ hon hout (by rw [himp]; exact h0)
      have h2 := lostFam_clean (hF (x, y) hon) hτ'.1 (xl, F.imp y (Tr.fst τ)) _
        (by show (F.out x y (Tr.fst τ)).map _ = _; rw [hout]; rfl) h1
      show RA (x, y) (e₁ x (Orcs.fst τ.read) (e₂ (aux (Orcs.fst τ.read)) (Orcs.snd τ.read)))
      rw [Orcs.fst_read, Orcs.snd_read]
      exact h2
  · intro y x
    have key := JWithin.app N F.shape Q.ior.shape (RoundSplits.allLocal F.shape) Q.ann ε₁ ε₂
      (fun j => (x j).map fun xj => (false, B₁ xj y))
      (fun j τ => (x j).elim (BadFam.empty _) fun xj => g xj y τ)
      (jWithin_of_within N RAnn.allLocal (fun _ => rfl) F.shape ε₁ _ fun j p hp => by
        obtain ⟨xj, _, rfl⟩ := Option.map_eq_some_iff.mp hp
        exact lostFam_within _ _ _)
      (fun τ => JWithin.weaken N Q.ior.shape Q.ann ε₂ _ _ (J₂ y fun j => (x j).bind fun xj => mid xj y (τ.slot j)) fun j p hp => by
        beta_reduce at hp
        cases hx : x j with
        | none =>
          rw [hx] at hp
          cases hp
        | some xj =>
          rw [hx] at hp
          obtain rfl : _ = p := Option.some.inj hp
          cases hm : mid xj y (τ.slot j) with
          | none =>
            right
            show ((mid xj y (τ.slot j)).map fun a => bad₂ a y).getD _ = _
            rw [hm]
            rfl
          | some a =>
            refine Or.inl ⟨(false, bad₂ a y), ?_, ?_, fun h => Bool.noConfusion h⟩
            · show ((some xj).bind fun xj => mid xj y (τ.slot j)).map _ = _
              rw [Option.bind_some, hm]
              rfl
            · show ((mid xj y (τ.slot j)).map fun a => bad₂ a y).getD _ = _
              rw [hm]
              rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) key
    funext j
    beta_reduce
    cases x j <;> rfl

end Iop
