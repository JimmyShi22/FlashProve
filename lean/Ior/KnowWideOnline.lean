-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowWideOnline.lean: knowledge soundness of "an IOR in every slot, then a batch IOP", with
extractors that may read the whole statement and the whole transcript.

A definition, statements and proofs. The wide form of `Spec.sndBK_online` (Ior/Batch.lean; proof:
Ior/OnlineK.lean).
A batch IOP (`BatchInteractiveOracleProof`, Iop/Batch.lean) is one IOP, for the local transcript of a slot, with an
annotation of its shape (`RoundSplits`): which verifier messages the slots share, and how each prover
message splits into a shared part and a slot's part. A slot is one of the N places of a batch, each
with one instance or empty, with its own local transcript.

F is an IOR that is run in every slot (local rounds, only the slot speaks); Q a batch IOP on the
implicit instances (shared oracle, the slot's own oracles) that F leaves. `Spec.sndBK_online` asks
that of the transcript both extractors read the oracles only, and that the oracles which F leaves
are a function of the oracles sent. Here:
  e₁ is F's extractor: the slot's statement, F's transcript in the slot, a witness of the middle
    statement.
  e₂ is Q's witness map (Ior/KnowWide.lean: `SndBKT` of `Q.curry`): the middle statement of the slot
    (explicit part, own oracles), the shared oracle, the slot's local transcript of Q.
  No premise of its own is asked of the own oracles that F leaves (no `aux`, which
    `Spec.sndBK_online` asks): they may depend on verifier messages (a fold's virtual oracle).
    Asked: F copies the shared oracle: (F.imp y τ).1 = y.

Main names:
  `witSeqT F e₁ e₂ d`: the composed witness map; where F's verifier rejects: d (then the composed
    verifier rejects, and the value is never read).
  `Spec.sndBKT_online`: under the hypotheses of its statement, the composition has `SndBKT`, at
    early = id, late = none, for the relation "on → RA", with `witSeqT`; the errors are
    concatenated.
  `Spec.sndBKT_online_ext`: the general form; see its docstring.

Limits: this file says nothing on the honest side, on queries, on running times.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowWide
import Ior.OnlineK

set_option autoImplicit false

namespace Iop
open Prob

/-- The composed witness map. -/
def witSeqT {X Xl WA WB : Type} {E0 Ej : ExtSpec} (F : IOR X E0 Xl (E0.prod Ej)) {t : Shape}
    (e₁ : X × E0.Str → Tr F.shape → WB → WA) (e₂ : Xl × Ej.Str → E0.Str → Tr t → WB) (d : WA) :
    X → E0.Str → Tr (F.shape ++ t) → WA := fun x y τ =>
  match F.out x y (Tr.fst τ) with
  | some xl => e₁ (x, y) (Tr.fst τ) (e₂ (xl, (F.imp y (Tr.fst τ)).2) y (Tr.snd (s := F.shape) τ))
  | none => d

namespace Spec

/-- The general form: any witness map that agrees with "the second's, then the first's" wherever F's
verifier outputs a statement. (not all hypotheses are named here: see the statement below) -/
def sndBKT_online_ext : Prop :=
  ∀ (X Xl WA WB : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej)) (Q : BIOP Xl (E0.prod Ej))
      (N : ℕ) (on : X × E0.Str → Prop) (RA : X × E0.Str → WA → Prop)
      (RB RB' : Xl × (E0.prod Ej).Str → WB → Prop) (e₁ : X × E0.Str → Tr F.shape → WB → WA)
      (e₂ : Xl × Ej.Str → E0.Str → Tr Q.ior.shape → WB)
      (wit : X → E0.Str → Tr (F.shape ++ Q.ior.shape) → WA) (ε₁ : Err F.shape)
      (ε₂ : Err Q.ior.shape),
    F.red.Know on RA RB e₁ ε₁ →
    Q.curry.SndBKT N id none (fun a y0 w => RB' (a.1, (y0, a.2)) w) e₂ ε₂ →
    (∀ y τ, (F.imp y τ).1 = y) →
    (∀ x y τ xl w,
      on (x, y) → F.out x y τ = some xl → RB' (xl, F.imp y τ) w → RB (xl, F.imp y τ) w) →
    (∀ x y (τ : Tr (F.shape ++ Q.ior.shape)) xl, F.out x y (Tr.fst τ) = some xl →
      wit x y τ =
        e₁ (x, y) (Tr.fst τ) (e₂ (xl, (F.imp y (Tr.fst τ)).2) y (Tr.snd (s := F.shape) τ))) →
    (online F Q).toBatch.SndBKT N id none (fun x y w => on (x, y) → RA (x, y) w) wit (Err.app ε₁ ε₂)

/-- Knowledge soundness of "an IOR in every slot, then a batch IOP", wide extractors. -/
def sndBKT_online : Prop :=
  ∀ (X Xl WA WB : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej)) (Q : BIOP Xl (E0.prod Ej))
      (N : ℕ) (on : X × E0.Str → Prop) (RA : X × E0.Str → WA → Prop)
      (RB RB' : Xl × (E0.prod Ej).Str → WB → Prop) (e₁ : X × E0.Str → Tr F.shape → WB → WA)
      (e₂ : Xl × Ej.Str → E0.Str → Tr Q.ior.shape → WB) (d : WA) (ε₁ : Err F.shape)
      (ε₂ : Err Q.ior.shape),
    F.red.Know on RA RB e₁ ε₁ →
    Q.curry.SndBKT N id none (fun a y0 w => RB' (a.1, (y0, a.2)) w) e₂ ε₂ →
    (∀ y τ, (F.imp y τ).1 = y) →
    (∀ x y τ xl w,
      on (x, y) → F.out x y τ = some xl → RB' (xl, F.imp y τ) w → RB (xl, F.imp y τ) w) →
    (online F Q).toBatch.SndBKT
      N id none (fun x y w => on (x, y) → RA (x, y) w) (witSeqT F e₁ e₂ d) (Err.app ε₁ ε₂)

end Spec

theorem sndBKT_online_ext : Spec.sndBKT_online_ext := by
  intro X Xl WA WB E0 Ej F Q N on RA RB RB' e₁ e₂ wit ε₁ ε₂ hF hQ himp hRB hwit
  obtain ⟨(bad₂ : Xl × Ej.Str → E0.Str → BadFam Q.ior.shape), c₂, J₂⟩ :=
    (sndBP_iff_badFam _ _ Q.curry N _ ε₂).1 hQ
  have himp' : ∀ y τ, F.imp y τ = (y, (F.imp y τ).2) := fun y τ => Prod.ext (himp y τ) rfl
  -- the bad values of the first part; the statement between the parts; the bad values of the second
  -- part
  let B₁ : X → E0.Str → BadFam F.shape := fun x y =>
    lostFam F.shape ε₁ fun τ =>
      ∀ b w, F.red.out (x, y) τ = some b → RB b w → RA (x, y) (e₁ (x, y) τ w)
  let mid : X → E0.Str → Tr F.shape → Option (Xl × Ej.Str) := fun x y τ =>
    (F.out x y τ).map fun xl => (xl, (F.imp y τ).2)
  let g : X → E0.Str → Tr F.shape → BadFam Q.ior.shape := fun x y τ =>
    ((mid x y τ).map fun a => bad₂ a y).getD (BadFam.empty Q.ior.shape)
  refine (sndBP_iff_badFam _ _ (online F Q).toBatch N _ (Err.app ε₁ ε₂)).2
    ⟨fun x y => BadFam.app (B₁ x y) (g x y), ?_, ?_⟩
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
      rw [hout, Option.bind_some, himp'] at hacc'
      have hg : g x y (Tr.fst τ) = bad₂ (xl, (F.imp y (Tr.fst τ)).2) y := by
        show (((F.out x y (Tr.fst τ)).map fun xl => (xl, (F.imp y (Tr.fst τ)).2)).map
            fun a => bad₂ a y).getD _ = _
        rw [hout]
        rfl
      have h0 : RB' (xl, (y, (F.imp y (Tr.fst τ)).2))
          (e₂ (xl, (F.imp y (Tr.fst τ)).2) y (Tr.snd (s := F.shape) τ)) :=
        c₂ (xl, (F.imp y (Tr.fst τ)).2) y (Tr.snd (s := F.shape) τ) (hg ▸ hτ'.2) hacc'
      have h1 := hRB x y (Tr.fst τ) xl _ hon hout (by rw [himp']; exact h0)
      have h2 := lostFam_clean (hF (x, y) hon) hτ'.1 (xl, F.imp y (Tr.fst τ)) _
        (by show (F.out x y (Tr.fst τ)).map _ = _; rw [hout]; rfl) h1
      show RA (x, y) (wit x y τ)
      rw [hwit x y τ xl hout]
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

theorem sndBKT_online : Spec.sndBKT_online := by
  intro X Xl WA WB E0 Ej F Q N on RA RB RB' e₁ e₂ d ε₁ ε₂ hF hQ himp hRB
  refine sndBKT_online_ext X Xl WA WB E0 Ej F Q N on RA RB RB' e₁ e₂
    (witSeqT F e₁ e₂ d) ε₁ ε₂ hF hQ himp hRB ?_
  intro x y τ xl hout
  simp only [witSeqT, hout]

/-- `Spec.sndBK_online`, proved again as an instance of `sndBKT_online_ext`. -/
theorem sndBK_online_of_T : Spec.sndBK_online := by
  intro X Xl WA WB E0 Ej F Q N aux on RA RB RB' e₁ e₂ ε₁ ε₂ hF hQ himp hRB
  refine sndBKT_online_ext X Xl WA WB E0 Ej F Q N on RA RB RB' (fun a τ w => e₁ a.1 τ.read w)
    (fun a _ τ => e₂ a.2 τ.read) (fun x _ τ => witSeq aux e₁ e₂ x τ.read) ε₁ ε₂ hF hQ
    (fun y τ => by rw [himp]) hRB ?_
  intro x y τ xl _
  show e₁ x (Orcs.fst τ.read) (e₂ (aux (Orcs.fst τ.read)) (Orcs.snd τ.read)) =
    e₁ x (Tr.fst τ).read (e₂ (F.imp y (Tr.fst τ)).2 (Tr.snd (s := F.shape) τ).read)
  rw [Orcs.fst_read, Orcs.snd_read, himp]

end Iop
