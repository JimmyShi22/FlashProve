-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/ChainTo.lean: the verifier's chain of a slot, up to a round.

This file is about the Fiat-Shamir queries of a compiled interactive oracle proof: the verifier's
recomputation of its own messages from the proof, stopped before a round j.
Definitions, a statement with its proof.
The compiled verifier recomputes the chain of an argument string (`recomputeChain`,
Compile/Batch/Verifier.lean): one Fiat-Shamir query a round (two queries in the joining round),
each, but for the first and for the joining round's second (F4), holding the tail of the Fiat-Shamir
answer before. An extractor whose witness map reads no verifier message from round j on need not
follow it further.

Main names:
  `Rho.dflt s`: some fixed verifier messages (which ones does not matter: they stand where nobody
    reads).
  `chainTo`, with an argument j: `recomputeChain`, stopped before round j (counted from where it starts):
    the same queries in the same order for the first j rounds; then no query; the verifier messages
    of the first j rounds, fixed values after them.
  `runsIn_chainTo`: where the whole chain runs within a trace to an end (result `some`), the chain
    up to round j runs within it too, and its verifier messages agree with the whole chain's before
    round j (`Rho.AgreeTo`, Ior/KnowWidePass.lean).

Limits: this file says nothing on probabilities. No converse: the chain up to j may run where the
whole chain does not.

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.Runs
import Ior.KnowWidePass
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop

/-- Some fixed verifier messages. -/
def Rho.dflt : (s : Shape) → Rho s
  | [] => ()
  | r :: s => (Classical.arbitrary r.Chal, Rho.dflt s)

end Iop

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- The chain, stopped before round j. -/
def chainTo (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ℕ → (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) →
    ℕ → Phase lam → List (Dig lam) → Plains s → TypedOracleComputation lam K L (Option (Rho s))
  | 0, s, _, _, _, _, _, _, _ => pure (some (Rho.dflt s))
  | _ + 1, [], _, _, _, _, _, _, _ => pure (some ())
  | j + 1, _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map L.early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.hasJ rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h.withLate (lateInstancePart L i x), rt,
                  embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)
              let r ← chainTo t cms x salt rtreq j s A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => (w.chal ans.1, z))
          | none => pure none
      | some (.one h false next) =>
          match takeRt w.has0 rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
              let r ← chainTo t cms x salt rtreq j s A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => (w.chal ans.1, z))
          | none => pure none
      | some (.join ρ) =>
          match takeRt w.hasJ rts with
          | some (rtj, rts1) =>
              match takeRt w.has0 rts1 with
              | some (rt0, rts') => do
                  let c ← askTypedOracle (L := L) (K := K) (OracleName.g t)
                    (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t)
                  let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                    (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                      embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
                  let r ← chainTo t cms x salt rtreq j s A W (fun z => embP (.inr z)) (i + 1)
                    (.shr (List.ofFn ans.2) c) rts' pls
                  pure (r.map fun z => (w.chal ans.1, z))
              | none => pure none
          | none => pure none
      | none => pure none

/-- Where the whole chain runs to an end, the chain up to round j runs, to the same verifier
messages before round j. -/
theorem runsIn_chainTo {tr : Trace (spec lam K L)} {t : Tag} {cms : List (Dig lam)} {x : Option X}
    {salt : Bits} {rtreq : Dig lam} :
    ∀ (j : ℕ) (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      ∃ ρ' : Rho s,
        RunsIn tr (chainTo (K := K) t cms x salt rtreq j s A ws embP i ph rts pls) (some ρ') ∧
        Rho.AgreeTo j ρ' ρ
  | 0, s, _, _, _, _, _, _, _, _, ρ, _, _ =>
    ⟨Rho.dflt s, by unfold chainTo; exact RunsIn.pure _, Rho.agreeTo_zero _ _⟩
  | _ + 1, [], _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨(), by unfold chainTo; exact RunsIn.pure _, trivial⟩
  | j + 1, _ :: s, (a, A), (w, ws), embP, i, ph, ph', rts, (pl, pls), (c, ρ), (rt, RTs), h => by
      unfold recomputeChain at h
      unfold chainTo
      cases hact : actOf cms (x.map L.early) salt a.kind ph with
      | none => simp only [hact] at h; cases runsIn_pure_iff.1 h
      | some act =>
        cases act with
        | one hd own next =>
          cases own with
          | true =>
            simp only [hact] at h ⊢
            cases hrt : takeRt w.hasJ rts with
            | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
            | some z =>
              obtain ⟨root, rts'⟩ := z
              simp only [hrt, bind_eq, pure_eq] at h ⊢
              obtain ⟨ans, ha, h2⟩ := (runsIn_bind_iff _ _ _).1 h
              obtain ⟨r', hr', h3⟩ := (runsIn_bind_iff _ _ _).1 h2
              have h4 := runsIn_pure_iff.1 h3
              cases r' with
              | none => cases h4
              | some z =>
                obtain ⟨ρ₁, RTs₁, ph₁⟩ := z
                have h5 : (((w.chal ans.1, ρ₁), ((none, some root), RTs₁), ph₁) :
                      (_ × Rho s) × ((RtC lam × RtC lam) × RootsOfChain lam s) × Phase lam) =
                    ((c, ρ), (rt, RTs), ph') :=
                  Option.some.inj h4
                simp only [Prod.mk.injEq] at h5
                obtain ⟨⟨h6, rfl⟩, ⟨-, rfl⟩, rfl⟩ := h5
                obtain ⟨ρ', hρ', hag⟩ := runsIn_chainTo j s A ws _ (i + 1) _ _ rts' pls _ _ hr'
                exact ⟨(w.chal ans.1, ρ'),
                  (runsIn_bind_iff _ _ _).2
                    ⟨ans, ha, (runsIn_bind_iff _ _ _).2 ⟨some ρ', hρ', RunsIn.pure _⟩⟩,
                  h6, hag⟩
          | false =>
            simp only [hact] at h ⊢
            cases hrt : takeRt w.has0 rts with
            | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
            | some z =>
              obtain ⟨root, rts'⟩ := z
              simp only [hrt, bind_eq, pure_eq] at h ⊢
              obtain ⟨ans, ha, h2⟩ := (runsIn_bind_iff _ _ _).1 h
              obtain ⟨r', hr', h3⟩ := (runsIn_bind_iff _ _ _).1 h2
              have h4 := runsIn_pure_iff.1 h3
              cases r' with
              | none => cases h4
              | some z =>
                obtain ⟨ρ₁, RTs₁, ph₁⟩ := z
                have h5 : (((w.chal ans.1, ρ₁), ((some root, none), RTs₁), ph₁) :
                      (_ × Rho s) × ((RtC lam × RtC lam) × RootsOfChain lam s) × Phase lam) =
                    ((c, ρ), (rt, RTs), ph') :=
                  Option.some.inj h4
                simp only [Prod.mk.injEq] at h5
                obtain ⟨⟨h6, rfl⟩, ⟨-, rfl⟩, rfl⟩ := h5
                obtain ⟨ρ', hρ', hag⟩ := runsIn_chainTo j s A ws _ (i + 1) _ _ rts' pls _ _ hr'
                exact ⟨(w.chal ans.1, ρ'),
                  (runsIn_bind_iff _ _ _).2
                    ⟨ans, ha, (runsIn_bind_iff _ _ _).2 ⟨some ρ', hρ', RunsIn.pure _⟩⟩,
                  h6, hag⟩
        | join ρ0 =>
          simp only [hact] at h ⊢
          cases hrt : takeRt w.hasJ rts with
          | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
          | some z =>
            obtain ⟨rtj, rts1⟩ := z
            simp only [hrt] at h ⊢
            cases hrt0 : takeRt w.has0 rts1 with
            | none => simp only [hrt0] at h; cases runsIn_pure_iff.1 h
            | some z =>
              obtain ⟨rt0, rts'⟩ := z
              simp only [hrt0, bind_eq, pure_eq] at h ⊢
              obtain ⟨cv, hcv, h1⟩ := (runsIn_bind_iff _ _ _).1 h
              obtain ⟨ans, ha, h2⟩ := (runsIn_bind_iff _ _ _).1 h1
              obtain ⟨r', hr', h3⟩ := (runsIn_bind_iff _ _ _).1 h2
              have h4 := runsIn_pure_iff.1 h3
              cases r' with
              | none => cases h4
              | some z =>
                obtain ⟨ρ₁, RTs₁, ph₁⟩ := z
                have h5 : (((w.chal ans.1, ρ₁), ((some rt0, some rtj), RTs₁), ph₁) :
                      (_ × Rho s) × ((RtC lam × RtC lam) × RootsOfChain lam s) × Phase lam) =
                    ((c, ρ), (rt, RTs), ph') :=
                  Option.some.inj h4
                simp only [Prod.mk.injEq] at h5
                obtain ⟨⟨h6, rfl⟩, ⟨-, rfl⟩, rfl⟩ := h5
                obtain ⟨ρ', hρ', hag⟩ := runsIn_chainTo j s A ws _ (i + 1) _ _ rts' pls _ _ hr'
                exact ⟨(w.chal ans.1, ρ'),
                  (runsIn_bind_iff _ _ _).2
                    ⟨cv, hcv,
                      (runsIn_bind_iff _ _ _).2
                        ⟨ans, ha, (runsIn_bind_iff _ _ _).2 ⟨some ρ', hρ', RunsIn.pure _⟩⟩⟩,
                  h6, hag⟩

end Compile.Batch
