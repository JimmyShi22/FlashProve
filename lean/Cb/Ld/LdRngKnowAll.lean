-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRngKnowAll.lean: under `p.OK`, round 1 of the range check (the draw), as an interactive
reduction, is knowledge sound on all statements: collision-free or not, whatever the condition of
what rides along.

In round 1 of the approximate range check (Cb/Ld/LdRng.lean) the prover sends nothing and the
verifier draws a ternary matrix. Knowledge soundness here is round-by-round, of this one reduction
(`Know`, Ior/Know.lean).

Statements and proofs. Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

A signature: the oracle messages of a statement: a finite type of names, with the data of an oracle
message for each; not a digital signature.
What a joint (`IOR.Rels`) consists of: the head of Cb/Ld/LdSend.lean.
Round-by-round knowledge soundness (`Know`), at a list of errors, asks: on every input statement of
a given set the prover has lost from the start towards this property: whenever the verifier outputs
a statement, the given extractor turns each witness of it in the output relation into a witness of
the input statement in the input relation.

Why: the bundles over a signature (`IOR.GoodT` between joints `S.over ..`) state knowledge soundness
on the statements with the joint's condition: the samples do not collide, and the condition of the
riding joint holds. This protocol's technical report (lean/CREDITS.md) states this block's knowledge
soundness on all statements. `Spec.ldRng_draw`, `Spec.ldRng2_draw` say less. The proofs use neither
condition.

Main names:
  `Spec.sigLift_knowOn`: the lifting rule (`Spec.sigLift_goodB`, its step `Spec.sigLift_know`,
    Cb/Ld/LdSigLift.lean) without "collision-free":
      knowledge soundness for each fixed tuple of messages, on the statements with any condition on₀
        of the base,
      gives knowledge soundness over the signature on the statements whose base part has on₀.
    (The decoder, `S.decs` of Cb/Ld/LdSig.lean, is a function of the statement on all statements.)
  `Spec.ldRng_knowAll`: under `p.OK` (`RngPar.OK`), knowledge soundness of round 1 of the range
    check over a signature (Cb/Ld/LdRng.lean): from the relaxed input relation to the relaxed output
    relation, with the same extractor and the same error as `Spec.ldRng_draw`, on all statements.
  `Spec.ldRng2_knowAll`: the same for a number of digits of one width (`RngPar2`, Cb/Ld/LdRng2.lean;
    there `p.OK` is `RngPar2.OK`).

Limits: what the heads of Cb/Ld/LdRng.lean and Cb/Ld/LdRng2.lean list as not said is not said here
either. The sending that follows the draw has its lists and its condition (`Spec.ldRng_goodT`,
Cb/Ld/LdRng.lean). This file says nothing on other blocks.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRng2Proofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk IOR

namespace Spec

/-- The lifting rule without "collision-free". -/
def sigLift_knowOn : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (Kc St St' Wp Wp' : Type) (E₀ E₀' : ExtSpec)
      (R : IOR St E₀ St' E₀') (A : Rels Kc St E₀ (S.Msg × Wp))
      (B : Rels Kc St' E₀' (S.Msg × Wp')) (on₀ : St × E₀.Str → Prop)
      (ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp) (ε : Err R.shape),
    (∀ m, R.red.Know on₀ (fun a wp => A.relR a (m, wp)) (fun b wp => B.relR b (m, wp)) (ext m) ε) →
    (R.keep S.Smp S.ext).red.Know (fun a => on₀ (a.1.1, a.2.1)) (S.over A).relR (S.over B).relR
      (fun a τ w => (w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)) ε

/-- Round 1 of the range check, on all statements. -/
def ldRng_knowAll : Prop :=
  ∀ (E St Kc Wp : Type) [Field E] (E₀ : ExtSpec) (p : RngPar) (S : Sig E)
      (r : RngRd p E St S.Msg Kc) (A₀ : Rels Kc St E₀ (S.Msg × Wp)),
    p.OK → (ldRngDraw p S St E₀).red.Know (fun _ => True) (S.over (rngIn p r A₀)).relR
      (S.over (rngOut p r A₀)).relR (fun _ _ w => (w.1, w.2.1)) (ldRngDrawN (E₀ := E₀) p S r).err

def ldRng2_knowAll : Prop :=
  ∀ (E St Kc Wp : Type) [Field E] (E₀ : ExtSpec) (p : RngPar2) (S : Sig E)
      (r : RngRd p.one E St S.Msg Kc) (A₀ : Rels Kc St E₀ (S.Msg × Wp)),
    p.OK → (ldRngDraw p.one S St E₀).red.Know (fun _ => True)
      (S.over (rngIn p.one r A₀)).relR (S.over (rngOut2 p r A₀)).relR
      (fun _ _ w => (w.1, w.2.1)) (ldRngDrawN (E₀ := E₀) p.one S r).err

end Spec

theorem sigLift_knowOn : Spec.sigLift_knowOn := by
  intro E _ S Kc St St' Wp Wp' E₀ E₀' R A B on₀ ext ε h a ha
  by_cases hdec : ∃ m : S.Msg, ∀ i, S.decs a.1.2 a.2.2 i = some (m i)
  · obtain ⟨m, hm⟩ := hdec
    refine Doomed.mono _ _ ?_ (h m (a.1.1, a.2.1) ha)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2, h3⟩ := keep_red_out R S.Smp S.ext a τ b hb
    have hw1 : ∀ i, S.decs a.1.2 a.2.2 i = some (w.1 i).1 := by
      rw [← h1, ← h2]
      exact hw.1
    have hmw : S.msgs w.1 = m := funext fun i => Option.some.inj ((hw1 i).symm.trans (hm i))
    have hw2 : B.relR (b.1.1, b.2.1) (S.msgs w.1, w.2) := hw.2
    refine ⟨hw1, ?_⟩
    show A.relR (a.1.1, a.2.1) (S.msgs w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)
    rw [hmw] at hw2 ⊢
    exact hτ (b.1.1, b.2.1) w.2 h3 hw2
  · refine Doomed.of_forall _ _ fun τ b w hb hw => ?_
    obtain ⟨h1, h2, _⟩ := keep_red_out R S.Smp S.ext a τ b hb
    refine absurd ⟨S.msgs w.1, ?_⟩ hdec
    rw [← h1, ← h2]
    exact hw.1

theorem ldRng_knowAll : Spec.ldRng_knowAll := by
  intro E St Kc Wp _ E₀ p S r A₀ h
  exact sigLift_knowOn E S Kc St (St × p.Chal) Wp (Wp × p.Dg E) E₀ E₀ (rngDraw p St E₀)
    (rngIn p r A₀) (rngOut p r A₀) (fun _ => True) (fun _ _ _ w => w.1)
    (rngDrawN (E₀ := E₀) p r).err
    (ldRng_at E St S.Msg Kc Wp E₀ p r ⟨A₀.rel, A₀.relR, fun _ => True, A₀.core⟩ h).know

theorem ldRng2_knowAll : Spec.ldRng2_knowAll := by
  intro E St Kc Wp _ E₀ p S r A₀ h
  exact sigLift_knowOn E S Kc St (St × p.one.Chal) Wp (Wp × p.Dg E) E₀ E₀ (rngDraw p.one St E₀)
    (rngIn p.one r A₀) (rngOut2 p r A₀) (fun _ => True) (fun _ _ _ w => w.1)
    (rngDrawN (E₀ := E₀) p.one r).err
    (ldRng2_at E St S.Msg Kc Wp E₀ p r ⟨A₀.rel, A₀.relR, fun _ => True, A₀.core⟩ h).know

end Cb
