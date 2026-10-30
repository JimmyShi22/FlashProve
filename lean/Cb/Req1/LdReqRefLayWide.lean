-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefLayWide.lean: where the masks come from, in wide facts: `L.Lay` from places,
readings and five kinds of wide facts that are laid and enter (`L.LayW`). (not all hypotheses are
named here: see `L.LayW`)

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs: an assembly.
L is a list (`LdRefL`) of reference segments S (`LdRefS`), each with a body `S.A` (an
`LdRefD E Kc I`, Cb/Req1/LdSegRefAll.lean) and an entry step `S.entry`; T (`LdRefT`) is the last
segment (Cb/Req1/LdReqRef.lean). A fact is a `MaskFact` (Cb/Req1/LdSegFresh.lean), a wide fact a
`LdStage.wideFact` (Cb/Req1/LdSegCarry.lean). `L.Laid`, `S.Enters` and `L.Lay` are in
Cb/Req1/LdReqRefLay.lean.
Cb/Req1/LdReqRefLay.lean asks, for each segment, what zero knowledge asks of its body (`A.ZkAt`,
Cb/Req1/LdReqRefZkP.lean), beside its hypotheses, at the facts that its entry step hands on from
facts laid before it.
Cb/Req1/LdSegRefAllZkWide.lean states `A.ZkAt pp X` (`Spec.ldSegRefAll_zkAtW`, with its other
hypotheses; the proof is in Cb/Req1/LdSegRefAllZkWideProofs.lean) from: X is closed under "follows
after every chain"; places; nested readings; and five kinds of wide facts in X (the own masks of:
the front's lookup, the zerocheck's sumcheck, each further sumcheck, the digits' lookup, the
batching of the tensor rows).

Main names:
  `Spec.ldReqRefLayW_closed`: the set of facts that an entry step hands on from facts laid is closed
    (`LdStage.Closed`).
  `A.ZkW pp X`: there are parameters (the wide reading `W : LdRefW A`, the front's parameters
    `F : LdRefF A` and places `P : LdRefP A F`, how the core reads the ghost (`κ`), what the digits'
    lookup reads) with the premises of `Spec.ldSegRefAll_zkAtW` but "closed".
  `Spec.ldReqRefLayW_zk`: see its statement.
  `L.LayW pp base`: for each segment S of L: `S.A.ZkW pp` at the facts that `S.Enters` hands on from
    facts laid before S.
  `Spec.ldReqRefLayW_segs`: `L.LayW pp base → L.Lay pp base`.
  `Spec.ldReqRefLayW_tail`: the same for the last segment.

So, beside `Nonempty I.C.E0.Str`, `A.Ghost κ` and `F.OK pp`, `L.Lay pp base` follows from: places
and readings; the two senders of each body do not look; and, for each of the five kinds of blocks of
each segment: a wide fact laid before the segment that enters it.
Rules that lay wide facts down are in Cb/Req1/LdReqStdLayVis.lean (after the first sending),
Cb/Req1/LdReqStdLay.lean and Cb/Ld/LdGroupNewRideFresh.lean (by a closing's one sending) and
Cb/Req1/LdSegRefPackSLay.lean (across a closing).

Limits: No theorem of this library states that the hypotheses of `ldReqRefLayW_segs` can be met
together.
-/
import Cb.Req1.LdReqRefLayProofs
import Cb.Req1.LdSegRefAllZkWideProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- What zero knowledge asks of a closed body, beside its hypotheses, in wide facts. -/
def LdRefD.ZkW {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)
    (pp : ℕ) (X : MaskFact A.V.Fp.s0.J.W → Prop) : Prop :=
  Nonempty I.C.E0.Str ∧
  ∃ (W : LdRefW A) (F : LdRefF A) (P : LdRefP A F) (κ : A.Gh → Kc) (RdL : A.Xa.Q.T.Ent → Prop),
    A.Ghost κ ∧ F.OK pp ∧ P.OKL W ∧ P.OK0 W ∧ (∀ i ≤ A.V.m, P.OKS W i) ∧
    F.Nest ∧ P.In W X ∧ A.LateW W F RdL X

def LdRefL.LayW {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}
    (pp : ℕ) (base : MaskFact a.J.W → Prop) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.LayW pp base ∧ S.A.ZkW pp fun f => ∃ g, L.Laid base g ∧ S.Enters g f

namespace Spec

def ldReqRefLayW_closed : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc)
      (en : LdMv a b) (B : MaskFact a.J.W → Prop),
    b.Closed fun f => ∃ g, B g ∧ ∀ Y : MaskFact a.J.W → Prop, Y g → en.After Y f

def ldReqRefLayW_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I)
      (pp : ℕ) (X : MaskFact A.V.Fp.s0.J.W → Prop),
    A.V.Fp.s0.Closed X → A.ZkW pp X → A.ZkAt pp X

def ldReqRefLayW_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b)
      (pp : ℕ) (base : MaskFact a.J.W → Prop),
    L.LayW pp base → L.Lay pp base

def ldReqRefLayW_tail : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (b : LdStage E Kc) (T : LdRefT R b) (pp : ℕ) (B : MaskFact b.J.W → Prop),
    T.A.ZkW pp (fun f => ∃ g, B g ∧ ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f) →
    T.A.ZkAt pp (fun f => ∃ g, B g ∧ ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f)

end Spec

theorem ldReqRefLayW_closed : Spec.ldReqRefLayW_closed := fun _ _ _ _ _ _ en _ _ _ h ⟨g, hg, hY⟩ =>
  ⟨g, hg, fun Y y => h _ en.chain Y (hY Y y)⟩

theorem ldReqRefLayW_zk : Spec.ldReqRefLayW_zk := by
  intro E Kc _ _ I A pp X hC ⟨hne, W, F, P, κ, RdL, h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ldSegRefAll_zkAtW E Kc pp I A W F P κ RdL X hC h1 h2 h3 h4 h5 h6 h7 h8

theorem ldReqRefLayW_segs : Spec.ldReqRefLayW_segs := by
  intro E Kc _ _ I a b L pp base
  induction L with
  | nil => intro _; simp only [LdRefL.Lay]
  | snoc L S ih =>
      intro h
      rw [LdRefL.LayW] at h
      rw [LdRefL.Lay]
      exact ⟨ih h.1,
        ldReqRefLayW_zk E Kc I S.A pp _ (ldReqRefLayW_closed E Kc _ _ S.entry (L.Laid base)) h.2⟩

theorem ldReqRefLayW_tail : Spec.ldReqRefLayW_tail := fun _ E Kc _ _ _ _ _ _ _ T pp B h =>
  ldReqRefLayW_zk E Kc _ T.A pp _ (ldReqRefLayW_closed E Kc _ _ T.entry B) h

end Cb
