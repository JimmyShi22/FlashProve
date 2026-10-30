-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefLast.lean: the end of a reference request with one pending row, from the last body's
data: the final batching's data and the last segment are functions of the body (and of R₀, Z', n',
wAt', Rd' and the entry step); the exit step is the identity.

Definitions, statements (in `Cb.Spec`) and proofs. An assembly; nothing of a text is rendered here
beyond what its parts render.
Cb/Obj/LdObjectReqEnd.lean takes the end of a request (`LdORE` R: the oracle messages that are left,
the rows that stay open, the pending tensor rows, the test's side) as data; Cb/Req1/LdReqRef.lean
takes the last segment (`LdRefT R b`: a closed body A over R's encoded index; what its batching
leaves; an entry and an exit step) as data. For a request whose only pending row is the last body's
(no segment with a closing before it), all of this but the configuration, the matrix of the index,
the test's side, the final batching's own Z', n', wAt', Rd' and the entry step is determined by the
body (Cb/Req1/LdSegRefPendEnds.lean).

Main names:
  `R₀.ofBody A Z' n' wAt' Rd' : LdORE`: R₀ gives the configuration, the matrix of the index and the
    test's side; oracle messages, rows that stay open: those of the body A; state: the last claim z
    of the body's batching; one pending row, read off z; ghost (`LdORE.G`): `A.W₁ × A.Gh`; core: the
    body's; Z', n', wAt', Rd': the final batching's own evader, degree, places of own masks,
    reading.
  `Spec.ldSegRefLast_ix`, `Spec.ldSegRefLast_X`: its encoded index is R₀'s; its batching's data are
    `A.X.after ..`: both by definition.
  `LdRefT.ofBody .. f g m back : LdRefT (R₀.ofBody ..) b`: the last segment: A; St₁, fz, Az of
    Cb/Req1/LdSegRefPendEnds.lean; the entry step (four maps: a parameter); the exit step: the
    identity.
  `Spec.ldSegRefLast_ends`: what the body's batching leaves goes over: from 1 ≤ A.nt (the degree of
    the body's batching) and: nothing else is claimed in the relaxed world at the last segment
    (where the condition of A0t holds, its relaxed relation holds).
  `Spec.ldSegRefLast_exit`: the exit step's hypothesis: none is left.
  `Spec.ldSegRefLast_model`: `T.Model` from the entry step's hypothesis, `A.Model`, and the two
    premises of `Spec.ldSegRefLast_ends`.
  `Spec.ldSegRefLast_own`: the final batching's conditions on places, from the six premises of
    `Spec.ldSegRef_pe_own` (Cb/Req1/LdSegRefPendEnds.lean).
  `Spec.ldSegRefLast_exitFmt`: the exit step has the format.
  `Spec.ldSegRefLast_exitAfter`: the exit step hands every fact on as it is.

Limits: the condition "nothing else is claimed in the relaxed world" (∀ a w, A.A0t.on a →
A.A0t.relR a w; a premise of `Spec.ldSegRefLast_ends` and `Spec.ldSegRefLast_model`) is meant. The
end of a request claims nothing beside rows and tensor rows (there "what else is claimed" is
"true"), so what the last body carries beside these has to be empty in the relaxed world. It is the
degenerate case of one segment.
This file says nothing on requests with segments before the last one (several pending rows).

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqModel
import Cb.Req1.LdSegRefPendEnds
import Cb.Req1.LdSegRefLkpPreProofs
import Cb.Req1.LdSegCarry
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood Cb.RngPk IOR IOR.Chain

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The end of the request, from the last body's data. -/
@[reducible] def LdORE.ofBody (R₀ : LdORE F E Kc) (A : LdRefD E Kc R₀.ix)
    (Z' : Evader E Unit) (n' : ℕ) (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent)
    (Rd' : A.Xa.Q.T.Ent → Prop) : LdORE F E Kc :=
  { R₀ with
    S := A.Xa.Q.T, Bn := A.Gr.B, Sb := fun _ => A.Gr.Sx, sl := A.Gr.sl, St := A.X.bt.par.Mid,
    rc := fun z => A.rc (A.X.stOf z).2, Q := Unit, finQ := inferInstance, g := fun z _ => A.X.pG z,
    pt := fun z _ => A.X.pPt z, Nm := A.X.PN, finNm := inferInstance, mf := fun z _ => A.X.pMf z,
    μAt := A.X.pAt, Z := Z', n := n', wAt := wAt', Rd := Rd', G := A.W₁ × A.Gh, core := A.A0t.core }

/-- what else is claimed beside the final batching's rows: nothing -/
@[reducible] def LdRefD.none' {I : LdRefIx E} (A : LdRefD E Kc I) :
    Rels Kc A.X.bt.par.Mid I.C.E0 ((I.C.Msg × A.Xa.Q.T.Msg) × (A.W₁ × A.Gh)) :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, A.A0t.core⟩

/-- The last segment, from the body's data and an entry step. The exit step is the identity. -/
@[reducible] def LdRefT.ofBody (R₀ : LdORE F E Kc) (A : LdRefD E Kc R₀.ix)
    (Z' : Evader E Unit) (n' : ℕ) (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent)
    (Rd' : A.Xa.Q.T.Ent → Prop) (b : LdStage E Kc) (f : b.X → Option A.V.Fp.s0.X)
    (g : ExtMap b.Ex A.V.Fp.s0.Ex) (m : b.X × b.W → A.V.Fp.s0.X × A.V.Fp.s0.W)
    (back : b.X × b.Ex.Str → A.V.Fp.s0.W → b.W) :
    LdRefT (R₀.ofBody A Z' n' wAt' Rd') b :=
  { A := A, St₁ := (Unit → E) × A.X.bt.par.Mid, fz := A.X.fzA, Az := A.X.AzA Z' n' wAt' A.none' Rd',
    f := f, g := g, m := m, back := back, f' := sideF A.Xa.Q.T id,
    g' := sideG A.Xa.Q.T (ExtMap.id R₀.Cf.conf.E0), m' := sideM A.Xa.Q.T id fun _ w => w.2,
    back' := sideB A.Xa.Q.T fun _ w => w.2 }

end

namespace Spec

def ldSegRefLast_ends : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R₀ : LdORE F E Kc)
      (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop),
    1 ≤ A.nt → (∀ a w, A.A0t.on a → A.A0t.relR a w) →
    A.X.Ends ((Unit → E) × A.X.bt.par.Mid) A.X.fzA (A.X.AzA Z' n' wAt' A.none' Rd')

def ldSegRefLast_exit : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R₀ : LdORE F E Kc)
      (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop)
      (b : LdStage E Kc) (f : b.X → Option A.V.Fp.s0.X) (g : ExtMap b.Ex A.V.Fp.s0.Ex)
      (m : b.X × b.W → A.V.Fp.s0.X × A.V.Fp.s0.W) (back : b.X × b.Ex.Str → A.V.Fp.s0.W → b.W),
    (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back).exit.Hyp

/-- The model's side of the last segment. -/
def ldSegRefLast_model : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R₀ : LdORE F E Kc)
      (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop)
      (b : LdStage E Kc) (f : b.X → Option A.V.Fp.s0.X) (g : ExtMap b.Ex A.V.Fp.s0.Ex)
      (m : b.X × b.W → A.V.Fp.s0.X × A.V.Fp.s0.W) (back : b.X × b.Ex.Str → A.V.Fp.s0.W → b.W),
    (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back).entry.Hyp → A.Model → 1 ≤ A.nt →
    (∀ a w, A.A0t.on a → A.A0t.relR a w) → (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back).Model

def ldSegRefLast_own : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R₀ : LdORE F E Kc)
      (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop),
    Function.Injective wAt' → (∀ i, Rd' (wAt' i)) → (∀ i, Rd' (A.wAt i)) → (∀ a, Rd' (A.μAt a)) →
    (∀ i j, wAt' i ≠ A.wAt j) → (∀ i a, wAt' i ≠ A.μAt a) → (R₀.ofBody A Z' n' wAt' Rd').X.Own

def ldSegRefLast_exitFmt : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R₀ : LdORE F E Kc)
      (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop)
      (b : LdStage E Kc) (f : b.X → Option A.V.Fp.s0.X) (g : ExtMap b.Ex A.V.Fp.s0.Ex)
      (m : b.X × b.W → A.V.Fp.s0.X × A.V.Fp.s0.W) (back : b.X × b.Ex.Str → A.V.Fp.s0.W → b.W)
      (E0 : ExtSpec) (Rc Pw : Type) (i : IxAt E0 R₀.Cf.conf.E0)
      (rc : A.X.Xr × ((Unit → E) × A.X.bt.par.Mid) → Rc) (px : R₀.Cf.conf.PIdx × (A.W₁ × A.Gh) → Pw)
      (q : Finset (R₀.Cf.conf.E0.prod A.Xa.Q.T.ext).Pos → Prop),
    (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back).exit.Fmt
      ((A.X.tgt ((Unit → E) × A.X.bt.par.Mid) (A.X.AzA Z' n' wAt' A.none' Rd')).fmt i rc px q)
      ((R₀.ofBody A Z' n' wAt' Rd').X.src.fmt i rc px q)

def ldSegRefLast_exitAfter : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R₀ : LdORE F E Kc)
      (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop)
      (b : LdStage E Kc) (f : b.X → Option A.V.Fp.s0.X) (g : ExtMap b.Ex A.V.Fp.s0.Ex)
      (m : b.X × b.W → A.V.Fp.s0.X × A.V.Fp.s0.W) (back : b.X × b.Ex.Str → A.V.Fp.s0.W → b.W)
      (Y : MaskFact (A.X.tgt ((Unit → E) × A.X.bt.par.Mid) (A.X.AzA Z' n' wAt' A.none' Rd')).J.W →
        Prop)
      (φ : MaskFact (A.X.tgt ((Unit → E) × A.X.bt.par.Mid) (A.X.AzA Z' n' wAt' A.none' Rd')).J.W),
    Y φ → (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back).exit.After Y φ

def ldSegRefLast_ix : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R₀ : LdORE F E Kc)
      (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop),
    (R₀.ofBody A Z' n' wAt' Rd').ix = R₀.ix

def ldSegRefLast_X : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R₀ : LdORE F E Kc)
      (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop),
    (R₀.ofBody A Z' n' wAt' Rd').X = A.X.after Z' n' wAt' A.none' Rd'

end Spec

theorem ldSegRefLast_ix : Spec.ldSegRefLast_ix := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
theorem ldSegRefLast_X : Spec.ldSegRefLast_X := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem ldSegRefLast_ends :
    Spec.ldSegRefLast_ends := fun _ E Kc _ _ _ _ _ _ A Z' n' wAt' Rd' hn hN =>
  ldSegRef_pe_ends E Kc A.X Z' n' wAt' A.none' Rd' hn
    ⟨fun _ _ _ _ => trivial, fun _ _ _ ho _ => hN _ _ ho, fun _ _ _ => trivial, fun _ => rfl⟩

theorem ldSegRefLast_exit :
    Spec.ldSegRefLast_exit := fun _ E _ _ _ _ _ _ R₀ A Z' n' wAt' Rd' _ _ _ _ _ =>
  (⟨fun _ _ _ h => h, fun _ _ h => h, fun _ => rfl, fun _ _ _ _ h => h⟩ : LdStepOK A.Xa.Q.T
    (A.X.tgt ((Unit → E) × A.X.bt.par.Mid) (A.X.AzA Z' n' wAt' A.none' Rd')).A
    (R₀.ofBody A Z' n' wAt' Rd').X.src.A id).hyp

theorem ldSegRefLast_model :
    Spec.ldSegRefLast_model := fun F E Kc _ _ _ _ _ R₀ A Z' n' wAt' Rd' b f g m back he hA hn hN =>
  ⟨he, hA,
    ldSegRefLast_ends F E Kc R₀ A Z' n' wAt' Rd' hn hN,
    ldSegRefLast_exit F E Kc R₀ A Z' n' wAt' Rd' b f g m back⟩

theorem ldSegRefLast_own :
    Spec.ldSegRefLast_own := fun _ E Kc _ _ _ _ _ _ A Z' n' wAt' Rd' h1 h2 h3 h4 h5 h6 =>
  ldSegRef_pe_own E Kc A.X Z' n' wAt' A.none' Rd' h1 h2 h3 h4 h5 h6

theorem ldSegRefLast_exitFmt :
    Spec.ldSegRefLast_exitFmt := fun _ E _ _ _ _ _ _ R₀ A Z' n' wAt' Rd' _ _ _ _ _ _ _ _ i rc px q =>
  ldStepF_fmt A.Xa.Q.T (A.X.tgt ((Unit → E) × A.X.bt.par.Mid) (A.X.AzA Z' n' wAt' A.none' Rd')).A
    (R₀.ofBody A Z' n' wAt' Rd').X.src.A id i rc rc px q fun _ => rfl

theorem ldSegRefLast_exitAfter :
    Spec.ldSegRefLast_exitAfter := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y φ hY =>
  segCarry_step _ _ _ _ _ _ Y φ _ φ.kc φ.put hY fun _ _ _ _ h => ⟨rfl, h⟩

end Cb
