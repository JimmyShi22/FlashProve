-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAllZkWide.lean: what zero knowledge asks of a closed body, beside its hypotheses
(`A.OK pp`), from wide facts alone: for each of its masked blocks the wide fact of its own masks is
fresh at the entry; under the hypotheses of its statement (`Spec.ldSegRefAll_zkAtW`), all else is
places, readings, and of the two senders that they do not look.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefAllZkWideProofs.lean.
Framework and wiring; nothing of a text is rendered here beyond what Cb/Req1/LdSegRefAllZk.lean
renders.

Why: Cb/Req1/LdSegRefAllZk.lean asks, at the entry of a body: the facts of the front's blocks in
the blocks' own letters (narrow readings), "quiet" for the blocks that run before; the wide facts
of the two late blocks, quiet for the front. What a sending lays down, and what crosses a closing,
are wide facts. Here, under the hypotheses of the statements below, everything is derived from wide
facts.

Main names (Mk is finite and not empty in the statements):
  `a.Follows f f'`: after any chain that ends at the stage a: if f is fresh, so is f'.
  `a.Closed X`: a set X of facts at a is closed under "follows". (The facts that are fresh after a
    chain are such a set; so is every set "handed on by a step from a fact that was laid".)
  `plOwn at'`, `plVal at' ve`: own entries and values from places: the entries at' i; the value
    ve M i at at' i, if at' is injective.
  `LdRefP A F`: the places, among the entries of the messages at the entry, of the own masks of the
    front's blocks: atL (the lookup's), at0 (the zerocheck's sumcheck's), atS i (the further
    sumchecks').
  `P.OKL`, `P.OK0`, `P.OKS i`: for each block: different places; the block reads its own masks
    there, as they are; at its other names its reading is a function of the entries of the wide
    reading that are not own; the places lie in the wide reading.
  `F.Nest`: nested readings: what an earlier block of the front reads is a function of what each
    later block reads at names that are none of its own masks.
  `W.Blind F own`: a wide fact's side of "quiet": what each block of the front reads is the same at
    messages that agree on the entries of the wide reading that are not own.
  `Spec.ldSegRefW_fresh`: the facts that are fresh after a chain are closed.
  `Spec.ldSegRefW_quietP`: a sumcheck's narrow fact is quiet for a reading that is a function of
    what the sumcheck reads at names that are none of its own masks.
  `Spec.ldSegRefW_quietW`: a wide fact is quiet for a reading that is a function of the entries of
    the wide reading that are not own.
  `Spec.ldSegRefW_front`: A.FrontFacts F X from: X closed; F.OK pp; the places; nested readings;
    the wide facts of the front's blocks in X.
  `Spec.ldSegRefW_pass`: W.Pass F X own Mk val from: the wide fact in X; W.Blind F own; the two
    senders do not look.
  `Spec.ldSegRefAll_zkAtW`: under `A.Ghost κ`, `Nonempty I.C.E0.Str`, X closed and `F.OK pp`:
    A.ZkAt pp X (Cb/Req1/LdReqRefZkP.lean) from these: five kinds of wide facts in X, places,
    readings, and of the two senders that they do not look.

Limits: this file does not say that the wide facts are in X. It says nothing on an instance of all
conditions of this file together. No theorem of this library states that the hypotheses of
`Spec.ldSegRefAll_zkAtW` can be met together.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefZkP
import Cb.Req1.LdSegFrontRefWide
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain

/-- after any chain that ends at a: if f is fresh, so is f' -/
def LdStage.Follows {E Kc : Type} [Field E] (a : LdStage E Kc) (f f' : MaskFact a.J.W) : Prop :=
  ∀ (A : Joint Kc) (c : Chain Kc A a.J) (base : MaskFact A.W → Prop),
    c.FreshGiven base f → c.FreshGiven base f'

/-- A set of facts that is closed under "follows". -/
def LdStage.Closed {E Kc : Type} [Field E] (a : LdStage E Kc) (X : MaskFact a.J.W → Prop) : Prop :=
  ∀ f f', a.Follows f f' → X f → X f'

/-- own entries and values, from places -/
def plOwn {N Ix : Type} (at' : Ix → N) : N → Prop := fun n => ∃ i, at' i = n
def plVal {N Ix Mk E : Type} [Zero E] (at' : Ix → N) (ve : Mk → Ix → E) (M : Mk) :
    N → E :=
  Function.extend at' (ve M) fun _ => 0

/-- The places of the own masks of the front's blocks. -/
structure LdRefP {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
    (A : LdRefD E Kc I) (F : LdRefF A) where
  atL : (A.V.Fp.A.plChain I.C.E0 A.Xa.Q.D.S.Msg (I.C.PIdx × (A.W₁ × A.Gh)) Kc A.V.Fp.msg F.RdK).I →
    A.Xa.Q.D.S.Ent
  at0 : PIdx A.V.Fp.Z.T.par.fmt ⊕ A.V.Fp.Z.T.A → A.Xa.Q.D.S.Ent
  atS : ∀ i, PIdx (A.V.T i).par.fmt ⊕ (A.V.T i).A → A.Xa.Q.D.S.Ent

namespace LdRefP
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I}
  {F : LdRefF A} (P : LdRefP A F)

/-- the places of the lookup's own masks among its names -/
abbrev plL :
    (A.V.Fp.A.mjChain I.C.E0 A.Xa.Q.D.S.Msg (I.C.PIdx × (A.W₁ × A.Gh)) Kc A.V.Fp.msg F.RdK).Pl :=
  A.V.Fp.A.plChain I.C.E0 A.Xa.Q.D.S.Msg (I.C.PIdx × (A.W₁ × A.Gh)) Kc A.V.Fp.msg F.RdK

/-- One block's places, for a reading msg on names J, read at RdJ, with own names pl. -/
structure At (W : LdRefW A) {J Ix : Type} (msg : A.Xa.Q.D.S.Msg → J → E) (RdJ : J → Prop)
    (pl : Ix → J) (at' : Ix → A.Xa.Q.D.S.Ent) : Prop where
  inj : Function.Injective at'
  p1  : ∀ m i, msg m (pl i) = A.Xa.Q.D.S.ents m (at' i)
  p2  : ∀ m m' j, RdJ j → (∀ i, pl i ≠ j) →
    (∀ n : A.Xa.Q.D.S.Ent, W.Rd n → ¬ plOwn at' n → m' n.1 n.2 = m n.1 n.2) → msg m' j = msg m j
  rd  : ∀ i, W.Rd (at' i)

def OKL (W : LdRefW A) : Prop := At W A.V.Fp.msg F.RdK (plL (F := F)).pl P.atL
def OK0 (W : LdRefW A) : Prop := At W A.V.Fp.msg0 F.Rd0 (A.V.Fp.Z.T.own F.Rd0).at P.at0
def OKS (W : LdRefW A) (i : ℕ) : Prop :=
  At W (A.V.msg i) (F.RdS i) ((A.V.T i).own (F.RdS i)).at (P.atS i)

end LdRefP

/-- what (msg', Rd') shows is a function of what (msg, RdJ) shows at names that are no pl i -/
def readsLess {M J J' Ix E : Type} (msg : M → J → E) (RdJ : J → Prop) (pl : Ix → J)
    (msg' : M → J' → E) (Rd' : J' → Prop) : Prop :=
  ∀ m m', (∀ j, RdJ j → (∀ i, pl i ≠ j) → msg m' j = msg m j) → ∀ y, Rd' y → msg' m' y = msg' m y

/-- Nested readings of the front. -/
structure LdRefF.Nest {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
    {A : LdRefD E Kc I} (F : LdRefF A) : Prop where
  n0L : readsLess A.V.Fp.msg0 F.Rd0 (A.V.Fp.Z.T.own F.Rd0).at A.V.Fp.msg (A.V.Fp.A.srAll F.Dt)
  nSL : ∀ i ≤ A.V.m,
    readsLess (A.V.msg i) (F.RdS i) ((A.V.T i).own (F.RdS i)).at A.V.Fp.msg (A.V.Fp.A.srAll F.Dt)
  nS0 : ∀ i ≤ A.V.m, readsLess (A.V.msg i) (F.RdS i) ((A.V.T i).own (F.RdS i)).at A.V.Fp.msg0 F.Rd0
  nSS : ∀ i ≤ A.V.m,
    ∀ j < i, readsLess (A.V.msg i) (F.RdS i) ((A.V.T i).own (F.RdS i)).at (A.V.msg j) (F.RdS j)

/-- What each block of the front reads does not depend on the own entries. -/
structure LdRefW.Blind {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I}
    (W : LdRefW A) (F : LdRefF A) (own : A.Xa.Q.D.S.Ent → Prop) : Prop where
  lk : ∀ m m',
    A.Xa.Q.D.S.Alike W.Rd own m m' → ∀ j, A.V.Fp.A.srAll F.Dt j → A.V.Fp.msg m' j = A.V.Fp.msg m j
  s0 : ∀ m m', A.Xa.Q.D.S.Alike W.Rd own m m' → ∀ j, F.Rd0 j → A.V.Fp.msg0 m' j = A.V.Fp.msg0 m j
  s  : ∀ i ≤ A.V.m,
    ∀ m m', A.Xa.Q.D.S.Alike W.Rd own m m' → ∀ j, F.RdS i j → A.V.msg i m' j = A.V.msg i m j

/-- The wide facts of the front's blocks are in X. -/
structure LdRefP.In {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I}
    {F : LdRefF A} (P : LdRefP A F) (W : LdRefW A) (X : MaskFact A.V.Fp.s0.J.W → Prop) : Prop where
  lk : X (A.V.Fp.s0.wideFact W.Rd W.Rr (plOwn P.atL) (A.V.Fp.dm F.RdK F.Cc).Mk
      (plVal P.atL fun M => (LdRefP.plL (F := F)).ve M))
  s0 : X (A.V.Fp.s0.wideFact W.Rd W.Rr (plOwn P.at0) (A.V.Fp.Z.T.own F.Rd0).Mk
      (plVal P.at0 fun M => Sum.elim M.1 M.2))
  s  : ∀ i ≤ A.V.m,
    X (A.V.Fp.s0.wideFact W.Rd W.Rr (plOwn (P.atS i)) ((A.V.T i).own (F.RdS i)).Mk
        (plVal (P.atS i) fun M => Sum.elim M.1 M.2))

/-- The late blocks' conditions, with "quiet" replaced by readings. -/
structure LdRefD.LateW {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)
    (W : LdRefW A) (F : LdRefF A) (RdL : A.Xa.Q.T.Ent → Prop) (X : MaskFact A.V.Fp.s0.J.W → Prop) :
    Prop where
  maskL : A.Xa.A.MaskOK A.Xa.Dt
  rdL   : ∀ j, A.Xa.A.srAll A.Xa.Dt j → RdL j
  inL   : ∀ j, A.Xa.A.swAll j → ∃ n, A.up n = j
  wideL : ∀ n, RdL n → W.Rd2 n
  factL : X (W.fact A.ownL (A.Xa.dm RdL).Mk (A.valL RdL))
  blL   : W.Blind F A.ownL
  s1L   : A.Xa.Q.D.d1.NoLook W.Rd W.Rr A.ownL
  s3L   : A.Xa.Q.D.d3.NoLook (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
    (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N A.ownL fun _ => False)
  ownT  : A.X.Own
  inT   : ∀ i, ∃ n, A.up n = A.wAt i
  wideT : ∀ n, A.Rdt n → W.Rd2 n
  factT : X (W.fact A.ownT A.X.mask.Mk A.valT)
  blT   : W.Blind F A.ownT
  s1T   : A.Xa.Q.D.d1.NoLook W.Rd W.Rr A.ownT
  s3T   : A.Xa.Q.D.d3.NoLook (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
    (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N A.ownT fun _ => False)
  apart : ∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 A.ownT n

namespace Spec

def ldSegRefW_fresh : Prop :=
  ∀ (E Kc : Type) [Field E] (A : Joint Kc) (a : LdStage E Kc)
      (c : Chain Kc A a.J) (base : MaskFact A.W → Prop),
    a.Closed (c.FreshGiven base)

def ldSegRefW_quietP : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd : T.J → Prop) (J' : Type)
      (msg' : S.Msg → J' → E) (Rd' : J' → Prop),
    readsLess msg Rd (T.own Rd).at msg' Rd' → ldQuiet S (frFact Kc T S E₀ Wp A0 msg Rd) msg' Rd'

def ldSegRefW_quietW : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
      (own : a.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E)
      (J : Type) (msg : a.S.Msg → J → E) (Rd' : J → Prop),
    (∀ m m', a.S.Alike Rd own m m' → ∀ j, Rd' j → msg m' j = msg m j) →
    ldQuiet a.S (a.wideFact Rd Rr own Mk val) msg Rd'

/-- The front's facts, from wide facts. (not all hypotheses are named here: see the statement
below) -/
def ldSegRefW_front : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) (I : LdRefIx E) (A : LdRefD E Kc I) (W : LdRefW A)
      (F : LdRefF A) (P : LdRefP A F) (X : MaskFact A.V.Fp.s0.J.W → Prop),
    A.V.Fp.s0.Closed X → F.OK pp → P.OKL W → P.OK0 W → (∀ i ≤ A.V.m, P.OKS W i) →
    F.Nest → P.In W X → A.FrontFacts F X

def ldSegRefW_pass : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (W : LdRefW A)
      (F : LdRefF A) (X : MaskFact A.V.Fp.s0.J.W → Prop) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E),
    X (W.fact own Mk val) → W.Blind F own → A.Xa.Q.D.d1.NoLook W.Rd W.Rr own →
    A.Xa.Q.D.d3.NoLook (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
      (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N own fun _ => False) →
    W.Pass F X own Mk val

/-- What zero knowledge asks of a closed body, beside its hypotheses (`A.OK pp`), from wide facts.
(not all hypotheses are named here: see the statement below) -/
def ldSegRefAll_zkAtW : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) (I : LdRefIx E) (A : LdRefD E Kc I)
      [Nonempty I.C.E0.Str] (W : LdRefW A) (F : LdRefF A) (P : LdRefP A F) (κ : A.Gh → Kc)
      (RdL : A.Xa.Q.T.Ent → Prop) (X : MaskFact A.V.Fp.s0.J.W → Prop),
    A.V.Fp.s0.Closed X → A.Ghost κ → F.OK pp → P.OKL W → P.OK0 W → (∀ i ≤ A.V.m, P.OKS W i) →
    F.Nest → P.In W X → A.LateW W F RdL X → A.ZkAt pp X

end Spec
end Cb
