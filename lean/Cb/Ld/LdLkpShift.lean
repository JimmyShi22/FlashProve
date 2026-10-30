-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpShift.lean: several lookups into one, by a random shift.
This file is about batching lookup arguments: several lookup claims, each with a table of its own,
become one lookup claim when a random multiple of a tag, one for each claim, different for different
claims (`TagInj`), is added to keys and table entries.

Definitions and statements (the statements in `Cb.Spec`); the proofs are in
Cb/Ld/LdLkpShiftProofs.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
The claim before. 2^g functions f, each with 2^v keys "key f b" (any functions of the public state
and of what the claims read; never sent) and a public table of 2^d entries "tab f u": for every f,
every key of f is an entry of the table of f.
The block. One round, no prover message: the verifier sends θ, uniform in E.
The claim after. One lookup, with 2^(g+v) keys and a table of 2^(g+d) entries, both over E:
key (f, b) := key f b + tag f · θ, entry (f, u) := tab f u + tag f · θ, tag f: a public field
element for each function, different for different functions (`TagInj`). (f, b) is numbered
f · 2^v + b, and (f, u) is numbered f · 2^d + u.

Why it is sound, for a fixed tuple of messages: let x be a key of f outside the table of f. If
x + tag f · θ is the entry τ + tag j · θ, then j is not f, and θ = (τ - x) / (tag f - tag j): one
value of θ for each entry of the joint table.

Main names:
  `Spec.ldLkpShift_fwd`: complete at every θ: if the claim before holds, the claim after holds.
  `Spec.ldLkpShift_cnt`: under `TagInj`, if some key is outside its own table, the claim after holds
    for at most 2^(g+d) values of θ (the size of the joint table).
  `Spec.ldLkpShift_goodAt`: under `TagInj`, the block at the base: good for each fixed tuple
    (Cb/Ld/LdSigLift.lean: `GoodAt`), for any tuple type M and any joint R0 that rides along (on the
    honest side: the multiplicities); error 2^(g+d) (values of θ); perfectly complete; the identity
    extracts.
  `Spec.ldLkpShift_goodB`: over a signature: it concludes `GoodB` (Ior/Masked.lean: `IOR.GoodT`
    without its clause on zero knowledge; there is no prover message) (premise: `TagInj`).
    (`IOR.GoodT`: Ior/KnowCollGood.lean) A signature: the oracle messages of a statement: a finite
    type of names, with the data of an oracle message for each; not a digital signature.

`Cb.GoodAt` asks, of a reduction with its honest side between two joints whose witnesses pair a
value of one type M with a further witness, the clauses of `GoodB` with two differences: a further
clause `same` asks that, on every run, the honest prover's output witness carries the M-part of its
input witness unchanged; and the clause `know`, in place of `GoodB`'s, asks, for each fixed m of
type M, round-by-round knowledge soundness (`Know`) on the input joint's set of statements and at
the numbers' list of errors, as `GoodB`'s does, but between the relaxed relations at (m, ·) and with
the extractor `ext m`.

Limits: the keys are functions of the tuple, and the count is for a fixed tuple. Over a signature
the tuple is what the statement decodes to: so the samples of the oracle messages that the keys read
stand in the input statement; θ comes after their answers. That it comes before the lookup's own
challenge is a matter of the chain that uses the block.
For whoever calls a lookup after this block: the honest multiplicities are taken function by
function (how many keys of f equal the entry u of f's table and no earlier entry of it); so they do
not depend on θ and can be sent before it. At a θ at which a shifted entry of a function f and one
of a later function f' (f < f') coincide they are not "the number of joint keys that equal the joint
entry and no earlier joint entry" (where a key of f' equals that entry of f'). A lookup that follows
must be complete for them: its exact claim must admit any assignment of keys to equal entries. Here
they ride along in R0, unread.
This file says nothing on tables of different sizes, or numbers of keys that differ: pad by
repeating an entry or a key.
2^(g+d) at or above |E| says nothing.
The block follows this protocol's technical report (the usual random combination of a tag and a
value; lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.LkpAlg
import Cb.Ld.LdBattKit
import Cb.Ld.LdSigLift

set_option autoImplicit false

namespace Cb.LdLkp
open Finset Cb.Lkp Iop IOR

section
variable {E : Type} [Field E]

/-- every key of every function is an entry of that function's table -/
def AllIn (g v d : ℕ) (key tab : ℕ → ℕ → E) : Prop := ∀ f < 2 ^ g, InTable v d (key f) (tab f)

/-- The joint keys and the joint table at θ. -/
def shKey (v : ℕ) (key : ℕ → ℕ → E) (tag : ℕ → E) (θ : E) : ℕ → E := fun X =>
  key (X / 2 ^ v) (X % 2 ^ v) + tag (X / 2 ^ v) * θ
def shTab (d : ℕ) (tab : ℕ → ℕ → E) (tag : ℕ → E) (θ : E) : ℕ → E := fun Y =>
  tab (Y / 2 ^ d) (Y % 2 ^ d) + tag (Y / 2 ^ d) * θ

/-- different functions have different tags -/
def TagInj (g : ℕ) (tag : ℕ → E) : Prop := ∀ f < 2 ^ g, ∀ f' < 2 ^ g, tag f = tag f' → f = f'

end

/-- The data of the block. -/
structure ShiftP (E St M : Type) where
  g : ℕ
  v : ℕ
  d : ℕ
  key : St → M → ℕ → ℕ → E
  tab : St → ℕ → ℕ → E
  tag : ℕ → E

namespace ShiftP
variable {E St M : Type} [Field E] (P : ShiftP E St M)

/-- The claim before; the claim after. -/
def inC : St → M → Prop := fun st m => AllIn P.g P.v P.d (P.key st m) (P.tab st)
def outC : St × E → M → Prop := fun x m =>
  InTable (P.g + P.v) (P.g + P.d) (shKey P.v (P.key x.1 m) P.tag x.2)
    (shTab P.d (P.tab x.1) P.tag x.2)

variable {Kc Wp : Type} {Ex : ExtSpec}

/-- The two joints: R0 rides along. -/
def jIn (R0 : Rels Kc St Ex (M × Wp)) : Rels Kc St Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x y w ∧ P.inC x w.1, fun a w => R0.relR a w ∧ P.inC a.1 w.1, R0.on, R0.core⟩
def jOut (R0 : Rels Kc St Ex (M × Wp)) : Rels Kc (St × E) Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x.1 y w ∧ P.outC x w.1,
    fun a w => R0.relR (a.1.1, a.2) w ∧ P.outC a.1 w.1,
    fun a => R0.on (a.1.1, a.2),
    R0.core⟩

end ShiftP
end Cb.LdLkp

namespace Cb.Spec
open Finset Prob Cb.Lkp Cb.LdLkp Iop IOR

/-- Complete at every θ. -/
def ldLkpShift_fwd : Prop :=
  ∀ (E : Type) [Field E] (g v d : ℕ) (key tab : ℕ → ℕ → E) (tag : ℕ → E) (θ : E),
    AllIn g v d key tab → InTable (g + v) (g + d) (shKey v key tag θ) (shTab d tab tag θ)

/-- For fixed keys, under `TagInj g tag`, if some key is outside its own table: at most as many bad
θ as the joint table has entries. -/
def ldLkpShift_cnt : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (g v d : ℕ) (key tab : ℕ → ℕ → E) (tag : ℕ → E), TagInj g tag →
    ¬ AllIn g v d key tab →
    cnt (fun θ : E => InTable (g + v) (g + d) (shKey v key tag θ) (shTab d tab tag θ)) ≤ 2 ^ (g + d)

/-- The block at the base. -/
def ldLkpShift_goodAt : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (St M Wp Kc : Type) (Ex : ExtSpec)
      (P : ShiftP E St M) (R0 : Rels Kc St Ex (M × Wp)),
    TagInj P.g P.tag →
    GoodAt (IOR.draw E (Prod.mk : St → E → St × E) Ex) (Honest.draw E Prod.mk Ex (M × Wp))
      (P.jIn R0) (P.jOut R0) (fun _ _ _ wp => wp) (Nums.draw Kc E Prod.mk Ex (2 ^ (P.g + P.d)))

/-- Over a signature. -/
def ldLkpShift_goodB : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (St Wp Kc : Type) (E₀ : ExtSpec)
      (P : ShiftP E St S.Msg) (R0 : Rels Kc St E₀ (S.Msg × Wp)),
    TagInj P.g P.tag →
    GoodB ((IOR.draw E (Prod.mk : St → E → St × E) E₀).keep S.Smp S.ext)
      (S.liftH (Honest.draw E Prod.mk E₀ (S.Msg × Wp))) (S.over (P.jIn R0)) (S.over (P.jOut R0))
      (fun _ _ w => w) ((Nums.draw Kc E Prod.mk E₀ (2 ^ (P.g + P.d))).keep S.Smp S.ext)

end Cb.Spec
