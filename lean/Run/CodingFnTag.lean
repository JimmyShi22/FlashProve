-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingFnTag.lean: the functions of Run/CodingFn.lean (from a typed query to the hash call of the
programs' format) at any tag: what they give at their own tag and at another.

Theorems, and two terms that show that the functions can be applied at the online protocol's tag
(`runB`) and at the tag "test" (`runT`).
In Run/CodingFn.lean the protocol's tag is a parameter of the data (`PageD`). A tag: In `Compile/`,
`CompileK/` and `Run/`, which of the compiled protocols of an interface is meant: the offline test,
the link or the session (`Tag`, Compile/Oracles.lean). A leaf's body and the name of a chain oracle
hold a tag of their own, which is compared with the data's. At a tag that is written out, that test
evaluates; for a variable tag, the theorems here are the equations to rewrite with.

Main names:
  `leafCall_self`, `leafCall_ne`: a leaf of a symbol under the data's tag: its call; under another
    tag: none.
  `famOf_fb_self`, `famOf_fb_ne`: a chain query under the data's tag: the K message blocks and the
    chain value, each by `fbCall`; under another tag: zeros.
  `runB`, `runT`: they elaborate for every interface and wiring.

Notation:
  `sMT`, `sFS`: the length of the salt of a leaf, and of the salt of a chain
    (Compile/Batch/Verifier.lean);
  `W`: the interface's wiring (`QueryLayout`, Iop/BatchWire.lean);
  `cm`: the external root (`vB`, Compile/Batch/Verifier.lean);
  `π`: the argument string of one slot (`OneProtocolProof`, Compile/Batch/Verifier.lean).

Limits: in this file nothing is run: `runB` is a term, no run. (The run functions of
Run/PlanQS.lean stand at the online protocol's
tag.) With shared rounds the online protocol asks queries of further formats, which have no call
here.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingFn
import Compile.Batch.Verifier
import Rom.Cache

set_option autoImplicit false

namespace Run
open Compile Compile.Batch Iop Rom

variable {I X : Type} {L : BatchProtocol I X} {t : Tag}

theorem leafCall_self (D : PageD L t) (s : SymAny (shapeOf L t)) (salt : Bits) :
    leafCall D ⟨some (.inr ⟨t, s⟩), salt⟩ =
      some ⟨0, 164, (D.leaf s).1, (D.leaf s).2.1, bitsToBytes (salt.take 256),
          (D.leaf s).2.2 ++ bitsToBytes (salt.drop 256)⟩ := by
  show (castTag (F := fun t => SymAny (shapeOf L t)) t t s).map _ = _
  rw [castTag_self]
  rfl

theorem leafCall_ne (D : PageD L t) {t' : Tag} (h : t' ≠ t)
    (s : SymAny (shapeOf L t')) (salt : Bits) :
    leafCall D ⟨some (.inr ⟨t', s⟩), salt⟩ = none := by
  show (castTag (F := fun t => SymAny (shapeOf L t)) t t' s).map _ = _
  rw [castTag_ne h]
  rfl

theorem famOf_fb_self (O : ByteArray → ByteArray) (D : PageD L t) (K : Nat) (q : FbIn 256 L t) :
    famOf O D K (.fb t) q =
      ((fun k : Fin K => ansOf O (fbCall D K q k.castSucc),
        ansOf O (fbCall D K q (Fin.last K))) : (Fin K → Dig 256) × Dig 256) := by
  simp only [famOf, castTag_self]

theorem famOf_fb_ne (O : ByteArray → ByteArray) (D : PageD L t) (K : Nat) {t' : Tag}
    (h : t' ≠ t) (q : FbIn 256 L t') :
    famOf O D K (.fb t') q =
      ((fun _ _ => false, fun _ => false) : (Fin K → Dig 256) × Dig 256) := by
  simp only [famOf, castTag_ne h]

/-- The library's verifier of a slot of the online protocol (`vBS`), run on the typed oracle
functions at data of that protocol's tag. -/
def runB (O : ByteArray → ByteArray) (W : QueryLayout 256 L) (D : PageD L .onl) (sMT sFS : ℕ)
    (cm : Dig 256) (x : X) (π : OneProtocolProof 256 L.onlineBatch) : Bool :=
  (vBS W sMT sFS cm x π).det (famOf O D W.K)

/-- The library's verifier of a key's test string (`vTS`), run on the typed oracle functions at data
of the tag "test". -/
def runT (O : ByteArray → ByteArray) (W : QueryLayout 256 L) (D : PageD L) (sMT sFS : ℕ) (cm : Dig 256)
    (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto L.offline)) : Bool :=
  (vTS W sMT sFS cm π).det (famOf O D W.K)

end Run
