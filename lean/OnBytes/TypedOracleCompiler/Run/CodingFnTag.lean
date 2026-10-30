-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingFnTag.lean.
Run/CodingFnTag.lean: THE FUNCTIONS OF Run/CodingFn.lean AT ANY TAG: WHAT THEY GIVE AT THEIR OWN TAG
AND AT ANOTHER. Theorems, and two terms that show that the functions can be applied at the online
protocol's tag.
In Run/CodingFn.lean the protocol's tag is a parameter of the data. A leaf's body and the name of a
chain oracle hold a tag of their own, which is compared with the data's. At a written tag that test
evaluates; for a variable tag these are the equations to rewrite with.
    leafCall_self, leafCall_ne      a leaf of a symbol under the data's tag: its call; under another
                                    tag: none
    famOf_fb_self, famOf_fb_ne      a chain query under the data's tag: the K message blocks and the
                                    chain value, each by fbCall; under another tag: zeros
    runB, runT           the library's verifier of a slot of the online protocol (vBS), and of a
                         key's test string (vTS), run on the typed oracle functions at the data of
                         that tag: they elaborate for every interface and wiring
WHAT IS NOT SAID. IN THIS FILE NOTHING IS RUN: runB is a term, no run. (The run functions of the
generic construction
stand at the online protocol's tag: Run/PlanQS.lean.) With shared rounds the online protocol asks
queries of further formats, which have no call here.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingFnTag
import OnBytes.TypedOracleCompiler.Run.CodingFn
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Rom.Cache

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-- TWO: over bodies: where D.leaf spells the body. (In the library: at a symbol under the page's
own tag.) -/
theorem leafCall_self (D : PageD L t) (b : L.Bd) (z : Nat × Nat × ByteArray)
    (hz : D.leaf b = some z)
    (salt : Bits) :
    leafCall D ⟨b, salt⟩ =
      some ⟨0, 164, z.1, z.2.1, bitsToBytes (salt.take 256),
          z.2.2 ++ bitsToBytes (salt.drop 256)⟩ := by
  show (D.leaf b).map _ = _
  rw [hz]
  rfl

/-- TWO: over bodies: where D.leaf spells nothing. (In the library: at a symbol under another tag.)
-/
theorem leafCall_ne (D : PageD L t) (b : L.Bd) (hz : D.leaf b = none) (salt : Bits) :
    leafCall D ⟨b, salt⟩ = none := by
  show (D.leaf b).map _ = _
  rw [hz]
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

/-- the verifier of a slot of the online protocol on the family at data of that protocol's tag -/
def runB (O : ByteArray → ByteArray) (W : QueryLayout 256 L) (D : PageD L .onl) (sMT sFS : ℕ)
    (cm : Dig 256) (x : X) (π : OneProtocolProof 256 L.onlineBatch) : Bool :=
  (vBS W sMT sFS cm x π).det (famOf O D W.K)

/-- the verifier of a key's test string on the family at data of the tag "test" -/
def runT (O : ByteArray → ByteArray) (W : QueryLayout 256 L) (D : PageD L) (sMT sFS : ℕ) (cm : Dig 256)
    (π : OneProtocolProof 256 L.batT) : Bool :=
  (vTS W sMT sFS cm π).det (famOf O D W.K)

end TypedOracleCompiler.Run
