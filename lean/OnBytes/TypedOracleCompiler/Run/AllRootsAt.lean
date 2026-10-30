-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/AllRootsAt.lean: one encoding for all roots, with the conclusion at the whole
wiring's compiled Link verifier. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

WHY. A judge speaks of `vLS` at a whole wiring (OnBytes/TypedOracleCompiler/Run/WireX.lean), not of `verifyOneProtocol` at
the wiring of one protocol.

NEW (1).
 `accepts_allRoots_at`   `accepts_allRoots` at `E.emb`, then `vls_any`.

WHAT IS NOT SAID. What the head of OnBytes/TypedOracleCompiler/Run/AllRoots.lean does not say. Nothing on soundness;
no probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.AllRoots
import OnBytes.TypedOracleCompiler.Run.WireX

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run

section
variable {Bd : Type} (B : BodyD Bd) (S0 : _root_.Fmt.SpecX)
  (stm : ByteArray → ByteArray → ByteArray) (Lf : LeafD (xdOf S0 stm) B) (dec : View → Bool)
  (hcfg : S0.base.cfg.size = 32) (V : StmInv (xdOf S0 stm)) (E : OwnE Bd (xdOf S0 stm))

/-- `accepts_allRoots` (OnBytes/TypedOracleCompiler/Run/AllRoots.lean) at the whole wiring's verifier: the
embedding of own symbols is `E.emb`, and the conclusion speaks of `vLS` at `WkAny B (xdOf S0 stm)
dec E`, on the typed string as a Link string (`vls_any`). The hypotheses are those of
`accepts_allRoots`. `WkAny` holds a carrying of the wiring along an equation between two batch
protocols (`wireTo`), as the original has. An implication between two yeses: nothing on soundness;
no probability. -/
theorem accepts_allRoots_at (pd : Dig 256) (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hOwn : OwnFits B (xdOf S0 stm) Lf E.emb)
    (hi : ∀ p a, B.own (E.emb (.inr p) a) =
      some (leafSL (xdOf S0 stm).C S0.base.plan.salt (xdOf S0 stm).ds ⟨p, a⟩))
    (hn : S0.base.rand.isNone = false)
    (honce : (S0.stored.flatten.map (·.item == 1)).Nodup)
    (g : Fam (rom 256)) (O' : ByteArray → ByteArray) (hO : ∀ s, (O' s).size = 32)
    (hpd : _root_.Fmt.HO O' 169 0 1 _root_.Fmt.zero32 S0.base.params = digToBytes pd)
    (hag : ∀ q : _root_.Fmt.OQ, q.number % 65536 ≠ 169 → O' (strOf q) = oB (g ()) (strOf q))
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : (xdOf (withStatement S0 (stm r0 r1)) stm).ok = true)
    (hroot : ∀ t ∈ S0.stored.flatten,
      _root_.Fmt.itemRoot (stm r0 r1) t.item = some (if t.item == 1 then r1 else r0))
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O') (withStatement S0 (stm r0 r1)) seen b
      i = some (o, j))
    (hdec : dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) = true) :
    ∃ π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up,
      toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
        (xdOf S0 stm).xs dec o = some π ∧
      (vLS (WkAny B (xdOf S0 stm) dec E) (256 + 8 * S0.base.plan.salt) 256 (bytesToDig r0)
        (bytesToDig r1) (asLink (Bd := Bd) (xdOf S0 stm) dec π)).det
        (readBlocks (implAtPd B S0 stm Lf dec hcfg V pd) g) = true := by
  obtain ⟨π, t1, t2⟩ := accepts_allRoots B S0 stm Lf dec hcfg V E.emb pd F hOwn hi hn honce g O' hO
    hpd hag r0 r1 h0 h1 hok hroot seen b i o j e hdec
  refine ⟨π, t1, ?_⟩
  rw [← vls_any B (xdOf S0 stm) dec E (256 + 8 * S0.base.plan.salt) (bytesToDig r0) (bytesToDig r1)
      π]
  exact t2

end

end TypedOracleCompiler.Run.PQ
