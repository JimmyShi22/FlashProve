-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/LeafTakenAt.lean: the code of leaf queries over strings of bits
(`KeyLeaves.leavesAt`, OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean), and that code carried along a pair of
readings to another interface (`LinkAlong.leavesAlong`, OnBytes/TypedOracleCompiler/Run/LinkAlong.lean), write the
string of the page's own call wherever they write: they are "silent or agreeing" in the sense of
OnBytes/Maker/Page/LeafAgree.lean.

That code is typed at an interface of its own. A leaf query of another interface is no query of that
one, even where both have strings of bits for bodies: so the code is carried along a pair.

Main names.
  `agrees_leavesAt`: what `leavesAt L0 nb cfg` writes at a leaf query is, as bytes, the string of
    the page's own call of that query, for a salt of whole bytes.
  `agrees_along`: the same of `leavesAlong G (leavesAt L0 nb cfg)` and the page's field
    `leafOf bd`, for a pair G that keeps the typed salt and reads the body by bd.
  `leafPairOf L0 e`: such a pair, at any interface L whose bodies are strings of bits by e.
  `leavesJ L0 nb cfg e`: the code of leaf queries at L. `agrees_leavesJ`: what it writes is the
    string of the call of `leafOf e`.

What they ask. nb = 8 k: the file's salt has whole bytes.

Limits: where the code writes nothing, nothing is said. L0, nb and cfg are letters. That a page's
field `leafX` is `leavesJ`'s code is said of no page here. `gJ P O` is a function of the typed
query, no one-to-one coding. Nothing on soundness.


-/
import OnBytes.Maker.Page.LeafTaken
import OnBytes.TypedOracleCompiler.Run.KeyLeaves
import OnBytes.TypedOracleCompiler.Run.LinkAlong

set_option autoImplicit false

noncomputable section

namespace OnBytes.Maker.Page
open _root_.Run TypedOracleCompiler.Strings TypedOracleCompiler.Run TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open TypedOracleCompiler.Run.LinkAlong

variable {I0 X0 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (nb k : ℕ) (hn : nb = 8 * k) (cfg : ByteArray)

include hn in
/-- What the code of leaf queries writes is the string of the page's own call. -/
theorem agrees_leavesAt (q : LeafIn (strung L0)) (s : List Bool)
    (h : (KeyLeaves.leavesAt L0 nb cfg).lf.put q = some s) (c : Fmt.OQ)
    (hc : leafCall q.body q.salt = some c) : bitsToBytes s = strOf c :=
  agrees_of_call2 L0 q s (KeyLeaves.leafCode_str L0 nb cfg k hn q s h) c hc

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

include hn in
/-- The same of the code carried along a pair that keeps the salt and reads the body by bd. -/
theorem agrees_along (G : LeafPair (strung L0) L) (bd : L.Bd → List Bool)
    (hG : ∀ q2 q1, G.sel q2 = some q1 → q1.body = bd q2.body ∧ q1.salt = q2.salt)
    (q : LeafIn L) (s : List Bool)
    (h : (leavesAlong G (KeyLeaves.leavesAt L0 nb cfg)).lf.put q = some s) (c : Fmt.OQ)
    (hc : leafOf bd q = some c) : bitsToBytes s = strOf c := by
  obtain ⟨q1, hq1, hs⟩ := PCode.pull_put (KeyLeaves.leavesAt L0 nb cfg).lf G.sel G.bk G.bk_sel
    G.sel_bk q s h
  refine agrees_leavesAt L0 nb k hn cfg q1 s hs c ?_
  rw [(hG q q1 hq1).1, (hG q q1 hq1).2]
  exact hc

/-! ## A code of leaves at any interface whose bodies are strings of bits -/

/-- The pair of readings between an interface whose bodies are strings of bits, by e, and the
interface at which the code of leaf queries is typed: body by e, the typed salt as it is. -/
def leafPairOf (e : L.Bd ≃ List Bool) : LeafPair (strung L0) L where
  sel := fun q => some ⟨e q.body, q.salt⟩
  bk := fun q => some ⟨e.symm q.body, q.salt⟩
  bk_sel := fun a b h => by
    cases h
    show some (⟨e.symm (e a.body), a.salt⟩ : LeafIn L) = some a
    rw [e.symm_apply_apply]
  sel_bk := fun b a h => by
    cases h
    show some (⟨e (e.symm b.body), b.salt⟩ : LeafIn (strung L0)) = some b
    rw [e.apply_symm_apply]

/-- The code of leaf queries, at that interface. -/
def leavesJ (e : L.Bd ≃ List Bool) : PageG.Leaves L :=
  leavesAlong (leafPairOf L0 e) (KeyLeaves.leavesAt L0 nb cfg)

include hn in
/-- What it writes is the string of the page's own call: no premise on a pair is left. -/
theorem agrees_leavesJ (e : L.Bd ≃ List Bool) (q : LeafIn L) (s : List Bool)
    (h : (leavesJ L0 nb cfg e).lf.put q = some s) (c : Fmt.OQ) (hc : leafOf e q = some c) :
    bitsToBytes s = strOf c :=
  agrees_along L0 nb k hn cfg (leafPairOf L0 e) e
    (fun _ _ h => by cases h; exact ⟨rfl, rfl⟩) q s h c hc

end OnBytes.Maker.Page
