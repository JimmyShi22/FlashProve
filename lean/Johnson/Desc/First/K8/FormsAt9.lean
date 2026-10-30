-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/FormsAt9.lean: **AT THE COMPOSED MEANING, THE FIELD "forms" OF THE
RUN "small" GIVES THE APPROXIMATE RANGE PROOF's LAW's SENTENCE `SmallAt`**, at the law's one table
of cells `cellsAhead` (Johnson/Desc/First/K8/CellsAhead.lean) with the composed meaning's own
parameters. Statements and proofs: a join of two files' lemmas.
  `small_at9`: segment m has the sort sub; the table's map of names at that sort sends (5 + o,
    "small") to just [(4 + o, "K8.equations")]; the chain has a link m; the state names a tail tl
    and that tail's own list of functions: then the field "forms" at (m, 5 + o, "small") gives
    `SmallAt (cellsAhead 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, s)) s w`.
  `small_at9_layers`, `small_at9_attention` (o = 0), `small_at9_head` (o = 1): the three sorts, the
    premise on the map paid.
Called: `formsQA_small`, `reader_small`, `runs_small` (Johnson/Desc/Sound/MgAt/SmallRun.lean);
`smallAt_of_formsQA` (Johnson/Desc/First/K8/LawSmallAhead.lean).
Nothing on the digits. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAt.SmallRun
import Johnson.Desc.First.K8.LawSmallAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning runsOf)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The field "forms" at the run "small" gives the law's sentence.** -/
theorem small_at9 (m o : ℕ) (sub : ModelPart) (hsub : 𝔇.links[m]? = some sub)
    (hr : runsOf sub (5 + o) "small" = [(4 + o, "K8.equations")]) (l : Link First.S Claim)
    (hl : 𝔇.lk m = some l) (z : P) (s : First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) {tl : HTailF2} (ht : s.tl? = some tl)
    (hf : s.funs? = some tl.funs) (h : (mgAll 𝔇 Mg).forms m (5 + o) "small" (z, s) y w) :
    SmallAt (cellsAhead 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, s)) s w :=
  smallAt_of_formsQA 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m z s (𝔇.Rd m) (4 + o) "K8.equations" ht hf
    (reader_small 𝔇 m l hl (4 + o) s) w (formsQA_small 𝔇 Mg m o sub hsub hr z s y w h)

theorem small_at9_layers (m : ℕ) (hsub : 𝔇.links[m]? = some .layers) (l : Link First.S Claim)
    (hl : 𝔇.lk m = some l) (z : P) (s : First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) {tl : HTailF2} (ht : s.tl? = some tl)
    (hf : s.funs? = some tl.funs) (h : (mgAll 𝔇 Mg).forms m (5 + 0) "small" (z, s) y w) :
    SmallAt (cellsAhead 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, s)) s w :=
  small_at9 𝔇 Mg m 0 .layers hsub runs_small.1 l hl z s y w ht hf h

theorem small_at9_attention (m : ℕ) (hsub : 𝔇.links[m]? = some .attention)
    (l : Link First.S Claim) (hl : 𝔇.lk m = some l) (z : P) (s : First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) {tl : HTailF2} (ht : s.tl? = some tl)
    (hf : s.funs? = some tl.funs) (h : (mgAll 𝔇 Mg).forms m (5 + 0) "small" (z, s) y w) :
    SmallAt (cellsAhead 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, s)) s w :=
  small_at9 𝔇 Mg m 0 .attention hsub runs_small.2.1 l hl z s y w ht hf h

theorem small_at9_head (m : ℕ) (hsub : 𝔇.links[m]? = some .head) (l : Link First.S Claim)
    (hl : 𝔇.lk m = some l) (z : P) (s : First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) {tl : HTailF2} (ht : s.tl? = some tl)
    (hf : s.funs? = some tl.funs) (h : (mgAll 𝔇 Mg).forms m (5 + 1) "small" (z, s) y w) :
    SmallAt (cellsAhead 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, s)) s w :=
  small_at9 𝔇 Mg m 1 .head hsub runs_small.2.2 l hl z s y w ht hf h

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.small_at9
#print axioms VerifiableInference.Desc.First.K8.small_at9_layers
#print axioms VerifiableInference.Desc.First.K8.small_at9_attention
#print axioms VerifiableInference.Desc.First.K8.small_at9_head
