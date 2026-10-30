-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/FillsK1.lean: WHAT K01_law ASKS OF THE MEANING Mg: NINE EQUATIONS, A LIGHT FILE.
Three fields are stated over letters of their own, so that the structure has a member both at the composed meaning and at a wider meaning laid over it:
  inOrder   Mg.inOrder a = (io0 a && inOrderK13 …): io0: whatever else "in order" says (at the composed meaning, under plus13: the base's own and the test on the public part)
  pub       Mg.pub = pubAll D base: base: what answers where no part of pubAll does (under plus13: the eight struck names' own tests, over the base's)
  pubP      Mg.pubP = (fillK3 X3 D3 MgP).pubP: MgP: the meaning beneath the lookups' part
  more      has no equation in this structure.
What is not claimed. That any meaning meets them (the member is a file of its own). Nothing on soundness.

-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.SmpRows
import Johnson.Desc.First.PubAll
import Johnson.Desc.First.Look.K3Fill
import Johnson.Desc.K13.Law.FillK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S Pub Meaning PubData pubAll)
open VerifiableInference.Desc.Sound (Sending Mem MsgT shownJT noCollJT pinJT decodesOf pinWOf)

/-- **K1's premises on the meaning.** -/
structure FillsK1 {Pp Xi Cells Tok : Type} (D : PubData) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (shape : Params.ReqShape) (layout : Params.ReqLayout) (io0 : Pp × S → Bool)
    (base : Pub → Pp × S → Bool) (X3 : OnBytes.Model.Verify.Public) (D3 : First.Look.Sent)
    (MgP Mg : Meaning Pp (Wit Cells Tok MsgT)) : Prop where
  held : Mg.held = fun j t a => smpHeld a.2.st a.2.book j t
  shown : Mg.shown = shownJT D.cs G ms
  noColl : Mg.noColl = noCollJT D.cs G smp ms
  pin : Mg.pin = pinJT D.cs G arr smp ms
  decodes : Mg.decodes = decodesOf decT
  pinW : Mg.pinW = pinWOf decT
  inOrder : ∀ a, Mg.inOrder a = (io0 a && K13.Law.inOrderK13 D.cs shape layout a.2)
  pub : Mg.pub = pubAll D base
  pubP : Mg.pubP = (First.Look.fillK3 X3 D3 MgP).pubP

end VerifiableInference.Desc.K1
