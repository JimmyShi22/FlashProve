-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/FromGood.lean: who has the plain law already. Four small theorems.

  `keeps_of_goodIn`: a piece with `Piece.GoodIn` (Johnson/Desc/Sound/GoodIn.lean) has `Keeps`, at
    the languages "there is a witness", at the same errors.
  `leads_map2_of_goodIn`: a piece with `Piece.GoodIn` whose extractor, at a yes, is a named map E of
    the two statements and the world has the plain law "the promise behind is kept; for every world
    w: behind at w gives in front at E a b w".
  `goodIn_of_keeps`: at W := Unit the two are one: `Keeps` gives `GoodIn` at the relations that
    forget the witness, whatever the piece's extractor is.
  `keeps_of_know`: a reduction with the library's `Know` that keeps the promise FOR CERTAIN has
    `Keeps`. WITHOUT THAT PREMISE `Know` (and `KnowInto`) GIVE `Leads` AT "a witness behind → a
    witness in front" ALONE (`Know.toLeads`), NOT `Keeps`: the promise is not paid.
Nearest kin: `GoodIn` (Johnson/Desc/Sound/GoodIn.lean); `keeps_of_know`:
`Cb.Pv.FoldSeam.knowInto_and` (not compared); `leads_map2_of_goodIn`: `sel_keeps`
(Johnson/Top/H/SwitchKeeps.lean) bears the same form at one kind.

-/
import Johnson.Desc.Plain.FoldChain
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound

variable {S Cl W : Type} {C : CK} {F : Frame}

theorem keeps_of_goodIn (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (h : p.GoodIn on on' R R') :
    p.ior.red.Keeps on on' (fun a => ∃ w, R a w) (fun b => ∃ w, R' b w) p.err := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb =>
    ⟨(hτ b hb).1, fun ⟨w, hw⟩ => ⟨p.ext a τ w, (hτ b hb).2 w hw⟩⟩) (h a ha)

/-- **ONE WITNESS ALONG THE STEP, THE EXTRACTOR NAMED**: where the block's extractor is, at every
yes, a named map E of the two statements and the world: the plain law "the promise behind is kept;
for every world w: behind at w gives in front at E a b w". No "there is". -/
theorem leads_map2_of_goodIn (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (E : S × F.E.Str → S × F.E.Str → W → W)
    (h : p.GoodIn on on' R R')
    (hx : ∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w = E a b w) :
    p.ior.red.Leads on (fun a b => on' b ∧ ∀ w, R' b w → R a (E a b w)) p.err := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb =>
    ⟨(hτ b hb).1, fun w hw => hx a τ b w hb ▸ (hτ b hb).2 w hw⟩) (h a ha)

theorem goodIn_of_keeps (p : Piece C F S Cl Unit) (on on' L L' : S × F.E.Str → Prop)
    (h : p.ior.red.Keeps on on' L L' p.err) :
    p.GoodIn on on' (fun a _ => L a) (fun b _ => L' b) := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b hb => ⟨(hτ b hb).1, fun _ hw => (hτ b hb).2 hw⟩) (h a ha)

theorem keeps_of_know {A B WA WB : Type} {K : Reduction A B} {on : A → Prop} {on' : B → Prop}
    {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Iop.Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : K.Know on RA RB ext ε)
    (carry : ∀ a τ b, on a → K.out a τ = some b → on' b) :
    K.Keeps on on' (fun a => ∃ w, RA a w) (fun b => ∃ w, RB b w) ε :=
  h.toLeads.conseq (fun _ h => h) fun a τ b ha hb hq => ⟨carry a τ b ha hb, hq⟩

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.keeps_of_goodIn
#print axioms VerifiableInference.Desc.Plain.leads_map2_of_goodIn
#print axioms VerifiableInference.Desc.Plain.goodIn_of_keeps
#print axioms VerifiableInference.Desc.Plain.keeps_of_know
