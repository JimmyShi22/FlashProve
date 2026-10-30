-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TypedFirst.lean: THE FIRST CONJUNCT OF
`T3At.typed` (Johnson/Top/H0/Tw/K2C/TieThreeR.lean) AT THE CALLER's LETTERS: at what an accept of
the code switch gives, every row that the switch lays has, inside the tables, no coefficient but at
a typed entry of the new sending. A call of `only_at_yes_light` (K2C/OnlyAtLight.lean) at the values
of LawAt.lean, after the pattern of `lawAfter_of` (AfterAt.lean).

  onlyAt_letters   at any letters X
  typed_first      at the plain letters: the sentence under "∀ ρ ∈ rows" in `T3At.typed`, in the
                   binders of `k02_t3R`'s premise hAt, with the drawn positions' range beside

Limits. `CallerAt`, `FrontLight`, `Held` and the range stay premises. The range is not among what
hAt has in hand: it follows from "the decision accepts" (`K2.inRangeOfYes`), which `seated_atYes`
has and does not hand on. `T3At` itself is not imported: the sentence is held against it by reading.
Shown at no real state. No soundness statement.

-/
import Johnson.Top.H0.K2Caller.AfterAt
import Johnson.Top.H0.K2Caller.Member
import Johnson.Top.H0.Tw.K2C.OnlyAtLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands

/-- **At any letters.** -/
theorem onlyAt_letters {r : SwRow} {H : r.OK} (X : Letters r H)
    (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    {p : K2.P2} (h32 : p.logN ≤ 32) {W₀ : SwitchFrame} {mem row : (selR X).Kp → ℕ}
    {pl : (selR X).Kp → KeptPlace} {aOf : (selLoc X iJ iQ).hd.K → ℕ}
    {iOf : ∀ k, ((selLoc X iJ iQ).hd.o k).Z.S → ℕ} {t t' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {Gg : Group} {c : Code}
    (Y1 : K2.AtYes p t t' r₁ r₂ gs x y S3 Y rows Gg c)
    (C : CallerAt (selR X) r.cs r.l iJ iQ mem row pl W₀) (P : FrontLight r.cs r.l W₀ x)
    (Hh : Held S3 W₀ aOf iOf) (hlen : r₂.drawn.poss.length = baseCount r.set .request r.g)
    (hin : ∀ v ∈ r₂.drawn.poss, v < 2 ^ p.logN) :
    ∀ ρ ∈ rows, OnlyAt r.cs r.l (fun i => x.st.oracles.size + i) (Inside (selR X).s W₀ pl) ρ :=
  only_at_yes_light (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ h32 Y1 C P Hh hlen hin

/-- **At the plain letters: `T3At.typed`'s first conjunct.** -/
theorem typed_first {r : SwRow} (H : r.OK)
    (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    {p : K2.P2} (h32 : p.logN ≤ 32) {W₀ : SwitchFrame}
    {mem row : (selR (Letters.plain r H)).Kp → ℕ} {pl : (selR (Letters.plain r H)).Kp → KeptPlace}
    {aOf : (selLoc (Letters.plain r H) iJ iQ).hd.K → ℕ}
    {iOf : ∀ k, ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S → ℕ} {t t' : Rec}
    {r₁ r₂ : Fmt.RoundView} {gs : Gs} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement}
    {Y : Array E} {rows : List OnBytes.Row} {Gg : Group} {c : Code}
    (Y1 : K2.AtYes p t t' r₁ r₂ gs x y S3 Y rows Gg c)
    (C : CallerAt (selR (Letters.plain r H)) r.cs r.l iJ iQ mem row pl W₀)
    (P : FrontLight r.cs r.l W₀ x) (Hh : Held S3 W₀ aOf iOf)
    (hlen : r₂.drawn.poss.length = baseCount r.set .request r.g)
    (hin : ∀ v ∈ r₂.drawn.poss, v < 2 ^ p.logN) :
    ∀ ρ ∈ rows, OnlyAt r.cs r.l (fun i => x.st.oracles.size + i)
      (Inside (selR (Letters.plain r H)).s W₀ pl) ρ :=
  onlyAt_letters (Letters.plain r H) iJ iQ h32 Y1 C P Hh hlen hin

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.onlyAt_letters
#print axioms VerifiableInference.Desc.First.K2Caller.typed_first
