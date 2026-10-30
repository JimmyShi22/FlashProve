-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupRideStd.lean: this file is for toys (a toy: a small example instance). Book-keeping for
a prover message with several oracle messages: the further oracle messages that go out with a
closing's one sending (riders) are made by one generic sender (the standard sender) from a table
that sorts each message's coordinates, and their coordinates get names in the statement after the
verifier's queries.

Definitions, statements as theorems, proofs. Generic.
Closing (lean/GLOSSARY.md): the last part of a test, of the link or of a segment.
Locations (lean/GLOSSARY.md): the one-round step in which the prover sends nothing and the verifier
draws long positions of an open word and reads it there.

Why: Cb/Ld/LdGroupNewRide.lean takes the riders of a closing's one sending with a sender for each
member. Cb/Ld/LdSendStdL.lean has the standard sender of a given family from a layout of its
messages (data read off the witness; free entries: coins: masks of coming blocks; pads). Here the
two are joined.

Main names:
  `rideStd_ok`: `Y.OK t`, the codes' laws, the lists, evading samples ⇒ `(RideD.std ..).OK`
    (`RideD.OK`: its six clauses are told in the head of Cb/Ld/LdGroupNewRide.lean).
  `rideStd_far`: the data are read off the further witness alone ⇒ `(RideD.std ..).Far`
    (Cb/Req1/LdSegRefPackSLay.lean).
  `V.rideAt .. n`: an entry of a rider, as an entry of the oracle messages after the locations.
    `stdNewR_rideAt_inj`: injective. `stdNewR_rideAt_new`: it is no entry of a new message (nor, by
    its form, of a message that crossed the closing): so no row that the locations leave reads it
    (Cb/Ld/LdGroupNewRide.lean: `stdNewR_rows_new`). These three need `G.P`, the group's set of
    common long positions, to be nonempty.

Limits: this file does not say that masks at free entries of a rider are fresh behind the segment
(Cb/Ld/LdGroupRideStdFresh.lean, Cb/Ld/LdGroupNewRideWFresh.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefPackSLay
import Cb.Ld.LdSendStdL
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {F E W : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (N : Sig E)
  (Y : N.StdL F) (dat : W → ∀ a, Y.Dt a → E) (w0 : W) (L t : N.O → ℕ)

/-- Riders under the standard sender. -/
@[reducible] def RideD.std : RideD E W := ⟨N, Y.mem dat w0, L, t⟩

theorem rideStd_ok (h : Y.OK t) (hl : ∀ a, (N.om a).C.Laws)
    (hs : ∀ a, (N.om a).ListLE (L a)) (he : ∀ a, (N.om a).Evades) :
    (RideD.std N Y dat w0 L t).OK where
  laws := hl
  list := hs
  evades := he
  enc := fun b m r => h.enc b m r
  blind := fun b => ldSend_blind_of_uniform E (N.om b) W Unit _ (Y.unifM dat w0 h b)
  hides := h.hides

end

theorem rideStd_far {F E Wl Wr : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (N : Sig E) (Y : N.StdL F) (dat : Wl × Wr → ∀ a, Y.Dt a → E) (w0 : Wl × Wr) (L t : N.O → ℕ)
    (h : ∀ w w' : Wl × Wr, w'.2 = w.2 → dat w' = dat w) :
    (RideD.std N Y dat w0 L t).Far := fun b w w' k hw => by
  show Y.msgOf b (Sum.elim (dat w' b) k.1) k.2 = Y.msgOf b (Sum.elim (dat w b) k.1) k.2
  rw [h w w' hw]

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ)
  (Rd : RideD E ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp))

/-- an entry of a rider, after the locations -/
def StdNew.rideAt (n : Rd.N.Ent) : (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.S.Ent :=
  ⟨.inr (.inr n.1), n.2⟩

theorem stdNewR_rideAt_inj : Function.Injective (V.rideAt Sb sl Z A₀ w0 L t tl Rd) := by
  rintro ⟨a, j⟩ ⟨a', j'⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  obtain rfl : a = a' := Sum.inr.inj (Sum.inr.inj h1)
  exact congrArg (Sigma.mk a) (eq_of_heq h2)

theorem stdNewR_rideAt_new (n : Rd.N.Ent) (a : V.N.N₀.O) :
    (V.rideAt Sb sl Z A₀ w0 L t tl Rd n).1 ≠ .inr (.inl a) :=
  fun h => by cases Sum.inr.inj h

end
end Cb
