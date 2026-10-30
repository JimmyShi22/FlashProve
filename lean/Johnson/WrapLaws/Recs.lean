-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WrapLaws/Recs.lean: the honest sides of the game that the reduction wrapW
(Johnson/WholeKey/Wrap.lean) plays against. One definition. This file states no goal of the release.

  recsG a   (namespace OnBytes.WrapLaws) out of the three honest sides of the scheme's letters
            (AtRecs, Johnson/WholeKey/Premises.lean), in the form of the game (RecsG,
            Hiop/Seeded/Game.lean: one honest side for each number of an encoded index): the first
            table's and the link's at every number; the session's on the encoded index number e is
            that for the number of the copy at the place e - 1 of the key's list, as simsG
            (Johnson/WholeKey/Wrap.lean) has it for the simulators.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Premises
import Hiop.Seeded.Game

set_option autoImplicit false

noncomputable section

namespace OnBytes.WrapLaws
open OnBytes.WholeKey Hiop.Seeded
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The game's honest sides. -/
def recsG (a : AtRecs lam L Bd aT aL) : RecsG L :=
  ⟨fun _ => a.Hs.T, fun _ => a.Hs.Lk, fun e => sessionAt a.Hs (a.nm (e - 1))⟩

end OnBytes.WrapLaws
