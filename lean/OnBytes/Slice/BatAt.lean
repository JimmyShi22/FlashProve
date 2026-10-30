-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BatAt.lean: two of the conditions on the batching round of the written link.

OnBytes/Slice/BlockBat.lean names conditions on the sizes and the main code (`BatOK`), on what six
rounds send and draw (`BatDraws`), and on the columns (`ColTie`). `batOK_of`: the first, for a stage
whose codes fit their length (OnBytes/Slice/Numbers.lean: `Sg.Sized`) and a radius e at most eU and
below its distance. `batDraws_of`: the second, for the format's six rounds.











Main theorems: `batDraws_of`, `batOK_of`.

Not claimed. Nothing at half the distance or beyond. `ColTie`; `BatHolds`
(OnBytes/Slice/BlockHolds.lean) of any stage; a bound on lists. No round is taken off here.
-/
import OnBytes.Slice.BatCol
import OnBytes.Slice.BlockHolds
import OnBytes.Slice.Numbers
import OnBytes.Slice.RoundsOf
import Run.PlanQXFastR
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M3Entry
import OnBytes.Slice.ToySg
import OnBytes.Slice.RoundsLink
import OnBytes.Slice.LinkAt

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The six rounds send and draw what the block asks, if they are the format's. -/
theorem batDraws_of (S : Sz) (d1 d2 d3 d4 d5 dA : PQ.RD) (work rows : ℕ)
    (h1 : IsRd d1 (Fmt.M3.rLinkPoint S.P.v)) (h2 : IsRd d2 (Fmt.M2.rSeedN (S.P.aR + S.P.aP)))
    (h3 : IsRd d3 (Fmt.M2.rAnswers 2))
    (h4 : IsRd d4 (Fmt.M3.rLink work (S.P.nu0 + S.P.nuj) S.P.T.a)) (ha : S.P.T.a ≤ 64)
    (h5 : IsRd d5 (Fmt.M3.rLinkPhi S.P.aPhi)) (hA : IsRd dA (Fmt.M2.rBatN rows)) :
    BatDraws S d1 d2 d3 d4 d5 dA :=
  ⟨rLinkPoint_sd h1, rSeedN_sd h2, rSeedN_nz h2, rAnswers_sd h3, rLink_sd h4 ha, rLinkPhi_sd h5,
    rBatN_sd hA⟩

/-- What the block asks of sizes, radius and main code, for a stage whose codes fit their length. -/
theorem batOK_of (S : Sz) (t e : ℕ) (hs : (S.sg t).Sized) (hf : S.P.fld = .two)
    (hh : S.P.high = true) (hl : S.P.C.l = 2 ^ S.P.aP) (he : e ≤ S.eU) (hd : e < (S.sg t).d) :
    BatOK S e (S.sg t).d :=
  ⟨⟨he, (Sg.fit_cM hs).dist, hd⟩, hf, hh, hl⟩



end OnBytes.Slice

#print axioms OnBytes.Slice.batDraws_of
#print axioms OnBytes.Slice.batOK_of
