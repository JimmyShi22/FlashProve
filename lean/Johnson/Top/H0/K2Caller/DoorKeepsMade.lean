-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/DoorKeepsMade.lean: the code switch (K2): THE FIELD hD OF ITS CONDITION
(Johnson/Top/H0/K2Ties/Assembly.lean: «the way out keeps what the law reads»), TO THE LETTER, FROM
ONE SENTENCE ON THE WAY OUT: KeepsOut leave (Johnson/Top/H0/K2Caller/DoorKeeps.lean). A new file
beneath the condition, which does not turn. A law file; no running text imports it.

  readKept_made   the three letters at which the field reads the state behind (no old sample · the
                  words BY MAKE off the oracles behind, strMadeB · no carried state) read nothing of
                  the state: so DoorKeeps.lean's named premise ReadKept holds of them outright.
  hD_of_keepsOut  KeepsOut leave ⟹ DoorKeeps (Letters.plain r H) iJ iQ p leave
                  (fbOf (Letters.plain r H) iJ iQ n0 b₀ (fun _ i => isEmptyElim i)
                    (strMadeB iJ iQ G seatN) (fun _ => ((), ()))): by doorKeeps_of.
WHAT STAYS: KeepsOut leave, at the way out of the door at which the sub-protocol sits: other files
pay it at the one door's own ways out. `P1K2.out_guards` | `out_head` | `out_finish` (Johnson/P1K2R/SitsDoor.lean) state KeepsOut of three ways out written there (the guards · "H.1.quiet", then the guards · "F.0.quiet", then the guards), under no premise; `out_opened` | `out_head_opened` state it of leaveOpened f and of "H.1.quiet", then leaveOpened f, under framesOf built first W = .ok fs and fs[l]? = some f.
Limits. Nothing on soundness.

-/
import Johnson.Top.H0.K2Caller.DoorKeeps
import Johnson.Top.H0.K2Caller.WordsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc (FileDescription)

variable {F : Frame} {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  {Xi : Type} (G : FileDescription Xi) (seatN : Fin r.l.length → ℕ × ℕ)

theorem readKept_made :
    ReadKept (F := F) (Letters.plain r H) iJ iQ (fun _ i => isEmptyElim i)
      (strMadeB iJ iQ G seatN) (fun _ => ((), ())) :=
  fun _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-- **The field hD.** -/
theorem hD_of_keepsOut (p : K2.P2) {leave : Rec → Rec → Except String Rec} (hk : KeepsOut leave)
    (n0 : ℕ) (b₀ : TB (Letters.plain r H) iJ iQ) :
    DoorKeeps (F := F) (Letters.plain r H) iJ iQ p leave
      (fbOf (Letters.plain r H) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seatN)
        (fun _ => ((), ()))) :=
  doorKeeps_of (Letters.plain r H) iJ iQ p hk n0 b₀ _ _ _ (readKept_made iJ iQ G seatN)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.readKept_made
#print axioms VerifiableInference.Desc.First.K2Caller.hD_of_keepsOut
