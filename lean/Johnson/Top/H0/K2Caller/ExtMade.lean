-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/ExtMade.lean: the code switch: THE TABLE OF JOINTS' EXTRACTOR AT A SWITCH
LEAVES THE NEW MEMBERS' MESSAGES: so the premise hExt of `k02_good_wit` (TopWit.lean) holds by the
make of the two readings of the witness.

Main names:
  `msgsOf_ext`: an extractor that lays no message, and pads at the tenants minePad alone (`extAt` at
    mine := [], Johnson/Desc/Sound/World.lean), leaves the typed messages (`msgsOf`,
    Johnson/Desc/Sound/MsgSig.lean) of every sending none of whose members is held by one of these
    tenants. By `extAt_other` and `extAt_other_pad`.
  `wtMade_ext`: so `wtMade` (Johnson/Top/H0/K2Caller/BehindSig.lean) is the same at the extractor's
    value.
Limits. That no tenant of the new sending is among the kept old ones is a premise: a fact on the
plan's numbers. That the piece's extractor is `extAt` at these lists is the table's `EachExtQ`.
Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.TopWit
import Johnson.Top.H0.K2Caller.BehindSig
import Johnson.Desc.Sound.World

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc (FileDescription Strs Wit)
open VerifiableInference.Desc.Sound (MsgT msgsOf Sending Mem seatOf extAt extAt_other
  extAt_other_pad)

section
variable (cs : Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (c₀ : Cells)

/-- **An extractor that lays pads alone leaves the messages of every member that none of these
tenants holds.** l: a sending's typed list, with the tree and tenant of each member. -/
theorem msgsOf_ext (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (minePad : List Mem)
    (tokNew : Option Tok) (a : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (hs : ∀ i, seat i ∉ minePad.map seatOf) :
    msgsOf cs l seat arr (extAt cs G arr smp decT c₀ [] minePad false tokNew a y w) =
      msgsOf cs l seat arr w := by
  have hm : ∀ n, (extAt cs G arr smp decT c₀ [] minePad false tokNew a y w).msg n = w.msg n :=
    fun n => extAt_other cs G arr smp decT c₀ [] minePad false tokNew a y w n (by simp)
  have hp : ∀ i, (extAt cs G arr smp decT c₀ [] minePad false tokNew a y w).pad (seat i).1
      (seat i).2 = w.pad (seat i).1 (seat i).2 :=
    fun i => extAt_other_pad cs G arr smp decT c₀ [] minePad false tokNew a y w (seat i).1
      (seat i).2 (by simpa using hs i)
  funext i j
  rcases j with q | q
  · show (extAt cs G arr smp decT c₀ [] minePad false tokNew a y w).tab cs (l.get i).1
      (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 false q.1.val q.2.val =
        w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 false q.1.val q.2.val
    unfold Wit.tab
    rw [hm, hp]
  · show (extAt cs G arr smp decT c₀ [] minePad false tokNew a y w).tab cs (l.get i).1
      (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 true q.1.val q.2.val =
        w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 true q.1.val q.2.val
    unfold Wit.tab
    rw [hm, hp]

/-- **So the typed witness behind, made of a witness of the table of joints, is the same at what
    such
an extractor gives**: the premise hExt of `k02_good_wit` (TopWit.lean) at inW _ w := the
    sub-protocol's
extractor's value at `wtMade` of w, and wtOf _ w := `wtMade` of w. -/
theorem wtMade_ext {r : SwRow} {H : r.OK}
    (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (smp' : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf r.cs s.l).om i).Smp)
    (seat : Fin r.l.length → ℕ × ℕ) (minePad : List Mem) (tokNew : Option Tok) (a : A) (y : Strs)
    (w : Wit Cells Tok MsgT) (hs : ∀ i, seat i ∉ minePad.map seatOf) :
    wtMade iJ iQ seat arr (extAt r.cs G arr smp' decT c₀ [] minePad false tokNew a y w) =
      wtMade iJ iQ seat arr w := by
  unfold wtMade
  rw [msgsOf_ext r.cs G arr smp' decT c₀ r.l seat minePad tokNew a y w hs]

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.wtMade_ext
#print axioms VerifiableInference.Desc.First.K2Caller.msgsOf_ext
