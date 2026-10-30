-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchBack.lean: back across the code switch: what the block's knowledge soundness
says of a message that was held in the open word.

The block "SEND seed, LOC with a rider" is knowledge sound between two joints
(`Cb.Pv.SendLocRide.hAt`, Cb/Pv/Switch/SendLocRide.lean). Its extractor and the joint in front are
the library's; here they are written out at the two callers that are made of a cut, as far as a held
message goes. The extractor hands back, as the open word's message and tail, what the cut reads off
the new messages (`LdSendD.link`, Cb/Req1/LdSegKit.lean: the sending's `bk`). The joint in front
says, on its promise, that each held message's word, cut out of the open word, decodes with its
sample to its slots of the open word's message (`heldB`, same file: the second clause of `relR`).
Statements and proofs; no new reasoning.
Main names:
  `KObj.SwI.ext_is`, `front_dec`, `back_dec`: at a caller `KObj.SwI.size`
    (Johnson/Top/H/SwitchOf.lean): the extractor's value, by definition; the clause of the joint in
    front; the two together.
  `newOf`, `sel_ext_open`, `sel_back_dec`: the same at `switchSel` (Johnson/Top/H/SwitchSel.lean).
  `sel_doomed_dec`: under the kind's condition, at a statement in front that keeps the promise: the
    prover has lost, at the block's own errors, towards: whatever witness the joint behind holds of
    what the verifier puts out, each held message's word decodes with its sample to what the cut
    reads off that witness's new messages.
See also: Johnson/Top/H/SwitchHeldSel.lean says which entries of the new messages these are.
Limits: the joints are the chain's: a relation holds or the promise fails (`Rels.cf`); so the
promise in front is a premise, and where the promise behind fails the joint behind holds of every
witness. A held message's word is the slot of the TYPED open word (`hd.sW`): that this slot is the
word of the old message as it was sent is the fold's matter (`LdFoldD.Hyp.word`) and is not said
here. The errors are counts; nothing says that they are small. Nothing on a text of the programs.

-/
import Johnson.Top.H.SwitchOf
import Johnson.Top.H.SwitchSel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.SwI
open Iop IOR Cb

variable {E : Type} [Field E] [Fintype E] (c : SwI E)

/-- What the block's extractor hands back. -/
theorem ext_is (a : (Cb.Pv.SendLoc.stage c.sw).X × (Cb.Pv.SendLoc.stage c.sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R c.size).shape) (w : (Cb.Pv.SendLoc.loc c.sw).tgt.W) :
    Cb.Pv.SendLocRide.ext c.size a τ w =
      (c.S₀.left c.N (T := OMsg.Wit) w.1,
        (c.cutN (c.N.msgs (c.S₀.right c.N (T := OMsg.Wit) w.1)), w.2)) := rfl

/-- What the joint in front says of a held message. -/
theorem front_dec (a : (Cb.Pv.SendLoc.stage c.sw).X × (Cb.Pv.SendLoc.stage c.sw).Ex.Str)
    (w : (Cb.Pv.SendLoc.stage c.sw).W)
    (hon : ((Cb.Pv.SendLoc.stage c.sw).S.over (Cb.Pv.SendLoc.stage c.sw).A).on a)
    (h : (Cb.Pv.SendLocRide.inJ c.size).relR a w) (k : c.hd.K) :
    (c.hd.o k).decW (c.hd.sW k a.2.1.1) (a.1.1.1.2 k) = some (c.hd.msg w.2.1.1 k) :=
  (h.resolve_right (not_not.2 hon)).2.2.1 k

/-- **Back across the switch**: where the joint in front holds at what the extractor hands back, on
the promise: each held message's word, cut out of the open word, decodes with its sample to what
the cut reads off the new messages. -/
theorem back_dec (a : (Cb.Pv.SendLoc.stage c.sw).X × (Cb.Pv.SendLoc.stage c.sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R c.size).shape) (w : (Cb.Pv.SendLoc.loc c.sw).tgt.W)
    (hon : ((Cb.Pv.SendLoc.stage c.sw).S.over (Cb.Pv.SendLoc.stage c.sw).A).on a)
    (h : (Cb.Pv.SendLocRide.inJ c.size).relR a (Cb.Pv.SendLocRide.ext c.size a τ w))
    (k : c.hd.K) :
    (c.hd.o k).decW (c.hd.sW k a.2.1.1) (a.1.1.1.2 k) =
      some (c.hd.msg (c.cutN (c.N.msgs (c.S₀.right c.N (T := OMsg.Wit) w.1))).1 k) :=
  c.front_dec a _ hon h k

end KObj.SwI

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack

variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : Sh.Cf.J → (sigOf cs l).Ent) (iQ : Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

set_option quotPrecheck false in
local notation "zS" => switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw
set_option quotPrecheck false in
local notation "hdS" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd

/-- The new messages of a witness behind the switch. -/
noncomputable def newOf (w : (Cb.Pv.SendLoc.loc (zS).sw).tgt.W) : (sigOf cs l).Msg :=
  (sigOf cs l).msgs ((zS).sw.S₀.right (sigOf cs l) (T := OMsg.Wit) w.1)

/-- What the block's extractor hands back as the open word's message and tail. -/
theorem sel_ext_open (a : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R (zS)).shape) (w : (Cb.Pv.SendLoc.loc (zS).sw).tgt.W) :
    (Cb.Pv.SendLocRide.ext (zS) a τ w).2.1 =
      cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w) := rfl

/-- **Back across the switch, at the caller with two maps of names.** -/
theorem sel_back_dec
    (a : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R (zS)).shape) (w : (Cb.Pv.SendLoc.loc (zS).sw).tgt.W)
    (hon : ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).on a)
    (h : (Cb.Pv.SendLocRide.inJ (zS)).relR a (Cb.Pv.SendLocRide.ext (zS) a τ w))
    (k : (hdS).K) :
    ((hdS).o k).decW ((hdS).sW k a.2.1.1) (a.1.1.1.2 k) =
      some ((hdS).msg (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)).1 k) :=
  (h.resolve_right (not_not.2 hon)).2.2.1 k

/-- **The same under the block's knowledge soundness**: at a statement in front that keeps the
promise the prover has lost, at the block's own errors, towards: whatever the verifier puts out, and
whatever witness the joint behind holds of it, each held message's word decodes with its sample to
what the cut reads off that witness's new messages. -/
theorem sel_doomed_dec (hz : Cb.Pv.SendLocRide.OK (zS))
    (a : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (ha : (Cb.Pv.SendLocRide.inJ (zS)).on a)
    (hon : ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).on a) :
    Doomed (Cb.Pv.SendLocRide.R (zS)).shape (Cb.Pv.SendLocRide.eps (zS)) fun τ =>
      ∀ b w, (Cb.Pv.SendLocRide.R (zS)).red.out a τ = some b →
        (Cb.Pv.SendLocRide.outJ (zS)).relR b w → ∀ k : (hdS).K,
          ((hdS).o k).decW ((hdS).sW k a.2.1.1)
              (a.1.1.1.2 k) =
            some ((hdS).msg (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)).1 k) :=
  Doomed.mono _ _
    (fun τ hτ b w hb hw k =>
      sel_back_dec Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw a τ w hon (hτ b w hb hw) k)
    (Cb.Pv.SendLocRide.hAt (zS) hz a ha)

end Johnson.Top.H

#print axioms KObj.SwI.ext_is
#print axioms KObj.SwI.front_dec
#print axioms KObj.SwI.back_dec
#print axioms Johnson.Top.H.sel_ext_open
#print axioms Johnson.Top.H.sel_back_dec
#print axioms Johnson.Top.H.sel_doomed_dec
