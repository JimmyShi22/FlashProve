-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PinP.lean: THE PIN WITH A PROMISE SLOT, AND THE PROMISE BEHIND THE KIND.
Two steps towards a table of borders whose items lean on a promise: (1) the item that pins the
world's part may fix it UNDER a clause of the promise in front, and the relation behind is asked for
the item only where the kind's own promise behind holds; (2) a promise that reads of the record what
the hearing's seat keeps, and of the oracles what lies below the base, rides from the statement in
front to the statement behind.

Main names:
  `PinItemP`: PinItem (Att/K05Seam.lean) with one field more, `ok`, and `fixes` under it: two worlds
    with the item at one statement AT WHICH ok HOLDS have one part. `PinItem.toP`: a PinItem is one
    at ok := True. `mOfItemP`: the part that the item fixes at a statement; `mOfItemP_toP`: at a
    PinItem it is mOfItem. `K05_goodIn_cap_of_P`: K05_goodIn_cap, to the letter, is K05_goodIn_capP
    at I.toP: nothing handed in falls.
  `seam_pin_itemP`: the law's premise "pin" at the kind's piece, at any ds, from hon (the condition
    in front gives ok) and hR' (WHERE LaidBehind HOLDS the relation behind gives the item).
  `K05_goodIn_anyDsP`, `K05_goodIn_capP`, `K05_goodIn_means_capP`: the law at the widest form
    (Att/K05AtCap.lean: any plain stretch with the kind's entries, any test on the plan, the errors
    bearErr | Err.cap kc) with such an item.
  `goodIn_on'_mono`: GENERAL, for every piece: Piece.GoodIn bears a weaker promise behind; the
    condition in front and the piece's own output may be used.
  `laid_rides`: at seatSO: q (rc b.1) b.2 holds at every b with LaidBehind, if rc has ReadsRest
    (Att/K05SeatKeeps.lean), q is carried along SameBelow, and the condition in front gives q.
  `K05_goodIn_promise`: the law at the cap with the promise behind LaidBehind ∧ q.

Why the slot. A pin by membership ("the witness's message is one of the committed word's list that
meets the sample") fixes the message only beside "no two members meet the sample alike", which a
table may hold in its promise and in no item; a pin by a decoder with a sample fixes it outright.
The slot serves both: ok := that clause, or True. ok is spent in front alone: it need not ride.
Limits. SILLY FILLINGS: ok := False makes hon say that "on" is empty: the law is idle; holds :=
False and a constant part as at PinItem: a shape shuts none of them. No item and no promise of a
table is typed here: Rc, rc, ok, holds, part, q are letters. A clause that reads the count of rows
owed, the open segment's ledger or what its own rounds have heard does not ride by laid_rides: these
turn. The premises of the laws are those of K05AtCap.lean's: NONE IS SHOWN HERE. NO MEMBER OF THE
WHOLE.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05AtCap
import Johnson.Desc.First.Att.K05SeatKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)
open VerifiableInference.Desc.Sound (Frame Piece)

/-! ## The item with a promise slot -/

/-- **An item of a border that pins the world's part, under a clause of the promise in front.** -/
structure PinItemP {S : Type} (F : Frame) (seat : Seat S) (base : ℕ) (W Mg : Type) where
  /-- what the item reads of the record -/
  Rc : Type
  rc : S → Rc
  /-- the clause of the promise in front on which the item leans -/
  ok : Rc → F.E.Str → Prop
  holds : Rc → F.E.Str → W → Prop
  part : W → Mg
  /-- under that clause, two worlds with the item at one statement have one part -/
  fixes : ∀ r y w w', ok r y → holds r y w → holds r y w' → part w = part w'
  /-- the seat's lay keeps what the item reads of the record -/
  lay : ∀ s h G s', seat.lay s h G = some s' → rc s' = rc s
  /-- the item reads the stored table and trees below the base alone -/
  fenced : ∀ r y y' w, SameBelow F base y y' → holds r y' w → holds r y w

section
variable {S Cl W Mg : Type} {F : Frame}

/-- A PinItem is one whose clause is free. -/
def PinItem.toP {seat : Seat S} {base : ℕ} (I : PinItem F seat base W Mg) :
    PinItemP F seat base W Mg :=
  ⟨I.Rc, I.rc, fun _ _ => True, I.holds, I.part, fun r y w w' _ => I.fixes r y w w', I.lay,
    I.fenced⟩

open Classical in
/-- The part that the item fixes at a statement; m0 where no world has the item there. -/
noncomputable def mOfItemP {seat : Seat S} {base : ℕ} (I : PinItemP F seat base W Mg) (m0 : Mg)
    (a : S × F.E.Str) : Mg :=
  if h : ∃ w, I.holds (I.rc a.1) a.2 w then I.part h.choose else m0

/-- At a PinItem the two readings of "the part that the item fixes" are one. -/
theorem mOfItemP_toP {seat : Seat S} {base : ℕ} (I : PinItem F seat base W Mg) (m0 : Mg) :
    mOfItemP I.toP m0 = mOfItem I m0 := rfl

/-- **The law's pin at the kind's piece, from an item with a promise slot.** -/
theorem seam_pin_itemP (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (ds : List RDT) (err : Err (uLT (ckP .two) ds)) (I : PinItemP F seat base W Mg) (m0 : Mg)
    (on : S × F.E.Str → Prop) (hon : ∀ a, on a → I.ok (I.rc a.1) a.2)
    (R' : S × F.E.Str → W → Prop)
    (hR' : ∀ b w, LaidBehind F seat p base on b → R' b w → I.holds (I.rc b.1) b.2 w)
    (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) ds)) (b : S × F.E.Str) (w : W) (ha : on a)
    (h : (k5Piece (W := W) (ckP .two) F seat claims p base ds err).ior.red.out a τ = some b)
    (hw : R' b w) : I.part w = mOfItemP I m0 a := by
  have hL := seam_on' seat claims p base ds err on a τ b ha h
  have hb := hR' b w hL hw
  obtain ⟨h1, _, _⟩ := seam_yes seat claims p base ds err a τ b h
  obtain ⟨_, _, hh, G, _, _, hy⟩ := (decide_lays seat p a.1 b.1 _).1 h1
  rw [I.lay _ _ _ _ hy] at hb
  have k : I.holds (I.rc a.1) a.2 w :=
    I.fenced _ _ _ _ (piece_same_below (k5Piece (W := W) (ckP .two) F seat claims p base ds err)
      a b τ h) hb
  have ex : ∃ w, I.holds (I.rc a.1) a.2 w := ⟨w, k⟩
  unfold mOfItemP
  rw [dif_pos ex]
  exact I.fixes _ _ _ _ (hon a ha) k ex.choose_spec

/-- `GoodIn` bears a weaker promise behind. -/
theorem goodIn_on'_mono {C : PQ.CK} (P : Piece C F S Cl W) {on on' on'' : S × F.E.Str → Prop}
    {R R' : S × F.E.Str → W → Prop} (h : P.GoodIn on on' R R')
    (hm : ∀ a τ b, on a → P.ior.red.out a τ = some b → on' b → on'' b) :
    P.GoodIn on on'' R R' := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb => ⟨hm a τ b ha hb (hτ b hb).1, (hτ b hb).2⟩) (h a ha)

end

/-- **A promise that reads what the seat keeps and what lies below the base rides.** -/
theorem laid_rides {F : Frame} (p : Par) (base : ℕ) (on : First.S × F.E.Str → Prop) {Rc : Type}
    (rc : First.S → Rc) (hrc : ReadsRest rc) (q : Rc → F.E.Str → Prop)
    (hq : ∀ r y y', SameBelow F base y y' → q r y → q r y')
    (hon : ∀ a, on a → q (rc a.1) a.2) (b : First.S × F.E.Str)
    (hb : LaidBehind F seatSO p base on b) : q (rc b.1) b.2 := by
  obtain ⟨a, _, G, h, _, ha, _, _, _, _, _, hy, hs⟩ := hb
  rw [seatSO_keeps rc hrc _ _ _ _ hy]
  exact hq _ _ _ hs (hon a ha)

section
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

open Classical in
/-- **The law at any plain stretch, with an item that leans on the promise in front.** -/
theorem K05_goodIn_anyDsP {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (m0 : (attSg x D rad).Msg)
    (hon : ∀ a, on a → I.ok (I.rc a.1) a.2)
    (R' : First.S × Fr.E.Str → W → Prop)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (hR' : ∀ b w, LaidBehind Fr seatSO p base on b → R' b w → I.holds (I.rc b.1) b.2 w) :
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w,
        bearErr ds _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' :=
  K05_keepsW_left_seats x tl D rad Ex Wp α claim hA H hfs hok p hp ns nx k j0 ds
    (k5Piece (W := W) (ckP .two) Fr seatSO claims p base ds
      (bearErr ds _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).ior.red.out
    (fun a => a.1) (fun b => b.1) x0 yOf on gOf pl hleft
    (fun a τ b _ h => seam_yes seatSO claims p base ds _ a τ b h)
    (fun a τ b h => seam_pass seatSO claims p base ds _ a τ b h)
    hd he I.part (mOfItemP I m0) (LaidBehind Fr seatSO p base on) R'
    (fun a τ b ha h => seam_on' seatSO claims p base ds _ on a τ b ha h) hb
    (fun a τ b w ha h hw =>
      seam_pin_itemP seatSO claims p base ds _ I m0 on hon R' hR' a τ b w ha h hw)

open Classical in
/-- **The same at the cap.** -/
theorem K05_goodIn_capP {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (m0 : (attSg x D rad).Msg)
    (hon : ∀ a, on a → I.ok (I.rc a.1) a.2)
    (R' : First.S × Fr.E.Str → W → Prop)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (hR' : ∀ b w, LaidBehind Fr seatSO p base on b → R' b w → I.holds (I.rc b.1) b.2 w)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (kc : ℕ)
    (hc : k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true) :
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w,
        Err.cap kc (uLT (ckP .two) ds)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' := by
  have hid := (OnBytes.Road.L5.plan_shape hA).1
  have PA := plan_all hid hok
  obtain ⟨_, _, _, _, _, _, _, U⟩ := PA.units
  have hrec : p.own = recOf (closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))) A.own.rows :=
    hp.trans (rec_of_plan hA PA.law.place (OnBytes.Road.Rows.norm_of_hid hid)
      (Nat.le_of_succ_le (OnBytes.Road.Rows.sizes_of_hid hid).lnT) U _ rfl rfl rfl)
  exact goodIn_err_le _ base ds [] _
    (Err.le_cap_of_below_inv kc _ (K05_below_fmt _ rfl A.own.rows p hrec Ex kc ds he hkind hc))
    (K05_goodIn_anyDsP x tl D rad Ex Wp α claim ok hA H hfs hok claims p hp ns nx k j0 base ds hd he
      x0 yOf on gOf pl hleft I m0 hon R' hb hR')

open Classical in
/-- **Nothing handed in falls**: K05_goodIn_cap (Att/K05AtCap.lean), to the letter, is
K05_goodIn_capP at
the item I.toP: ok := True; hR' asked at every b gives it where LaidBehind holds. -/
theorem K05_goodIn_cap_of_P {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItem Fr seatSO base W (attSg x D rad).Msg) (m0 : (attSg x D rad).Msg)
    (R' : First.S × Fr.E.Str → W → Prop)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (kc : ℕ)
    (hc : k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true) :
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w,
        Err.cap kc (uLT (ckP .two) ds)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' :=
  K05_goodIn_capP x tl D rad Ex Wp α claim ok hA H hfs hok claims p hp ns nx k j0 base ds hd he
    x0 yOf on gOf pl hleft I.toP m0 (fun _ _ => trivial) R' hb (fun b w _ h => hR' b w h) hkind kc hc

open Classical in
/-- **The same with what it means in front.** -/
theorem K05_goodIn_means_capP {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (m0 : (attSg x D rad).Msg)
    (hon : ∀ a, on a → I.ok (I.rc a.1) a.2)
    (R' : First.S × Fr.E.Str → W → Prop)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (hR' : ∀ b w, LaidBehind Fr seatSO p base on b → R' b w → I.holds (I.rc b.1) b.2 w)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (kc : ℕ)
    (hc : k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true) :
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w,
        Err.cap kc (uLT (ckP .two) ds)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => OwnMeans x A.S tl D rad (x0 a).2.1.pt (I.part w)) R' :=
  goodIn_conseq _
    (K05_goodIn_capP x tl D rad Ex Wp α claim ok hA H hfs hok claims p hp ns nx k j0 base ds hd he
      x0 yOf on gOf pl hleft I m0 hon R' hb hR' hkind kc hc)
    (fun _ _ _ _ _ _ _ h => h)
    (fun a _ _ w _ _ _ _ h => K05_means x tl D rad Ex Wp α hA ns _ (x0 a) (I.part w) h)

open Classical in
/-- **The law at the cap, with a promise behind that has ridden.** -/
theorem K05_goodIn_promise {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (m0 : (attSg x D rad).Msg)
    (hon : ∀ a, on a → I.ok (I.rc a.1) a.2)
    (R' : First.S × Fr.E.Str → W → Prop)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (hR' : ∀ b w, LaidBehind Fr seatSO p base on b → R' b w → I.holds (I.rc b.1) b.2 w)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (kc : ℕ)
    (hc : k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true)
    {Rq : Type} (rq : First.S → Rq) (hrq : ReadsRest rq) (q : Rq → Fr.E.Str → Prop)
    (hq : ∀ r y y', SameBelow Fr base y y' → q r y → q r y')
    (honq : ∀ a, on a → q (rq a.1) a.2) :
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w,
        Err.cap kc (uLT (ckP .two) ds)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (fun b => LaidBehind Fr seatSO p base on b ∧ q (rq b.1) b.2)
      (fun a w => OwnMeans x A.S tl D rad (x0 a).2.1.pt (I.part w)) R' :=
  goodIn_on'_mono _
    (K05_goodIn_means_capP x tl D rad Ex Wp α claim ok hA H hfs hok claims p hp ns nx k j0 base ds
      hd he x0 yOf on gOf pl hleft I m0 hon R' hb hR' hkind kc hc)
    (fun _ _ b _ _ hL => ⟨hL, laid_rides p base on rq hrq q hq honq b hL⟩)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seam_pin_itemP
#print axioms VerifiableInference.Desc.First.Att.P.goodIn_on'_mono
#print axioms VerifiableInference.Desc.First.Att.P.laid_rides
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_anyDsP
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_capP
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_cap_of_P
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_means_capP
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_promise
