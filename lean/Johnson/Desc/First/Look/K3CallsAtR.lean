-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsAtR.lean: the lookup on a link's CALLS: THE TIES OF THE FILLING
(AttTiesR, LayTiesR, Johnson/Desc/First/Look/K3CallsMeanR.lean) AND THE PARTS OF THE PROMISE BEHIND
(BehindPartsR, Johnson/Desc/First/Look/K3CallsBehindR.lean) FROM EQUATIONS ON THE MEANING, IN THE
SECOND FORM OF THE CHAIN OF PROMISES: K3CallsAt.lean's three theorems again: ownIn is a premise in
codesIn's place; fLive and askLive are gone: so of the kind's K3At the fields live and asks are
spent no more. PAID: of AttTiesR's 13 fields seven (pubIn, worthP, worthK, worthR, cf, pinIn,
pinBack); of LayTiesR's 15 the same seven; of BehindPartsR's 22 fourteen.
THE TEXT IS THE FIRST FORM's (Johnson/Desc/First/Look/K3CallsAt.lean), TURNED BY A PROGRAM, after
the pattern at the
head's calls (Johnson/Desc/First/Look/K3HeadAtTableR.lean); the law beneath is called as it lies;
the first form's file is not touched. NO SOUNDNESS IS CLAIMED.

USER: Johnson/Desc/Sound/MgAt/K3Calls.lean.
OBJECT, LETTERS: the first form's; and Rc (Rch): a condition on the statement that stands
  beside the table's promise in front (meant: "this verifier's state is reached from the state at
  the start by the sub-protocols in front"): A LETTER: no term is named here.

Main names: `attTies_ofR`, `layTies_ofR`, `behindParts_ofR`.

Limits. The first form's. Rc is a letter; ownIn is a premise, shown at no term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsAt
import Johnson.Desc.First.Look.K3CallsMeanR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open VerifiableInference.Desc (Strs)

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) {X : Verify.Public}
  {Dn : Desc.First.Look.Sent} {L : K3Letters Cells Tok} {N : Numbers}
  {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} (claim : Aff → Cl)
  {a a' : Desc.Place} {k l : ℕ} {x : Desc.First.Look.Place} {tl : HTailF2}
  {smp : Desc.First.S → (i : Fin (sigListCalls Dn L.rad x.link).length) →
    Option ((attSg x Dn L.rad).om i).Smp}
  {smpT : P × Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf Dn.codes s.l).om i).Smp}
  {ms : List Mem}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT)}
  (B' : Desc.Block Desc.First.S Cl) (z : P) {Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dn L.rad x.link).length =>
  L.seat x.link false j.1

/-! ## The ties -/

/-- **AttTiesR: seven of thirteen.** -/
theorem attTies_ofR {A : Attention.Shape} (hK : K3At X Dn L Mg)
    (hpin : Mg.pin = pinJT Dn.codes G L.arr smpT ms)
    (hnc : Mg.noColl = noCollJT Dn.codes G smpT ms)
    (hlook : lookAt X l false = some x) (hx : attAt X l = some (x, A, tl))
    (hp2 : Desc.K3.pieceAt X l false = 2)
    (T : ListSits G x Dn L.rad seatL smpT smp ms N l)
    (hbase : ∀ t ∈ N.sent l 0, t.1 < q.base)
    (hsm : ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v → ∀ e ∈ ms,
      smpT (z, v.1) e.1 e.2 = smpT (z, u.1) e.1 e.2)
    (cellsIn : planesInB x A tl = true)
    (ownIn : ∀ u : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      Rch k ((z, u.1), u.2) → u.1.failed = none → OwnIs Dn x.link u.1)
    (objects : ∀ u v : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      Rch k ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true → onQ N Mg linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, Mg.formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      attObjects x A tl Dn L.rad seatL L.arr (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard v.1 w)
    (model : ∀ s y w, AttSays x A tl Dn L.rad (attMs x Dn L.rad seatL L.arr w) →
      Mg.constr l .small (z, s) y w →
      Mg.constr l .lookCalls (z, s) y w ∧ Mg.constr l .rider (z, s) y w)
    (smallBack : ∀ (u v : Desc.First.S × Fr.E.Str) w,
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Mg.constr l .small (z, v.1) (strsOf Fr v.2) w →
      Mg.constr l .small (z, u.1) (strsOf Fr u.2) w)
    (decodes : ∀ u v : Desc.First.S × Fr.E.Str,
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Mg.decodes (z, u.1) (strsOf Fr u.2) → Mg.decodes (z, v.1) (strsOf Fr v.2)) :
    AttTiesR (Fr := Fr) G x A tl Dn L.rad SET seatL L.arr smp claim N Mg linksFull PS z k l
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) := by
  obtain ⟨f, hf⟩ := hK.worth
  refine
    { cellsIn := cellsIn
      pubIn := fun s h => fLook_at hK l false hlook z s (by rw [hp2]; exact h)
      worthP := fun s y w h => ?_
      worthK := fun s y w h => ?_
      worthR := fun s y w h => ?_
      cf := fun i s y _ _ h => calls_cf G T z i s y (by rw [hnc] at h; exact h)
      pinIn := fun s y w h => calls_pinIn G L.arr T z s y w (by rw [hpin] at h; exact h)
      pinBack := fun u v w hy _ h => by
        rw [hpin] at h ⊢
        exact calls_pinBack Dn.codes G L.arr smpT ms z (strictAt B' q) (N.sent l 0) hbase hsm u v
          w hy h
      ownIn := ownIn
      objects := objects
      model := model
      smallBack := smallBack
      decodes := decodes }
  · rw [hf, ← hp2, worthK3_att X Dn L f l hx] at h
    unfold worthAtt at h
    rw [if_pos rfl] at h
    exact h
  · rw [hf, ← hp2, worthK3_att X Dn L f l hx] at h
    unfold worthAtt at h
    rw [if_neg (by decide), if_pos rfl] at h
    exact h
  · rw [hf, ← hp2, worthK3_att X Dn L f l hx] at h
    unfold worthAtt at h
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at h
    exact h

/-- **LayTiesR: seven of fifteen.** -/
theorem layTies_ofR {smpW : Desc.First.S → Option L.oW.Smp} {strW : Fr.E.Str → L.oW.Str}
    (hK : K3At X Dn L Mg)
    (hpin : Mg.pin = pinJT Dn.codes G L.arr smpT ms)
    (hnc : Mg.noColl = noCollJT Dn.codes G smpT ms)
    (hlook : lookAt X l false = some x) (hna : attAt X l = none) (hx : layAt X l = some x)
    (ht : tlAt X l = some tl) (hp2 : Desc.K3.pieceAt X l false = 2)
    (T : ListSits G x Dn L.rad seatL smpT smp ms N l)
    (hbase : ∀ t ∈ N.sent l 0, t.1 < q.base)
    (hsm : ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v → ∀ e ∈ ms,
      smpT (z, v.1) e.1 e.2 = smpT (z, u.1) e.1 e.2)
    (tabIn : ∀ u : Desc.First.S × Fr.E.Str, Mg.decodes (z, u.1) (strsOf Fr u.2) →
      ∃ σW, smpW u.1 = some σW ∧ ¬ L.oW.Clash (strW u.2) σW.1)
    (pinWIn : ∀ (u : Desc.First.S × Fr.E.Str) w, Mg.pinW (z, u.1) (strsOf Fr u.2) w →
      ∃ σW, smpW u.1 = some σW ∧ L.oW.dec (strW u.2) σW = some (L.msgW w))
    (pinWOut : ∀ (u : Desc.First.S × Fr.E.Str) w,
      (∃ σW, smpW u.1 = some σW ∧ L.oW.dec (strW u.2) σW = some (L.msgW w)) →
      Mg.pinW (z, u.1) (strsOf Fr u.2) w)
    (ownIn : ∀ u : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      Rch k ((z, u.1), u.2) → u.1.failed = none → OwnIs Dn x.link u.1)
    (objects : ∀ u v : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      Rch k ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true → onQ N Mg linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, Mg.formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      layObjects x (pubAt X (l / Desc.First.Look.stepOf X)) tl Dn L.rad L.oW L.wOf L.nr L.nc seatL
        L.arr L.msgW (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w)
    (model : ∀ s y w, LaySays x (pubAt X (l / Desc.First.Look.stepOf X)) tl Dn L.rad L.oW L.wOf
        L.nr L.nc (layMs x Dn L.rad L.oW seatL L.arr L.msgW w) →
      Mg.constr l .small (z, s) y w → Mg.pinW (z, s) y w →
      Mg.constr l .lookCalls (z, s) y w ∧ Mg.constr l .rider (z, s) y w)
    (smallBack : ∀ (u v : Desc.First.S × Fr.E.Str) w,
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Mg.constr l .small (z, v.1) (strsOf Fr v.2) w →
      Mg.constr l .small (z, u.1) (strsOf Fr u.2) w)
    (decodes : ∀ u v : Desc.First.S × Fr.E.Str,
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Mg.decodes (z, u.1) (strsOf Fr u.2) → Mg.decodes (z, v.1) (strsOf Fr v.2)) :
    LayTiesR (Fr := Fr) G x (pubAt X (l / Desc.First.Look.stepOf X)) tl Dn L.rad L.oW L.wOf L.nr
      L.nc SET seatL L.arr smp smpW strW L.msgW claim N Mg linksFull PS z k l
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) := by
  obtain ⟨f, hf⟩ := hK.worth
  refine
    { pubIn := fun s h => fLook_at hK l false hlook z s (by rw [hp2]; exact h)
      worthP := fun s y w h => ?_
      worthK := fun s y w h => ?_
      worthR := fun s y w h => ?_
      cf := fun i s y _ _ h => calls_cf G T z i s y (by rw [hnc] at h; exact h)
      pinIn := fun s y w h => calls_pinIn G L.arr T z s y w (by rw [hpin] at h; exact h)
      pinBack := fun u v w hy _ h => by
        rw [hpin] at h ⊢
        exact calls_pinBack Dn.codes G L.arr smpT ms z (strictAt B' q) (N.sent l 0) hbase hsm u v
          w hy h
      tabIn := tabIn
      pinWIn := pinWIn
      pinWOut := pinWOut
      ownIn := ownIn
      objects := objects
      model := model
      smallBack := smallBack
      decodes := decodes }
  · rw [hf, ← hp2, worthK3_lay X Dn L f l hna hx ht] at h
    unfold worthLay at h
    rw [if_pos rfl] at h
    exact h
  · rw [hf, ← hp2, worthK3_lay X Dn L f l hna hx ht] at h
    unfold worthLay at h
    rw [if_neg (by decide), if_pos rfl] at h
    exact h
  · rw [hf, ← hp2, worthK3_lay X Dn L f l hna hx ht] at h
    unfold worthLay at h
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at h
    exact h

/-! ## The parts of the promise behind -/

/-- **BehindPartsR: fourteen of twenty-two**, at every sort of segment (pc := 2 + shift sub). -/
theorem behindParts_ofR {sub : ModelPart} {told : List (List Desc.Oracle)} {nsOf : ℕ → Option ℕ}
    (hK : K3At X Dn L Mg)
    (hnc : Mg.noColl = noCollJT Dn.codes G smpT ms)
    (hsh : Mg.shown = shownJT Dn.codes G ms)
    (hled : ∀ m u, Mg.pub (.ledger m) u = Desc.First.ledgerB u.2)
    (hfree : ∀ m u, Mg.pub (.freeAbove m) u = (nsOf m).any fun n => Desc.First.freeAboveB n u.2)
    (hns : nsOf l = some (theP).ns)
    (hIn : InOrderReads Mg) (hHe : HeldReads Mg)
    (hlook : lookAt X l false = some x)
    (hpX : Desc.K3.pieceAt X l false = 2 + shift sub)
    (here : PS[k]? = some a) (next : PS[k + 1]? = some a') (hl : a.link = some l)
    (hs : linksFull[l]? = some sub) (hpc : a.piece = 2 + shift sub)
    (stand : sameStand linksFull a a' = true) (fit : bookFit N PS told = true)
    (tells : told[k]? = some []) (hfit : pubFit Mg.more linksFull PS = true)
    (askFresh : Pub.linkFresh l ∈ (pubSets Mg.more linksFull PS)[k]?.getD [])
    (hbase : ∀ t ∈ sampledIn N ((openSets linksFull PS (start linksFull))[k]?.getD []),
      t.1 < q.base)
    (hsm : ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v → ∀ e ∈ ms,
      smpT (z, v.1) e.1 e.2 = smpT (z, u.1) e.1 e.2)
    (bPub : ∀ u v : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      Rch k ((z, u.1), u.2) → u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCallsR l (2 + shift sub) → Mg.pub p (z, v.1) = true)
    (bPubP : ∀ u v : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      Rch k ((z, u.1), u.2) → u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a),
        p ≠ .left l → Mg.pubP p (z, v.1)) :
    BehindPartsR (Fr := Fr) x SET N Mg linksFull PS z k l (2 + shift sub)
      (Dn.arrayOf.getD l #[]) a a' told
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) (fun u => Rch k ((z, u.1), u.2)) :=
  { here := here
    next := next
    quiet := calls_quiet hl hs hpc
    stand := stand
    fit := fit
    tells := tells
    askIn := calls_asks_open Mg.more linksFull PS k a l sub hfit here hl hs hpc _
      (by simp)
    askFree := calls_asks_open Mg.more linksFull PS k a l sub hfit here hl hs hpc _
      (by simp)
    askFresh := askFresh
    pubIn := fun s h => k3LookIn_onIn (fLook_at hK l false hlook z s (by rw [hpX]; exact h))
    fOut := fun s h => by
      rw [← hpX]
      exact fOut_at hK l false hlook z s h
    fLedger := fun s h => by
      rw [hled, ledgerB_is]
      exact h
    fFree := fun s => by
      rw [hfree, hns, Option.any_some, freeAboveB_is]
    fFresh := fun s => by
      rw [hK.linkFresh]
    fLeft := fun s => hK.left l (z, s)
    fLeftP := fun s h => by
      rw [hK.pLeft]
      exact ⟨_, by unfold placeAt; rw [hlook]; rfl, h⟩
    bOrder := fun u v _ _ _ _ hsb h => inOrder_sameBut hIn hsb z h
    bPub := bPub
    bPubP := bPubP
    bHeld := fun u v _ _ _ _ hsb t _ h => held_sameBut hHe hsb t.1 t.2 z h
    bShown := fun u v _ _ _ hy _ t ht h => by
      rw [hsh] at h ⊢
      exact calls_shown Dn.codes G ms (strictAt B' q) _ hbase u v hy t ht h
    bNoColl := fun u v _ _ _ hy _ t ht h => by
      rw [hnc] at h ⊢
      exact calls_noColl Dn.codes G smpT ms z (strictAt B' q) _ hbase hsm u v hy t ht h }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attTies_ofR
#print axioms VerifiableInference.OnPublicFiles.layTies_ofR
#print axioms VerifiableInference.OnPublicFiles.behindParts_ofR
