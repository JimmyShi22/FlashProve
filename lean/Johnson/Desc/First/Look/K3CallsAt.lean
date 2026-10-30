-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3CallsAt.lean: the lookup on a link's CALLS: THE TIES OF THE FILLING
(AttTies, LayTies, Johnson/Desc/First/Look/K3CallsMeanOf.lean) AND THE PARTS OF THE PROMISE BEHIND
(BehindParts, Johnson/Desc/First/Look/K3CallsBehind.lean) FROM EQUATIONS ON THE MEANING: the kind's
K3At (Johnson/Desc/First/Look/K3At.lean: at the kind's own items and fields Mg says what the
lookups' layer says) and plain equations on the fields that read the oracles and on the table's own
two items. No new structure: each equation is a premise by itself, so that any structure that holds
it can feed it. A sorting and calls. General in N and Mg. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' meaning at the kind's items.
USER: K3CallsAtR.lean (worthK3_att, worthK3_lay). attTies_of, layTies_of, behindParts_of: nobody
  yet. Meant: attMean_of, layMean_of at the composed meaning.
LETTERS: those of K3Means.lean; smpT, ms, G: the letters of the fields that read the oracles
  (Johnson/Desc/Sound/MeaningSig.lean); nsOf: the table's numbers of slots.

THE EQUATIONS, BY NAME: hK : K3At X Dn L Mg · hV : K3AtLive Dn Mg (the door's name "frame.liveIs":
  the first form alone spends it) · hpin : Mg.pin = pinJT ... · hnc : Mg.noColl = noCollJT ... · hsh
  : Mg.shown = shownJT ... · hled, hfree: the items ledger and freeAbove are the table's own two
  tests · hIn : InOrderReads Mg · hHe : HeldReads Mg (Look/K3FillDigits.lean).

Main names:
  `worthK3_att`, `worthK3_lay`: the field worth's term at the calls' piece.
  `attTies_of`: of AttTies' 14 fields EIGHT are paid: pubIn, worthP, worthK, worthR, cf, pinIn,
    pinBack, fLive. LEFT: cellsIn, codesIn, objects, model, smallBack, decodes.
  `layTies_of`: of LayTies' 16 the same eight. LEFT: tabIn, pinWIn, pinWOut, codesIn, objects,
    model, smallBack, decodes.
  `behindParts_of`: of BehindParts' 24 fields SIXTEEN are paid. LEFT: here, next, stand, fit, tells
    (tests on the table and the numbers), askFresh, bPub, bPubP.

Limits. A rule over letters. ListSits (Look/K3CallsFill.lean), hbase (every tenant that is read sits
below the piece's base) and hsm (an accept leaves the members' samples) stay premises.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsMeanOf
import Johnson.Desc.First.Look.K3At
import Johnson.Desc.First.Look.K3CallsFill
import Johnson.Desc.First.Look.K3CallsRides
import Johnson.Desc.First.Look.K3KeeperRides
import Johnson.Desc.First.Look.K3FillDigits

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

/-! ## The field worth at the calls' piece -/

section
variable {P Cells Tok : Type} (X : Verify.Public) (D : Desc.First.Look.Sent)
  (L : K3Letters Cells Tok)
  (f : ℕ → ℕ → String → P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop)

theorem worthK3_att (m : ℕ) {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt X m = some (x, A, tl)) (r : String) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT) :
    worthK3 X D L f m (Desc.K3.pieceAt X m false) r a y w =
      worthAtt D L x A tl r a.2 w (f m (Desc.K3.pieceAt X m false) r a y w) := by
  unfold worthK3
  rw [sort_calls, hx]

theorem worthK3_lay (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hna : attAt X m = none) (hx : layAt X m = some x) (ht : tlAt X m = some tl) (r : String)
    (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    worthK3 X D L f m (Desc.K3.pieceAt X m false) r a y w =
      worthLay D L x (pubAt X (m / Desc.First.Look.stepOf X)) tl r a.2 w
        (f m (Desc.K3.pieceAt X m false) r a y w) := by
  unfold worthK3
  rw [sort_calls, hna, hx, ht]

end

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
  (B' : Desc.Block Desc.First.S Cl) (z : P)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dn L.rad x.link).length =>
  L.seat x.link false j.1

/-! ## The ties -/

/-- **AttTies: eight of fourteen.** -/
theorem attTies_of {A : Attention.Shape} (hK : K3At X Dn L Mg) (hV : K3AtLive Dn Mg)
    (hpin : Mg.pin = pinJT Dn.codes G L.arr smpT ms)
    (hnc : Mg.noColl = noCollJT Dn.codes G smpT ms)
    (hlook : lookAt X l false = some x) (hx : attAt X l = some (x, A, tl))
    (hp2 : Desc.K3.pieceAt X l false = 2)
    (T : ListSits G x Dn L.rad seatL smpT smp ms N l)
    (hbase : ∀ t ∈ N.sent l 0, t.1 < q.base)
    (hsm : ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v → ∀ e ∈ ms,
      smpT (z, v.1) e.1 e.2 = smpT (z, u.1) e.1 e.2)
    (cellsIn : planesInB x A tl = true)
    (codesIn : ∀ u : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      u.1.failed = none → u.1.st.codes = Dn.codes)
    (objects : ∀ u v : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
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
    AttTies (Fr := Fr) G x A tl Dn L.rad SET seatL L.arr smp claim N Mg linksFull PS z k l
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) := by
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
      codesIn := codesIn
      fLive := fLive_at hV l z
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

/-- **LayTies: eight of sixteen.** -/
theorem layTies_of {smpW : Desc.First.S → Option L.oW.Smp} {strW : Fr.E.Str → L.oW.Str}
    (hK : K3At X Dn L Mg) (hV : K3AtLive Dn Mg)
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
    (codesIn : ∀ u : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      u.1.failed = none → u.1.st.codes = Dn.codes)
    (objects : ∀ u v : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
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
    LayTies (Fr := Fr) G x (pubAt X (l / Desc.First.Look.stepOf X)) tl Dn L.rad L.oW L.wOf L.nr
      L.nc SET seatL L.arr smp smpW strW L.msgW claim N Mg linksFull PS z k l
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) := by
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
      codesIn := codesIn
      fLive := fLive_at hV l z
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

/-- **BehindParts: sixteen of twenty-four**, at every sort of segment (pc := 2 + shift sub). -/
theorem behindParts_of {sub : ModelPart} {told : List (List Desc.Oracle)} {nsOf : ℕ → Option ℕ}
    (hK : K3At X Dn L Mg) (hV : K3AtLive Dn Mg)
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
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCalls l (2 + shift sub) → Mg.pub p (z, v.1) = true)
    (bPubP : ∀ u v : Desc.First.S × Fr.E.Str, onQ N Mg linksFull PS (fun s => (z, s)) k u →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a),
        p ≠ .left l → Mg.pubP p (z, v.1)) :
    BehindParts (Fr := Fr) x Dn SET N Mg linksFull PS z k l (2 + shift sub)
      (Dn.arrayOf.getD l #[]) a a' told
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) :=
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
    askLive := calls_live_open Mg.more linksFull PS k a l hfit here
      (hV.asks linksFull a l sub hl hs (Or.inl hpc))
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
    fLive := fLive_at hV l z
    fLeft := fun s => hK.left l (z, s)
    fLeftP := fun s h => by
      rw [hK.pLeft]
      exact ⟨_, by unfold placeAt; rw [hlook]; rfl, h⟩
    bOrder := fun u v _ _ _ hsb h => inOrder_sameBut hIn hsb z h
    bPub := bPub
    bPubP := bPubP
    bHeld := fun u v _ _ _ hsb t _ h => held_sameBut hHe hsb t.1 t.2 z h
    bShown := fun u v _ _ hy _ t ht h => by
      rw [hsh] at h ⊢
      exact calls_shown Dn.codes G ms (strictAt B' q) _ hbase u v hy t ht h
    bNoColl := fun u v _ _ hy _ t ht h => by
      rw [hnc] at h ⊢
      exact calls_noColl Dn.codes G smpT ms z (strictAt B' q) _ hbase hsm u v hy t ht h }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attTies_of
#print axioms VerifiableInference.OnPublicFiles.layTies_of
#print axioms VerifiableInference.OnPublicFiles.behindParts_of
