-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsOwedScope.lean: THE LOOKUP ON A LINK's CALLS: A BUILDER INTO THE
LEDGER (AttOwedR, LayOwedR: Johnson/Desc/Sound/MgAt/K3Owed.lean): EVERY FIELD THAT IS
A THEOREM IN THE GOALS' SCOPE IS LAID IN, at tls := Meaning.tlAt X: at attention nine (odd, shapeIs,
cellsIn, tabs, room, hlt, hhd, htl, fit), at the layers seven (even, noAtt, step, hlt, hhd, htl,
fit); and the conjunct "lookAt answers the same place" that the ledger lays beside each. NO NEW
STRUCTURE: the twenty fields that are kept are plain premises, IN THE LEDGER's OWN TEXTS (laid by a
program out of K3Owed.lean); Lean holds each against its field. A carrying of theorems in scope:
nothing new is shown. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the ledger of what the kind's law still owes at the composed meaning.
Used by K03LeftAt.lean, K03Due2.lean, K03Due4.lean (Johnson/P5J/) and 3 more.
LETTERS: the ledger's own; Z, pp, lay as in the scope's theorems.

BY WHAT EACH IS PAID: odd: attAt's own test (attAt_odd) · even, hlt at the layers: layAt's own test
  (layAt_even) · shapeIs, htl, the conjunct: attAt_letters, lay_letters, layAt_letters · cellsIn:
  attAt_scope · tabs, room: tabsAre_scope · hhd, step: Meaning.scope_plans · noAtt: attAt_even ·
  fit:
  fit_at_tlAt.

Main names: `attAt_odd`, `layAt_even` · `attOwed_scope`, `layOwed_scope`.

Limits. The full size's scope alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3Owed
import Johnson.Desc.Sound.MgAt.K3CallsLeftR
import Johnson.Desc.First.Look.K3PlanLettersLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

/-- Attention's reader answers at odd links alone. -/
theorem attAt_odd {X : Verify.Public} {i : ℕ}
    {y : Desc.First.Look.Place × Attention.Shape × HTailF2} (h : attAt X i = some y) :
    i % 2 = 1 := by
  unfold attAt at h
  split at h
  · rename_i hc
    exact hc.2
  · cases h

/-- Where a group has two links and there are twelve groups, the layers' reader answers at even
links other than 24 alone. -/
theorem layAt_even {X : Verify.Public} {i : ℕ} {y : Desc.First.Look.Place} (hp4 : X.p4 = true)
    (hN : X.NGr = 12) (h : layAt X i = some y) : i % 2 = 0 ∧ i ≠ 24 := by
  unfold layAt at h
  split at h
  · rename_i hc
    have e : Desc.First.Look.stepOf X = 2 := by
      unfold Desc.First.Look.stepOf
      rw [if_pos hp4]
    rw [e, hN] at hc
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    exact ⟨hc.1, by omega⟩
  · cases h

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl)
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (tls : ℕ → HTailF2)
  (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V)
  (a a' : Desc.Place) (k l : ℕ) (x : Desc.First.Look.Place)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

variable {Dm Mg Rch claim num idx tls tok a a' k l x}
  {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {tl : HTailF2}
  {smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
    Option ((attSg x Dm.sent Dm.rad3).om i).Smp}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
  {b' : Desc.Block Desc.First.S Cl} {told : List (List Desc.Oracle)}

/-- **AttOwedR, in scope.** -/
theorem attOwed_scope {A : Attention.Shape} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : Verify.publicOf Z.pol Z.KL lay = .ok X)
    (htls : tls = _root_.Meaning.tlAt X) (hl : l < 25) (hx : attAt X l = some (x, A, tl))
    (tie : linkTieB X Dm.sent Dm.rad3 num idx x.link tl = true)
    (one : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id)
    (own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N)
    (seated : GroupsSeated Dm.ms Dm.N)
    (base : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
      t.1 < q.base)
    (slots : (Dm.built[l]?).map (·.ns) = some (theP).ns)
    (stand : sameStand linksFull a a' = true)
    (book : bookFit Dm.N PS told = true)
    (tells : told[k]? = some [])
    (pubs : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hid : ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j)) (tok w)
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w))
    (small : ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j)
    (reads : ∀ w : Desc.Wit (CellsQ rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w))
    (objects : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      attObjects x A tl Dm.sent Dm.rad3 seatL Dm.arr
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w)
    (othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true)
    (othersP : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a),
        p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1))
    (rides : RidesAtR Dm.N (mgAll Dm Mg) Rch k q b')
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨callsSending x Dm.sent Dm.rad3 seatL, i⟩)
    (sent : ∀ i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length,
      Dm.seat3 x.link false i.1 ∈ Dm.N.sent l 0)
    (fits : Desc.Sound.SeatFits Dm.G Dm.sent.codes (sigListCalls Dm.sent Dm.rad3 x.link) seatL) :
    lookAt X l false = some x ∧
      AttOwedR Dm Mg Rch claim num idx tls tok a a' k l x A tl smp q b' told := by
  have hodd := attAt_odd hx
  obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
  have hg : g < 12 := by omega
  subst htls
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR h
  obtain ⟨-, hA, htl, hlook⟩ := attAt_letters hZ hR h hg hx
  obtain ⟨x', a0, hlook', -, e', -, hc⟩ := attAt_scope hZ hR h (l := 2 * g + 1) (by omega)
    (by omega) Dm.sent Dm.rad3
  have ex : x' = x := Option.some.inj (hlook'.symm.trans hlook)
  rw [ex] at e' hc
  have e1 := Option.some.inj (e'.symm.trans hx)
  have eA : a0.S = A := congrArg (fun t => t.2.1) e1
  have et : a0.seam.tl = tl := congrArg (fun t => t.2.2) e1
  rw [eA, et] at hc
  obtain ⟨hT, hU⟩ := tabsAre_scope hZ hR h hg hlook
  have hk : (2 * g + 1) / 2 = g := by omega
  exact ⟨hlook,
  { odd := hodd
    shapeIs := by rw [hk]; exact hA
    cellsIn := hc
    tabs := by rw [hA]; exact hT
    room := by rw [hA]; exact hU
    hlt := by omega
    hhd := by
      unfold headLink
      rw [if_pos hp4, hN]
      omega
    htl := htl
    fit := fit_at_tlAt h (Road.Hd.core_of_scope hZ hR h)
    tie := tie
    one := one
    own := own
    seated := seated
    base := base
    slots := slots
    stand := stand
    book := book
    tells := tells
    pubs := pubs
    hid := hid
    small := small
    reads := reads
    objects := objects
    othersPub := othersPub
    othersP := othersP
    rides := rides
    some := hsome
    sent := sent
    fits := fits }⟩

/-- **LayOwedR, in scope.** -/
theorem layOwed_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : Verify.publicOf Z.pol Z.KL lay = .ok X)
    (htls : tls = _root_.Meaning.tlAt X) (hl : l < 25) (hx : layAt X l = some x)
    (ht : tlAt X l = some tl)
    (tie : linkTieB X Dm.sent Dm.rad3 num idx x.link tl = true)
    (one : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id)
    (own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N)
    (seated : GroupsSeated Dm.ms Dm.N)
    (base : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
      t.1 < q.base)
    (slots : (Dm.built[l]?).map (·.ns) = some (theP).ns)
    (stand : sameStand linksFull a a' = true)
    (book : bookFit Dm.N PS told = true)
    (tells : told[k]? = some [])
    (pubs : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hid : ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j)) (tok w)
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w))
    (small : ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j)
    (reads : ∀ w : Desc.Wit (CellsQ rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w))
    (objects : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      layObjects x (pubAt X (l / Desc.First.Look.stepOf X)) tl Dm.sent Dm.rad3
        (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard v.1 w)
    (othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true)
    (othersP : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a),
        p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1))
    (rides : RidesAtR Dm.N (mgAll Dm Mg) Rch k q b')
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨callsSending x Dm.sent Dm.rad3 seatL, i⟩)
    (sent : ∀ i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length,
      Dm.seat3 x.link false i.1 ∈ Dm.N.sent l 0)
    (fits : Desc.Sound.SeatFits Dm.G Dm.sent.codes (sigListCalls Dm.sent Dm.rad3 x.link) seatL) :
    lookAt X l false = some x ∧
      LayOwedR Dm Mg Rch claim num idx tls tok a a' k l x tl smp q b' told := by
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR h
  obtain ⟨hev, h24⟩ := layAt_even hp4 hN hx
  obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
  have hg : g < 12 := by omega
  subst htls
  obtain ⟨hlook, hxl⟩ := layAt_letters hZ hR h hg hx
  have htl : tl = _root_.Meaning.tlAt X x.link := by
    rw [hxl]
    exact lay_letters hZ hR h hg ht
  exact ⟨hlook,
  { even := hev
    noAtt := attAt_even hev
    step := by
      unfold Desc.First.Look.stepOf
      rw [if_pos hp4]
    hlt := by omega
    hhd := by
      unfold headLink
      rw [if_pos hp4, hN]
      omega
    htl := htl
    fit := fit_at_tlAt h (Road.Hd.core_of_scope hZ hR h)
    tie := tie
    one := one
    own := own
    seated := seated
    base := base
    slots := slots
    stand := stand
    book := book
    tells := tells
    pubs := pubs
    hid := hid
    small := small
    reads := reads
    objects := objects
    othersPub := othersPub
    othersP := othersP
    rides := rides
    some := hsome
    sent := sent
    fits := fits }⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attAt_odd
#print axioms VerifiableInference.OnPublicFiles.layAt_even
#print axioms VerifiableInference.OnPublicFiles.attOwed_scope
#print axioms VerifiableInference.OnPublicFiles.layOwed_scope
