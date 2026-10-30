-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3CallsMeanOf.lean: the lookup on a link's CALLS: WHAT THE KIND's
STRUCTURES AttMean AND LayMean (Johnson/Desc/First/Look/K3Means.lean: all that an attention or a
layers' place asks of the table of joints' numbers, meaning and readers of samples) ARE MADE OF,
WITH ALL THAT IS PAID TAKEN OUT: attMean_of, layMean_of END IN THESE NAMES. A sorting and calls:
nothing new is shown of any block. General in N and Mg. NO SOUNDNESS IS CLAIMED.

OBJECT: Desc.K3.theStated claim readers X codes shape a = some b', at a.link = some l; the table's
  words at block number k of the full size's written list of places.
USER: K3CallsAt.lean (AttTies, LayTies); K3CallsMeanR.lean and others (seat_yes). attMean_of,
  layMean_of: nobody. Meant: the composed meaning's files, at the fields att and lay of K3Mean.
LETTERS: those of K3Means.lean; a': the next place; told, arrs: BehindParts' letters.

PAID INSIDE, SO NOT ASKED: hsmp, hsmpW (calls_hsmp, from "the reader reads the statement and
  the book alone") · smp0 (every signature's type of samples has a member:
  smp_nonempty) · of the tables: ins, outs, ctx (att_row_at, lay_row_at) · askIn, askLive (they
  stand in BehindParts) · seats (from "pin l 0 is open in front" and "every seat is sent by segment
  l at moment 0") · behind (calls_behind: from BehindParts).
LEFT, BY NAME: hseat · hread (hreadW) · hpin · hsent · (layers) hstrW, smpW0 · AttTies (14 fields) |
  LayTies (16): THE TABLES' OWN FIELDS THAT ARE TIES OF THE FILLING, to the letter [cut out of the
  two structures by program] · BehindParts (Johnson/Desc/First/Look/K3CallsBehind.lean) · rides.

Main names: `AttTies`, `attAtTable_of`, `attMean_of` · `LayTies`, `layAtTable_of`, `layMean_of`.

Limits. A rule over letters. The full size's written lists alone (as K3Means.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Means
import Johnson.Desc.First.Look.K3CallsBehind
import Johnson.Desc.First.Look.K3CallsMean
import Johnson.Desc.First.Look.K3RowIndex
import Johnson.Desc.First.Look.K3SmpMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn)

/-! ## Attention -/

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (A : Attention.Shape) (tl : HTailF2) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ) (set : Params.Setting)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (claim : Aff → Cl) (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) (links : List ModelPart)
  (ps : List Desc.Place) (pi : P) (k m : ℕ)
  (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)

/-- **The table's fields that are ties of the filling**, at one value of the public part. -/
structure AttTies : Prop where
  cellsIn : planesInB x A tl = true
  pubIn : ∀ s, Mg.pub (.lookIn m 2) (pi, s) = true →
    k3LookIn (Desc.First.Look.P.ofPlace set false x) (D.arrayOf.getD x.link #[]) s = true
  worthP : ∀ s y w, Mg.worth m 2 "planes" (pi, s) y w →
    attWorthPlanes x A tl D rad seatT arr (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard s w
  worthK : ∀ s y w, Mg.worth m 2 "keys" (pi, s) y w →
    attWorthKeys x A tl D rad seatT arr (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard s w
  worthR : ∀ s y w, Mg.worth m 2 "rider" (pi, s) y w →
    attWorthRider x A tl D rad seatT arr (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard s w
  cf : ∀ i s y, Mg.held (seatT i).1 (seatT i).2 (pi, s) = true →
    Mg.shown (seatT i).1 (seatT i).2 y → Mg.noColl (seatT i).1 (seatT i).2 (pi, s) y →
    CfAt G D.codes (sigListCalls D rad x.link) seatT smp i s y
  pinIn : ∀ s y w, (∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, s) y w) →
    PinSig G D.codes (sigListCalls D rad x.link) seatT smp arr (fun _ => True) s y w
  pinBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    (∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, b.1) (strsOf Fr b.2) w) →
    ∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, a.1) (strsOf Fr a.2) w
  codesIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → a.1.st.codes = D.codes
  fLive : ∀ s, Mg.pub (liveItem m) (pi, s) = true ↔ LiveIs D s
  objects : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → Yes a b → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
    onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
    ∀ w, Mg.formsT m 2 "objects" (pi, b.1) (strsOf Fr b.2) w →
    attObjects x A tl D rad seatT arr (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard b.1 w
  model : ∀ s y w, AttSays x A tl D rad (attMs x D rad seatT arr w) →
    Mg.constr m .small (pi, s) y w →
    Mg.constr m .lookCalls (pi, s) y w ∧ Mg.constr m .rider (pi, s) y w
  smallBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    Mg.constr m .small (pi, b.1) (strsOf Fr b.2) w → Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w
  decodes : ∀ a b : Desc.First.S × Fr.E.Str, Yes a b → SameBut a.1 b.1 →
    Mg.decodes (pi, a.1) (strsOf Fr a.2) → Mg.decodes (pi, b.1) (strsOf Fr b.2)

variable {G x A tl D rad set seatT arr smp claim N Mg links ps pi k m Yes}

/-- **The table's structure, from the ties and the parts of the promise behind.** -/
theorem attAtTable_of {arrs : Array (Nat × String)} {p p' : Desc.Place}
    {told : List (List Desc.Oracle)} (hl : p.link = some m)
    (hs : links[m]? = some .attention) (hpc : p.piece = 2)
    (hsh : (Desc.First.Look.P.ofPlace set false x).shape = some x.fs)
    (hY : ∀ a c, Yes a c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
          (Desc.First.Look.P.ofPlace set false x) guests).decide a.1 rs cols = .ok c.1)
    (hpin : Item.pin m 0 ∈ (openSets links ps (start links))[k]?.getD [])
    (hsent : ∀ i, seatT i ∈ N.sent m 0)
    (B : BehindParts (Fr := Fr) x D set N Mg links ps pi k m 2 arrs p p' told Yes)
    (O : AttTies (Fr := Fr) G x A tl D rad set seatT arr smp claim N Mg links ps pi k m Yes) :
    AttAtTable (Fr := Fr) G x A tl D rad set seatT arr smp claim N Mg links ps pi k m Yes :=
  { ins := (att_row_at B.here hl hs hpc).1
    outs := (att_row_at B.here hl hs hpc).2.1
    ctx := (att_row_at B.here hl hs hpc).2.2
    askIn := B.askIn
    askLive := B.askLive
    seats := fun i => by
      unfold sampledIn
      exact List.mem_flatMap.2 ⟨_, hpin, hsent i⟩
    behind := calls_behind claim hsh hY B
    cellsIn := O.cellsIn
    pubIn := O.pubIn
    worthP := O.worthP
    worthK := O.worthK
    worthR := O.worthR
    cf := O.cf
    pinIn := O.pinIn
    pinBack := O.pinBack
    codesIn := O.codesIn
    fLive := O.fLive
    objects := O.objects
    model := O.model
    smallBack := O.smallBack
    decodes := O.decodes }

end

/-! ## The layers -/

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (q : LayPub) (tl : HTailF2) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
  (set : Params.Setting)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)
  (claim : Aff → Cl) (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) (links : List ModelPart)
  (ps : List Desc.Place) (pi : P) (k m : ℕ)
  (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)

/-- **The table's fields that are ties of the filling**, at one value of the public part. -/
structure LayTies : Prop where
  pubIn : ∀ s, Mg.pub (.lookIn m 2) (pi, s) = true →
    k3LookIn (Desc.First.Look.P.ofPlace set false x) (D.arrayOf.getD x.link #[]) s = true
  worthP : ∀ s y w, Mg.worth m 2 "planes" (pi, s) y w →
    layWorthPlanes x q tl D rad oW wOf nr nc seatT arr msgW (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard s w
  worthK : ∀ s y w, Mg.worth m 2 "keys" (pi, s) y w →
    layWorthKeys x q tl D rad oW wOf nr nc seatT arr msgW (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard s w
  worthR : ∀ s y w, Mg.worth m 2 "rider" (pi, s) y w →
    layWorthRider x q tl D rad oW wOf nr nc seatT arr msgW (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard s w
  cf : ∀ i s y, Mg.held (seatT i).1 (seatT i).2 (pi, s) = true →
    Mg.shown (seatT i).1 (seatT i).2 y → Mg.noColl (seatT i).1 (seatT i).2 (pi, s) y →
    CfAt G D.codes (sigListCalls D rad x.link) seatT smp i s y
  pinIn : ∀ s y w, (∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, s) y w) →
    PinSig G D.codes (sigListCalls D rad x.link) seatT smp arr (fun _ => True) s y w
  pinBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    (∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, b.1) (strsOf Fr b.2) w) →
    ∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, a.1) (strsOf Fr a.2) w
  tabIn : ∀ a : Desc.First.S × Fr.E.Str, Mg.decodes (pi, a.1) (strsOf Fr a.2) →
    ∃ σW, smpW a.1 = some σW ∧ ¬ oW.Clash (strW a.2) σW.1
  pinWIn : ∀ (a : Desc.First.S × Fr.E.Str) w, Mg.pinW (pi, a.1) (strsOf Fr a.2) w →
    ∃ σW, smpW a.1 = some σW ∧ oW.dec (strW a.2) σW = some (msgW w)
  pinWOut : ∀ (a : Desc.First.S × Fr.E.Str) w,
    (∃ σW, smpW a.1 = some σW ∧ oW.dec (strW a.2) σW = some (msgW w)) →
    Mg.pinW (pi, a.1) (strsOf Fr a.2) w
  codesIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → a.1.st.codes = D.codes
  fLive : ∀ s, Mg.pub (liveItem m) (pi, s) = true ↔ LiveIs D s
  objects : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → Yes a b → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
    onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
    ∀ w, Mg.formsT m 2 "objects" (pi, b.1) (strsOf Fr b.2) w →
    layObjects x q tl D rad oW wOf nr nc seatT arr msgW (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard b.1 w
  model : ∀ s y w, LaySays x q tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w) →
    Mg.constr m .small (pi, s) y w → Mg.pinW (pi, s) y w →
    Mg.constr m .lookCalls (pi, s) y w ∧ Mg.constr m .rider (pi, s) y w
  smallBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    Mg.constr m .small (pi, b.1) (strsOf Fr b.2) w → Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w
  decodes : ∀ a b : Desc.First.S × Fr.E.Str, Yes a b → SameBut a.1 b.1 →
    Mg.decodes (pi, a.1) (strsOf Fr a.2) → Mg.decodes (pi, b.1) (strsOf Fr b.2)

variable {G x q tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW claim N Mg links ps pi k m
  Yes}

/-- **The table's structure, from the ties and the parts of the promise behind.** -/
theorem layAtTable_of {arrs : Array (Nat × String)} {p p' : Desc.Place}
    {told : List (List Desc.Oracle)} (hl : p.link = some m)
    (hs : links[m]? = some .layers) (hpc : p.piece = 2)
    (hsh : (Desc.First.Look.P.ofPlace set false x).shape = some x.fs)
    (hY : ∀ a c, Yes a c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
          (Desc.First.Look.P.ofPlace set false x) guests).decide a.1 rs cols = .ok c.1)
    (hpin : Item.pin m 0 ∈ (openSets links ps (start links))[k]?.getD [])
    (hsent : ∀ i, seatT i ∈ N.sent m 0)
    (B : BehindParts (Fr := Fr) x D set N Mg links ps pi k m 2 arrs p p' told Yes)
    (O : LayTies (Fr := Fr) G x q tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW claim N Mg
      links ps pi k m Yes) :
    LayAtTable (Fr := Fr) G x q tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW claim N Mg
      links ps pi k m Yes :=
  { ins := (lay_row_at B.here hl hs hpc).1
    outs := (lay_row_at B.here hl hs hpc).2.1
    ctx := (lay_row_at B.here hl hs hpc).2.2
    askIn := B.askIn
    askLive := B.askLive
    seats := fun i => by
      unfold sampledIn
      exact List.mem_flatMap.2 ⟨_, hpin, hsent i⟩
    behind := calls_behind claim hsh hY B
    pubIn := O.pubIn
    worthP := O.worthP
    worthK := O.worthK
    worthR := O.worthR
    cf := O.cf
    pinIn := O.pinIn
    pinBack := O.pinBack
    tabIn := O.tabIn
    pinWIn := O.pinWIn
    pinWOut := O.pinWOut
    codesIn := O.codesIn
    fLive := O.fLive
    objects := O.objects
    model := O.model
    smallBack := O.smallBack
    decodes := O.decodes }

end

/-! ## Ending in the names of K3Means.lean -/

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) {X : Verify.Public}
  {Dn : Desc.First.Look.Sent} {L : K3Letters Cells Tok} {N : Numbers}
  {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} (claim : Aff → Cl)
  (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes) (shape : Params.ReqShape)
  {a a' : Desc.Place} {k l : ℕ} {x : Desc.First.Look.Place} {tl : HTailF2}
  {smp : Desc.First.S → (i : Fin (sigListCalls Dn L.rad x.link).length) →
    Option ((attSg x Dn L.rad).om i).Smp}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT)}
  {b' : Desc.Block Desc.First.S Cl} {arrs : Array (Nat × String)}
  {told : List (List Desc.Oracle)}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- A yes of the piece at the seat is a yes of K3.block's decide at the place's parameters. -/
theorem seat_yes (h : Desc.K3.theStated claim readers X codes shape a = some b')
    (hOk : b'.planOk = true) (hl : a.link = some l) (hpcX : a.piece = Desc.K3.pieceAt X l false)
    (e : placeAt X l false = some theP) (hback : q.back = []) (B' : Desc.Block Desc.First.S Cl)
    (hB : SeatOf b' B') :
    ∀ u v, (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide u.1 rs
          cols = .ok v.1 := by
  rintro u v ⟨τ, hout⟩
  obtain ⟨laid, sent, rs, cols, hw, hd⟩ := k3_calls_stated_yes claim readers codes shape a b' B' h
    hOk hB.1 (strictAt B' q) rfl hl hpcX e hback u v τ hout
  exact ⟨a.piece, laid, sent, [], rs, cols, hw, hd⟩

/-- **AttMean.** -/
theorem attMean_of {A : Attention.Shape}
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hl : a.link = some l) (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hsub : linksFull[l]? = some .attention) (e : placeAt X l false = some theP)
    (hback : q.back = []) (H : AttOK SET x A tl Dn L.rad)
    (hread : ∀ s s' : Desc.First.S, s'.st = s.st → s'.book = s.book → smp s' = smp s)
    (hseat : ∀ i : Fin (sigListCalls Dn L.rad x.link).length,
      (L.seat x.link false i.1).1 < q.base)
    (hpin : Item.pin l 0 ∈ (openSets linksFull PS (start linksFull))[k]?.getD [])
    (hsent : ∀ i : Fin (sigListCalls Dn L.rad x.link).length,
      L.seat x.link false i.1 ∈ N.sent l 0)
    (Bp : ∀ B', SeatOf b' B' → ∀ z : P,
      BehindParts (Fr := Fr) x Dn SET N Mg linksFull PS z k l 2 arrs a a' told
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v))
    (O : ∀ B', SeatOf b' B' → ∀ z : P,
      AttTies (Fr := Fr) G x A tl Dn L.rad SET (fun j => L.seat x.link false j.1) L.arr smp claim
        N Mg linksFull PS z k l (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v))
    (rides : RidesAt N Mg k q b') :
    AttMean G X Dn L N Mg claim a k l x A tl smp q b' :=
  { hsmp := calls_hsmp claim a.piece theP smp hread
    hseat := hseat
    smp0 := smp_nonempty _
    table := fun B' hB z =>
      attAtTable_of hl hsub hpc H.shape
        (seat_yes claim readers codes shape h hOk hl hpcX e hback B' hB) hpin hsent (Bp B' hB z)
        (O B' hB z)
    rides := rides }

/-- **LayMean.** -/
theorem layMean_of {smpW : Desc.First.S → Option L.oW.Smp} {strW : P → Fr.E.Str → L.oW.Str}
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hl : a.link = some l) (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hsub : linksFull[l]? = some .layers) (e : placeAt X l false = some theP)
    (hback : q.back = []) (H : LayOK SET x)
    (hread : ∀ s s' : Desc.First.S, s'.st = s.st → s'.book = s.book → smp s' = smp s)
    (hreadW : ∀ s s' : Desc.First.S, s'.st = s.st → s'.book = s.book → smpW s' = smpW s)
    (hstrW : ∀ (z : P) y (τ : Tr (uLT (ckP .two) q.ds)),
      strW z (behind (ckP .two) Fr q.base q.ds y τ) = strW z y)
    (hseat : ∀ i : Fin (sigListCalls Dn L.rad x.link).length,
      (L.seat x.link false i.1).1 < q.base)
    (smpW0 : Nonempty L.oW.Smp)
    (hpin : Item.pin l 0 ∈ (openSets linksFull PS (start linksFull))[k]?.getD [])
    (hsent : ∀ i : Fin (sigListCalls Dn L.rad x.link).length,
      L.seat x.link false i.1 ∈ N.sent l 0)
    (Bp : ∀ B', SeatOf b' B' → ∀ z : P,
      BehindParts (Fr := Fr) x Dn SET N Mg linksFull PS z k l 2 arrs a a' told
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v))
    (O : ∀ B', SeatOf b' B' → ∀ z : P,
      LayTies (Fr := Fr) G x (pubAt X (l / Desc.First.Look.stepOf X)) tl Dn L.rad L.oW L.wOf L.nr
        L.nc SET (fun j => L.seat x.link false j.1) L.arr smp smpW (strW z) L.msgW claim N Mg
        linksFull PS z k l (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v))
    (rides : RidesAt N Mg k q b') :
    LayMean G X Dn L N Mg claim a k l x tl smp smpW strW q b' :=
  { hsmp := calls_hsmp claim a.piece theP smp hread
    hsmpW := calls_hsmp claim a.piece theP smpW hreadW
    hstrW := hstrW
    hseat := hseat
    smp0 := smp_nonempty _
    smpW0 := smpW0
    table := fun B' hB z =>
      layAtTable_of hl hsub hpc H.shape
        (seat_yes claim readers codes shape h hOk hl hpcX e hback B' hB) hpin hsent (Bp B' hB z)
        (O B' hB z)
    rides := rides }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attAtTable_of
#print axioms VerifiableInference.OnPublicFiles.layAtTable_of
#print axioms VerifiableInference.OnPublicFiles.attMean_of
#print axioms VerifiableInference.OnPublicFiles.layMean_of
