-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3AttAtTable.lean: the lookup on an ATTENTION link's calls AT THE TABLE OF
JOINTS: the law k3_att_goodIn_any, carried through the table's wide door (OwnAtTableWide,
Johnson/Desc/Sound/BordersQ.lean) to WHAT THE TABLE ASKS OF THE BLOCK AT THE LOOKUP's PLACE:
Piece.Own between the table's promises at the two borders and the items that the row closes and
opens. A RULE: its worth is THE LIST OF ITS NAMED PREMISES. NO SOUNDNESS IS CLAIMED.

OBJECT: Desc.K3.block's decide, as K3.theOwn lays it (Johnson/Desc/First/Look/K3Own.lean:78:
  seat := seatCalls claim or seatDigits claim, guests := []), THROUGH
  hyes: the piece holds "below b" for ANY block b whose decide says yes only where that one does: so
  the guarded, named block that a seat lays, and the block with the hearing exchanged where its own
  test on the plan says yes (blockVia_decide), fall under it.
Used by K3AttAtTableR.lean, K3CallsMaskOkAt.lean and K3DigitsMaskAt.lean (Johnson/Desc/First/Look)
  and others.
LETTERS: those of k3_att_goodIn_any; N, Mg, links, ps, k, m, pi: the table's, free, under
  AttAtTable.
Built on: Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean. The table:
  (Johnson/Desc/First/Borders.lean, Johnson/Desc/Sound/BordersQ.lean and SpinePlain.lean).

The chain's state is taken as the first chain's own, with a fixed public part pi beside it
(get s := (pi, s)): the lift to the pair with the public part is not made in this file.

THE NAMED PREMISES (the structure `AttAtTable`), sorted by whose they are.
  THE TABLE's INDEX (tests on the table; they can be evaluated at the real index): `ins`, `outs`,
    `ctx`: block number k's row is the lookup's row of segment m · `askIn`: the public item lookIn
    is open in front · `seats`: every seat of the link's list is a tenant whose pin is open in
    front.
  THE FILLING OF THE TABLE's LETTERS: `pubIn`: lookIn is Johnson/Desc/First/Look/K3LookIn.lean's
    k3LookIn at the link's arrayOf in D · `worthP`, `worthK`, `worthR`:
    worth "planes", "keys", "rider" are Johnson/Top/H/K3Worth.lean's three at attention's letters
    · `cf`: held, shown, noColl at a member's seat give the
    library's CfAt at that member · `pinIn`: pin m 0 gives PinSig over the link's list.
  LEFT TO OTHER FILES: `codesIn`: the chain's codes are D's (meant for the promise's clause "in
    order") · `askLive`, `fLive`: the live request's shape and its rows' layout are D's: the public
    item "frame.liveIs", which comes through the table's door
    (Johnson/Desc/First/Look/K3LiveIs.lean); the two others of the five come from lookIn ·
    `objects`: formsT "objects" gives the residues' item in our form (the dictionary between the
    table's world and the library's): ASKED AT THE STATE BEHIND A YES OF THE PIECE ALONE,
    with the promises at both borders, SameBut and k3OnOut in hand: at every state it is met
    by no filling (by reading alone) · `model`: our sentence in front, with the packing, gives
    the model's two clauses constr lookCalls and constr rider · `smallBack`, `pinBack`: constr small
    and the pins of moment 0 ride back over a yes of the piece · `behind`: THE REST OF THE PROMISE
    BEHIND: from the promise in front, a yes, "all but the open link's ledger and what was heard is
    the same" and k3OnOut: the promise behind (the book-keeping at the next place; the public items
    that the row makes beside lookOut: look, callerIn, formsIn; those that ride) · `decodes`: "the
    stored table decodes" rides.
  THE FOUR THAT SPEAK OF TWO STATEMENTS (smallBack, pinBack, behind, decodes) ARE ASKED AT A YES OF
  THE PIECE ALONE (the letter Yes; in the theorems: "there is a transcript at which the piece puts b
  out at a"), with SameBut handed beside: run over all pairs with
  SameBut alone, the strings behind tied to nothing, they would be false at a filled meaning.
  `cellsIn`: the planes' cells lie in the list's matrix: spent by no proof.

Limits. NO PREMISE OF THE STRUCTURE IS SHOWN AT ANY DESCRIPTION, FILLING OR INDEX. `behind` IS THE
LARGEST AND IS A FORM OF WHAT IS TO BE SHOWN, cut only by what the lookup's files can give: k3OnOut
and SameBut. The premises of k3_att_goodIn_any stay as they are. Attention alone.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.First.Look.K3AttRounds
import Johnson.Desc.First.Look.K3CallsTies
import Johnson.Desc.First.Look.K3CallsTurns
import Johnson.Desc.First.Look.K3CallsLookOut
import Johnson.Desc.First.Look.K3LookIn
import Johnson.Desc.First.Look.K3AttGuards
import Johnson.Desc.First.Look.K3LiveIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn)

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

/-- **What is asked beside the law.** Yes a b: the piece says yes at a and puts out b. -/
structure AttAtTable : Prop where
  ins : (rowQ links ps k).ins = [.constr m .lookCalls, .constr m .rider]
  outs : (rowQ links ps k).outs =
    [.formsT m 2 "objects", .worth m 2 "planes", .worth m 2 "keys", .worth m 2 "rider"]
  ctx : (rowQ links ps k).ctx = [.pin m 0, .constr m .small]
  /-- the planes' cells lie in the list's matrix: SPENT BY NO PROOF HERE: without it the reading of
  a cell outside is 0, and worth "planes" speaks of that 0 -/
  cellsIn : planesInB x A tl = true
  askIn : Pub.lookIn m 2 ∈ (pubSets Mg.more links ps)[k]?.getD []
  seats : ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD [])
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
  askLive : liveItem m ∈ (pubSets Mg.more links ps)[k]?.getD []
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
  behind : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → Yes a b → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
    Mg.decodes (pi, b.1) (strsOf Fr b.2) → onQ N Mg links ps (fun s => (pi, s)) (k + 1) b
  decodes : ∀ a b : Desc.First.S × Fr.E.Str, Yes a b → SameBut a.1 b.1 →
    Mg.decodes (pi, a.1) (strsOf Fr a.2) → Mg.decodes (pi, b.1) (strsOf Fr b.2)

end

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {set : Params.Setting}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  {claim : Aff → Cl} {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {pi : P} {k m : ℕ}

/-- What the unmarked arm of the table's promise holds. -/
theorem onQ_arm {a : Desc.First.S × Fr.E.Str}
    (h : onQ N Mg links ps (fun s => (pi, s)) k a) (hu : a.1.failed = none) :
    (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pub q (pi, a.1) = true) ∧
      ∀ t ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.held t.1 t.2 (pi, a.1) = true ∧ Mg.shown t.1 t.2 (strsOf Fr a.2) ∧
          Mg.noColl t.1 t.2 (pi, a.1) (strsOf Fr a.2) := by
  obtain ⟨-, hm | ⟨h1, h2, h3, -⟩⟩ := h
  · exact absurd hu hm
  · simp only [Bool.and_eq_true] at h1
    have hp := h1.1.2
    unfold Desc.First.pubHeld at hp
    rw [List.all_eq_true] at hp
    unfold Desc.First.samplesHeld at h2
    rw [List.all_eq_true] at h2
    exact ⟨fun q hq => hp q (List.mem_append_left _ hq),
      fun t ht => ⟨h2 t ht, (h3 t ht).1, (h3 t ht).2⟩⟩

/-- **THE LOOKUP's ROW AT THE TABLE, at an attention link: THE RULE**: from ANY law of the piece
between our conditions and relations, and "a yes of the piece is a yes of K3.block's decide at the
place's parameters, at rounds whose words are below the prime". -/
theorem k3_att_atTable_of
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hext : ∀ a τ w, p.ext a τ w = w)
    (hs : (Desc.First.Look.P.ofPlace set false x).shape = some x.fs)
    (law : p.GoodIn
      (AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard))
    (hY : ∀ a τ c, p.ior.red.out a τ = some c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
          (Desc.First.Look.P.ofPlace set false x) guests).decide a.1 rs cols = .ok c.1)
    (T : AttAtTable (Fr := Fr) G x A tl D rad set seatT arr smp claim N Mg links ps pi k m
      (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
    p.Own (onQ N Mg links ps (fun s => (pi, s)) k) (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) := by
  have hyesAt : ∀ a τ c, p.ior.red.out a τ = some c → SameBut a.1 c.1 := by
    intro a τ c hc
    obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ := hY a τ c hc
    exact k3_calls_sameBut claim piece laid before _ guests _ _ rs cols hd
  have hun : ∀ a : Desc.First.S × Fr.E.Str, ¬ a.1.failed ≠ none → a.1.failed = none :=
    fun a h => Classical.not_not.1 h
  refine ownAtTableWide _ _ _ _ _ _ N Mg links ps (fun s => (pi, s)) k p _ _ _ _ law
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- t1
    intro a ha hm
    obtain ⟨hp, hc⟩ := onQ_arm ha (hun a hm)
    have o1 := T.codesIn a ha (hun a hm)
    obtain ⟨o2, o3⟩ := (T.fLive _).1 (hp _ T.askLive)
    exact k3_att_t1 G seatT smp claim a
      (ownIs_of (p := Desc.First.Look.P.ofPlace set false x) (T.pubIn _ (hp _ T.askIn)) o1 o2 o3)
      (fun i => T.cf i _ _ (hc _ (T.seats i)).1 (hc _ (T.seats i)).2.1 (hc _ (T.seats i)).2.2)
      (k3LookIn_onIn (T.pubIn _ (hp _ T.askIn)))
  · -- t2
    intro a τ c ha hm hc _
    obtain ⟨hp, -⟩ := onQ_arm ha (hun a hm)
    obtain ⟨piece, laid, before, guests, rs, cols, hw, hd⟩ := hY a τ c hc
    exact T.behind a c ha (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc)
      (k3_calls_lookOut claim piece laid before _ guests hs rfl a.1 c.1 rs cols hw hd
        (k3LookIn_onIn (T.pubIn _ (hp _ T.askIn))))
      (T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) ha.1)
  · -- t3
    intro a τ c w ha hm hc ho' hw
    obtain ⟨hp, -⟩ := onQ_arm ha (hun a hm)
    obtain ⟨piece, laid, before, guests, rs, cols, hwd, hd⟩ := hY a τ c hc
    have hout := k3_calls_lookOut claim piece laid before _ guests hs rfl a.1 c.1 rs cols hwd hd
      (k3LookIn_onIn (T.pubIn _ (hp _ T.askIn)))
    have hbe := T.behind a c ha (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc) hout
      (T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) ha.1)
    have ho : ∀ i, i ∈ (rowQ links ps k).outs → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_left _ hi))
    have hx : ∀ i, i ∈ (rowQ links ps k).ctx → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_right _ hi))
    rw [T.outs] at ho
    rw [T.ctx] at hx
    exact k3_att_t3 G seatT arr _ _ smp _ c w (T.pinIn _ _ _ (hx (.pin m 0) (by simp))) ho'
      (T.objects a c ha (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc) hout hbe w
        (ho (.formsT m 2 "objects") (by simp)))
      (T.worthP _ _ _ (ho (.worth m 2 "planes") (by simp)))
      (T.worthK _ _ _ (ho (.worth m 2 "keys") (by simp)))
      (T.worthR _ _ _ (ho (.worth m 2 "rider") (by simp)))
  · -- t4
    intro a τ c w _ hm hc _ hw hRa
    rw [hext] at hRa ⊢
    obtain ⟨hS, hPin⟩ := k3_att_t4 G seatT arr smp a w hRa
    have hx : ∀ i, i ∈ (rowQ links ps k).ctx → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_right _ hi))
    rw [T.ctx] at hx
    have hsm : Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w :=
      T.smallBack a c w ⟨τ, hc⟩ (hyesAt a τ c hc) (hx (.constr m .small) (by simp))
    obtain ⟨hk, hrd⟩ := T.model _ _ _ hS hsm
    intro i hi
    unfold insQ at hi
    rw [T.ins, T.ctx] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | (rfl | rfl)) | rfl
    · exact hk
    · exact hrd
    · exact T.pinBack a c w ⟨τ, hc⟩ (hyesAt a τ c hc) (hx (.pin m 0) (by simp))
    · exact hsm
    · exact hun a hm
  · -- a mark stays
    intro a τ c hc hm
    rw [(hyesAt a τ c hc).failed]
    exact hm
  · -- "decodes" rides
    intro a τ c hc hd
    exact T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) hd

/-- **THE LOOKUP's ROW AT THE TABLE, at an attention link**, at any block b whose decide says yes
only where K3.block's does. -/
theorem k3_att_atTable (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hb : p.b = below b)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [attRider x A tl D rad extNone Unit]).ε
      (attRider x A tl D rad extNone Unit)) = some p.err)
    (hsmp : ∀ s rs cols s', b.decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp)
    (T : AttAtTable (Fr := Fr) G x A tl D rad set seatT arr smp claim N Mg links ps pi k m
      (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
    p.Own (onQ N Mg links ps (fun s => (pi, s)) k) (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) :=
  k3_att_atTable_of G seatT arr smp p hext H.shape
    (k3_att_goodIn_any G seatT arr smp claim piece laid before guests b hyes p hb hback hext H hr
      hR hε hsmp hseat σ₀)
    (fun a τ c hc => by
      obtain ⟨-, -, hw, cols, hd⟩ := piece_hears_below p b hb hback a τ c hc
      exact ⟨piece, laid, before, guests, _, cols, hw, hyes _ _ _ _ hd⟩) T

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.onQ_arm
#print axioms VerifiableInference.OnPublicFiles.k3_att_atTable_of
#print axioms VerifiableInference.OnPublicFiles.k3_att_atTable
