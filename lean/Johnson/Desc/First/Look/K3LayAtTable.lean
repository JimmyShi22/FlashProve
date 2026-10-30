-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3LayAtTable.lean: the lookup on a LAYERS' link's calls AT THE TABLE OF
JOINTS: the law k3_lay_goodIn_any, carried through the table's wide door (OwnAtTableWide,
Johnson/Desc/Sound/BordersQ.lean) to Piece.Own between the table's promises at the two borders and
the items that the row closes and opens. The layers' like of K3AttAtTable.lean. A RULE: its worth is
THE LIST OF ITS NAMED PREMISES. NO SOUNDNESS IS CLAIMED.

OBJECT: Desc.K3.block's decide, as K3.theOwn lays it (Johnson/Desc/First/Look/K3Own.lean:78:
  seat := seatCalls claim, guests := []), THROUGH hyes: the piece holds "below b" for ANY block b
  whose decide says yes only where that one does.
USER: Johnson/Desc/First/Look/K3RowsStated.lean calls k3_lay_atTable_of; no file calls
  k3_lay_atTable.
LETTERS: those of k3_lay_goodIn_any; N, Mg, links, ps, k, m, pi: the table's, free, under
  LayAtTable.
Built on: Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean. The table:
  (Johnson/Desc/First/Borders.lean, Johnson/Desc/Sound/BordersQ.lean and SpinePlain.lean).

THE NAMED PREMISES (the structure `LayAtTable`): those of AttAtTable at the layers' letters, and
what the stored table brings: the row's ctx holds pinW too · `tabIn`: "the stored table decodes"
gives our condition's clause on it (the state holds its sample; no collision at its word) ·
`pinWIn`, `pinWOut`: pinW and the second half of LayPin (the word decodes, with that sample, to the
witness's message msgW w), both ways · `model` HAS pinW IN FRONT: the model's
clause on the keys is asked at the matrix to which THE STRINGS decode, the caller's relation speaks
of THE WITNESS's cells: pinW ties the two, and the row's proof has it · `objects` IS ASKED AT THE
STATE BEHIND A YES OF THE PIECE ALONE, as in K3AttAtTable.lean. pinBack stands in
pinOut's place. THE FOUR THAT SPEAK OF TWO STATEMENTS (smallBack, pinBack, behind, decodes) ARE
ASKED AT A YES OF THE PIECE ALONE, as in K3AttAtTable.lean.

Limits. NO PREMISE OF THE STRUCTURE IS SHOWN AT ANY DESCRIPTION, FILLING OR INDEX. NOTHING IS TRIED
FOR EMPTINESS. `behind` is a form of what is to be shown, cut by k3OnOut and SameBut alone. THE
STORED TABLE STANDS AT LETTERS (oW, wOf, nr, nc, smpW, strW, msgW). q's shape, scale file and group
are tied to the public parameters by nothing. The full size alone (LayOK). What rides past the block
(Frames) is not here.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.First.Look.K3AttAtTable
import Johnson.Desc.First.Look.K3LayTies

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

/-- **What is asked beside the law.** Yes a b: the piece says yes at a and puts out b. -/
structure LayAtTable : Prop where
  ins : (rowQ links ps k).ins = [.constr m .lookCalls, .constr m .rider]
  outs : (rowQ links ps k).outs =
    [.formsT m 2 "objects", .worth m 2 "planes", .worth m 2 "keys", .worth m 2 "rider"]
  ctx : (rowQ links ps k).ctx = [.pin m 0, .constr m .small, .pinW]
  askIn : Pub.lookIn m 2 ∈ (pubSets Mg.more links ps)[k]?.getD []
  seats : ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD [])
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
  askLive : liveItem m ∈ (pubSets Mg.more links ps)[k]?.getD []
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
  behind : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → Yes a b → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
    Mg.decodes (pi, b.1) (strsOf Fr b.2) → onQ N Mg links ps (fun s => (pi, s)) (k + 1) b
  decodes : ∀ a b : Desc.First.S × Fr.E.Str, Yes a b → SameBut a.1 b.1 →
    Mg.decodes (pi, a.1) (strsOf Fr a.2) → Mg.decodes (pi, b.1) (strsOf Fr b.2)

end

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {q : LayPub} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  {set : Params.Setting}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)
  {claim : Aff → Cl} {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {pi : P} {k m : ℕ}

/-- **THE LOOKUP's ROW AT THE TABLE, at a layers' link: THE RULE**: from ANY law of the piece
between our conditions and relations, and "a yes of the piece is a yes of K3.block's decide at the
place's parameters, at rounds whose words are below the prime". -/
theorem k3_lay_atTable_of
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hext : ∀ a τ w, p.ext a τ w = w)
    (hs : (Desc.First.Look.P.ofPlace set false x).shape = some x.fs)
    (law : p.GoodIn
      (LayOn G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (LayOn' G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (LayFront G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW)
      (LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard))
    (hY : ∀ a τ c, p.ior.red.out a τ = some c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
          (Desc.First.Look.P.ofPlace set false x) guests).decide a.1 rs cols = .ok c.1)
    (T : LayAtTable (Fr := Fr) G x q tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW claim N
      Mg links ps pi k m (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
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
    obtain ⟨hq, hc⟩ := onQ_arm ha (hun a hm)
    have o1 := T.codesIn a ha (hun a hm)
    obtain ⟨o2, o3⟩ := (T.fLive _).1 (hq _ T.askLive)
    exact k3_lay_t1 G seatT smp smpW strW claim a
      (ownIs_of (p := Desc.First.Look.P.ofPlace set false x) (T.pubIn _ (hq _ T.askIn)) o1 o2 o3)
      (fun i => T.cf i _ _ (hc _ (T.seats i)).1 (hc _ (T.seats i)).2.1 (hc _ (T.seats i)).2.2)
      (T.tabIn a ha.1) (k3LookIn_onIn (T.pubIn _ (hq _ T.askIn)))
  · -- t2
    intro a τ c ha hm hc _
    obtain ⟨hq, -⟩ := onQ_arm ha (hun a hm)
    obtain ⟨piece, laid, before, guests, rs, cols, hw, hd⟩ := hY a τ c hc
    exact T.behind a c ha (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc)
      (k3_calls_lookOut claim piece laid before _ guests hs rfl a.1 c.1 rs cols hw hd
        (k3LookIn_onIn (T.pubIn _ (hq _ T.askIn))))
      (T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) ha.1)
  · -- t3
    intro a τ c w ha hm hc ho' hw
    obtain ⟨hq, -⟩ := onQ_arm ha (hun a hm)
    obtain ⟨piece, laid, before, guests, rs, cols, hwd, hd⟩ := hY a τ c hc
    have hout := k3_calls_lookOut claim piece laid before _ guests hs rfl a.1 c.1 rs cols hwd hd
      (k3LookIn_onIn (T.pubIn _ (hq _ T.askIn)))
    have hbe := T.behind a c ha (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc) hout
      (T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) ha.1)
    have ho : ∀ i, i ∈ (rowQ links ps k).outs → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_left _ hi))
    have hx : ∀ i, i ∈ (rowQ links ps k).ctx → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_right _ hi))
    rw [T.outs] at ho
    rw [T.ctx] at hx
    exact k3_lay_t3 G seatT arr msgW _ _ smp smpW strW _ c w
      ⟨T.pinIn _ _ _ (hx (.pin m 0) (by simp)), T.pinWIn c w (hx .pinW (by simp))⟩ ho'
      (T.objects a c ha (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc) hout hbe w
        (ho (.formsT m 2 "objects") (by simp)))
      (T.worthP _ _ _ (ho (.worth m 2 "planes") (by simp)))
      (T.worthK _ _ _ (ho (.worth m 2 "keys") (by simp)))
      (T.worthR _ _ _ (ho (.worth m 2 "rider") (by simp)))
  · -- t4
    intro a τ c w _ hm hc _ hw hRa
    rw [hext] at hRa ⊢
    obtain ⟨hS, hPin, hPW⟩ := k3_lay_t4 G seatT arr msgW smp smpW strW a w hRa
    have hx : ∀ i, i ∈ (rowQ links ps k).ctx → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_right _ hi))
    rw [T.ctx] at hx
    have hsm : Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w :=
      T.smallBack a c w ⟨τ, hc⟩ (hyesAt a τ c hc) (hx (.constr m .small) (by simp))
    obtain ⟨hk, hrd⟩ := T.model _ _ _ hS hsm (T.pinWOut a w hPW)
    intro i hi
    unfold insQ at hi
    rw [T.ins, T.ctx] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | (rfl | rfl | rfl)) | rfl
    · exact hk
    · exact hrd
    · exact T.pinBack a c w ⟨τ, hc⟩ (hyesAt a τ c hc) (hx (.pin m 0) (by simp))
    · exact hsm
    · exact T.pinWOut a w hPW
    · exact hun a hm
  · -- a mark stays
    intro a τ c hc hm
    rw [(hyesAt a τ c hc).failed]
    exact hm
  · -- "decodes" rides
    intro a τ c hc hd
    exact T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) hd

/-- **THE LOOKUP's ROW AT THE TABLE, at a layers' link**, at any block b whose decide says yes only
where K3.block's does. -/
theorem k3_lay_atTable (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hb : p.b = below b)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : LayOK set x)
    (hp : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [layRider x q tl D rad oW wOf nr nc extNone Unit]).ε
      (layRider x q tl D rad oW wOf nr nc extNone Unit)) = some p.err)
    (hsmp : ∀ s rs cols s', b.decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ s rs cols s', b.decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp)
    (T : LayAtTable (Fr := Fr) G x q tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW claim N
      Mg links ps pi k m (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
    p.Own (onQ N Mg links ps (fun s => (pi, s)) k) (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) :=
  k3_lay_atTable_of G seatT arr smp smpW strW msgW p hext H.shape
    (k3_lay_goodIn_any (q := q) (tl := tl) (wOf := wOf) (nr := nr) (nc := nc) G seatT arr smp smpW
      strW msgW claim piece laid before guests b hyes p hb hback hext H hp hr hR hε hsmp hsmpW
      hstrW hseat σ₀ σW₀)
    (fun a τ c hc => by
      obtain ⟨-, -, hw, cols, hd⟩ := piece_hears_below p b hb hback a τ c hc
      exact ⟨piece, laid, before, guests, _, cols, hw, hyes _ _ _ _ hd⟩) T

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_lay_atTable_of
#print axioms VerifiableInference.OnPublicFiles.k3_lay_atTable
