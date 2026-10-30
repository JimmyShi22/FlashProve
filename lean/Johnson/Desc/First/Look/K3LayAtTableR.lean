-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3LayAtTableR.lean: the lookup on a LAYERS' link's calls AT THE TABLE OF
JOINTS, IN THE SECOND FORM OF THE CHAIN OF PROMISES: LayAtTableR := LayAtTable with the letter Rc a
premise more wherever a field has the promise in front (objects, behind), AND ONE FIELD ownIn IN THE
PLACE OF codesIn, askLive, fLive; the row ends in p.Own (onR ...) (onQ ... (k + 1)) through
ownAtTableWideR (Johnson/Desc/Sound/OwnAtTableR.lean). The layers' like of K3AttAtTableR.lean.
THE TEXT IS THE FIRST FORM's (Johnson/Desc/First/Look/K3LayAtTable.lean), TURNED BY A PROGRAM, after
the pattern at the
head's calls (Johnson/Desc/First/Look/K3HeadAtTableR.lean); the law beneath is called as it lies;
the first form's file is not touched. NO SOUNDNESS IS CLAIMED.

Used by K3CallsBehindR.lean, K3CallsMeanR.lean, K3CallsSeatLawsR.lean (Johnson/Desc/First/Look/) and
  1 more.
OBJECT, LETTERS: the first form's; and Rc (Rch): a condition on the statement that stands
  beside the table's promise in front (meant: "this verifier's state is reached from the state at
  the start by the sub-protocols in front"): A LETTER: no term is named here.

Main names: `LayAtTableR`, `k3_lay_atTable_ofR`.

Limits. The first form's. Rc is a letter; ownIn is a premise, shown at no term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LayAtTable
import Johnson.Desc.Sound.OwnAtTableR

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
  (Rc : Desc.First.S × Fr.E.Str → Prop)

/-- **What is asked beside the law.** Yes a b: the piece says yes at a and puts out b. -/
structure LayAtTableR : Prop where
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
  /-- the state's own numbers are the plan's at this link: the codes, the open link's number and
  list of arrays, the live copy's shape and layout: ONE SENTENCE, a fact along the fold -/
  ownIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none → OwnIs D x.link a.1
  objects : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    Rc a → a.1.failed = none → Yes a b → SameBut a.1 b.1 →
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
    Rc a → a.1.failed = none → Yes a b → SameBut a.1 b.1 →
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
  {ps : List Desc.Place} {pi : P} {k m : ℕ} (Rc : Desc.First.S × Fr.E.Str → Prop)

/-- **THE LOOKUP's ROW AT THE TABLE, at a layers' link: THE RULE**: from ANY law of the piece
between our conditions and relations, and "a yes of the piece is a yes of K3.block's decide at the
place's parameters, at rounds whose words are below the prime". -/
theorem k3_lay_atTable_ofR
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
    (T : LayAtTableR (Fr := Fr) G x q tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW claim
      N Mg links ps pi k m (fun a c => ∃ τ, p.ior.red.out a τ = some c) Rc) :
    p.Own (onR N Mg links ps (fun s => (pi, s)) (fun _ => Rc) k)
      (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) := by
  have hyesAt : ∀ a τ c, p.ior.red.out a τ = some c → SameBut a.1 c.1 := by
    intro a τ c hc
    obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ := hY a τ c hc
    exact k3_calls_sameBut claim piece laid before _ guests _ _ rs cols hd
  have hun : ∀ a : Desc.First.S × Fr.E.Str, ¬ a.1.failed ≠ none → a.1.failed = none :=
    fun a h => Classical.not_not.1 h
  refine ownAtTableWideR N Mg links ps (fun s => (pi, s)) (fun _ => Rc) k p _ _ _ _ law
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- t1
    intro a ha hr hm
    obtain ⟨hq, hc⟩ := onQ_arm ha (hun a hm)
    exact k3_lay_t1 G seatT smp smpW strW claim a (T.ownIn a ha hr (hun a hm))
      (fun i => T.cf i _ _ (hc _ (T.seats i)).1 (hc _ (T.seats i)).2.1 (hc _ (T.seats i)).2.2)
      (T.tabIn a ha.1) (k3LookIn_onIn (T.pubIn _ (hq _ T.askIn)))
  · -- t2
    intro a τ c ha hr hm hc _
    obtain ⟨hq, -⟩ := onQ_arm ha (hun a hm)
    obtain ⟨piece, laid, before, guests, rs, cols, hw, hd⟩ := hY a τ c hc
    exact T.behind a c ha hr (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc)
      (k3_calls_lookOut claim piece laid before _ guests hs rfl a.1 c.1 rs cols hw hd
        (k3LookIn_onIn (T.pubIn _ (hq _ T.askIn))))
      (T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) ha.1)
  · -- t3
    intro a τ c w ha hr hm hc ho' hw
    obtain ⟨hq, -⟩ := onQ_arm ha (hun a hm)
    obtain ⟨piece, laid, before, guests, rs, cols, hwd, hd⟩ := hY a τ c hc
    have hout := k3_calls_lookOut claim piece laid before _ guests hs rfl a.1 c.1 rs cols hwd hd
      (k3LookIn_onIn (T.pubIn _ (hq _ T.askIn)))
    have hbe := T.behind a c ha hr (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc) hout
      (T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) ha.1)
    have ho : ∀ i, i ∈ (rowQ links ps k).outs → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_left _ hi))
    have hx : ∀ i, i ∈ (rowQ links ps k).ctx → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_right _ hi))
    rw [T.outs] at ho
    rw [T.ctx] at hx
    exact k3_lay_t3 G seatT arr msgW _ _ smp smpW strW _ c w
      ⟨T.pinIn _ _ _ (hx (.pin m 0) (by simp)), T.pinWIn c w (hx .pinW (by simp))⟩ ho'
      (T.objects a c ha hr (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc) hout hbe w
        (ho (.formsT m 2 "objects") (by simp)))
      (T.worthP _ _ _ (ho (.worth m 2 "planes") (by simp)))
      (T.worthK _ _ _ (ho (.worth m 2 "keys") (by simp)))
      (T.worthR _ _ _ (ho (.worth m 2 "rider") (by simp)))
  · -- t4
    intro a τ c w _ _ hm hc _ hw hRa
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

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_lay_atTable_ofR
