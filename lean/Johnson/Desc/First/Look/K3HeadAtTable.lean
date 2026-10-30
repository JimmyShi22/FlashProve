-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadAtTable.lean: the kind "lookup" (K3), the lookup on the calls AT THE
HEAD's LINK: its row of the table of joints, from its law; and what the kind's files owe at that
seat (`SeatLaws`). After the pattern of Johnson/Desc/First/Look/K3LayAtTable.lean, K3RowsStated.lean
and K3CallsSeatLaws.lean, which do the same at a layers' link.

Why. The chain of promises asks a tie at the table's own words of every block. At 24 of the 25 links
the lookup on the calls has its row from the files named above. The head's law
(Johnson/Desc/First/Look/K3KeepsFree.lean: `k3_head_free_at`) stands between other conditions: a
token is heard; the keys are read at that token; what the lookup left, and the free room above the
ledger's next slot, ride.

Main names:
  `HeadAtTable`: what is asked beside the law, a field a sentence: the row's three lists; which
    public items are open in front; what each letter of the table's meaning gives or takes.
  `k3_head_atTable_of`: from ANY law of the piece between the head's four conditions and relations,
    "a yes of the piece is a yes of K3.block's decide", and `HeadAtTable`: the row's own law.
  `k3_head_atTable_stated`: the same at a piece that holds the strict reading of a block that
    narrows what `K3.theStated` returns at the head's address.
  `k3_head_seatLaws`: `SeatLaws` at that constant; the kind's letter "the request" is there a
    function of the public part.

WHERE IT PARTS FROM THE LAYERS' FILE: the pieces are 3, not 2; the first item in front is
`lookCallsHeard`; the places are read by `headNu`, at the head's addresses (there: `layNu`); the
keys and the rider are read at the reply that the record has heard (`replyTok?`, 0 where none);
three fields more in front (`qIn`, `tokIn`, `freeIn`); `model` is asked only where the promise in
front holds and no mark stands, with the stored table's pin in hand; `behind` is handed two facts
more (what the lookup left; the free room).

THE GUARD. The keys at the head's calls read the output matrix's weights; the two
kinds whose laws meet at the items worth (this kind's, which spends them; the head's kind's, which
pays them) read these weights alike just where the witness's cells hold an index. So the three
fields on worth are asked under a guard on the witness, the letter gd (meant: the witness's cells
hold an index). The law bears it: on a good transcript it is pointwise in the witness, and the
extractor is the identity; so it holds between "gd w → the relation in front" and "gd w → the
relation behind". Where gd w fails, the two items in front hold of themselves (`free`) and the
row's context goes back past the accepting (`pinBack`, `smallBack`, `pinWBack`). Also:
`objects` is asked behind an accepting at a statement inside the promise, not at every state.

Limits: a rule over letters. `HeadAtTable` is a premise: it is shown at no filling of the table's
meaning and has not been tried for emptiness. The letter Q (what is known of the ledger in front) is
free. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3KeepsFree
import Johnson.Desc.First.Look.K3RowsStated
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider HeadOK head_says)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy] [Desc.Kinds.Head.Request]

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (adr : HeadAdr)
  (x : Desc.First.Look.Place) (tl : HTailF2) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
  (set : Params.Setting)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)
  (gd : Desc.Wit Cells Tok MsgT → Prop)
  (claim : Aff → Cl) (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) (links : List ModelPart)
  (ps : List Desc.Place) (pi : P) (k m : ℕ)
  (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)

local notation "theR" => headRider adr x tl D rad oW wOf nr nc extNone Unit

/-- **What is asked beside the law, at the head's link.** Yes a b: the piece says yes at a and puts
out b. -/
structure HeadAtTable : Prop where
  ins : (rowQ links ps k).ins = [.constr m .lookCallsHeard, .constr m .rider]
  outs : (rowQ links ps k).outs =
    [.formsT m 3 "objects", .worth m 3 "planes", .worth m 3 "keys", .worth m 3 "rider"]
  ctx : (rowQ links ps k).ctx = [.pin m 0, .constr m .small, .pinW]
  askIn : Pub.lookIn m 3 ∈ (pubSets Mg.more links ps)[k]?.getD []
  seats : ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD [])
  pubIn : ∀ s, Mg.pub (.lookIn m 3) (pi, s) = true →
    k3LookIn (Desc.First.Look.P.ofPlace set false x) (D.arrayOf.getD x.link #[]) s = true
  /-- what is known of the ledger in front -/
  qIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → ∀ F, (Desc.K3.seatCalls claim).fork a.1 = some F → Q F
  /-- a reply has been heard -/
  tokIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → a.1.replyTok?.isSome = true
  /-- the ledger is free above its next slot -/
  freeIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → FreeAt (Desc.K3.seatCalls claim).fork a.1
  /-- asked behind a yes of the piece at a statement inside the promise and without a mark, not at
  every state -/
  objects : ∀ (a b : Desc.First.S × Fr.E.Str) w, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → Yes a b → Mg.formsT m 3 "objects" (pi, b.1) (strsOf Fr b.2) w →
    K3Objects (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (headNu adr x tl D rad oW wOf nr nc seatT arr msgW) b.1 w
  worthP : ∀ s y w, Mg.worth m 3 "planes" (pi, s) y w → gd w →
    K3WorthPlanes (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm
      x.F.next (headNu adr x tl D rad oW wOf nr nc seatT arr msgW) s w
  /-- the keys, AT THE REPLY THAT THE RECORD HAS HEARD (written out: `K3WorthKeys` takes keys that
  read the witness alone) -/
  worthK : ∀ (s : Desc.First.S) y w, Mg.worth m 3 "keys" (pi, s) y w → gd w → ∀ g F',
    (Desc.K3.seatCalls claim).fork s = some F' → (Desc.K3.seatCalls claim).heard s = some g →
    K3OutKeys x.fs x.lm x.F.next (headNu adr x tl D rad oW wOf nr nc seatT arr msgW w)
      (forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns tl nr nc) (s.replyTok?.getD 0)
        (zext (layMu x tl D rad oW wOf nr nc seatT arr msgW w))) Reading.gl g F'
  /-- the rider, at that reply -/
  worthR : ∀ (s : Desc.First.S) y w, Mg.worth m 3 "rider" (pi, s) y w → gd w → ∀ g F',
    (Desc.K3.seatCalls claim).fork s = some F' → (Desc.K3.seatCalls claim).heard s = some g →
    K3OutRider theR x.lm x.F.next (s.replyTok?.getD 0) (layMs x D rad oW seatT arr msgW w) g F'
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
  /-- the head's sentence at the heard reply gives the two items in front: asked where the promise
  in front holds and no mark stands (so a reply is heard, and it is a token), with the stored
  table's pin in hand (the row's ctx has it) -/
  model : ∀ (a : Desc.First.S × Fr.E.Str) w, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none →
    HeadSays adr x tl D rad oW wOf nr nc (a.1.replyTok?.getD 0)
      (layMs x D rad oW seatT arr msgW w) →
    Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w → Mg.pinW (pi, a.1) (strsOf Fr a.2) w →
    Mg.constr m .lookCallsHeard (pi, a.1) (strsOf Fr a.2) w ∧
      Mg.constr m .rider (pi, a.1) (strsOf Fr a.2) w
  /-- where the guard fails, the two items in front hold of themselves (they bear a guard of their
  own, which the stored table's pin turns into this one) -/
  free : ∀ (a : Desc.First.S × Fr.E.Str) w, ¬ gd w → Mg.pinW (pi, a.1) (strsOf Fr a.2) w →
    Mg.constr m .lookCallsHeard (pi, a.1) (strsOf Fr a.2) w ∧
      Mg.constr m .rider (pi, a.1) (strsOf Fr a.2) w
  /-- the stored table's pin goes back past the yes -/
  pinWBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    Mg.pinW (pi, b.1) (strsOf Fr b.2) w → Mg.pinW (pi, a.1) (strsOf Fr a.2) w
  smallBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    Mg.constr m .small (pi, b.1) (strsOf Fr b.2) w → Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w
  behind : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
    a.1.failed = none → Yes a b → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
    Mg.decodes (pi, b.1) (strsOf Fr b.2) →
    K3LeftAt (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next Q
      b.1 →
    FreeAt (Desc.K3.seatCalls claim).fork b.1 → onQ N Mg links ps (fun s => (pi, s)) (k + 1) b
  decodes : ∀ a b : Desc.First.S × Fr.E.Str, Yes a b → SameBut a.1 b.1 →
    Mg.decodes (pi, a.1) (strsOf Fr a.2) → Mg.decodes (pi, b.1) (strsOf Fr b.2)

end

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) {adr : HeadAdr}
  {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  {set : Params.Setting}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)
  (gd : Desc.Wit Cells Tok MsgT → Prop)
  {claim : Aff → Cl} {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {pi : P} {k m : ℕ}

/-- **THE LOOKUP's ROW AT THE TABLE, at the head's link: THE RULE.** -/
theorem k3_head_atTable_of
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hext : ∀ a τ w, p.ext a τ w = w)
    (hs : (Desc.First.Look.P.ofPlace set false x).shape = some x.fs)
    (law : p.GoodIn
      (HeadOnQ G x D rad oW seatT smp smpW strW (·.replyTok?) (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link) Q (FreeAt (Desc.K3.seatCalls claim).fork))
      (HeadOnQ' G x D rad oW seatT smp smpW strW (·.replyTok?) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link) Q
        (FreeAt (Desc.K3.seatCalls claim).fork))
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        fun s => s.replyTok?.getD 0)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (fun s => s.replyTok?.getD 0) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard))
    (hY : ∀ a τ c, p.ior.red.out a τ = some c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
          (Desc.First.Look.P.ofPlace set false x) guests).decide a.1 rs cols = .ok c.1)
    (T : HeadAtTable (Fr := Fr) G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q gd
      claim N Mg links ps pi k m (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
    p.Own (onQ N Mg links ps (fun s => (pi, s)) k) (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) := by
  have hyesAt : ∀ a τ c, p.ior.red.out a τ = some c → SameBut a.1 c.1 := by
    intro a τ c hc
    obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ := hY a τ c hc
    exact k3_calls_sameBut claim piece laid before _ guests _ _ rs cols hd
  have hun : ∀ a : Desc.First.S × Fr.E.Str, ¬ a.1.failed ≠ none → a.1.failed = none :=
    fun a h => Classical.not_not.1 h
  -- the law under the guard: on a good transcript it is pointwise in the witness
  have lawG := fun a ha => Doomed.mono _ _ (fun τ h b hb => And.intro (h b hb).1 fun w
    (hw : gd w → _) (hg : gd (p.ext a τ w)) => (h b hb).2 w (hw (by rw [hext] at hg; exact hg)))
    (law a ha)
  refine ownAtTableWide _ _ _ _ _ _ N Mg links ps (fun s => (pi, s)) k p _ _
    (fun a w => gd w → _) (fun b w => gd w → _) lawG ?_ ?_ ?_ ?_ ?_ ?_
  · -- t1
    intro a ha hm
    obtain ⟨hq, hc⟩ := onQ_arm ha (hun a hm)
    have o1 := T.codesIn a ha (hun a hm)
    obtain ⟨o2, o3⟩ := (T.fLive _).1 (hq _ T.askLive)
    exact ⟨⟨k3_lay_t1 G seatT smp smpW strW claim a
      (ownIs_of (p := Desc.First.Look.P.ofPlace set false x) (T.pubIn _ (hq _ T.askIn)) o1 o2 o3)
      (fun i => T.cf i _ _ (hc _ (T.seats i)).1 (hc _ (T.seats i)).2.1 (hc _ (T.seats i)).2.2)
      (T.tabIn a ha.1) (k3LookIn_onIn (T.pubIn _ (hq _ T.askIn))),
      T.qIn a ha (hun a hm)⟩, T.tokIn a ha (hun a hm), T.freeIn a ha (hun a hm)⟩
  · -- t2
    intro a τ c ha hm hc ho'
    obtain ⟨hq, -⟩ := onQ_arm ha (hun a hm)
    obtain ⟨piece, laid, before, guests, rs, cols, hw, hd⟩ := hY a τ c hc
    exact T.behind a c ha (hun a hm) ⟨τ, hc⟩ (hyesAt a τ c hc)
      (k3_calls_lookOut claim piece laid before _ guests hs rfl a.1 c.1 rs cols hw hd
        (k3LookIn_onIn (T.pubIn _ (hq _ T.askIn))))
      (T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) ha.1) ho'.1.2 ho'.2.2
  · -- t3
    intro a τ c w ha hm hc ho' hw hg
    have ho : ∀ i, i ∈ (rowQ links ps k).outs → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_left _ hi))
    have hx : ∀ i, i ∈ (rowQ links ps k).ctx → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_right _ hi))
    rw [T.outs] at ho
    rw [T.ctx] at hx
    obtain ⟨-, g, F', hf, hh, -, -⟩ := ho'.1.1
    exact ⟨⟨T.pinIn _ _ _ (hx (.pin m 0) (by simp)), T.pinWIn c w (hx .pinW (by simp))⟩, g, F', hf,
      hh,
      ⟨T.objects a c w ha (hun a hm) ⟨τ, hc⟩ (ho (.formsT m 3 "objects") (by simp)) g F' hf hh,
        T.worthP _ _ _ (ho (.worth m 3 "planes") (by simp)) hg g F' hf hh,
        T.worthK _ _ _ (ho (.worth m 3 "keys") (by simp)) hg g F' hf hh⟩,
      T.worthR _ _ _ (ho (.worth m 3 "rider") (by simp)) hg g F' hf hh⟩
  · -- t4
    intro a τ c w ha hm hc _ hw hRa
    rw [hext] at hRa ⊢
    have hx : ∀ i, i ∈ (rowQ links ps k).ctx → meansQ N Mg (fun s => (pi, s)) i c w :=
      fun i hi => hw i (List.mem_append_left _ (List.mem_append_right _ hi))
    rw [T.ctx] at hx
    have hsm : Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w :=
      T.smallBack a c w ⟨τ, hc⟩ (hyesAt a τ c hc) (hx (.constr m .small) (by simp))
    have hpw : Mg.pinW (pi, a.1) (strsOf Fr a.2) w :=
      T.pinWBack a c w ⟨τ, hc⟩ (hyesAt a τ c hc) (hx .pinW (by simp))
    obtain ⟨hk, hrd⟩ : Mg.constr m .lookCallsHeard (pi, a.1) (strsOf Fr a.2) w ∧
        Mg.constr m .rider (pi, a.1) (strsOf Fr a.2) w := by
      by_cases hg : gd w
      · exact T.model a w ha (hun a hm) (hRa hg).2 hsm hpw
      · exact T.free a w hg hpw
    intro i hi
    unfold insQ at hi
    rw [T.ins, T.ctx] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | (rfl | rfl | rfl)) | rfl
    · exact hk
    · exact hrd
    · exact T.pinBack a c w ⟨τ, hc⟩ (hyesAt a τ c hc) (hx (.pin m 0) (by simp))
    · exact hsm
    · exact hpw
    · exact hun a hm
  · -- a mark stays
    intro a τ c hc hm
    rw [(hyesAt a τ c hc).failed]
    exact hm
  · -- "decodes" rides
    intro a τ c hc hd
    exact T.decodes a c ⟨τ, hc⟩ (hyesAt a τ c hc) hd

end

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {adr : HeadAdr} {x : Desc.First.Look.Place} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc floor : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)
  (gd : Desc.Wit Cells Tok MsgT → Prop)
  {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {k m : ℕ}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **THE LOOKUP's ROW AT THE TABLE, AT WHAT IS SEATED, at the head's link.** -/
theorem k3_head_atTable_stated {pi : P} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (hl : a.link = some (headLink X)) (hpc : a.piece = Desc.K3.pieceAt X (headLink X) false)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hB : Desc.Kinds.Head.Law.headB floor x.fs = true)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp)
    (T : HeadAtTable (Fr := Fr) G adr x tl D rad oW wOf nr nc (Params.settingOf X.P.frame) seatT
      arr smp smpW strW msgW Q gd claim N Mg links ps pi k m
      (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
    p.Own (onQ N Mg links ps (fun s => (pi, s)) k) (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) :=
  k3_head_atTable_of G seatT arr smp smpW strW msgW Q gd p hext (headOK_at hx hB).shape
    (k3_head_free_at (floor := floor) G seatT arr smp smpW strW msgW Q claim readers codes shape a
      B B' h hOk hN p hp hx hl hpc hback hext hB hpl hr hR hcap hsmp hsmpW hstrW hseat σ₀ σW₀)
    (fun s τ c hc => by
      obtain ⟨laid, sent, rs, cols, hw, hd⟩ :=
        k3_calls_stated_yes claim readers codes shape a B B' h hOk hN p hp hl hpc
          (placeAt_headAt hx) hback s c τ hc
      exact ⟨a.piece, laid, sent, [], rs, cols, hw, hd⟩) T

omit [Desc.Kinds.Head.Request] in
/-- **WHAT IS OWED AT THE CALLS' SEAT OF THE HEAD's LINK.** rq: the kind's letter "the request", OF
THE PUBLIC PART: `SeatLaws` runs over every value z of the public part, and the head's keys read the
request: so the law is called, and `HeadAtTable` asked, at z's own request. -/
theorem k3_head_seatLaws (rq : P → Desc.Kinds.Head.Request) (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place) (Bst : Desc.Block Desc.First.S Cl)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (h : Desc.K3.theStated claim readers X codes shape a = some Bst) (hOk : Bst.planOk = true)
    (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (hl : a.link = some (headLink X)) (hpc : a.piece = Desc.K3.pieceAt X (headLink X) false)
    (hback : q.back = [])
    (hB : Desc.Kinds.Head.Law.headB floor x.fs = true)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs q.ds (theP).rounds)
    (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) q.ds)),
      strW (behind (ckP .two) Fr q.base q.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < q.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp)
    (T : ∀ B', SeatOf Bst B' → ∀ z : P, letI := rq z
      HeadAtTable (Fr := Fr) G adr x tl D rad oW wOf nr nc (Params.settingOf X.P.frame) seatT arr
        smp smpW strW msgW Q gd claim N Mg links ps z k m
        (fun a c => ∃ τ, (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some c))
    (rides : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) :
    SeatLaws links ps k q N Mg Bst := by
  -- the lemma's statement reads no request; it was typed under the letter: any value serves
  have e : placeAt X (headLink X) false = some theP :=
    letI : Desc.Kinds.Head.Request := ⟨fun _ => 0, 0, 0⟩
    placeAt_headAt hx
  have hT : ∀ B' : Desc.Block Desc.First.S Cl, B'.Narrows Bst → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 := by
    intro B' hN u τ v hout
    obtain ⟨laid, sent, rs, cols, -, hd⟩ := k3_calls_stated_yes claim readers codes shape a Bst B' h
      hOk hN
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
      rfl hl hpc e hback u v τ hout
    exact k3_calls_sameBut claim a.piece laid sent theP [] u.1 v.1 rs cols hd
  refine ⟨?_, rides, ?_, ?_⟩
  · intro B' hN z
    letI := rq z
    exact k3_head_atTable_stated (floor := floor) G seatT arr smp smpW strW msgW Q gd claim readers
      codes shape a Bst B' h hOk hN.1 _ rfl hx hl hpc hback (fun _ _ _ => rfl) hB hpl hr hR
      hcap hsmp hsmpW hstrW hseat σ₀ σW₀ (T B' hN z)
  · intro B' hN u τ v hout hm
    rw [(hT B' hN.1 u τ v hout).failed]
    exact hm
  · intro B' hN z u τ v hout hd
    letI := rq z
    exact (T B' hN z).decodes u v ⟨τ, hout⟩ (hT B' hN.1 u τ v hout) hd

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_head_atTable_of
#print axioms VerifiableInference.OnPublicFiles.k3_head_atTable_stated
#print axioms VerifiableInference.OnPublicFiles.k3_head_seatLaws
