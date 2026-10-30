-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK9.lean: the closing of a segment (K10): kind K9's members (the batching, the
one equation, the marking behind the closing: Johnson/Desc/First/Batch/Kind.lean, Text.lean, Place.lean) have like
outcomes at two states that are equal once wiped. Two definitions with code, one structure of type Prop and one local
notation; the rest are theorems.

Words. The wiped state (wipeS, Honest/K10/WipeS.lean) is the state with these targets set to zero: those of the
statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched row; the
rows on the table (the pile out.pending, and the claim at the chain's end) keep theirs; the wipings of parts do the like
to a part. Two outcomes are alike (AlikeE, Wipe/Alike.lean) if both refuse with the same word, or both return and the
two values are equal once wiped.

  wipeDrawn, wipeOut   what the draw and the door hand on, with the link's context (and the carried record) wiped
  LensWipe w Y     what is asked of a lens Y into a state with a wiping w: the part of the wiped state is the state's
                   part, wiped (wipePart, Wipe/WipeLenses.lean); parts that are equal once wiped, laid into states that
                   are equal under w, give states that are equal under w

What is proved.
  thereA, pair_rel, pair_parts, wipePart_parts, LensWipe.part   small laws on a value that must be there, on pairs and
                   on parts
  drawn_wipe, drawnClean_wipe   the draw commutes with the wiping of the context
  equation_wipe, termsRow_wipe, termsRow_rel   the one equation and the row of its terms read no target: the same value
                   at the wiped arguments
  takeN_rel, asRow_rel, door_rel   the door: the row that it lays is the same at both, its target too (it is made of the
                   sub-proof's ledger); the records behind it are equal once wiped
  drawAlone_decides2, adds_decides2, batch_whole2, oneEquation_decides2   the members, at any lens with LensWipe
  atS_lensWipe, shut_whole2   the lens at the first chain's state; the marking behind the closing
  **batch2**, **closeOf2**   the fields batch and closeOf of SeatKeeps2 (Wipe/Lots2.lean) at wipeS

By what. The members' texts are followed bind by bind with the laws of AlikeE (Wipe/Alike.lean, Wipe/Carry.lean), at two
states at once; the ground's two functions by Wipe/WipeGround.lean (takeMaskP_rel, addRowP_rel); K10's own member by
closing_whole2 (Wipe/KeepK10.lean).

Limits. The laws speak of all states, reachable or not. That the claims' function has like outcomes is a premise
(FnCl2). No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Carry
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeLenses
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK10
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement Row ReqFrame ReqTerm ReqRows)
open OnBytes.Model (LinkCtx Fork)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Lens Where Drawn Out Equation St RowsOwed there drawn drawnClean drawAlone adds
  batch oneEquation equation termsRow messageNow takeN asRow door shut closeOf atS)

variable {T Cl X : Type}

/-- K9's part of a state, by its full name: the short one is taken in this namespace. -/
local notation "Part9" => VerifiableInference.Desc.K9.Part

/-! ## 1 Small laws -/

/-- A value that must be there: two Options with equal images under u give like outcomes. -/
theorem thereA {α β : Type} {u : α → β} {n : String} {o o' : Option α} (ho : o.map u = o'.map u) :
    AlikeE u (there n o) (there n o') := by
  rcases Carry.optA ho with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · subst h1 h2
    exact AlikeE.error n
  · subst h1 h2
    exact AlikeE.ok ha

/-- The same value beside two carried records that are equal once wiped: the pairs are equal under the wiping. -/
theorem pair_rel {α : Type} (a : α) {d d' : St X} (h : wipeD d = wipeD d') :
    Prod.map id wipeD (a, d) = Prod.map id wipeD (a, d') := congrArg (fun z => (a, z)) h

/-- Two pairs that are equal under the wiping of the record have equal first parts, and records equal once wiped. -/
theorem pair_parts {α : Type} {x x' : α × St X} (h : Prod.map id wipeD x = Prod.map id wipeD x') :
    x.1 = x'.1 ∧ wipeD x.2 = wipeD x'.2 :=
  ⟨(congrArg Prod.fst h :), (congrArg Prod.snd h :)⟩

/-- Two parts that are equal once wiped agree in every field; in the context and the record, once these are wiped. -/
theorem wipePart_parts {p p' : Part9} (h : wipePart p = wipePart p') :
    p.owed = p'.owed ∧ p.used = p'.used ∧ p.laid = p'.laid ∧ wipeCtx p.L = wipeCtx p'.L ∧ p.F = p'.F ∧
      wipeD p.d = wipeD p'.d :=
  ⟨(congrArg (fun z : Part9 => z.owed) h :), (congrArg (fun z : Part9 => z.used) h :),
    (congrArg (fun z : Part9 => z.laid) h :), (congrArg (fun z : Part9 => z.L) h :),
    (congrArg (fun z : Part9 => z.F) h :), (congrArg (fun z : Part9 => z.d) h :)⟩

/-! ## 2 The lens -/

/-- **What is asked of a lens** into a state with a wiping w. -/
structure LensWipe (w : T → T) (Y : Lens T) : Prop where
  get : ∀ t, Y.get? (w t) = (Y.get? t).map wipePart
  set : ∀ t t' p p', w t = w t' → wipePart p = wipePart p' → w (Y.set t p) = w (Y.set t' p')

/-- The parts of two states that are equal under w are alike. -/
theorem LensWipe.part {w : T → T} {Y : Lens T} (hY : LensWipe w Y) {t t' : T} (h : w t = w t') :
    AlikeE wipePart (Y.part t) (Y.part t') := by
  have e : (Y.get? t).map wipePart = (Y.get? t').map wipePart := by rw [← hY.get t, ← hY.get t', h]
  exact thereA e

/-- The lens at the first chain's state meets LensWipe at wipeS. -/
theorem atS_lensWipe : LensWipe wipeS atS where
  get := atSGet_wipe
  set := fun t t' p p' ht hp => by rw [atSSet_wipe, atSSet_wipe, ht, hp]

/-! ## 3 The batching -/

/-- What the draw hands on, the link's context wiped. -/
def wipeDrawn (o : Drawn) : Drawn := { o with L := wipeCtx o.L }

/-- The draw commutes with the wiping of the context. -/
theorem drawn_wipe (rows : Nat) (chi : E) (owed : RowsOwed) (used : Nat) (L : LinkCtx) (F : Fork) :
    drawn rows chi owed used (wipeCtx L) F = (drawn rows chi owed used L F).map wipeDrawn := by
  unfold drawn
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  rfl

/-- The draw at an empty ledger commutes with the wiping of the context. -/
theorem drawnClean_wipe (rows : Nat) (chi : E) (owed : RowsOwed) (used : Nat) (F : Fork) (L : LinkCtx) :
    drawnClean rows chi owed used (wipeCtx L) F = (drawnClean rows chi owed used L F).map wipeDrawn := by
  unfold drawnClean
  refine Carry.bindE wipeDrawn wipeDrawn (drawn_wipe rows chi owed used L F) fun o => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  rfl

/-- The member that draws alone has like outcomes at two states that are equal under w. -/
theorem drawAlone_decides2 {w : T → T} {Y : Lens T} (hY : LensWipe w Y) (p : Where) :
    Decides2 w (drawAlone (Cl := Cl) Y p) := by
  intro t t' rs gs gs' ht _
  rcases rs with _ | ⟨r, _ | ⟨r', l⟩⟩
  · exact AlikeE.error _
  · refine AlikeE.bind' (hY.part ht) fun s s' hs => ?_
    obtain ⟨h1, h2, -, h4, h5, -⟩ := wipePart_parts hs
    refine AlikeE.head' fun chi => ?_
    have hd : AlikeE wipeDrawn (drawnClean p.rows chi s.owed s.used s.L s.F)
        (drawnClean p.rows chi s'.owed s'.used s'.L s'.F) := by
      rw [h1, h2, h5]
      exact Carry.relE (u := wipeCtx) (f := fun L => drawnClean p.rows chi s'.owed s'.used L s'.F)
        (drawnClean_wipe p.rows chi s'.owed s'.used s'.F) h4
    refine AlikeE.bind' hd fun o o' ho => ?_
    have k1 : o.owed = o'.owed := (congrArg (fun z : Drawn => z.owed) ho :)
    have k2 : wipeCtx o.L = wipeCtx o'.L := (congrArg (fun z : Drawn => z.L) ho :)
    have k3 : o.F = o'.F := (congrArg (fun z : Drawn => z.F) ho :)
    refine AlikeE.ok (hY.set t t' _ _ ht ?_)
    show ({ wipePart s with owed := o.owed, L := wipeCtx o.L, F := o.F } : Part9) =
      { wipePart s' with owed := o'.owed, L := wipeCtx o'.L, F := o'.F }
    rw [hs, k1, k2, k3]
  · exact AlikeE.error _

/-- The member that makes and adds claims has like outcomes, if the claims' function has. -/
theorem adds_decides2 {w : T → T} {Y : Lens T} (hY : LensWipe w Y) (p : Where) (piece : Nat) (what : String)
    {claims : T → Except String (List Claim × T)} (hc : FnCl2 w claims) :
    Decides2 w (adds (Cl := Cl) Y p piece what claims) := by
  intro t t' rs gs gs' ht _
  refine AlikeE.bind' (hY.part ht) fun s₀ s₀' h0 => ?_
  have hh : s₀.L.handed = s₀'.L.handed := (congrArg (fun z : Part9 => z.L.handed) h0 :)
  refine AlikeE.head_eq' (congrArg (VerifiableInference.Desc.K9.need "K9.draw-has-run") hh) fun _ => ?_
  refine AlikeE.bind' (hc t t' ht) fun x x' hx => ?_
  have hx1 : x.1 = x'.1 := (congrArg Prod.fst hx :)
  have hx2 : w x.2 = w x'.2 := (congrArg Prod.snd hx :)
  refine AlikeE.bind' (hY.part hx2) fun s s' hs => ?_
  have hF : s.F = s'.F := (wipePart_parts hs).2.2.2.2.1
  refine AlikeE.head_eq' (by rw [hF, hx1]) fun F => ?_
  refine AlikeE.ok (hY.set _ _ _ _ hx2 ?_)
  show ({ wipePart s with F := F } : Part9) = { wipePart s' with F := F }
  rw [hs]

/-- **The batching** has like outcomes, if the claims' function has; it states no run. -/
theorem batch_whole2 {w : T → T} {Y : Lens T} (hY : LensWipe w Y) (p : Where)
    {claims : T → Except String (List Claim × T)} (hc : FnCl2 w claims) : Whole2 w (batch Y p claims) := by
  refine ⟨fun t t' rs gs gs' ht hg => ?_, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  exact AlikeE.bind' (drawAlone_decides2 hY p t t' rs gs gs' ht hg) fun t₁ t₁' h1 =>
    adds_decides2 hY p p.piece "the segment's" hc t₁ t₁' [] [] [] h1 SameG.rfl'

/-! ## 4 The one equation -/

/-- The one equation is the same at the wiped context: it reads no frame's rows. -/
theorem equation_wipe (L : LinkCtx) (F : Fork) : equation (wipeCtx L) F = equation L F := by
  unfold equation VerifiableInference.Desc.K9.allTerms
  rfl

/-- The row of the equation's terms is the same at a frame and a statement and at both wiped. -/
theorem termsRow_wipe (lay : OnBytes.Params.ReqLayout) (f : ReqFrame) (U : Statement) :
    ∀ (ts : List ReqTerm) (row : Row),
      termsRow lay (wipeFrame f) (wipeSt U) ts row = termsRow lay f U ts row
  | [], _ => rfl
  | t :: ts, row => by
    refine Carry.sameE fun a => ?_
    refine Carry.sameE fun o => ?_
    refine Carry.sameEqE (by rw [rowBits_wipe, placeBits_wipe]) fun c => ?_
    exact termsRow_wipe lay f U ts _

/-- So it is the same at two frames and two statements that are equal once wiped. -/
theorem termsRow_rel (lay : OnBytes.Params.ReqLayout) {f f' : ReqFrame} {U U' : Statement}
    (hf : wipeFrame f = wipeFrame f') (hU : wipeSt U = wipeSt U') (ts : List ReqTerm) (row : Row) :
    termsRow lay f U ts row = termsRow lay f' U' ts row := by
  rw [← termsRow_wipe lay f U ts row, ← termsRow_wipe lay f' U' ts row, hf, hU]

/-- The next free mask entries: the same list, and records that are equal once wiped. -/
theorem takeN_rel (o : Nat) : ∀ (n : Nat) (d d' : St X) (acc : List Nat), wipeD d = wipeD d' →
    AlikeE (Prod.map id wipeD) (takeN o n d acc) (takeN o n d' acc)
  | 0, d, d', acc, h => AlikeE.ok (pair_rel acc.reverse h)
  | n + 1, d, d', acc, h => by
    refine AlikeE.bind' (thereA (takeMaskP_rel h o)) fun x x' hx => ?_
    obtain ⟨h1, h2⟩ := pair_parts hx
    rw [h1]
    exact takeN_rel o n x.2 x'.2 (x'.1 :: acc) h2

/-- **The equation as a row**: the same row at both, its target too; the records behind are equal once wiped. -/
theorem asRow_rel (R : ReqRows) {f f' : ReqFrame} (q : Equation) {d d' : St X}
    (hf : wipeFrame f = wipeFrame f') (hd : wipeD d = wipeD d') :
    AlikeE (Prod.map id wipeD) (asRow R f q d) (asRow R f' q d') := by
  have hst : wipeSt d.st = wipeSt d'.st := (congrArg (fun z : St X => z.st) hd :)
  have h1 : f.shape = f'.shape := (congrArg (fun z : ReqFrame => z.shape) hf :)
  have h2 : f.link = f'.link := (congrArg (fun z : ReqFrame => z.link) hf :)
  have h3 : ∀ a b, messageNow f a b = messageNow f' a b :=
    fun a b => (congrArg (fun z : ReqFrame => messageNow z a b) hf :)
  unfold asRow
  rw [termsRow_rel R.layout hf hst, h1, h2]
  refine AlikeE.head' fun row => ?_
  refine Carry.iteA (AlikeE.ok (pair_rel _ hd)) ?_
  refine AlikeE.head' fun m => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head_eq' (congrArg (there "K9.mask-message-here") (h3 _ _)) fun o => ?_
  refine AlikeE.bind' (takeN_rel o _ d d' [] hd) fun x x' hx => ?_
  obtain ⟨k1, k2⟩ := pair_parts hx
  rw [k1]
  refine AlikeE.head' fun _ => ?_
  exact AlikeE.ok (pair_rel _ k2)

/-- What the door hands on, the link's context and the carried record wiped. -/
def wipeOut (o : Out X) : Out X := { o with L := wipeCtx o.L, d := wipeD o.d }

/-- **The door** has like outcomes at contexts and records that are equal once wiped. -/
theorem door_rel (owed : RowsOwed) (laid : Option Nat) {L L' : LinkCtx} (F : Fork) {d d' : St X}
    (hL : wipeCtx L = wipeCtx L') (hd : wipeD d = wipeD d') :
    AlikeE wipeOut (door owed laid L F d) (door owed laid L' F d') := by
  have e1 : equation L F = equation L' F := by rw [← equation_wipe L F, ← equation_wipe L' F, hL]
  have b1 : (L.link == L.check.link) = (L'.link == L'.check.link) :=
    (congrArg (fun z : LinkCtx => z.link == z.check.link) hL :)
  have b2 : (L.check.inLink && L.check.moments == L.check.momentsDue) =
      (L'.check.inLink && L'.check.moments == L'.check.momentsDue) :=
    (congrArg (fun z : LinkCtx => z.check.inLink && z.check.moments == z.check.momentsDue) hL :)
  have hr : L.check.rows = L'.check.rows := (congrArg (fun z : LinkCtx => z.check.rows) hL :)
  have hf : wipeFrame L.check.frame = wipeFrame L'.check.frame :=
    (congrArg (fun z : LinkCtx => z.check.frame) hL :)
  have hg : L.check.group = L'.check.group := (congrArg (fun z : LinkCtx => z.check.group) hL :)
  unfold door
  refine AlikeE.head' fun n => ?_
  refine AlikeE.head_eq' e1 fun x => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head_eq' (congrArg (VerifiableInference.Desc.K9.need "K9.link-is-the-walks") b1) fun _ => ?_
  refine AlikeE.head_eq' (congrArg (VerifiableInference.Desc.K9.need "K9.moments-passed") b2) fun _ => ?_
  have ha : AlikeE (Prod.map id wipeD) (asRow L.check.rows L.check.frame x.1 d)
      (asRow L'.check.rows L'.check.frame x.1 d') := by
    rw [hr]
    exact asRow_rel L'.check.rows x.1 hf hd
  refine AlikeE.bind' ha fun y y' hy => ?_
  obtain ⟨k1, k2⟩ := pair_parts hy
  have hp : (VerifiableInference.Desc.Ground.addRowP y.2 L.check.group y.1).map wipeD =
      (VerifiableInference.Desc.Ground.addRowP y'.2 L'.check.group y'.1).map wipeD := by
    rw [k1, hg]
    exact addRowP_rel k2 L'.check.group rfl
  refine AlikeE.bind' (thereA hp) fun e e' he => ?_
  refine AlikeE.ok ?_
  show ({ owed := none, L := wipeCtx L, F := x.2, d := wipeD e } : Out X) =
    { owed := none, L := wipeCtx L', F := x.2, d := wipeD e' }
  rw [hL, he]

/-- The member that adds the one equation as a row has like outcomes at two states that are equal under w. -/
theorem oneEquation_decides2 {w : T → T} {Y : Lens T} (hY : LensWipe w Y) (p : Where) :
    Decides2 w (oneEquation (Cl := Cl) Y p) := by
  intro t t' rs gs gs' ht _
  refine AlikeE.bind' (hY.part ht) fun s s' hs => ?_
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := wipePart_parts hs
  have hd : AlikeE wipeOut (door s.owed s.laid s.L s.F s.d) (door s'.owed s'.laid s'.L s'.F s'.d) := by
    rw [h1, h3, h5]
    exact door_rel s'.owed s'.laid s'.F h4 h6
  refine AlikeE.bind' hd fun o o' ho => ?_
  have k1 : o.owed = o'.owed := (congrArg (fun z : Out Unit => z.owed) ho :)
  have k2 : wipeCtx o.L = wipeCtx o'.L := (congrArg (fun z : Out Unit => z.L) ho :)
  have k3 : o.F = o'.F := (congrArg (fun z : Out Unit => z.F) ho :)
  have k4 : wipeD o.d = wipeD o'.d := (congrArg (fun z : Out Unit => z.d) ho :)
  refine AlikeE.ok (hY.set t t' _ _ ht ?_)
  show ({ wipePart s with owed := o.owed, L := wipeCtx o.L, F := o.F, d := wipeD o.d } : Part9) =
    { wipePart s' with owed := o'.owed, L := wipeCtx o'.L, F := o'.F, d := wipeD o'.d }
  rw [hs, k1, k2, k3, k4]

/-! ## 5 At the first chain's state -/

/-- The marking behind the closing commutes with the wiping; it states no run. -/
theorem shut_whole2 (p : Where) (piece : Nat) : Whole2 wipeS (shut (Cl := Cl) p piece) := by
  refine ⟨Decides2.of_comm (fun _ _ _ _ => rfl) fun s rs gs => ?_, (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩
  have hx : there "K9.in-a-segment" (wipeS s).link? = (there "K9.in-a-segment" s.link?).map wipeCtx := by
    rw [link?_wipe]
    cases s.link? <;> rfl
  refine Carry.bindE wipeCtx wipeS hx fun L => ?_
  exact congrArg Except.ok (putLink_wipe s (VerifiableInference.Desc.K9.closed L L.check.frame)).symm

/-- **The batching at the first chain's state** has like outcomes, if the claims' function has. -/
theorem batch2 (p : Where) {claims : S → Except String (List Claim × S)} (hc : FnCl2 wipeS claims) :
    Whole2 wipeS (batch atS p claims) := batch_whole2 atS_lensWipe p hc

/-- **Each of the three members that close a segment** has like outcomes at two states that are equal once wiped. -/
theorem closeOf2 (p : Where) (P : VerifiableInference.Desc.First.Close.Par) :
    ∀ b ∈ closeOf (Cl := Unit) p P, Whole2 wipeS b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEquation_decides2 (Cl := Unit) atS_lensWipe p, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  · exact closing_whole2 P
  · exact shut_whole2 p _

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.thereA
#print axioms ProofFile.Honest.K10.pair_rel
#print axioms ProofFile.Honest.K10.pair_parts
#print axioms ProofFile.Honest.K10.wipePart_parts
#print axioms ProofFile.Honest.K10.LensWipe
#print axioms ProofFile.Honest.K10.LensWipe.part
#print axioms ProofFile.Honest.K10.atS_lensWipe
#print axioms ProofFile.Honest.K10.wipeDrawn
#print axioms ProofFile.Honest.K10.drawn_wipe
#print axioms ProofFile.Honest.K10.drawnClean_wipe
#print axioms ProofFile.Honest.K10.drawAlone_decides2
#print axioms ProofFile.Honest.K10.adds_decides2
#print axioms ProofFile.Honest.K10.batch_whole2
#print axioms ProofFile.Honest.K10.equation_wipe
#print axioms ProofFile.Honest.K10.termsRow_wipe
#print axioms ProofFile.Honest.K10.termsRow_rel
#print axioms ProofFile.Honest.K10.takeN_rel
#print axioms ProofFile.Honest.K10.asRow_rel
#print axioms ProofFile.Honest.K10.wipeOut
#print axioms ProofFile.Honest.K10.door_rel
#print axioms ProofFile.Honest.K10.oneEquation_decides2
#print axioms ProofFile.Honest.K10.shut_whole2
#print axioms ProofFile.Honest.K10.batch2
#print axioms ProofFile.Honest.K10.closeOf2
