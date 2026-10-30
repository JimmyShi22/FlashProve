-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK1.lean: the closing of a segment (K10): kind K1's members on the first chain
(the first segment's opening and a segment's later moment: Johnson/Desc/K1/Own.lean, First.lean, AtS.lean, Places.lean)
have like outcomes at two states that are equal once wiped. Five definitions with code and one local notation; the rest
are theorems.

Words. The wiped state (wipeS, Honest/K10/WipeS.lean) is the state with these targets set to zero: those of the
statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched row; the
rows on the table (the pile out.pending, and the claim at the chain's end) keep theirs; the wipings of parts do the like
to a part. Two outcomes are alike (AlikeE, Wipe/Alike.lean) if both refuse with the same word, or both return and the
two values are equal once wiped.

  wipeFD, wipeCD, wipeLF, wipeHeld, wipeOw   the wiping on a frame or a state of the calls beside a carried record, on a
                   link's context beside a fork, and on what a commitment's step carries

What is proved.
  layRows_rel, notSampled_wipe, decideSend_rel   the sending's decision: the sample rows that it lays are the same at
                   both, their targets too (they are made of the rounds' seeds and answers); the numbers returned are
                   the same, the records are equal once wiped
  joinAll_rel, joinOwnP_rel, groundJoin_rel   the joining of a moment's messages
  firstOwn_wiped, laterOwn_wiped   the opening's and a later moment's decision, at a wiped state of the calls and at
                   that state unwiped
  commitBehind_wiped, commitStep_wiped, commitOwn_wiped, commitCore, commitAtS_whole2   a commitment's step, around a
                   sending, up to the first chain's state
  **k1First2**, **k1Later2**   the fields k1First and k1Later of SeatKeeps2 (Wipe/Lots2.lean) at wipeS

By what. The texts are followed bind by bind and arm by arm with the laws of AlikeE (Wipe/Alike.lean, Wipe/Carry.lean);
the ground's four functions by Wipe/WipeGround.lean (newGroupP_rel, recvP_rel, admitP_rel, joinP_rel). What is asked of
a state of the calls or of a context unfolds to the same term at the wiped value and at the value. These members write
targets: at the wiped state the new rows bear their true targets. So the member at the wiped state is only like the
member at the state, and Decides2.of_wiped (Wipe/Alike.lean) is what applies.

Limits. The laws speak of all states, reachable or not. W's sending stands behind the last link and is not spoken of. No
property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Carry
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeLenses
import Johnson.Desc.K1.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement ReqFrame OracleShape)
open OnBytes.Model (ChainCheck LinkCtx Fork HTailF2)
open Desc.Plain (DState GPar)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Send (joinAll joinOwnP)
open VerifiableInference.Desc.K1 (Par Owing layRows decideSend firstOwn laterOwn commitOwn commitAtS firstSegmentOpening laterAt
  stateOf owedOf laid)

variable {L Cl : Type}

/-- The record of the seven ground functions, by its full name: the short one is taken in this namespace. -/
local notation "GroundP" => _root_.Desc.Plain.Ground

/-! ## 1 The sending's decision -/

/-- Message by message: the same sample rows, laid into records that are equal once wiped, give like outcomes. -/
theorem layRows_rel (codes : OnBytes.Codes) (seeds : List (List E × E)) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L), wipeD d = wipeD d' →
      AlikeE wipeD (layRows codes seeds l ys d) (layRows codes seeds l ys d')
  | [], ys, d, d', h => Carry.iteA (AlikeE.ok h) (AlikeE.error _)
  | (o, s) :: l, ys, d, d', h => by
    refine Carry.iteA (layRows_rel codes seeds l ys d d' h) ?_
    refine Carry.iteA (AlikeE.error _) ?_
    refine Carry.iteA (AlikeE.error _) ?_
    refine AlikeE.bind (AlikeE.named_alone (admitP_rel h o rfl)) fun e e' he => ?_
    exact layRows_rel codes seeds l (ys.drop s.answers) e e' he

/-- Whether a message is not yet sampled is the same at the wiped statement. -/
theorem notSampled_wipe (U : Statement) (o : Nat) :
    (((wipeSt U).oracles[o]?).map (!·.sampled)).getD false = ((U.oracles[o]?).map (!·.sampled)).getD false := by
  rw [wipeSt_oracle_at]
  cases U.oracles[o]? <;> rfl

/-- **The sending's decision**, at records that are equal once wiped: the same refusal, or the same numbers and records
that are equal once wiped. -/
theorem decideSend_rel (P : Par) (owed : Option Nat) {d d' : DState L} (h : wipeD d = wipeD d')
    (rs : List Fmt.RoundView) :
    AlikeE (Prod.map id wipeD) (decideSend P owed d rs) (decideSend P owed d' rs) := by
  have hc : d.st.codes = d'.st.codes := (congrArg (fun z : DState L => z.st.codes) h :)
  rcases rs with _ | ⟨r₁, _ | ⟨r₂, _ | ⟨r₃, l⟩⟩⟩
  · exact AlikeE.error _
  · exact AlikeE.error _
  · refine AlikeE.head' fun _ => ?_
    refine AlikeE.head_eq' (by rw [hc]) fun _ => ?_
    refine AlikeE.head' fun _ => ?_
    refine AlikeE.head' fun _ => ?_
    refine AlikeE.bind' (AlikeE.named_alone (recvP_rel h P.gp.firstTree P.sent)) fun x x' hx => ?_
    obtain ⟨k1, k2⟩ := Carry.pairParts hx
    have hst : wipeSt x.2.st = wipeSt x'.2.st := (congrArg (fun z : DState L => z.st) k2 :)
    have hs : ∀ o : Nat, ((x.2.st.oracles[o]?).map fun y : OnBytes.Oracle => !y.sampled).getD false =
        ((x'.2.st.oracles[o]?).map fun y : OnBytes.Oracle => !y.sampled).getD false := fun o => by
      rw [← notSampled_wipe x.2.st o, ← notSampled_wipe x'.2.st o, hst]
    rw [k1]
    refine AlikeE.head' fun _ => ?_
    refine AlikeE.head_eq' (by
      exact congrArg (fun p : Nat → Bool =>
        VerifiableInference.Desc.need "K1: a message was sampled before" (List.all _ p)) (funext hs)) fun _ => ?_
    refine AlikeE.bind' (layRows_rel P.codes _ _ _ x.2 x'.2 k2) fun e e' he => ?_
    exact AlikeE.ok (Carry.pairE wipeD _ he)
  · exact AlikeE.error _

/-! ## 2 The joining -/

/-- A frame beside a carried record, both wiped. -/
def wipeFD (y : ReqFrame × DState L) : ReqFrame × DState L := (wipeFrame y.1, wipeD y.2)

/-- Message by message, into records that are equal once wiped: both yield nothing, or records that are equal once
wiped. hG: the like of the ground function join. -/
theorem joinAll_rel {G : GroundP L}
    (hG : ∀ p d d' g o k, wipeD d = wipeD d' → (G.join p d g o k).map wipeD = (G.join p d' g o k).map wipeD)
    (p : GPar) (g : Nat) : ∀ (l : List (OnBytes.Params.ReqMessage × Nat)) (d d' : DState L), wipeD d = wipeD d' →
      (joinAll G p g l d).map wipeD = (joinAll G p g l d').map wipeD
  | [], _, _, h => congrArg some h
  | x :: l, d, d', h =>
    bind_rel wipeD wipeD (hG p d d' g x.2 (decide (0 < x.1.life)) h) fun e e' he => joinAll_rel hG p g l e e' he

/-- A moment's own messages join the link's group: the like at frames and records that are equal once wiped. -/
theorem joinOwnP_rel {G : GroundP L}
    (hG : ∀ p d d' g o k, wipeD d = wipeD d' → (G.join p d g o k).map wipeD = (G.join p d' g o k).map wipeD)
    (p : GPar) {d d' : DState L} {f f' : ReqFrame} (hd : wipeD d = wipeD d') (hf : wipeFrame f = wipeFrame f')
    (sent : List OnBytes.Params.ReqMessage) (ids : Array Nat) :
    (joinOwnP G p d f sent ids).map wipeFD = (joinOwnP G p d' f' sent ids).map wipeFD := by
  have hg : f.group = f'.group := (congrArg (fun z : ReqFrame => z.group) hf :)
  unfold joinOwnP
  rw [hg]
  cases (sent.length == ids.size) with
  | false => rfl
  | true =>
    rcases Carry.optA (joinAll_rel hG p f'.group (OnBytes.zipT sent ids.toList) d d' hd) with
      ⟨e1, e2⟩ | ⟨a, a', e1, e2, ha⟩
    · rw [e1, e2]
      rfl
    · rw [e1, e2]
      show some (({ wipeFrame f with group := f'.group, own := (wipeFrame f).own ++ ids } : ReqFrame), wipeD a) =
        some (({ wipeFrame f' with group := f'.group, own := (wipeFrame f').own ++ ids } : ReqFrame), wipeD a')
      rw [hf, ha]

/-- The premise hG holds of the description's own record of ground functions. -/
theorem groundJoin_rel (p : GPar) (d d' : DState L) (g o : Nat) (k : Bool) (h : wipeD d = wipeD d') :
    ((_root_.Desc.Plain.groundG : GroundP L).join p d g o k).map wipeD =
      ((_root_.Desc.Plain.groundG : GroundP L).join p d' g o k).map wipeD := joinP_rel h g o k

/-! ## 3 The first segment's opening -/

/-- A state of the calls beside a carried record, both wiped. -/
def wipeCD (y : ChainCheck × DState L) : ChainCheck × DState L := (wipeCheck y.1, wipeD y.2)

/-- **The opening's decision**, at a wiped state of the calls and at that state unwiped, and at records that are equal
once wiped, has like outcomes. -/
theorem firstOwn_wiped (P : Par) (owed : Option Nat) (c : ChainCheck) {d d' : DState Unit}
    (hd : wipeD d = wipeD d') (rs : List Fmt.RoundView) :
    AlikeE wipeCD (firstOwn P owed (wipeCheck c) d rs) (firstOwn P owed c d' rs) := by
  unfold firstOwn
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun Lk => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.bind' (AlikeE.named_alone (newGroupP_rel hd c.frame.shape.code c.frame.shape.maskCode))
    fun x x' hx => ?_
  obtain ⟨g, d₁⟩ := x
  obtain ⟨g', d₁'⟩ := x'
  obtain ⟨k1, k2⟩ := Carry.pairParts hx
  have k1' : g = g' := k1
  subst k1'
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.bind' (decideSend_rel P owed k2 rs) fun y y' hy => ?_
  obtain ⟨ids, d₂⟩ := y
  obtain ⟨ids', d₂'⟩ := y'
  obtain ⟨m1, m2⟩ := Carry.pairParts hy
  have m1' : ids = ids' := m1
  subst m1'
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun mask => ?_
  refine AlikeE.bind' (AlikeE.named_alone (joinOwnP_rel groundJoin_rel P.gp m2 ?_ _ _)) fun z z' hz => ?_
  · rfl
  · obtain ⟨f₂, d₃⟩ := z
    obtain ⟨f₂', d₃'⟩ := z'
    have n1 : wipeFrame f₂ = wipeFrame f₂' := (congrArg Prod.fst hz :)
    have n2 : wipeD d₃ = wipeD d₃' := (congrArg Prod.snd hz :)
    refine AlikeE.ok ?_
    show (({ c with frame := { wipeFrame f₂ with next := .laterOrClose }, sent := _, inLink := true,
                    moments := 1 } : ChainCheck), wipeD d₃) =
      (({ c with frame := { wipeFrame f₂' with next := .laterOrClose }, sent := _, inLink := true,
                 moments := 1 } : ChainCheck), wipeD d₃')
    rw [n1, n2]
    rfl

/-- **The first segment's opening** has like outcomes at two states that are equal once wiped; it states no run. -/
theorem k1First2 (q : OnBytes.Params.First) (gp : GPar) : Whole2 wipeS (firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨Decides2.of_wiped (fun _ _ _ _ => rfl) fun s rs gs => ?_, (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩
  refine AlikeE.head_eq' (congrArg (VerifiableInference.Desc.need "K1: a link is open") (atBetween_wipe s))
    fun _ => ?_
  refine AlikeE.bind' (firstOwn_wiped (VerifiableInference.Desc.K1.firstPar q gp) (owedOf s) s.check
    (wipeD_idem (stateOf s ())) rs) fun x x' hx => ?_
  obtain ⟨c, d⟩ := x
  obtain ⟨c', d'⟩ := x'
  have h1 : wipeCheck c = wipeCheck c' := (congrArg Prod.fst hx :)
  have h2 : wipeD d = wipeD d' := (congrArg Prod.snd hx :)
  refine AlikeE.ok ?_
  show ({ laid (wipeS (wipeS s)) (wipeD d) with check := wipeCheck c } : S) =
    { laid (wipeS s) (wipeD d') with check := wipeCheck c' }
  rw [wipeS_idem, h1, h2]

/-! ## 4 A segment's later moment -/

/-- **A later moment's decision**, at a wiped state of the calls and at that state unwiped, and at records that are
equal once wiped, has like outcomes. -/
theorem laterOwn_wiped (P : Par) (owed : Option Nat) (c : ChainCheck) {w w' : DState Unit}
    (hw : wipeD w = wipeD w') (rs : List Fmt.RoundView) :
    AlikeE wipeCD (laterOwn P owed (wipeCheck c) w rs) (laterOwn P owed c w' rs) := by
  have e : (wipeCheck c).frame.shape.link[(wipeCheck c).frame.link]? = c.frame.shape.link[c.frame.link]? := rfl
  unfold laterOwn
  dsimp only
  rw [e]
  refine Carry.iteA (AlikeE.error _) ?_
  cases c.frame.shape.link[c.frame.link]? with
  | none => exact AlikeE.error _
  | some Lk =>
    refine Carry.iteA (AlikeE.error _) ?_
    rcases (decideSend_rel P owed hw rs).split with ⟨e0, h1, h2⟩ | ⟨x, x', h1, h2, hx⟩
    · rw [h1, h2]
      exact AlikeE.error e0
    · rw [h1, h2]
      obtain ⟨k1, k2⟩ := Carry.pairParts hx
      dsimp only
      rw [k1]
      rcases Carry.optA (joinOwnP_rel groundJoin_rel P.gp k2
          (f := { (wipeCheck c).frame with moment := (wipeCheck c).frame.moment + 1 })
          (f' := { c.frame with moment := c.frame.moment + 1 }) rfl
          (c.frame.atMoment c.frame.moment) x'.1) with ⟨e1, e2⟩ | ⟨y, y', e1, e2, hy⟩
      · have e1' : joinOwnP _root_.Desc.Plain.groundG P.gp x.2
            { (wipeCheck c).frame with moment := (wipeCheck c).frame.moment + 1 }
            ((wipeCheck c).frame.atMoment (wipeCheck c).frame.moment) x'.1 = none := e1
        rw [e1', e2]
        exact AlikeE.error _
      · have e1' : joinOwnP _root_.Desc.Plain.groundG P.gp x.2
            { (wipeCheck c).frame with moment := (wipeCheck c).frame.moment + 1 }
            ((wipeCheck c).frame.atMoment (wipeCheck c).frame.moment) x'.1 = some y := e1
        rw [e1', e2]
        have n1 : wipeFrame y.1 = wipeFrame y'.1 := (congrArg Prod.fst hy :)
        have n2 : wipeD y.2 = wipeD y'.2 := (congrArg Prod.snd hy :)
        refine AlikeE.ok ?_
        show (({ c with frame := wipeFrame y.1, sent := x'.1, moments := c.moments + 1 } : ChainCheck), wipeD y.2) =
          (({ c with frame := wipeFrame y'.1, sent := x'.1, moments := c.moments + 1 } : ChainCheck), wipeD y'.2)
        rw [n1, n2]

/-- A link's context beside a fork, the context wiped. -/
def wipeLF (y : LinkCtx × Fork) : LinkCtx × Fork := (wipeCtx y.1, y.2)

/-- Behind a commitment's sending the arrays are marked and the state of the calls is laid into the context: like
outcomes at the wiped context and at states of the calls that are equal once wiped. -/
theorem commitBehind_wiped (C : LinkCtx) {ck ck' : ChainCheck} (hk : wipeCheck ck = wipeCheck ck') (F : Fork)
    (trees : List Nat) :
    AlikeE wipeLF (L3.commitBehind (wipeCtx C) ck F trees) (L3.commitBehind C ck' F trees) := by
  unfold L3.commitBehind
  refine AlikeE.head' fun F' => ?_
  refine Carry.iteA (AlikeE.ok ?_) (AlikeE.error _)
  show (({ wipeCtx C with check := wipeCheck ck, moments := C.moments + 1 } : LinkCtx), F') =
    (({ wipeCtx C with check := wipeCheck ck', moments := C.moments + 1 } : LinkCtx), F')
  rw [hk]

/-- What a commitment's step carries, its context and its record wiped. -/
def wipeHeld (x : L3.St (DState L)) : L3.St (DState L) := { x with L := wipeCtx x.L, w := wipeD x.w }

/-- **A commitment's step** has like outcomes at the wiped context, if the sending inside it has (hs). -/
theorem commitStep_wiped {send : L3.Send (DState L)} (rs : List Fmt.RoundView)
    (hs : ∀ c w w', wipeD w = wipeD w' → AlikeE wipeCD (send (wipeCheck c) w rs) (send c w' rs))
    (trees : List Nat) (C : LinkCtx) (F : Fork) (tl : HTailF2) {w w' : DState L} (hw : wipeD w = wipeD w') :
    AlikeE wipeHeld (L3.commitStep send trees ⟨wipeCtx C, F, tl, w⟩ rs)
      (L3.commitStep send trees ⟨C, F, tl, w'⟩ rs) := by
  unfold L3.commitStep
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.bind' (hs C.check w w' hw) fun x x' hx => ?_
  obtain ⟨ck, v⟩ := x
  obtain ⟨ck', v'⟩ := x'
  have h1 : wipeCheck ck = wipeCheck ck' := (congrArg Prod.fst hx :)
  have h2 : wipeD v = wipeD v' := (congrArg Prod.snd hx :)
  refine AlikeE.bind' (commitBehind_wiped C h1 F trees) fun y y' hy => ?_
  obtain ⟨C₁, F₁⟩ := y
  obtain ⟨C₁', F₁'⟩ := y'
  have h3 : wipeCtx C₁ = wipeCtx C₁' := (congrArg Prod.fst hy :)
  have h4 : F₁ = F₁' := (congrArg Prod.snd hy :)
  refine AlikeE.ok ?_
  show (⟨wipeCtx C₁, F₁, tl, wipeD v⟩ : L3.St (DState L)) = ⟨wipeCtx C₁', F₁', tl, wipeD v'⟩
  rw [h2, h3, h4]

/-- What K1's member on the step's own record carries, with what it holds wiped. -/
def wipeOw (y : Owing (L3.St (DState L))) : Owing (L3.St (DState L)) := { y with held := wipeHeld y.held }

/-- A segment's later moment, on the step's own record, has like outcomes at the wiped context. -/
theorem commitOwn_wiped (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (owed : Option Nat)
    (C : LinkCtx) (F : Fork) (tl : HTailF2) {w w' : DState Unit} (hw : wipeD w = wipeD w') (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    AlikeE wipeOw
      ((commitOwn (Cl := Cl) P link moment arrays).decide { owed := owed, held := ⟨wipeCtx C, F, tl, w⟩ } rs gs)
      ((commitOwn (Cl := Cl) P link moment arrays).decide { owed := owed, held := ⟨C, F, tl, w'⟩ } rs gs) := by
  cases arrays with
  | none => exact Carry.iteA (AlikeE.error _) (AlikeE.error _)
  | some ts =>
    refine Carry.iteA ?_ (AlikeE.error _)
    refine AlikeE.map (commitStep_wiped rs (fun c v v' h => laterOwn_wiped P owed c h rs) ts C F tl hw)
      fun x x' hx => ?_
    show ({ owed := none, held := wipeHeld x } : Owing (L3.St (DState Unit))) = { owed := none, held := wipeHeld x' }
    rw [hx]

/-- The same with the outcome laid back into the first chain's state. -/
theorem commitCore (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s : S) (C : LinkCtx) (F : Fork)
    (tl : HTailF2) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    AlikeE wipeS
      (((commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := owedOf (wipeS s), held := { L := wipeCtx C, F := F, tl := tl, w := stateOf (wipeS s) () } } rs
          gs).map fun y => ((laid (wipeS s) y.held.w).putLink y.held.L).putFork y.held.F)
      (((commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := owedOf s, held := { L := C, F := F, tl := tl, w := stateOf s () } } rs
          gs).map fun y => ((laid s y.held.w).putLink y.held.L).putFork y.held.F) := by
  refine AlikeE.map (commitOwn_wiped P link moment arrays (owedOf s) C F tl (wipeD_idem (stateOf s ())) rs gs)
    fun y y' hy => ?_
  have h1 : wipeD y.held.w = wipeD y'.held.w := (congrArg (fun z : Owing (L3.St (DState Unit)) => z.held.w) hy :)
  have h2 : wipeCtx y.held.L = wipeCtx y'.held.L :=
    (congrArg (fun z : Owing (L3.St (DState Unit)) => z.held.L) hy :)
  have h3 : y.held.F = y'.held.F := (congrArg (fun z : Owing (L3.St (DState Unit)) => z.held.F) hy :)
  rw [putFork_wipe, putLink_wipe, laid_wipe, putFork_wipe, putLink_wipe, laid_wipe, wipeS_idem, h1, h2, h3]

/-- A segment's later moment, at the first chain's state, has like outcomes at two states that are equal once wiped. -/
theorem commitAtS_whole2 (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Whole2 wipeS (commitAtS (Cl := Cl) P link moment arrays) := by
  refine ⟨Decides2.of_wiped (fun _ _ _ _ => rfl) fun s rs gs => ?_, (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩
  unfold commitAtS
  dsimp only
  rw [link?_wipe, fork?_wipe, tl?_wipe]
  cases s.link? with
  | none => cases s.fork? <;> cases s.tl? <;> exact AlikeE.error _
  | some C =>
    cases s.fork? with
    | none => cases s.tl? <;> exact AlikeE.error _
    | some F =>
      cases s.tl? with
      | none => exact AlikeE.error _
      | some tl => exact commitCore P link moment arrays s C F tl rs gs

/-- **A segment's later moment**, at the numbers that laterAt lays, has like outcomes at two such states. -/
theorem k1Later2 (q : OnBytes.Params.First) (gp : GPar) (link piece moment : Nat) (arrays : Option (List Nat)) :
    Whole2 wipeS (laterAt (Cl := Cl) q gp link piece moment arrays) :=
  commitAtS_whole2 (VerifiableInference.Desc.K1.parLater q gp link piece moment) link moment arrays

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.layRows_rel
#print axioms ProofFile.Honest.K10.notSampled_wipe
#print axioms ProofFile.Honest.K10.decideSend_rel
#print axioms ProofFile.Honest.K10.wipeFD
#print axioms ProofFile.Honest.K10.joinAll_rel
#print axioms ProofFile.Honest.K10.joinOwnP_rel
#print axioms ProofFile.Honest.K10.groundJoin_rel
#print axioms ProofFile.Honest.K10.wipeCD
#print axioms ProofFile.Honest.K10.firstOwn_wiped
#print axioms ProofFile.Honest.K10.k1First2
#print axioms ProofFile.Honest.K10.laterOwn_wiped
#print axioms ProofFile.Honest.K10.wipeLF
#print axioms ProofFile.Honest.K10.commitBehind_wiped
#print axioms ProofFile.Honest.K10.wipeHeld
#print axioms ProofFile.Honest.K10.commitStep_wiped
#print axioms ProofFile.Honest.K10.wipeOw
#print axioms ProofFile.Honest.K10.commitOwn_wiped
#print axioms ProofFile.Honest.K10.commitCore
#print axioms ProofFile.Honest.K10.commitAtS_whole2
#print axioms ProofFile.Honest.K10.k1Later2
