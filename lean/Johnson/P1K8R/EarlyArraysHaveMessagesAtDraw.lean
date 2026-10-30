-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/EarlyArraysHaveMessagesAtDraw.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
COMPLEMENT OF `CellsIn`, ITS OTHER CLAUSE: AT EVERY REACHED STATE IN FRONT OF THE DRAW EVERY EARLY
ARRAY HAS A MESSAGE NOW. SO NO EARLY CELL IS READ OFF THE TABLE OF ZEROS. NO SOUNDNESS.

`seated_at_draw` speaks of an early array t with `Named.msgNow L t = some
o`. Where `msgNow` finds nothing the tie's reader reads zeros too. Here that arm is shut.
  `k8AllNowB d lay Xl l`: A CLOSED TEST WITH CODE: at every array t of `Named.arrays Xl.tl`: the
    built link's list names it; the layout has the array; the shape has its message; the plan's term
    `whereD d l 2` finds the message's number.
  `liesAt_of_parts`: the way back of `reqArray_of_liesAt` (Johnson/Desc/First/K8/LawCellsAt.lean).
  `now_at_draw`: **under the head, the facts along "reached" and a yes of the test: at every reached
    state in front of link l's draw on which no check has failed, at every early cell's array t:
    `Named.msgNow L t = some o` for some o.**
  `early_read_at_draw`: **with `seated_at_draw`: at every early cell's array: a message o now, a
    seat q of the link's own group in the book at o, and a member of the plan's list at q.**
Limits. `k8AllNowB` does not pin the layout: it asks that the layout has an array of the name, not
which (with two links' lists of arrays swapped it still accepted at one link of 25, by evaluation).
What pins it is `layout_in_scope` (Johnson/Goal/Numbers/MadeInScope.lean): in the goals' scope,
under the entry tests' pin on the made plan, the layout is the written one. The two tests are
theorems in no file of this folder's; they have been evaluated at the release's public files. THE
TEST `k8AllNowB` IS NOT NEEDED FOR WHAT IT BUYS: "a message now" follows from the head without it
(Johnson/P1K8R/EarlyReadFromHead.lean). AT `OnBytes.secondHashFunction` ALONE. Nothing on
soundness.

-/
import Johnson.P1K8R.SeatedAtDraw
import Johnson.Desc.First.K8.LawCellsAt

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Params (ReqArray ReqMessage)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail (early)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S FoldData FoldFacts flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (seven lay7 lay7_of_test)
open VerifiableInference.Desc.LinkJoin (whereD whereIs_reached)
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- The closed test: every early array is named, laid, in a message of the shape, and found. -/
def k8AllNowB (d : FoldData) (lay : OnBytes.Params.ReqLayout) (Xl : LinkH) (l : ℕ) : Bool :=
  (Named.arrays Xl.tl).all fun t =>
    match Xl.arrayOf[t]? with
    | some x =>
      match OnBytes.reqArray lay x.1 x.2 with
      | some a =>
        (_root_.Meaning.messageAt d.sent.shape x.1 a.message).isSome &&
          (whereD d l 2 x.1 a.message).isSome
      | none => false
    | none => false

/-- What its yes says. -/
theorem allNow_of_test {d : FoldData} {lay : OnBytes.Params.ReqLayout} {Xl : LinkH} {l : ℕ}
    (h : k8AllNowB d lay Xl l = true) {t : ℕ} (ht : t ∈ Named.arrays Xl.tl) :
    ∃ (x : ℕ × String) (a : ReqArray) (m : ReqMessage) (o : ℕ), Xl.arrayOf[t]? = some x ∧
      OnBytes.reqArray lay x.1 x.2 = some a ∧
      _root_.Meaning.messageAt d.sent.shape x.1 a.message = some m ∧
      whereD d l 2 x.1 a.message = some o := by
  have b := List.all_eq_true.1 h t ht
  split at b
  · rename_i x hx
    split at b
    · rename_i a ha
      rw [Bool.and_eq_true] at b
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 b.1
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 b.2
      exact ⟨x, a, m, o, hx, ha, hm, ho⟩
    · exact nomatch b
  · exact nomatch b

/-- The way back: the parts give what `liesAt` finds. -/
theorem liesAt_of_parts {L : LinkCtx} {t : ℕ} {x : ℕ × String} {a : ReqArray} {m : ReqMessage}
    (hx : L.arrayOf[t]? = some x)
    (ha : OnBytes.reqArray L.check.rows.layout x.1 x.2 = some a)
    (hm : _root_.Meaning.messageAt L.check.frame.shape x.1 a.message = some m) :
    Order.liesAt L t = some ⟨x.1, a.message, m.moment, m.life⟩ := by
  unfold OnBytes.reqArray at ha
  obtain ⟨ls, hls, hf⟩ := Option.bind_eq_some_iff.1 ha
  unfold _root_.Meaning.messageAt at hm
  obtain ⟨Lk, hLk, hmm⟩ := Option.bind_eq_some_iff.1 hm
  unfold Order.liesAt
  simp only [Option.bind_eq_bind, Option.pure_def, hx, Option.bind_some,
    List.getD_eq_getElem?_getD, hls, Option.getD_some, hf, hLk, hmm]

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **EVERY EARLY ARRAY HAS A MESSAGE NOW.** -/
theorem now_at_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Ld : Laid} {Fr : Frame}
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF Ld) P5J.At.reqW P5J.At.links P5J.At.ps)
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    (hT : k8AllNowB (P5J.At.foldD Zp cF Ld) (P5J.At.layout Zp) Xl l = true)
    (a : (ProofFile.InstPub × S) × Fr.E.Str) {tl : HTailF2} {L : LinkCtx}
    (hr : Rch (drawAt l) a) (hm : a.1.2.failed = none) (ht : a.1.2.tl? = some tl)
    (hL : a.1.2.link? = some L) {t r c : ℕ} (he : early tl (.cell t r c) = true) :
    ∃ o, Named.msgNow L t = some o := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hr0 := hRch _ _ hr
  have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) a := by
    rw [← drawAt_place]
    exact hr0
  obtain ⟨tlP, hv, h7, -⟩ := P1K8S.k8LaidOwn h.scope h.reads O hx a hr'
  have eP : tlP = Xl.tl := P1K8S.planAt_built h.scope h.reads O e3 hv
  have e7 : seven tl = seven Xl.tl := by
    have e := lay7_of_test h7
    unfold lay7 at e
    rw [ht] at e
    rw [← eP]
    exact Option.some.inj e
  have eA : Named.arrays tl = Named.arrays Xl.tl := by
    unfold Named.arrays
    rw [show tl.gtTree = Xl.tl.gtTree from congrArg (·.1) e7,
      show tl.ix = Xl.tl.ix from congrArg (·.2.1) e7]
  obtain ⟨L', -, -, hL', -, -, -, e1, e2, -, e4, -⟩ := k08_fold_at h hG hl e3 a hr0
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  obtain ⟨p, hp, hlk, hpc, hmo⟩ := draw_place_full l hl
  obtain ⟨x, ar, m, o, hx1, hx2, hx3, hx4⟩ :=
    allNow_of_test hT (eA ▸ (early_iff_named tl t r c).1 he)
  have hmo' : VerifiableInference.Desc.First.momentAt
      (VerifiableInference.Desc.First.shiftAt P5J.At.links l) p.piece = 2 := hmo
  have hw : L.check.frame.whereIs x.1 ar.message = some o := by
    rw [whereIs_reached FF hr hm hp hlk hpc hL x.1 ar.message, hmo']
    exact hx4
  have hlies := liesAt_of_parts (L := L) (t := t) (x := x) (a := ar) (m := m)
    (by rw [e1]; exact hx1) (by rw [e2, layout_at hG]; exact hx2) (by rw [e4]; exact hx3)
  refine ⟨o, ?_⟩
  unfold Named.msgNow
  rw [hlies]
  show Order.namedNow L.check.frame ⟨x.1, ar.message, m.moment, m.life⟩ = some o
  rw [← whereIs_namedNow]
  exact hw

/-- **AT EVERY EARLY CELL's ARRAY: A MESSAGE NOW, A SEAT OF THE OWN GROUP, A MEMBER THERE.** -/
theorem early_read_at_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Ld : Laid} {Fr : Frame}
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF Ld) P5J.At.reqW P5J.At.links P5J.At.ps)
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    (hN : k8AllNowB (P5J.At.foldD Zp cF Ld) (P5J.At.layout Zp) Xl l = true)
    (hT : k8SeatedB Ld (P5J.At.ms Zp Z.lay) ((P5J.At.N Zp cF).group l)
      ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
      (k8NumsOf (P5J.At.foldD Zp cF Ld) (P5J.At.layout Zp) Xl l) = true) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      a.1.failed = none → a.1.tl? = some tl → a.1.link? = some L →
      ∀ t r c, early tl (.cell t r c) = true →
        ∃ o q y, Named.msgNow L t = some o ∧
          seatAt ((P5J.At.N Zp cF).group l) a.1.book o = some q ∧
          ((P5J.At.ms Zp Z.lay).find? fun y => decide (seatOf y = q)) = some y := by
  intro z a tl L ha hr hm ht hL t r c he
  obtain ⟨o, ho⟩ := now_at_draw h FF hRch hG hl e3 hN ((z, a.1), a.2) hr hm ht hL he
  obtain ⟨q, y, hq, hy⟩ :=
    seated_at_draw h FF hRch hG hl e3 hT z a tl L ha hr hm ht hL t r c o he ho
  exact ⟨o, q, y, ho, hq, hy⟩

end P1K8T

#print axioms P1K8T.allNow_of_test
#print axioms P1K8T.liesAt_of_parts
#print axioms P1K8T.now_at_draw
#print axioms P1K8T.early_read_at_draw
