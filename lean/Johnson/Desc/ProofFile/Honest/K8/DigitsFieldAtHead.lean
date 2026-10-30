-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/DigitsFieldAtHead.lean: THE SMALLNESS TEST, AT THE FIRST CHAIN's
THREAD AT THE HEAD: THE FIELD digits OF THE RECORD `K8ItemsAt`
(Johnson/Desc/ProofFile/Honest/K8/SeatedItemsAt.lean) IS MET AT ALL 25 DRAWS, AT THE LIBRARY's TABLE
`cellsAhead`, AT EVERY LETTER Said THAT GIVES `SaidOk`, WHERE THE KIND's MEMBER IS SEATED AT THE
DESCRIPTION's OWN PARAMETERS. One theorem and one unnamed check; no definition; none of the
library's goals.

  **`digits_field_at_head`**   under the library's head (h : `P5J.AtMgA`): hOk: what is said gives
                   SaidOk · l < 25 · the blank ground G · the built segment Xl · `K8Seated` at the
                   border 14 * l + (if l = 24 then 5 else 4) + 2 at the parameters ProofFile.k8Par Zp G Xl
                   l ⊢ the field's sentence, to the letter, at A a := cellsAhead … l a and iD :=
                   constr l lookDigits: from the pair of a stand and what is said, and a step of the
                   member: DigitsAt at the seat behind gives the item's meaning there, at every
                   input, every z and every witness
WHY SaidOk. The library's laws on the state behind a draw stand at `RchAt`: reached by the members
UNDER `below`. The thread alone gives the reach by the members' own steps; the pair with SaidOk
gives RchAt (`thrS_rchAt`, Johnson/Desc/ProofFile/Honest/Thread/ReachAtHead.lean).
HOW. `constr_of_digitsAt` (Johnson/Desc/K8/Honest/DigitsBack.lean) · its hE by the library's
`digMu_cellsAhead` (Johnson/Desc/First/Look/K3DigitsAhead.lean) at `digAhead_at_reach`
(Johnson/Desc/K8/Honest/DigAheadAtReach.lean) · its hT by the library's `six_behind_draw`,
`tlAt_of_plan` (Johnson/P1K8R/DigitsAtDraw.lean) and `digitsOf_six`, as `k08_digits_of_ahead` there
has them the other way · `matrix_at_built` (Johnson/Desc/K8/Honest/HeldOutright.lean) ·
`Q38.digAt_at_head` (Johnson/HB/LLHARD/Q38E/DigAtHead.lean).
ONE OPTION IS RAISED (maxHeartbeats) AND ONE INSTANCE IS TAKEN AWAY (attribute [-instance]
Inst.Model.Scl.ref), as in the files beneath. TACTICS THAT SEARCH: `omega` on one line, on l.
Limits. ONE FIELD OF SIX; no witness's content is read: v is a letter. `K8Seated` is a premise; the
form behind the step is not spent. THAT THE THREAD STANDS AT ANY OF THESE BORDERS, AT ANY PROVER, IS
NOT SAID HERE: where it stands at none, all is idle. THE FULL SIZE ALONE.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SeatedItemsAt
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.K8.Honest.DigitsBack
import Johnson.Desc.K8.Honest.DigAheadAtReach
import Johnson.Desc.K8.Honest.HeldOutright
import Johnson.P1K8R.DigitsAtDraw
import Johnson.HB.LLHARD.Q38E.DigAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (Par DigitsAt cellsAhead step_seats_iff decide_atS_iff approximateRangeProofDrawKind
  atS drawAt)
open VerifiableInference.Desc.First.K8.Honest
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script thrS_rchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE FIELD digits, AT ALL 25 DRAWS, AT EVERY Said THAT GIVES SaidOk.** Behind a yes at which
the second stop is silent. NOT IN FRONT OF A LAW OVER COINS. -/
theorem digits_field_at_head {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {blk : Block S ProofFile.Cl} {cells : Tr → Cells} {mats : List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats)) :
    ∀ k s m E ds y cols s' w₀ z yy v,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      DigitsAt (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')) s' v →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means w₀
        (Item.constr l .lookDigits) (z, s') yy v := by
  intro k s m E ds y cols s' w₀ z yy v hA _ hS _ hDg
  have hl' : l ≤ 24 := by omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨xd, tl, hx⟩ := Q38.digAt_at_head h hl'
  -- reached, under `below`, in front of the draw
  have hr0 := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ()
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hK.here).1) ⟨hA.1, hOk _ _ _ hA.2⟩
  have hr : Johnson.Desc.First.Walk.Tied.RchAt
      (P1K8T.FD Zp (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np) cF) (drawAt l)
      ((m.st.input.x.pub, s), ()) := by
    rw [P1K8T.drawAt_place l]
    exact hr0
  have hu : s.failed = none := Option.isNone_iff_eq_none.1 hA.1.2.2.1.1
  -- the draw's yes
  obtain ⟨-, hstep⟩ := hS
  obtain ⟨rv, -, -, hm, -, -⟩ :=
    (step_seats_iff (ProofFile.k8Par Zp Bs.G₀ Xl l) blk hK.seats _ s s' _ _ _).1 hstep
  have hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar).decide s rs gs =
      .ok s' := ⟨[rv], [], (decide_atS_iff _ s s' rv []).2 hm⟩
  -- the state's parameters behind the draw, and the plan's
  obtain ⟨ts, hts, c1, c2, c3, c4, c5, c6⟩ :=
    P1K8T.six_behind_draw h hG hl' e3 ((m.st.input.x.pub, s), ()) hr hy
  have eW : Bs.G₀.W = P5J.At.X Zp := Except.ok.inj (O.public.symm.trans h.pubOne)
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  have hx' : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨tlP, hP, -, -⟩ := P1K8S.k8LaidOwn h.scope h.reads O hx' _ hr0
  have eP : tlP = Xl.tl := P1K8S.planAt_built h.scope h.reads O e3 hP
  rw [eW] at hP
  have eT : tl = Xl.tl := (P1K8T.tlAt_of_plan p4 ng
    (VerifiableInference.Desc.First.Look.digAt_is
      (VerifiableInference.Desc.First.Look.shapeZAll_of_public h.pubOne) hx) hP).trans eP
  have hN : 0 < tl.NM := by
    rw [eT]
    exact matrix_at_built h.scope h.reads O h.laid.planOk hl e3
  exact constr_of_digitsAt
    { h.𝔇 with decT := fun _ _ => some (Q.cells w₀), cr1 := carryX } mgBase h.pubOne rfl hx hN z s'
    yy v
    (fun ts' hts' A => by
      obtain rfl : ts = ts' := Option.some.inj (hts.symm.trans hts')
      exact VerifiableInference.OnPublicFiles.digitsOf_six ts tl (by rw [c1, eT]) (by rw [c2, eT])
        (by rw [c3, eT]) (by rw [c4, eT]) (by rw [c5, eT]) (by rw [c6, eT]) A)
    (VerifiableInference.OnPublicFiles.digMu_cellsAhead xd tl h.𝔇.sent h.𝔇.l3.rad _ h.𝔇.l3.arr h.𝔇.ms
      h.𝔇.N l z s' v
      (digAhead_at_reach h hG hl' e3 hx m.st.input.x.pub s s' hr hu hy v)) hDg

/- A check by Lean, no statement: the theorem's end is the record's field. -/
example {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {blk : Block S ProofFile.Cl} {cells : Tr → Cells} {mats : List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats))
    {iS i₀ : Item}
    (hI : K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats)
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a) iS i₀) :
    K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats)
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a) iS (Item.constr l .lookDigits) :=
  { hI with
    digits := digits_field_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl hG e3 hK }

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.digits_field_at_head
