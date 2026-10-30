-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/OpenAtHead.lean: CONDITIONAL.

What is here. Two items of the table that are open in front of the member of the feed-forward
layers' own rounds (sub-protocol K4), taken out of the thread: `Item.constr m .idn` and `Item.worth
m 2 "rider"`: the hypothesis c of `part_head` (Law/W/IdnHotAt.lean) at the part .idn, and the
hypothesis hW of Johnson/Road/K4/W/HotOfRider.lean. The thread (`Thr`, Honest/Thread/Thr.lean) holds
the sentence of every open item at every continuation of the challenges heard; K4's forward row asks
these two; what a row asks is open in front of it.

  1  `asks_k4`, `open_k4`, `item_of_thr`   general in the first chain's parameters: the eight items
     that the thread's forward row asks at K4's member; each is open there, under hone; the thread
     holds an open item's sentence.
  2  `idn_item_head`, `rider_item_head`   **the two sentences at the thread with the library's own
     values laid in** (`lettersHead`, Honest/Thread/FirstHead.lean), in the form of `part_head`'s
     hypothesis c.
  3  `rider_lay_head`   the second in the lookup's own terms (`layWorthRider`,
     Johnson/Desc/First/Look/K3LayTies.lean), by the library's `mgAll_worth_lay_rider`
     (Johnson/Desc/Sound/MgAllAt.lean): the form of hW.

Not shown here. THAT THE THREAD HOLDS AT ANY RUN: hT : Thr is a hypothesis. hone, in section 1
alone: a test on two lists (whatever a forward row asks or shuts is open in front of it, in one
pass; `asks_open`, Honest/Thread/FirstFits.lean, is the lemma that is called); at the full size's
two written lists it is the theorem `onePass_full` (Law/W/OnePassFull.lean), which sections 2 and 3
call. For `rider_lay_head` three returns of public functions at the segment (hna, hx, ht) and one
public number (hpc). The side library AtFullSide proves, with no hypothesis, that h has a member at
one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits
say what it is worth). Of h together with A, hone, hi, hT, hpc, hna, hx and ht no example is known
to us. THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`), from section 2
on. Nothing on soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 16 modules under Johnson/Goal/ and at 4 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 20 is not counted: all the numbers are floors. They come with
h. A LAW, NOT A PART: no file that defines a part of the proof file's description may import this
one.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OnePassFull
import Johnson.Desc.Sound.MgAllAt
import Johnson.Road.K4.More.FrontList

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Road.K4 (AtK4)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.First.Look (pubAt stepOf attAt layAt tlAt)
open VerifiableInference.Desc.Sound (MsgT linksFull mgAll mgBase mgAll_worth_lay_rider)
open VerifiableInference.OnPublicFiles (layWorthRider)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstRows (opens rowAt)
open ProofFile.Honest.FirstThread (Letters Script WtF lettersHead)

/-! ## 1 General in the first chain's parameters -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)

/-- **What the thread's forward row asks at K4's member**: eight items: the four that the table's
row closes, and the four that it reads. CONDITIONAL: on A. -/
theorem asks_k4 {b m : Nat} {pl : Place} (A : AtK4 L.links L.ps b m pl) :
    (L.thread.row b).asks =
      [Item.constr m .idn, .worth m 2 "planes", .worth m 2 "keys", .worth m 2 "rider", .pin m 0,
        .pinW, .constr m .small, .pinI] := by
  have hr : VerifiableInference.Desc.First.rowOf L.links pl =
      VerifiableInference.Desc.First.segRow .layers m 3 := by
    simp only [VerifiableInference.Desc.First.rowOf, A.link, A.sub, A.piece]
  show (FirstRows.rows L.links L.ps b).asks = _
  simp only [FirstRows.rows, A.here, Option.map_some, Option.getD_some, FirstRows.rowAt,
    FirstRows.turn, A.link, Option.isNone_some, Bool.false_and, hr]
  rfl

/-- **What the row asks is open in front of the member.** CONDITIONAL: on hone. -/
theorem open_k4
    (hone : (((opens L.links L.ps (start L.links)).zip L.ps).all fun x =>
      ((rowAt L.links x.2).asks ++ (rowAt L.links x.2).shuts).all x.1.contains) = true)
    {b : Nat} {i : Item} (hi : i ∈ (L.thread.row b).asks) : i ∈ L.thread.opened b := by
  have h1 := FirstRows.asks_open L.links L.ps (start L.links) hone b
  have hi' : i ∈ (FirstRows.rows L.links L.ps b).asks := hi
  have h2 := List.all_eq_true.1 h1 i (List.mem_append_left _ hi')
  have h3 : i ∈ fwdOpen (start L.links) (FirstRows.rows L.links L.ps) b := by simpa using h2
  exact h3

/-- **The thread holds the sentence of every open item, at every continuation.** CONDITIONAL: on hT
and hi. -/
theorem item_of_thr {b : Nat} {k : Coins Bk} {s : VerifiableInference.Desc.First.S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr L.thread b k s m E) {i : Item}
    (hi : i ∈ L.thread.opened b) (ds : List Fmt.Drawn) :
    L.thread.means m.st.input i (L.thread.seat k m s) (L.thread.strs E)
      (L.thread.wit k m.st.input (m.st.heard ++ ds)) := by
  unfold Thr at hT
  exact hT.2.2.2.1 ds i hi

end

/-! ## 2 At the thread with the library's own values -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE SENTENCE OF `Item.constr m .idn` OUT OF THE THREAD**, at every continuation ds' of the
challenges heard: the hypothesis c of `part_head` (Law/W/IdnHotAt.lean) at the part .idn, at v :=
the run's input, y := the thread's strings, ds := heard ++ ds', where m is twice the group's number.
CONDITIONAL: on h, A and hT. -/
theorem idn_item_head
    {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.means mm.st.input
      (Item.constr m .idn) (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) :=
  item_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT
    (open_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) onePass_full
      (i := Item.constr m .idn)
      (by
        rw [asks_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) A]
        exact List.Mem.head _)) ds'

/-- **THE SENTENCE OF `Item.worth m 2 "rider"` OUT OF THE THREAD**, in the same form. CONDITIONAL:
on h, A and hT. -/
theorem rider_item_head
    {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.means mm.st.input
      (Item.worth m 2 "rider") (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) :=
  item_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT
    (open_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) onePass_full
      (i := Item.worth m 2 "rider")
      (by
        rw [asks_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) A]
        exact .tail _ (.tail _ (.tail _ (.head _))))) ds'

/-! ## 3 In the lookup's own terms -/

/-- **THE ITEM worth "rider" IN THE LOOKUP's OWN TERMS, OUT OF THE THREAD**: the hypothesis hW of
Johnson/Road/K4/W/HotOfRider.lean, at the library's own values. x: the lookup's place at the
segment. tl: the sub-proof's plan there. CONDITIONAL: on h, A, hT, hpc, hna, hx and ht. -/
theorem rider_lay_head
    {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) (hpc : VerifiableInference.Desc.K3.pieceAt (P5J.At.X Zp) m false = 2)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hna : attAt (P5J.At.X Zp) m = none) (hx : layAt (P5J.At.X Zp) m = some x)
    (ht : tlAt (P5J.At.X Zp) m = some tl) :
    layWorthRider x (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) tl h.𝔇.sent h.𝔇.l3.rad
      h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc (fun j => h.𝔇.l3.seat x.link false j.1)
      h.𝔇.l3.arr h.𝔇.l3.msgW (fun t : TS => t.fork?) (fun t : TS => t.lookHeard?) s
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) := by
  have q := rider_item_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A hT ds'
  have q' : (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX }
      mgBase).worth m 2 "rider" (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) := q
  rw [← hpc, mgAll_worth_lay_rider _ _ m hna hx ht] at q'
  exact q'

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.asks_k4
#print axioms ProofFile.Honest.K4.W.open_k4
#print axioms ProofFile.Honest.K4.W.item_of_thr
#print axioms ProofFile.Honest.K4.W.idn_item_head
#print axioms ProofFile.Honest.K4.W.rider_item_head
#print axioms ProofFile.Honest.K4.W.rider_lay_head
