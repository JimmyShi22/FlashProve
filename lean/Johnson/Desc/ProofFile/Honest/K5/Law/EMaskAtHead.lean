-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/EMaskAtHead.lean: CONDITIONAL: UNDER THE LIBRARY's HYPOTHESIS
ON THE PUBLIC INPUT (`P5J.AtMgA`) THE FIRST OF THE TWO EQUATIONS THAT THE HONEST SIDE OF AN
ATTENTION SEGMENT's OWN ROUNDS (kind K5) SPENDS OF THE SCRIPT (`K5ScriptQ`.eMask,
Honest/K5/Law/ScriptQ.lean) FOLLOWS FROM THE EQUATION IN THE SCRIPT's OWN LETTERS (`EMaskRaw`,
Honest/K5/Law/ScriptQRaw.lean), with no premise on public data left but which plan, place and
message are meant. One definition of a proposition, and statements with their proofs.

  `K5CellsQ`           the second equation's text, by a name: a premise's form
  `slots_in_K5`        CONDITIONAL: each slot under which a coin of the row lies is below the plan's
                       number of slots
  `eMask_of_raw`       CONDITIONAL: **`K5ScriptQ`.eMask's text from `EMaskRaw`**
  `k5ScriptQ_of_raw`   CONDITIONAL: `K5ScriptQ` from `EMaskRaw` and `K5CellsQ`
  `k5ScriptQ_head`     CONDITIONAL: the same at the letters as they are laid, the premise on the
                       number of coins paid by one return of the frame's `ready`

THE PREMISES OF `k5ScriptQ_head`, ALL OF THEM. h · hg: g is below 12 · Pl, hx, hm: which plan, place
and message are meant (`letters_head`, Honest/K5/Law/MaskRoomAtHead.lean, has such letters under h
and hg) · hr: `ready` returns once · Hs : `K5Seated` at the plan's numbers · hE : `EMaskRaw` at the
number `Forest.elems` a.fs of the member's first scalar · hC : `K5CellsQ`.

The road. `eMask_iff` (Honest/K5/Law/ScriptQRaw.lean) has the two forms equivalent under three
premises on public data. All three are paid here: the library's test on the seats of mask entries by
`masks_head` (Honest/K5/Law/ReaderReadsK5.lean); `MaskRoom` by `maskRoom_at_head`
(Honest/K5/Law/MaskRoomAtHead.lean); "the slots lie below the plan's number" by `slots_in_K5`, from
`PlanAt`'s field fits and `CoinsFew` (Honest/K5/Law/ScriptQAt.lean), which one return of `ready`
gives (`k5_lent_head`, Honest/K5/Law/Lent.lean; `coinsFew_of_lent`, Honest/K5/Law/CoinsFewOf.lean).

What it is for. `EMaskRaw` names no reader of the library and no state of the verifier. With this
file the mask's half of the premise `K5ScriptQ` of the joined forms (Honest/K5/Law/AllJoined.lean
and those behind it) COMES DOWN TO `EMaskRaw`. BY THIS ROAD IT IS NOT PAID: `K5ScriptQ` whole, the
mask's half with it, is had, among others: at a Script that is laid from lots, under premises on the
list of lots that their files pay nowhere (`k5ScriptQ_ofLots`, Honest/K5/Law/LotsK5.lean;
`k5ScriptQ_of_senders`, Honest/K5/Law/SendersScript.lean); at the joined Script, under the premises
that the head of AtFullSide/K5/TieAtJoinTop.lean lists (`k5ScriptQ_at_joinQ`,
`k5ScriptQ_at_joinQ_fit`); and at the first chain's Script at the base prover, at each group below
12, under three premises: the head at the return, that the maker returns, and that at each ready
input the trace's cells are the integer model's (`k5ScriptQ_at_firstScript`,
Honest/K5/Law/ScriptAtFirst.lean, with that file's Limits: it speaks of the ready inputs alone;
eMask says nothing where the book lends K5's row no coins; nothing there says that the prover's
sides play the Script's texts; NOT IN FRONT OF A LAW OVER COINS: the rule:
Johnson/Bind/ForProver/FiveFieldsAt.lean's head).

THE FORM WITH hLent. Of hr (one return of the frame's `ready`, a routine over the whole prover, the
whole book and all three chains) `k5ScriptQ_head` spends one thing alone: hLent: the book's lending
to the kind's own row returns, at all coins: `Lends5` (Honest/K5/Law/CoinsFewOf.lean) at the seat.
It names no input, no trace, no other kind's half and no other chain; of the book it reads the first
chain's rows and the entries. `k5ScriptQ_head_lent` takes hLent in hr's stead. hr gives hLent by
`k5_lent_head` (Honest/K5/Law/Lent.lean). The forms with hr keep their names and statements and
follow from these. hLent is shown nowhere either.

Limits. Conditional. `EMaskRaw` AND `K5CellsQ` ARE SHOWN OF NO SCRIPT HERE. That `ready` returns
anywhere is not shown here. h is a hypothesis of every statement that names it. At the library's
full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskRoomAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.CoinsFewOf
import Johnson.Desc.ProofFile.Honest.K5.Law.Lent

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls seatCalls valAt)
open VerifiableInference.Desc.First.Att.P (maskMsg slotsOf script matsOfMsg)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (attMs)
open H2K5.Door (seatAll)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM F0T)

/-- **EACH SLOT UNDER WHICH A COIN OF THE ROW LIES IS BELOW THE PLAN's NUMBER OF SLOTS.**
CONDITIONAL: the plan's facts; the place's numbers of rounds are the plan's; the book lends the row
no more coins than the kind takes slots. -/
theorem slots_in_K5 {Zp : ProofFile.Pub} {g : Nat} {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {Bk : ProverCoinCounts} {Z5 : Seat5} (hZ : Z5.P.x = a.own)
    (hc : CoinsFew Bk Z5 (slotsOf (script Z5.P.x))) (k : Coins Bk) (j : Nat)
    (hj : j < (coins5 Bk k Z5).length) : OnBytes.Model.Forest.elems a.fs + j < a.ns := by
  have e := hc k
  rw [hZ] at e
  have f := Pl.fits
  omega

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **The second equation's text** (`K5ScriptQ`.eCells, Honest/K5/Law/ScriptQ.lean): inside every
matrix but the lookup's planes' the witness's messages hold the trace's cell. It is a definition: a
premise's form. -/
def K5CellsQ (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat)
    (x₁ : VerifiableInference.Desc.First.Look.Place) (A : OnBytes.Attention.Plan)
    (cells : Tr → Cells) (Z5 : Seat5) : Prop :=
  ∀ k v hd, Vd v → N ≤ hd.length → ∀ i r c, i ≠ Z5.P.S.cf.NAs + 2 →
    r < (A.seam.tl.mats.getD i {}).m → c < (A.seam.tl.mats.getD i {}).k →
    matsOfMsg x₁ A.seam.tl h.𝔇.sent h.𝔇.l3.rad
        (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr (Q.wit k v hd)) i r c =
      Reading.gl.val (cellAt Z5.P.S Z5.link (cells v.trace) i r c)

variable {Q}

/-- **THE FIRST EQUATION's TEXT FROM THE EQUATION IN THE SCRIPT's OWN LETTERS.** CONDITIONAL: under
the hypothesis h; g is below 12; which plan, place and message are meant; hZ; hc; `EMaskRaw`. -/
theorem eMask_of_raw {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) {Z5 : Seat5} (hZ : Z5.P.x = a.own)
    (hc : CoinsFew Bk Z5 (slotsOf (script Z5.P.x))) {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {N : Nat} (hE : EMaskRaw h Q Vd N x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs)) :
    ∀ k v hd, Vd v → N ≤ hd.length → ∀ j, j < (coins5 Bk k Z5).length →
      (valAt h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link)
        (seatCalls h.𝔇.sent x₁.link)
        (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr (Q.wit k v hd))
        (.mask (OnBytes.Model.Forest.elems a.fs + j))).getD 0 =
        Reading.gl.val ((coins5 Bk k Z5).getD j zeroE) :=
  (eMask_iff (masks_head h hg Pl.plan hx).1 (maskRoom_at_head h hg Pl.plan hx hm)
    (slots_in_K5 Pl hZ hc)).2 hE

/-- **`K5ScriptQ` FROM `EMaskRaw` AND `K5CellsQ`.** CONDITIONAL: as `eMask_of_raw`; `K5CellsQ`. -/
theorem k5ScriptQ_of_raw {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) {Z5 : Seat5} (hZ : Z5.P.x = a.own)
    (hc : CoinsFew Bk Z5 (slotsOf (script Z5.P.x))) {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {N : Nat} (hE : EMaskRaw h Q Vd N x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs))
    {cells : Tr → Cells} (hC : K5CellsQ h Q Vd N x₁ a cells Z5) :
    K5ScriptQ h Q Vd N x₁ a cells Z5 (OnBytes.Model.Forest.elems a.fs) :=
  ⟨eMask_of_raw h hg Pl hx hm hZ hc hE, hC⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **`K5ScriptQ` AT THE LETTERS AS THEY ARE LAID, THE NUMBER OF COINS PAID BY hLent**: the book's
lending to the kind's own row returns, at all coins. CONDITIONAL: as `k5ScriptQ_head`, with hLent in
the stead of one return of `ready`, which gives it. -/
theorem k5ScriptQ_head_lent {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (Pl : PlanAt Zp g a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) {b : Nat}
    {cells : Tr → Cells} {Z5 : Seat5} {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread b cells Z5
      (parAt Zp g a) blk)
    (hLent : Lends5 W₀ Rc ProofFile.Inst X Bk cells Z5)
    {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    (hE : EMaskRaw h Q Vq N x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs))
    (hC : K5CellsQ h Q Vq N x₁ a cells Z5) :
    K5ScriptQ h Q Vq N x₁ a cells Z5 (OnBytes.Model.Forest.elems a.fs) :=
  k5ScriptQ_of_raw h hg Pl hx hm Hs.own.symm
    (coinsFew_of_lent (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (cells := cells) hLent)
    hE hC

/-- **`K5ScriptQ` AT THE LETTERS AS THEY ARE LAID, THE NUMBER OF COINS PAID BY ONE RETURN OF
`ready`.** CONDITIONAL: every premise stands, by name, in the file's head.
By `k5ScriptQ_head_lent` and `k5_lent_head` (Honest/K5/Law/Lent.lean). -/
theorem k5ScriptQ_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) {w₀ : W₀} {rc : Rc} {xi : ProofFile.Inst} {c : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc xi c = .ok R) {b : Nat}
    {cells : Tr → Cells} {Z5 : Seat5} {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread b cells Z5
      (parAt Zp g a) blk)
    {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    (hE : EMaskRaw h Q Vq N x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs))
    (hC : K5CellsQ h Q Vq N x₁ a cells Z5) :
    K5ScriptQ h Q Vq N x₁ a cells Z5 (OnBytes.Model.Forest.elems a.fs) :=
  k5ScriptQ_head_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg Pl hx hm Hs
    (fun k => k5_lent_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hr Hs k) hE hC

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.slots_in_K5
#print axioms ProofFile.Honest.K5.eMask_of_raw
#print axioms ProofFile.Honest.K5.k5ScriptQ_of_raw
#print axioms ProofFile.Honest.K5.k5ScriptQ_head_lent
#print axioms ProofFile.Honest.K5.k5ScriptQ_head
