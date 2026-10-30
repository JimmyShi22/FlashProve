-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqExchangeHead.lean: THE FRAME's DEBT AT THE ITEM "row l equation" (`ExchangeAtS` at
`SaidOk`), AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD, AT K9's MEMBER "THE ONE EQUATION" OF EACH OF THE 25
SEGMENTS: UNDER THE HEAD ALONE: NO NAMED PREMISE BESIDE l < 25. AN IMPLICATION STILL: that the thread stands in front of
that member at any run is shown by nobody; and the open item total l, whose sentence is spent, is the frame's own
member's to pay. No definition is made; no prover is made in this file; no goal is stated.
  § 1 **`exchange_row_of`**: AT A VARIABLE THREAD (after `exchange_totalB_seat`, Honest/K9/TotalExchangeSeat.lean): a
      share at a member that turns one open item into another, from four plain premises: the item in front is open and
      says no less than Tot; Row gives what the item behind says; behind each step Tot in front gives Row behind, at
      every witness. WHY IT STANDS APART: typed straight at the head's thread, the same steps made Lean's unfolding run
      away (no end within twenty times the usual limit); here nothing of the head's can be unfolded
  § 2 `head_means_total`, `head_means_rowEq`, `rowSays_at_state`   what the two items say at the laid letters: by
      unfolding (after the frame's `head_means_totalB`): total l: `totalQ` at the segment's group and `seatTab`, and the
      rows' test; row l equation: `AllSay` of the class's rows at the witness's words through the state's book. Neither
      reads the letter test, the strings or what was handed to the chain
  § 3 `eqx_N`, `eqx_pubD_N`, `eqx_bs`, `eqx_step`, `eqx_stepYes`, `eqx_form`, `eqx_mark`   each "by unfolding" its own
      small lemma, both sides stated · § 4 `eqx_totalIn`, `eqx_xk_behind` (our `xk_eq_thr`, called as the frame's
      `k9_form_behind_eq` calls it), `eqx_bools_behind` · § 5 `eqx_go`: the step at the head: from the pair in front and
      the step, `rowSays_behind` (Honest/K9/EqRowAtHead.lean) · § 6 `eqx_total_gives`, `eqx_row_means`
  § 7 **`exchange_rowEq_head`**   l < 25: `ExchangeAtS` of the thread of `lettersHead …`, EVERY LETTER FREE, at
      `SaidOk`, at 14 l + `IM.nAt l` + 4, at `Item.row l .equation`: one term
WHERE THE WITNESS STANDS: under "for all" throughout: in the open item's sentence and in the item's. No term of a Script
stands in a statement (Q in the thread's letters alone).
WHAT IS NOT CLAIMED. NO MEMBER: that a stand is there. Who pays total l (the frame's member "the runs behind", one
border in front). That the closing's test takes in no other row. Called outside this file: `exchange_rowEq_head`, by
Honest/K9/ExchangeByKind.lean and ExchangeEq.lean. At the full size and the format's second hash function alone. Nothing
on any property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 381 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqRowAtHead
import Johnson.Desc.ProofFile.Honest.K9.ThrBehind
import Johnson.Desc.ProofFile.Honest.K9.XkEqReach
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.HeadMeans
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share FoldOnce)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open LPFK9.HandsAt (EW)
open VerifiableInference.Desc.Sound (mgBase)

/-! ## 1 AT A VARIABLE THREAD: the share from four plain premises. Nothing of the head's is unfolded here -/

section
variable {V₁ W₁ X₁ Pb₁ : Type} {Bk₁ : ProverCoinCounts} {T₁ : Thread Bk₁ S Claim V₁ W₁ X₁ Pb₁}

/-- **A share at a member that turns one open item into another**: iT is open in front and says no less than Tot of the
state and the witness; Row of the state and the witness gives what iR says; and behind each step of the member, from the
pair in front, Tot in front gives Row behind, AT EVERY WITNESS. After `exchange_totalB_seat`. -/
theorem exchange_row_of (e : ℕ) (iT iR : T₁.ι) (Tot Row : S → T₁.Wt → Prop) (hopen : iT ∈ T₁.opened e)
    (hT : ∀ wI a st v, T₁.means wI iT a st v → Tot a.2 v)
    (hR : ∀ wI a st v, Row a.2 v → T₁.means wI iR a st v)
    (hgo : ∀ blk, T₁.bs[e]? = some blk → ∀ κ s m En ds y cols s', ThrS T₁ SaidOk e κ s m En →
      T₁.Stepped blk κ s m En ds y cols s' → ∀ v, Tot s v → Row s' v) :
    ExchangeAtS T₁ SaidOk e iR := by
  intro blk hblk κ s m En ds y cols s' hA hd hS
  obtain ⟨hi, hh⟩ := moved_mid T₁ blk κ m En ds y cols hS.1
  intro ds' j hj
  obtain rfl := List.mem_singleton.1 hj
  refine hR _ _ _ _ ?_
  rw [hi, hh, List.append_assoc]
  exact hgo blk hblk κ s m En ds y cols s' hA hS _
    (hT m.st.input (T₁.seat κ m s) (T₁.strs En) _ (hA.1.2.2.2.1 (ds ++ ds') iT hopen))

end

/-! ## 2 What the two items say at the laid letters -/

/-- **WHAT total SAYS AT THE LAID LETTERS**: after the frame's `head_means_totalB`. -/
theorem head_means_total (m : Nat) (v : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (y : Strs) (u : WtF) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means v (Item.total m) a y u ↔
      (Sound.totalQ (h.𝔇.N.group m) a.2 (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms u) ∧
        h.𝔇.rw m a.2 = true) := Iff.rfl

/-- **WHAT THE EQUATION's ROW SAYS AT THE LAID LETTERS.** -/
theorem head_means_rowEq (m : Nat) (v : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (y : Strs) (u : WtF) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means v (Item.row m .equation) a y u ↔
      rowSays h.𝔇.N (wordsAtFirst h.𝔇.arr) m .equation a y u := Iff.rfl

/-- The row's sentence, written at the state alone: it reads neither what was handed to the chain nor the strings. -/
theorem rowSays_at_state {P : Type} (N : Numbers) (arr : ℕ → ℕ → ℕ) (m : ℕ) (c : RowClass) (a : P × S)
    (y : Strs) (u : WtF) :
    rowSays N (wordsAtFirst arr) m c a y u ↔
      OnBytes.Means.AllSay OnBytes.Slice.rdE a.2.st (classRows N m c a.2)
        (Sound.wordsFirst arr a.2.st a.2.book u) := Iff.rfl

/-! ## 3 EACH «BY UNFOLDING» AS ITS OWN LEMMA, both sides stated -/

/-- The table's numbers are the data's. (Twins: the library's `P5J.kind_N`; our `data_numbers`.) -/
theorem eqx_N : P5J.At.N Zp cF = h.𝔇.N := rfl

/-- So are the public tests' data's. (Twin: the library's `H2K5.Door.tie_N`.) -/
theorem eqx_pubD_N : h.𝔇.pubD.N = h.𝔇.N := rfl

/-- The thread's members are the first chain's flat list. -/
theorem eqx_bs {b : ℕ} {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk) :
    cF.blocksInOrder[b]? = some blk := hb

/-- The verifier's half of a member's step of the thread, at the first tree 0. -/
theorem eqx_step {blk : Block TS ProofFile.Cl} {κ : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List Desc.OpenedColumn}
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk κ s m En ds y cols s') :
    blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2

/-- The same as the library's one form of a yes. -/
theorem eqx_stepYes {blk : Block TS ProofFile.Cl} {κ : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {En : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List Desc.OpenedColumn}
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk κ s m En ds y cols s') :
    StepYes 0 blk s s' := stepped_yes hS

/-- The thread's third clause. -/
theorem eqx_form {b : ℕ} {κ : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b κ s m En) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form b κ s m := hT.2.2.1

/-- The form says: no mark. -/
theorem eqx_mark {b : ℕ} {κ : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form b κ s m) :
    s.failed = none := Option.isNone_iff_eq_none.1 hF.1

/-! ## 4 In front of the member and behind it: from the thread to plain facts on the two states -/

/-- "The one sum can be taken", in front. -/
theorem eqx_totalIn {l : ℕ} (hl : l < 25) {κ : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (14 * l + IM.nAt l + 4) κ s m) :
    Desc.K9.totalIn (h.𝔇.N.group l) s = true := by
  have hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW
      (EW h.𝔇.pubD (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub) (14 * l + IM.nAt l + 4) s = true :=
    xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  have e1 : Desc.K9.totalIn (h.𝔇.pubD.N.group l) s = true := totalIn_of_xk hl hx
  rw [eqx_pubD_N h] at e1
  exact e1

/-- The promise's five Bools behind: NOT through the form behind: our `xk_eq_thr`, as the frame's `k9_form_behind_eq`
itself calls it. -/
theorem eqx_xk_behind {l : ℕ} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4]? = some blk) {κ : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + IM.nAt l + 4) κ s m En) (hy : IM.Yes 0 blk s s') :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW
      (EW h.𝔇.pubD (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub) (14 * l + IM.nAt l + 4 + 1) s' = true := by
  have hF := eqx_form h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT
  have hu := eqx_mark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  have hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW
      (EW h.𝔇.pubD (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub) (14 * l + IM.nAt l + 4) s = true :=
    xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  exact xk_eq_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl 0 (mgBase : Meaning ProofFile.InstPub WtF).pub
    (fun _ _ _ => rfl) hb hT hy hu hx

/-- The two Bools that the row's road spends, at the data's own numbers. -/
theorem eqx_bools_behind {l : ℕ} {E : ℕ → S → Bool} {s' : S}
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW E (14 * l + IM.nAt l + 4 + 1) s' = true) :
    rowsHeld h.𝔇.N
      ((openSets P5J.fullLinks P5J.At.ps (start P5J.fullLinks))[14 * l + IM.nAt l + 4 + 1]?.getD []) s' = true ∧
      bookAt h.𝔇.N P5J.At.ps[14 * l + IM.nAt l + 4 + 1]? s' = true := by
  have hb := bools_of_xk hx
  rw [eqx_N h] at hb
  exact hb

/-! ## 5 The step at the head: "total" in front gives the row's sentence behind -/

/-- The premise hgo of `exchange_row_of`, at the frame's own thread at the head. -/
theorem eqx_go {l : ℕ} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4]? = some blk) {κ : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List Desc.OpenedColumn}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (14 * l + IM.nAt l + 4) κ s m En)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk κ s m En ds y cols s') (v : WtF)
    (h0 : Sound.totalQ (h.𝔇.N.group l) s (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) :
    OnBytes.Means.AllSay OnBytes.Slice.rdE s'.st (classRows h.𝔇.N l .equation s')
      (Sound.wordsFirst h.𝔇.arr s'.st s'.book v) := by
  have hlt : 14 * l + IM.nAt l + 4 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1
  -- the library's own step
  obtain ⟨p, hb₃⟩ := eq_step_sealed h hl hb
  have hst : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) :=
    eqx_step h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hS
  have hs : (Desc.K9.oneEquation (Cl := ProofFile.Cl) Desc.K9.atS p).step 0 s (roundsOf y.1) cols =
      .ok (s', cols.length) := hb₃ 0 s (roundsOf y.1) cols (s', cols.length) hst
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hst⟩
  -- in front
  have hF := eqx_form h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1
  have hu : s.failed = none := eqx_mark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  have hTin : Desc.K9.totalIn (h.𝔇.N.group l) s = true :=
    eqx_totalIn h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hF
  have hw : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (m.st.input.x.pub, s) :=
    thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT
  have hraw : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (m.st.input.x.pub, s) :=
    thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT.1
  -- behind
  have hu' : s'.failed = none := mark_eq_at h hl 0 hb hyes
  have hx' := eqx_xk_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hb hT.1 hyes
  obtain ⟨hRows', hB'⟩ := eqx_bools_behind h hx'
  have hR' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4 + 1) (m.st.input.x.pub, s') :=
    Reach.succ hraw hb (eqx_stepYes h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hS)
  -- the join (Honest/K9/EqRowAtHead.lean)
  have E : rowSays h.𝔇.N (wordsAtFirst h.𝔇.arr) l .equation (m.st.input.x.pub, s') noStrs v :=
    rowSays_behind h hl hs hw hu hTin hR' hu' hB' hRows' noStrs v h0
  exact (rowSays_at_state h.𝔇.N h.𝔇.arr l .equation (m.st.input.x.pub, s') noStrs v).1 E

/-! ## 6 The other two premises, stated -/

/-- The premise hT of `exchange_row_of`. -/
theorem eqx_total_gives (l : ℕ) (wI : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (st : Strs) (v : WtF)
    (hh : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means wI (Item.total l) a st v) :
    Sound.totalQ (h.𝔇.N.group l) a.2 (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) :=
  ((head_means_total h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w l wI a st v).1 hh).1

/-- The premise hR of `exchange_row_of`. -/
theorem eqx_row_means (l : ℕ) (wI : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (st : Strs) (v : WtF)
    (hh : OnBytes.Means.AllSay OnBytes.Slice.rdE a.2.st (classRows h.𝔇.N l .equation a.2)
      (Sound.wordsFirst h.𝔇.arr a.2.st a.2.book v)) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means wI (Item.row l .equation) a st v :=
  (head_means_rowEq h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w l wI a st v).2
    ((rowSays_at_state h.𝔇.N h.𝔇.arr l .equation a st v).2 hh)

/-! ## 7 The share -/

/-- **THE FRAME's DEBT AT THE ITEM "row l equation", AT THE FRAME's OWN THREAD AT THE HEAD, AT "THE ONE EQUATION" OF
EACH OF THE 25 SEGMENTS.** -/
theorem exchange_rowEq_head {l : ℕ} (hl : l < 25) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (14 * l + IM.nAt l + 4) (Item.row l .equation) :=
  exchange_row_of (T₁ := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread)
    (14 * l + IM.nAt l + 4) (Item.total l) (Item.row l .equation)
    (fun s v => Sound.totalQ (h.𝔇.N.group l) s (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v))
    (fun s v => OnBytes.Means.AllSay OnBytes.Slice.rdE s.st (classRows h.𝔇.N l .equation s)
      (Sound.wordsFirst h.𝔇.arr s.st s.book v))
    (head_eq_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl)
    (fun wI a st v hh => eqx_total_gives h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w l wI a st v hh)
    (fun wI a st v hh => eqx_row_means h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w l wI a st v hh)
    (fun _ hblk _ _ _ _ _ _ _ _ hA hS v h0 =>
      eqx_go h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl
        (eqx_bs h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk) hA hS v h0)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.exchange_row_of
#print axioms ProofFile.Honest.K9.head_means_total
#print axioms ProofFile.Honest.K9.head_means_rowEq
#print axioms ProofFile.Honest.K9.rowSays_at_state
#print axioms ProofFile.Honest.K9.eqx_N
#print axioms ProofFile.Honest.K9.eqx_pubD_N
#print axioms ProofFile.Honest.K9.eqx_bs
#print axioms ProofFile.Honest.K9.eqx_step
#print axioms ProofFile.Honest.K9.eqx_stepYes
#print axioms ProofFile.Honest.K9.eqx_form
#print axioms ProofFile.Honest.K9.eqx_mark
#print axioms ProofFile.Honest.K9.eqx_totalIn
#print axioms ProofFile.Honest.K9.eqx_xk_behind
#print axioms ProofFile.Honest.K9.eqx_bools_behind
#print axioms ProofFile.Honest.K9.eqx_go
#print axioms ProofFile.Honest.K9.eqx_total_gives
#print axioms ProofFile.Honest.K9.eqx_row_means
#print axioms ProofFile.Honest.K9.exchange_rowEq_head
