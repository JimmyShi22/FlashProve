-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/K9FormBehind.lean: the part `Form` of the first chain's
invariant at the border after each of the three sub-protocols of kind K9 in a segment: the batching,
"the one equation" and "the segment is shut". There are 25 segments, so 75 such sub-protocols, at
the numbers `14 * l + IM.nAt l + 2`, `+ 4 + 0` and `+ 4 + 2` of the chain's list. The file holds
seven conditional lemmas and no definition.

The work is done in other places. Honest/K9/XkAtHead.lean and Honest/K9/XkEqReach.lean
speak of the verifier's states: after an
accepting step there is no failure mark, and two of the facts that make up `Form` hold after the
step if they held before it. Honest/Thread/PubPAtK9.lean shows the remaining fact at these borders
outright. Honest/Thread/FormXK.lean shows that these four facts are the part `Form`
(`form_behind_of_xk`). This file joins them, as Honest/Thread/K11FormBehind.lean does for another
kind.

One step is new here. The lemmas for K9 state the first fact with the library's public test `EW` and
the written lists `IM.linksW` and `IM.placesW`; `Form` states it with the test `P1K2.EQ` and the
lists of `lettersHead`. The lemmas of items 1 to 3 go from one form to the other, by the four
equations of Honest/Thread/HeadLetters.lean, `xk_ew_of_eq` and `ew_gives_pub`
(Honest/K9/XkFront.lean) and `head_xk_of_pub` (Honest/Thread/FormXKPub.lean). They name no kind and
can serve any lemma that is stated with `EW` at these letters.

  1  `head_held_smp`   the test "held" of `lettersHead` is the library's `smpHeld`
  2  `xk_ew_front`, `held_w_front`   from `Form` at a border to the two facts in the form with `EW`
  3  `form_behind_of_ew`   from the four facts in that form after a step to `Form` after it
  4  `k9_form_behind_bat`   after the batching of segment `l`
  5  `k9_form_behind_eq`    after "the one equation" of segment `l`
  6  `k9_form_behind_shut`  after "the segment is shut" of segment `l`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the format's second hash function.
  * The step is a hypothesis: nothing here shows that the sub-protocol accepts.
  * The part `Form` before the step is a hypothesis. Nothing here shows that it holds in any run.
  * `k9_form_behind_eq` takes the whole invariant before the step, not only its part `Form`: the
    lemma that it calls (`K9.xk_eq_thr`, Honest/K9/XkEqReach.lean) uses that the state is reached.
    Nothing here shows that the invariant holds in any run.
  * Only the part `Form` is shown, not the parts `rides` and `keeps`.
  * The file depends on files of other authors under Honest/K9/.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormXKPub
import Johnson.Desc.ProofFile.Honest.Thread.HeadLetters
import Johnson.Desc.ProofFile.Honest.Thread.PubPAtK9
import Johnson.Desc.ProofFile.Honest.K9.XkAtHead
import Johnson.Desc.ProofFile.Honest.K9.XkEqReach
import Johnson.Desc.ProofFile.Honest.K9.XkFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.First (samplesHeld Meaning)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open LPFK9.HandsAt (EW)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The test "held" of `lettersHead` is the library's `smpHeld` on the state's statement and
book. -/
theorem head_held_smp (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.held =
      fun j t (a : ProofFile.InstPub × TS) => VerifiableInference.Desc.smpHeld a.2.st a.2.book j t :=
  (head_held_is h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).trans
    (VerifiableInference.Desc.Sound.mgAll_held h.𝔇 mgBase)

/-- From `Form` at border `b`: the five Bools at the public test `EW` and the written lists. -/
theorem xk_ew_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form b k s m) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW
      (EW h.𝔇.pubD (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub) b s = true :=
  K9.xk_ew_of_eq (head_pub_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)

/-- From `Form` at border `b`: `samplesHeld` at the items that are open by the written lists. -/
theorem held_w_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form b k s m) :
    samplesHeld (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
      (IM.openAt IM.linksW IM.placesW b) (m.st.input.x.pub, s) = true := by
  rw [head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w]
  exact held_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF

/-- `Form` after a step, from `Form` before it and four facts after it: no failure mark, the five
Bools at `EW`, `samplesHeld` at the written lists, and what the open public items say. -/
theorem form_behind_of_ew (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {blk : Block TS ProofFile.Cl} {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s')
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form b k s m)
    (h' : s'.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW
      (EW h.𝔇.pubD (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub) (b + 1) s' = true)
    (hs : samplesHeld (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
      (IM.openAt IM.linksW IM.placesW (b + 1)) (m.st.input.x.pub, s') = true)
    (hPP : ∀ q ∈ P1K2.pubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps (b + 1),
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP q
        (m.st.input.x.pub, s')) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (b + 1) k s' y.2 := by
  rw [head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hx hs
  exact form_behind_of_xk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS h'
    (head_xk_of_pub h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF hx fun he =>
      K9.ew_gives_pub (head_pub_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
        (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
        (head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
        (head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) he)
    hs hPP

/-- The part `Form` of the invariant after the batching of segment `l`, from `Form` before it (`hF`)
and the sub-protocol's step (`hS`). -/
theorem k9_form_behind_bat (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (14 * l + IM.nAt l + 2) k s m)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (14 * l + IM.nAt l + 2 + 1) k s' y.2 := by
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  refine form_behind_of_ew h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hS hF
    (K9.mark_bat_at h hl 0 hblk hyes)
    (K9.xk_bat_at h hl 0 (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub (fun _ _ _ => rfl)
      hblk hyes (Option.isNone_iff_eq_none.1 hF.1)
      (xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF))
    (K9.samples_bat_at h hl 0 _ _ (head_held_smp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _
      hblk hyes (held_w_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF)) ?_
  rw [show 14 * l + IM.nAt l + 2 + 1 = 14 * l + IM.nAt l + 3 by omega]
  exact head_pubP_after_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl (by decide) _

/-- The part `Form` of the invariant after "the one equation" of segment `l`, from the invariant
before it (`hT`) and the sub-protocol's step (`hS`). -/
theorem k9_form_behind_eq (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + IM.nAt l + 4 + 0) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (14 * l + IM.nAt l + 4 + 0 + 1) k s' y.2 := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  refine form_behind_of_ew h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hS hF
    (K9.mark_eq_at h hl 0 hblk hyes)
    (K9.xk_eq_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl 0
      (mgBase : Meaning ProofFile.InstPub WtF).pub (fun _ _ _ => rfl) hblk hT hyes
      (Option.isNone_iff_eq_none.1 hF.1)
      (xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF))
    (K9.samples_eq_at h hl 0 _ _ (head_held_smp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _
      hblk hyes (held_w_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF)) ?_
  rw [show 14 * l + IM.nAt l + 4 + 0 + 1 = 14 * l + IM.nAt l + 5 by omega]
  exact head_pubP_after_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl (by decide) _

/-- The part `Form` of the invariant after "the segment is shut" of segment `l`, from `Form` before
it (`hF`) and the sub-protocol's step (`hS`). -/
theorem k9_form_behind_shut (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (14 * l + IM.nAt l + 4 + 2) k s m)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (14 * l + IM.nAt l + 4 + 2 + 1) k s' y.2 := by
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  refine form_behind_of_ew h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hS hF
    (K9.mark_shut_at h hl 0 hblk hyes)
    (K9.xk_shut_at h hl 0 (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub (fun _ _ _ => rfl)
      hblk hyes (Option.isNone_iff_eq_none.1 hF.1)
      (xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF))
    (K9.samples_shut_at h hl 0 _ _ (head_held_smp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _
      hblk hyes (held_w_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF)) ?_
  rw [show 14 * l + IM.nAt l + 4 + 2 + 1 = 14 * l + IM.nAt l + 7 by omega]
  exact head_pubP_after_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl (by decide) _

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_held_smp
#print axioms ProofFile.Honest.FirstThread.xk_ew_front
#print axioms ProofFile.Honest.FirstThread.held_w_front
#print axioms ProofFile.Honest.FirstThread.form_behind_of_ew
#print axioms ProofFile.Honest.FirstThread.k9_form_behind_bat
#print axioms ProofFile.Honest.FirstThread.k9_form_behind_eq
#print axioms ProofFile.Honest.FirstThread.k9_form_behind_shut
