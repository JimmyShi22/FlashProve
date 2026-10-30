-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstBack.lean: THE BACK HALF OF THE KEY FILE's FIRST CHAIN ON THE CHAIN's ONE SHAPE
(`Sh₁ BackSh`: E2E/KeyShapeFirst.lean's type at E2E/KeyShapeBack.lean's back part): the ranges'
proximity test · "batt.1.batt" · the last step of "w.1.send" · the seal: each one's guards as a
function of that shape, and the two forms (B1r), (B2r) of
Johnson/Desc/ProofFile/Honest/Thread/ShapeJoin.lean as far as they are had. The laws at explicit
arguments are other files'; here they are laid into the product. Definitions, statements and proofs.
Sub-protocols of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

  `Sh₁B`, `sh₁B`: the type and the reader. cs: the public codes, at which the mark on the claim's
    weights is said.
  `entersB`, **`gRng`**, **`rng_carries`**: the ranges' test: (B1r). Over E2E/KeyShapeRanges.lean.
    The guard asks in front what the seat asks of the chain's state, and
    Johnson/Desc/K12/Honest/Shape/TestSeatAsks.lean's `guardK12`: for (B2), which is
    E2E/KeyRangesReturns.lean's.
  `gBattA`, **`gBatt`**, **`batt_carries`**, **`batt_returns`**: "batt.1.batt": (B1r); and (B2) in
    the form that a sub-protocol with rounds has: the rounds fit the declared ones. Over
    E2E/KeyShapeBatch.lean.
  **`gRowsB`**, **`rowsB_carries₁`**, **`rowsB_returns₁`**: the kind K13's step behind W's
    commitment: (B1r) and (B2r), with no test on values. The guard asks the kind's two tests on its
    own shape too (`readyS`). Over E2E/KeyShapeRows.lean.
  **`gSealB`**, **`seal_both`**: the seal: (B1r) and (B2r), with no test on values. Over
    E2E/KeyShapeBack.lean's `seal_law`.
  `parW`, `gAnn`, `gIds`, **`gSendW`**, **`sendW_carries`**, **`sendW_returns`**: "w.1.send" whole:
    what is announced; the sending (E2E/KeyShapeSend.lean's `gSend`); the numbers sent; the kind
    K13's step: (B1r) and (B2r) at rounds that fit, with no test on values.
  `sentAt`, `groupsW`, `flat₁`, `sendWAt`, `flat₁_cut`: the description's own flat list, cut (over
    the library's `keyFirst_cut`).

Limits.
- `flat₁_cut` has a premise on public values: "w.1.send" is there (the shape has a message with W).
  `rng_carries` has two: the conditions on the ranges' test's place (`ranges_place`).
- (B2) of the ranges' test is not here: E2E/KeyRangesReturns.lean.
- `gRng`, `gBatt` and `gRowsB` ask the mark on the statement; that it holds at the chain's first
  state and is kept along the front half is another file's.


-/
import E2E.KeyShapeFirst
import E2E.KeyShapeRanges
import E2E.KeyShapeBatch
import E2E.KeyShapeRows
import E2E.KeyShapeFirstFront
import Johnson.Desc.K12.Honest.Shape.TestSeatAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest (CarriesR ReturnsR)
open ProofFile.Honest.Sh (testCore guardK12)
open VerifiableInference.Desc.Ground (has)
open VerifiableInference.Desc (Block roundsFit noDigest)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges rangesTest rangesParams
  batchTableRows batchWhere batchLens firstChainEnd Pieces lookupsOf)
open VerifiableInference.Desc.K13 (battRounds)
open AtPublicFiles.KeyShape (Sh₁ sh₁ Pub1)

/-- **The first chain's shape**, with the back part. -/
abbrev Sh₁B : Type := Sh₁ BackSh

/-- **The reader.** -/
abbrev sh₁B (Q : Pub1) (cs : Codes) (s : FirstState) : Sh₁B := sh₁ Q (backOf Q.one.lin cs) s

/-- Where the lookups' claims on the keys lie in the chain's state. -/
abbrev keysAt : VerifiableInference.Desc.Key.LookupRecord → List (List Lkp.Keys) := fun b => b.keys

variable (Q : Pub1) (cs : Codes)

/-! ## The ranges' proximity test -/

/-- **What the test's seat asks of the chain's state, on the shape**: no count of rows waits; all
lookups are laid; the ranges' group's test has not begun, and the group holds as many rows as the
lookups have laid. -/
def entersB (a : Sh₁B) : Bool :=
  a.2.owed.all (· == 0) && a.2.look.keys.length == (lookupsOf Q.one).length &&
    has a.1.st.groups[a.2.grp]? fun G => !G.inRun && G.kinds.length == a.2.look.rows.sum

/-- **The ranges' test on the shape.** In front: what the seat asks (`entersB`), and what the test
asks of the shape for its decision to return
(Johnson/Desc/K12/Honest/Shape/TestSeatAsks.lean's `guardK12`). -/
def gRng (N : H2U.PlaceNums) (a : Sh₁B) : Except String Sh₁B :=
  if entersB Q a && guardK12 (rangesParams N) a.1 a.2.grp a.2.rider then
    if a.2.tidy && a.1.st.codes.lengthsOk then
      match testCore (rangesParams N) a.1 a.2.grp a.2.rider with
      | some c => .ok (c, { a.2 with owed := none })
      | none => .error "the ranges' proximity test: a guard on the core's shape"
    else .error "the mark on the statement, or the codes' message lengths"
  else .error "the ranges' proximity test: what the seat and the test ask of the shape"

/-- **(B1r).** -/
theorem rng_carries {Cl : Type} (N : H2U.PlaceNums) (he : (rangesParams N).early = true)
    (ha : (rangesParams N).answers = 1) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    CarriesR (sh₁B Q cs) (fun s =>
      (rangesTest (enterRanges Q.one) leaveRanges N : Block FirstState Cl).decide s rs gs)
      (gRng Q N) := by
  intro s s' t hf hg
  obtain ⟨c, d, hs'⟩ := ranges_core Q.one N s s' rs gs hf he ha
  unfold gRng at hg
  split at hg
  swap
  · cases hg
  split at hg
  · rename_i hm
    rw [Bool.and_eq_true] at hm
    have hT : stTidyB s.d.st = true := hm.1
    have hl : s.d.st.codes.lengthsOk = true := hm.2
    have hT' := ranges_tidy Q.one N s s' rs gs hf hl hT
    have c' : testCore (rangesParams N) (sh₁B Q cs s).1 (sh₁B Q cs s).2.grp
        (sh₁B Q cs s).2.rider = some (shD s'.d) := c
    rw [c'] at hg
    obtain rfl := Except.ok.inj hg
    subst hs'
    refine Prod.ext rfl ?_
    show ({ AtPublicFiles.KeyShape.locSh Q (backOf Q.one.lin cs) s with owed := none } :
        AtPublicFiles.KeyShape.LocSh BackSh) =
      AtPublicFiles.KeyShape.locSh Q (backOf Q.one.lin cs) { s with d := d, owed := none }
    unfold AtPublicFiles.KeyShape.locSh
    have hT'' : stTidyB d.st = true := hT'
    rw [hT, hT'']
    rfl
  · cases hg

/-! ## "batt.1.batt" -/

/-- **"batt.1.batt" on the shape.** adm: `gPileA`'s argument. -/
def gBattA (adm : Bool) (N : Pieces) (sent : Nat) (a : Sh₁B) : Except String Sh₁B :=
  if a.2.tidy then
    (gBatchA adm Q.one cs N sent a.1 a.2.idx a.2.owed a.2.atEnd a.2.look.keysOk a.2.look.keys
      a.2.back).map fun y => (y.1, { a.2 with atEnd := true, owed := none, back := y.2 })
  else .error "the mark on the statement"

/-- The same, with "the parameters are admitted" laid in. -/
def gBatt (N : Pieces) (sent : Nat) (a : Sh₁B) : Except String Sh₁B :=
  gBattA Q cs (Wf.admitted a.1.st.codes Q.one.ranges (Wf.matrixOf Q.one.lin)) N sent a

theorem gBatt_eq (N : Pieces) (sent : Nat) (a : Sh₁B) : gBatt Q cs N sent a =
    if a.2.tidy then
      (gBatch Q.one cs N sent a.1 a.2.idx a.2.owed a.2.atEnd a.2.look.keysOk a.2.look.keys
        a.2.back).map fun y => (y.1, { a.2 with atEnd := true, owed := none, back := y.2 })
    else .error "the mark on the statement" := rfl

/-- **(B1r).** -/
theorem batt_carries {Cl : Type} (N : Pieces) (sent : Nat) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    CarriesR (sh₁B Q cs) (fun s =>
      (batchTableRows (Cl := Cl) keysAt Q.one N sent).decide s rs gs) (gBatt Q cs N sent) := by
  intro s s' t hf hg
  rw [gBatt_eq] at hg
  split at hg
  · rename_i hm
    have hT : stTidyB s.d.st = true := hm
    cases hy : gBatch Q.one cs N sent (sh₁B Q cs s).1 (sh₁B Q cs s).2.idx (sh₁B Q cs s).2.owed
        (sh₁B Q cs s).2.atEnd (sh₁B Q cs s).2.look.keysOk (sh₁B Q cs s).2.look.keys
        (sh₁B Q cs s).2.back with
    | error e =>
      rw [hy] at hg
      cases hg
    | ok y =>
      rw [hy] at hg
      obtain rfl := Except.ok.inj hg
      have hT' := batch_tidy (Cl := Cl)
        keysAt Q.one N sent s s' rs gs hf hT
      obtain ⟨rfl, rows, msg, l, d, rfl⟩ := batch_carries (Cl := Cl)
        keysAt Q.one cs N sent s s' rs gs hf
        _ y hy
      refine Prod.ext rfl ?_
      have hT'' : stTidyB d.st = true := hT'
      show ({ AtPublicFiles.KeyShape.locSh Q (backOf Q.one.lin cs) s with
          atEnd := true, owed := none
          back := backOf Q.one.lin cs (rows, msg, s.ids, some l) } :
            AtPublicFiles.KeyShape.LocSh BackSh) = AtPublicFiles.KeyShape.locSh Q (backOf Q.one.lin cs)
          { s with pile := rows, atEnd := true, owed := none, msgW := msg, lin := some l, d := d }
      unfold AtPublicFiles.KeyShape.locSh
      rw [hT, hT'']
      rfl
  · cases hg

/-- **(B2)**: the guards return, the rounds fit the declared ones, the one named test on values
passes: the decision returns. -/
theorem batt_returns {Cl : Type} (N : Pieces) (sent : Nat) (s : FirstState) (t : Sh₁B)
    (hg : gBatt Q cs N sent (sh₁B Q cs s) = .ok t)
    (hv : keysSumB (Wf.matrixOf Q.one.lin) Q.one.ranges.lookups s.base.keys = true)
    (rs : List Fmt.RoundView) (hr : roundsFit (battRounds (batchWhere Q.one N sent)) rs = true)
    (gs : List (List (Nat × List UInt64))) :
    ∃ s', (batchTableRows (Cl := Cl) keysAt Q.one N sent).decide s (rs.map noDigest) gs =
      .ok s' := by
  rw [gBatt_eq] at hg
  split at hg
  · cases hy : gBatch Q.one cs N sent (sh₁B Q cs s).1 (sh₁B Q cs s).2.idx (sh₁B Q cs s).2.owed
        (sh₁B Q cs s).2.atEnd (sh₁B Q cs s).2.look.keysOk (sh₁B Q cs s).2.look.keys
        (sh₁B Q cs s).2.back with
    | error e =>
      rw [hy] at hg
      cases hg
    | ok y => exact batch_returns (Cl := Cl) keysAt Q.one cs N sent s y hy hv rs hr gs
  · cases hg

/-! ## The step behind W's commitment -/

/-- **The kind K13's step behind W's commitment, on the shape.** -/
def gRowsB (a : Sh₁B) : Except String Sh₁B :=
  if a.2.tidy && a.2.atEnd && readyS Q.one.lin a.1 (a.2.owed.filter (· != 0)) a.2.back then
    (gRows Q.one.lin a.1 a.2.back).map fun y =>
      (y.1, { a.2 with owed := a.2.owed.filter (· != 0), back := y.2 })
  else .error "the mark on the statement; the chain's end; the kind's two tests on its shape"

/-- **(B1r).** -/
theorem rowsB_carries₁ {Cl : Type} (N : Pieces) (sent : Nat) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    CarriesR (sh₁B Q cs) (fun s => (VerifiableInference.Desc.K13.rowsB (Cl := Cl) batchLens
      (batchWhere Q.one N sent)).decide s rs gs) (gRowsB Q) := by
  intro s s' t hf hg
  unfold gRowsB at hg
  split at hg
  · rename_i hm
    rw [Bool.and_eq_true, Bool.and_eq_true] at hm
    have hT : stTidyB s.d.st = true := hm.1.1
    cases hy : gRows Q.one.lin (sh₁B Q cs s).1 (sh₁B Q cs s).2.back with
    | error e =>
      rw [hy] at hg
      cases hg
    | ok y =>
      rw [hy] at hg
      obtain rfl := Except.ok.inj hg
      have hT' := rowsB_tidy (Cl := Cl) (batchWhere Q.one N sent) s s' rs gs hf hT
      obtain ⟨rfl, l, d, rfl⟩ :=
        rowsB_carries (Cl := Cl) (batchWhere Q.one N sent) cs s s' rs gs hf y hy
      refine Prod.ext rfl ?_
      have hT'' : stTidyB d.st = true := hT'
      show ({ AtPublicFiles.KeyShape.locSh Q (backOf Q.one.lin cs) s with
          owed := s.owed.filter (· != 0)
          back := backOf Q.one.lin cs (s.pile, s.msgW, s.ids, some l) } :
            AtPublicFiles.KeyShape.LocSh BackSh) = AtPublicFiles.KeyShape.locSh Q (backOf Q.one.lin cs)
          { s with owed := s.debt, lin := some l, d := d }
      unfold AtPublicFiles.KeyShape.locSh
      rw [hT, hT'']
      rfl
  · cases hg

/-- **(B2r)**: no test on values: E2E/KeyShapeRows.lean's `rowsB_returns`. -/
theorem rowsB_returns₁ {Cl : Type} (N : Pieces) (sent : Nat) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ReturnsR (sh₁B Q cs) (fun s => (VerifiableInference.Desc.K13.rowsB (Cl := Cl) batchLens
      (batchWhere Q.one N sent)).decide s rs gs) (gRowsB Q) fun _ => true := by
  intro s t hg _
  unfold gRowsB at hg
  split at hg
  · rename_i hm
    rw [Bool.and_eq_true, Bool.and_eq_true] at hm
    exact rowsB_returns (Cl := Cl) (batchWhere Q.one N sent) cs s hm.1.2 hm.2 rs gs
  · cases hg

/-! ## "w.1.send" -/

/-- W's sending's numbers. groups: the groups told. -/
abbrev parW (N : Pieces) (groups : List (List Nat)) : VerifiableInference.Desc.K1.Par :=
  VerifiableInference.Desc.Key.sendingPar Q.one N.w "W and what rides with it"
    ((linMessageW Q.one.lin).getD #[]) groups

/-- "What is announced", on the shape. -/
def gAnn (P : VerifiableInference.Desc.K1.Par) (a : Sh₁B) : Except String Sh₁B :=
  if a.2.back.msgW == P.sent.toList then .ok a else .error "what is announced is not what is sent"

/-- "The numbers sent with W", on the shape. -/
def gIds (a : Sh₁B) : Except String Sh₁B :=
  .ok (a.1, { a.2 with back := { a.2.back with ids := a.2.sent } })

/-- **"w.1.send" on the shape**: what is announced; the sending; the numbers sent; the kind K13's
step. -/
def gSendW (N : Pieces) (groups : List (List Nat)) (a : Sh₁B) : Except String Sh₁B :=
  ((((gAnn (parW Q N groups) a).bind (gSend (parW Q N groups))).bind gIds).bind (gRowsB Q))

/-- **(B1r), at rounds that fit.** -/
theorem sendW_carries {Cl : Type} (N : Pieces) (sent : Nat) (groups : List (List Nat))
    (bw : Block FirstState Cl)
    (hw : VerifiableInference.Desc.Key.sendW Q.one N sent groups = some bw) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hfit : roundsFit bw.rounds rs = true) :
    CarriesR (sh₁B Q cs) (fun s => bw.decide s (rs.map noDigest) gs) (gSendW Q N groups) := by
  unfold VerifiableInference.Desc.Key.sendW at hw
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hw
  have hP : VerifiableInference.Desc.Key.sendingPar Q.one N.w "W and what rides with it" msg
      groups = parW Q N groups := by
    show _ = VerifiableInference.Desc.Key.sendingPar Q.one N.w "W and what rides with it"
      ((linMessageW Q.one.lin).getD #[]) groups
    rw [hmsg]
    rfl
  dsimp only at hfit ⊢
  rw [hP] at hfit ⊢
  obtain ⟨hf1, hd1⟩ := fit_front (Cl := Cl) "w.1.send" _
    (VerifiableInference.Desc.K13.rowsB batchLens (batchWhere Q.one N sent)) rfl rs hfit
  obtain ⟨hf2, hd2⟩ := fit_front (Cl := Cl) "sent and numbered" _
    (VerifiableInference.Desc.Key.quietAt "the numbers sent with W" (parW Q N groups).place
      fun s : FirstState => pure { s with ids := s.sent }) rfl rs hf1
  have hf3 : roundsFit (VerifiableInference.Desc.K1.rounds (parW Q N groups)) rs = true := hf2
  intro s s' t hs hg
  obtain ⟨s₃, h3, h4⟩ := ProofFile.Honest.bindR_ok ((hd1 s gs).symm.trans hs)
  obtain ⟨s₂, h2, h2'⟩ := ProofFile.Honest.bindR_ok ((hd2 s _).symm.trans h3)
  obtain ⟨s₁, h1, h1'⟩ := ProofFile.Honest.bindR_ok h2
  obtain ⟨t₃, g3, g4⟩ := ProofFile.Honest.bindR_ok hg
  obtain ⟨t₂, g2, g2'⟩ := ProofFile.Honest.bindR_ok g3
  obtain ⟨t₁, g1, g1'⟩ := ProofFile.Honest.bindR_ok g2
  -- what is announced: the state stays
  have e1 : s₁ = s := by
    have h1a : (do
      VerifiableInference.Desc.need "K1: the record does not announce what ROUNDS says"
        (s.msgW == (parW Q N groups).sent)
      pure s : Except String FirstState) = .ok s₁ := h1
    obtain ⟨_, _, h1a⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h1a
    exact (Except.ok.inj h1a).symm
  subst e1
  have f1 : t₁ = sh₁B Q cs s₁ := by
    unfold gAnn at g1
    split at g1
    · exact (Except.ok.inj g1).symm
    · cases g1
  subst f1
  obtain rfl := send_carries (Cl := Cl) Q (backOf Q.one.lin cs) "K1: W's sending"
    (parW Q N groups) rs _ hf3 s₁ s₂ t₂ h1' g1'
  obtain rfl : { s₂ with ids := s₂.sent } = s₃ := Except.ok.inj h2'
  obtain rfl : t₃ = sh₁B Q cs { s₂ with ids := s₂.sent } := (Except.ok.inj g2').symm
  exact rowsB_carries₁ (Cl := Cl) Q cs N sent _ _ _ s' t h4 g4

/-- **(B2r), at rounds that fit**: no test on values. -/
theorem sendW_returns {Cl : Type} (N : Pieces) (sent : Nat) (groups : List (List Nat))
    (bw : Block FirstState Cl)
    (hw : VerifiableInference.Desc.Key.sendW Q.one N sent groups = some bw) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hfit : roundsFit bw.rounds rs = true) :
    ReturnsR (sh₁B Q cs) (fun s => bw.decide s (rs.map noDigest) gs) (gSendW Q N groups)
      (fun _ => true) := by
  unfold VerifiableInference.Desc.Key.sendW at hw
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hw
  have hP : VerifiableInference.Desc.Key.sendingPar Q.one N.w "W and what rides with it" msg
      groups = parW Q N groups := by
    show _ = VerifiableInference.Desc.Key.sendingPar Q.one N.w "W and what rides with it"
      ((linMessageW Q.one.lin).getD #[]) groups
    rw [hmsg]
    rfl
  dsimp only at hfit ⊢
  rw [hP] at hfit ⊢
  obtain ⟨hf1, hd1⟩ := fit_front (Cl := Cl) "w.1.send" _
    (VerifiableInference.Desc.K13.rowsB batchLens (batchWhere Q.one N sent)) rfl rs hfit
  obtain ⟨hf2, hd2⟩ := fit_front (Cl := Cl) "sent and numbered" _
    (VerifiableInference.Desc.Key.quietAt "the numbers sent with W" (parW Q N groups).place
      fun s : FirstState => pure { s with ids := s.sent }) rfl rs hf1
  have hf3 : roundsFit (VerifiableInference.Desc.K1.rounds (parW Q N groups)) rs = true := hf2
  intro s t hg _
  obtain ⟨t₃, g3, g4⟩ := ProofFile.Honest.bindR_ok hg
  obtain ⟨t₂, g2, g2'⟩ := ProofFile.Honest.bindR_ok g3
  obtain ⟨t₁, g1, g1'⟩ := ProofFile.Honest.bindR_ok g2
  -- what is announced
  have hann : (s.msgW == (parW Q N groups).sent) = true ∧ t₁ = sh₁B Q cs s := by
    unfold gAnn at g1
    split at g1
    · rename_i c
      have c' : (s.msgW.toList == (parW Q N groups).sent.toList) = true := c
      exact ⟨by rw [← Array.beq_toList]; exact c', (Except.ok.inj g1).symm⟩
    · cases g1
  obtain ⟨ha, rfl⟩ := hann
  obtain ⟨s₂, h2⟩ := send_returns₁ (Cl := Cl) Q (backOf Q.one.lin cs) "K1: W's sending"
    (parW Q N groups) (rs.map noDigest) [] s t₂ g1' (vSend_fit (parW Q N groups) rs hf3)
  have h2' : (VerifiableInference.Desc.Key.sendingSeat (Cl := Cl) "K1: W's sending"
      (parW Q N groups)).decide s (rs.map noDigest) [] = .ok s₂ := h2
  obtain rfl := send_carries (Cl := Cl) Q (backOf Q.one.lin cs) "K1: W's sending"
    (parW Q N groups) rs _ hf3 s s₂ t₂ h2 g1'
  obtain rfl : t₃ = sh₁B Q cs { s₂ with ids := s₂.sent } := (Except.ok.inj g2').symm
  obtain ⟨s', h4⟩ := rowsB_returns₁ (Cl := Cl) Q cs N sent [] (gs.drop _)
    { s₂ with ids := s₂.sent } t g4 rfl
  refine ⟨s', (hd1 s gs).trans ?_⟩
  rw [hd2 s _]
  show ((((do
      VerifiableInference.Desc.need "K1: the record does not announce what ROUNDS says"
        (s.msgW == (parW Q N groups).sent)
      pure s : Except String FirstState).bind fun a =>
        (VerifiableInference.Desc.Key.sendingSeat (Cl := Cl) "K1: W's sending"
          (parW Q N groups)).decide a (rs.map noDigest) _).bind fun a =>
        (pure { a with ids := a.sent } : Except String FirstState)).bind fun a =>
      (VerifiableInference.Desc.K13.rowsB (Cl := Cl) batchLens
        (batchWhere Q.one N sent)).decide a [] _) = .ok s'
  rw [ha]
  show (((VerifiableInference.Desc.Key.sendingSeat (Cl := Cl) "K1: W's sending"
      (parW Q N groups)).decide s (rs.map noDigest) []).bind _).bind _ = .ok s'
  rw [h2']
  exact h4

/-! ## The seal -/

/-- **The seal on the shape.** -/
def gSealB (a : Sh₁B) : Except String Sh₁B :=
  if gSeal a.1.st a.2.owed a.2.back then .ok a else .error "the seal: a clause on the shape"

/-- **(B1r) and (B2r)**: no test on values. -/
theorem seal_both {Cl : Type} (N : Pieces) (inFront : List Fmt.DeclaredRound) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    CarriesR (sh₁B Q cs) (fun s => (firstChainEnd (Cl := Cl) N inFront).decide s rs gs) gSealB ∧
      ReturnsR (sh₁B Q cs) (fun s => (firstChainEnd (Cl := Cl) N inFront).decide s rs gs) gSealB
        fun _ => true :=
  AtPublicFiles.KeyShape.both_of_exact fun s t h => by
    unfold gSealB at h
    split at h
    · rename_i c
      exact ⟨s, (seal_law (Cl := Cl) Q.one.lin cs N inFront s rs gs).2 c, Except.ok.inj h⟩
    · cases h

/-! ## The description's own list -/

section Chain

variable (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (N : H2U.PlaceNums)

/-- The trees that the chain has sent in front of the batching, as the description counts them. -/
abbrev sentAt : Nat :=
  VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.batchRound D)

/-- The groups that W's sending's messages are told to join, as the description reads them. -/
abbrev groupsW : List (List Nat) :=
  VerifiableInference.Desc.Key.groupsTold told
    (VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.lastSendRound D))
    (VerifiableInference.Desc.Key.rootsAt D (VerifiableInference.Desc.Key.lastSendRound D))

/-- The description's own flat list of the first chain. -/
abbrev flat₁ : List (Block FirstState Claim) :=
  (VerifiableInference.Desc.Key.firstChain Q.one D told Q.set N).blocksInOrder

/-- W's sending, as the description lays it. -/
abbrev sendWAt : Option (Block FirstState Claim) :=
  VerifiableInference.Desc.Key.sendW Q.one VerifiableInference.Desc.Key.pieces (sentAt D)
    (groupsW D told)

/-- **The list is cut**: the front; the ranges' test; "batt.1.batt"; "w.1.send"; the seal. -/
theorem flat₁_cut (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw) :
    flat₁ Q D told N = H2K.JointK.keyFirstPre Q.one D told Q.set N ++
      [H2K.JointK.rngEntry Q.one N,
        (batchTableRows keysAt Q.one VerifiableInference.Desc.Key.pieces (sentAt D)).asBare,
        bw.asBare,
        (VerifiableInference.Desc.Key.firstChain Q.one D told Q.set N).last.asBare] := by
  show (VerifiableInference.Desc.Key.firstChain Q.one D told Q.set N).blocksInOrder = _
  rw [H2K.JointK.keyFirst_cut]
  congr 2
  unfold H2K.JointK.keyFirstPost
  show (([batchTableRows keysAt Q.one VerifiableInference.Desc.Key.pieces (sentAt D)] ++
    (sendWAt Q D told).toList).map Block.asBare) ++ _ = _
  rw [hw]
  rfl

end Chain

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.rng_carries
#print axioms AtPublicFiles.AtFiles.gBatt_eq
#print axioms AtPublicFiles.AtFiles.batt_carries
#print axioms AtPublicFiles.AtFiles.batt_returns
#print axioms AtPublicFiles.AtFiles.rowsB_carries₁
#print axioms AtPublicFiles.AtFiles.rowsB_returns₁
#print axioms AtPublicFiles.AtFiles.sendW_carries
#print axioms AtPublicFiles.AtFiles.sendW_returns
#print axioms AtPublicFiles.AtFiles.seal_both
#print axioms AtPublicFiles.AtFiles.flat₁_cut
