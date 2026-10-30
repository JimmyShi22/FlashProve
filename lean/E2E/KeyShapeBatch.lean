--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeBatch.lean: "batt.1.batt", THE KEY FILE's FIRST CHAIN's BATCHING OF THE ROWS ON THE
TABLE, CUT IN TWO: STRUCTURE | VALUES (the cut: Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), ON
THE ONE SHAPE OF STATEMENT, BOOK AND ROOTS (Johnson/Desc/Ground/Shape/) AND THE CHAIN's BACK PART
(E2E/KeyShapeBack.lean). BOTH DIRECTIONS. Definitions, statements and proofs. A sub-protocol of the
verifier's: NOTHING IS SHOWN OF ANY PROVER.

The sub-protocol is four in a row: "the rows on the table" · the kind K13's front · its batching ·
its step in front of W. The kind's own guards on a shape of its own (`readySh`, nine tests) and the
law that under them the three return (`m3_returns_at`, general in the lens) are
Johnson/Desc/K13/Honest/Shape.lean's and PartM3.lean's: CALLED. Here: that shape is read off the one
shape; the four are joined; the shape behind is written on the one shape.

  `sh3Of`, **`sh3_eq`**: the kind's shape of what its lens yields is a function of the statement's
    shape, two named values and the back part.
  `claimOfRow`, `claimSh4_member`: the claim's shape, off the shape of the row that is handed on.
  `gBatchA`, **`gBatch`**: the sub-protocol on the shape: `gPile`; "the chain has not come to its
    end"; the kind's nine tests; two bounds on public numbers, by which the mark on the claim's
    weights is laid; the taking of the mask entries (`takeMasksS`); what W's sending announces.
  `batch_says`: the sub-protocol's accept, read back: the library's `Key.seat_says` with what W's
    sending announces and the batching's own inversion (`batt_ok`).
  **`batch_carries`**: (B1): where it accepts and the guards return, they return the core's shape
    and the back part behind; of the other named values two turn: the chain has come to its end; no
    count of rows waits.
  `batch_tidy`: the mark on the statement is kept.
  **`batch_returns`**: (B2): the guards return, the rounds fit the declared ones, and ONE named test
    on values passes (`keysSumB`: of "the rows on the table"): the decision returns.

Limits.
- The guards are enough, not needed (`gPile` asks "the parameters are admitted"; the two bounds).
- The kind's files that are called are the hash build's working files and lots for the next seal:
  unread there.
- decide alone: not the sub-protocol's own test on public values, not its step's tests on columns.


-/
import E2E.KeyShapeBack
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.K13.Honest.PartM3
import Johnson.Desc.K13.Honest.ClaimShape
import Johnson.Desc.K13.Honest.ShapeBack
import Johnson.Desc.K13.Law.Then
import Johnson.Desc.K13.Keeps
import Johnson.Desc.Tidy.Stay
import Johnson.Desc.Ground.Shape.Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc (named need roundsFit noDigest Block)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (ChainState layPile batchTableRows batchWhere batchLens Pieces)
open VerifiableInference.Desc.K13 (battRounds)
open VerifiableInference.Desc.K13.Honest (RowSh rowSh LaidSh laidSh ClaimSh claimSh4 Sh MsgSh
  partSh3 readySh claimSh)
open VerifiableInference.Desc.K13.Law (ebind_ok)
open VerifiableInference.Desc.Third.Law (ok_of_bind some_of_named true_of_need)

variable {β Cl : Type}

/-! ## The kind's shape, off the one shape -/

/-- The kind's shape of what its lens yields at a state that has come to the batching. a: the
statement's shape; idx: the index-mask message's number; owed: the count of rows that waits. -/
def sh3Of (a : StSh) (idx : Nat) (owed : Option Nat) (b : BackSh) : Sh :=
  ⟨b.lin.isNone, false, (owed.filter (· != 0)).isNone, idx, b.pile, a.codes,
    (a.oracles.map fun x => (⟨x.shape, x.ledger⟩ : MsgSh)).toArray⟩

/-- The part that the lens yields. -/
def partAt (s : ChainState β) : VerifiableInference.Desc.K13.Part :=
  { owed := s.debt, heard := none, indexMasks := s.idx, pile := s.pile, msg := s.msgW
    ids := s.ids, lin := s.lin, d := s.d }

/-- **It is the kind's own.** -/
theorem sh3_eq (S : LinShape) (cs : Codes) (s : ChainState β) :
    partSh3 (partAt s) = sh3Of (stSh s.d.st) s.idx s.owed (backSh S cs s) := by
  unfold partSh3 sh3Of partAt backSh backOf VerifiableInference.Desc.K13.Honest.msgsOf
  have e1 : (s.lin.map laidSh).isNone = s.lin.isNone := by cases s.lin <;> rfl
  have e2 : ((stSh s.d.st).oracles.map fun x => (⟨x.shape, x.ledger⟩ : MsgSh)).toArray =
      s.d.st.oracles.map fun x => ⟨x.shape, x.ledger⟩ := by
    apply Array.toList_inj.1
    show (s.d.st.oracles.toList.map orcSh).map _ = _
    rw [List.map_map, Array.toList_map]
    rfl
  dsimp only
  rw [e1, e2]
  rfl

/-! ## The claim's shape -/

/-- The claim's shape, off the shape of the row that is handed on. -/
def claimOfRow (r : RowSh) : ClaimSh := ⟨r.point, r.slots.map fun x => (x.oracle, .mask, x.index)⟩

theorem claimSh4_member (row : TensorRow) :
    claimSh4 (memberClaim row) = claimOfRow (rowSh row) := by
  unfold claimSh4 claimOfRow rowSh memberClaim
  simp only [List.map_map]
  rfl

/-! ## The sub-protocol on the shape -/

/-- **"batt.1.batt" on the shape.** c: the core's shape; idx, owed, atEnd: three of the chain's
named values; keysOk, slots: the mark on the claims on the keys, and each claim's slots; b: the back
part; adm: `gPileA`'s argument. -/
def gBatchA (adm : Bool) (one : OneTime) (cs : Codes) (N : Pieces) (sent : Nat) (c : CoreSh)
    (idx : Nat) (owed : Option Nat) (atEnd keysOk : Bool) (slots : List (List (List Slot)))
    (b : BackSh) : Except String (CoreSh × BackSh) := do
  let b₁ ← gPileA adm one c.st idx keysOk slots b
  need "the chain has not come to its end" (!atEnd)
  need "K13: the nine tests" (readySh (batchWhere one N sent) (sh3Of c.st idx owed b₁))
  need "the matrix's row bits fit Omega's table, of at most 63 index bits"
    (decide (one.lin.kRow ≤ (linLayOmega cs one.lin).bits) &&
      decide ((linLayOmega cs one.lin).bits ≤ 63))
  let x ← named "K13: the mask entries" (takeMasksS c idx (Batt.masksOf one.lin.kCol))
  let msg ← named "K13: W's message" (linMessageW one.lin)
  pure (x.2, { b₁ with
    msgW := msg.toList
    lin := some ⟨noId, noId, noId, none,
      claimOfRow (claimSh one.lin.kCol b₁.pile (x.1.map fun i => ⟨idx, i⟩))⟩
    weights := true })

/-- The same, with "the parameters are admitted" laid in. -/
def gBatch (one : OneTime) (cs : Codes) (N : Pieces) (sent : Nat) (c : CoreSh) (idx : Nat)
    (owed : Option Nat) (atEnd keysOk : Bool) (slots : List (List (List Slot))) (b : BackSh) :
    Except String (CoreSh × BackSh) :=
  gBatchA (Wf.admitted c.st.codes one.ranges (Wf.matrixOf one.lin)) one cs N sent c idx owed atEnd
    keysOk slots b

/-- The sub-protocol's accept, read back. -/
theorem batch_says (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat)
    (s s' : ChainState β) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') :
    ∃ (rows : List TensorRow) (t : List Nat × VerifiableInference.Desc.K13.St) (row : TensorRow)
      (msg : Array OracleNotice),
      layPile keysOf one s = .ok { s with pile := rows } ∧ s.atEnd = false ∧
      VerifiableInference.Desc.Ground.takeMasksP s.d s.idx (Batt.masksOf one.lin.kCol) = some t ∧
      rowSh row = claimSh one.lin.kCol (rows.map rowSh) (t.1.map fun i => ⟨s.idx, i⟩) ∧
      (∀ kRow len, (∀ r ∈ rows, ∀ v ∈ r.g, Low kRow len v) → ∀ v ∈ row.g, Low kRow len v) ∧
      linMessageW one.lin = some msg ∧
      s' = { s with pile := rows, atEnd := true, owed := none, msgW := msg
                    lin := some { claim := memberClaim row }, d := t.2 } := by
  unfold batchTableRows at h
  dsimp only at h
  rw [VerifiableInference.Desc.decide_andThen] at h
  obtain ⟨t₃, h3, hq⟩ := ebind_ok.1 h
  rw [VerifiableInference.Desc.decide_andThen] at h3
  obtain ⟨t₂, h2, hb⟩ := ebind_ok.1 h3
  rw [VerifiableInference.Desc.decide_andThen] at h2
  obtain ⟨t₁, h1, hf⟩ := ebind_ok.1 h2
  have h1' : layPile keysOf one s = .ok t₁ := h1
  obtain ⟨rows, rfl⟩ := VerifiableInference.Desc.Key.layPile_says keysOf one s t₁ h1'
  obtain ⟨p, he, _, _⟩ := VerifiableInference.Desc.K13.Law.frontB_fit batchLens _ hf
  obtain ⟨hend, rfl⟩ := (VerifiableInference.Desc.Key.lens_enter _ _).1 he
  obtain ⟨p₂, out, hp₂, hbt, rfl⟩ := VerifiableInference.Desc.K13.Law.battB_ok batchLens _ hb
  obtain ⟨_, rfl⟩ := (VerifiableInference.Desc.Key.lens_get _ _).1 hp₂
  simp only [VerifiableInference.Desc.K13.quietB, VerifiableInference.Desc.K13.still,
    VerifiableInference.Desc.K13.Law.quiet_is, VerifiableInference.Desc.K13.Law.bind_ok,
    VerifiableInference.Desc.K13.Law.there_ok, VerifiableInference.Desc.K13.Law.need_ok,
    VerifiableInference.Desc.K13.Law.pure_ok, VerifiableInference.Desc.K13.Lens.part] at hq
  obtain ⟨p₃, hp₃, _, _, msg, ⟨_, _, hmsg⟩, rfl⟩ := hq
  obtain ⟨_, rfl⟩ := (VerifiableInference.Desc.Key.lens_get _ _).1 hp₃
  obtain ⟨r, rs', x, t, hd, o, _, _, hfit, _, _, ht, _, hrun, _, rfl⟩ :=
    VerifiableInference.Desc.K13.Law.batt_ok hbt
  exact ⟨rows, t, Batt.rowOf rows o, msg, h1', hend, ht,
    VerifiableInference.Desc.K13.Honest.rowSh_rowOf hfit hrun,
    fun _ _ hl => rowOf_low rows o hl, hmsg, rfl⟩

/-- **(B1)**: where the sub-protocol accepts and the guards return, they return the core's shape and
the back part behind. -/
theorem batch_carries (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (cs : Codes) (N : Pieces)
    (sent : Nat) (s s' : ChainState β) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') (k : Bool)
    (y : CoreSh × BackSh)
    (hg : gBatch one cs N sent (shD s.d) s.idx s.owed s.atEnd k (keysSlots (keysOf s.base))
      (backSh one.lin cs s) = .ok y) :
    y = (shD s'.d, backSh one.lin cs s') ∧ ∃ rows msg l d, s' =
      { s with pile := rows, atEnd := true, owed := none, msgW := msg, lin := some l, d := d } := by
  obtain ⟨rows, t, row, msg, h1, -, ht, hrow, hlow, hmsg, rfl⟩ :=
    batch_says keysOf one N sent s s' rs gs h
  refine ⟨?_, _, _, _, _, rfl⟩
  unfold gBatch gBatchA at hg
  obtain ⟨b₁, hb₁, hg⟩ := ok_of_bind hg
  obtain ⟨_, _, hg⟩ := ok_of_bind hg
  obtain ⟨_, _, hg⟩ := ok_of_bind hg
  obtain ⟨_, hbd, hg⟩ := ok_of_bind hg
  obtain ⟨x, hx, hg⟩ := ok_of_bind hg
  obtain ⟨msg', hm', hg⟩ := ok_of_bind hg
  obtain rfl := Except.ok.inj hg
  obtain ⟨-, -, -, -, ha, -⟩ := gPile_spec hb₁
  obtain ⟨rfl, -⟩ := pile_carries keysOf one cs s _ h1 k b₁ hb₁
  obtain rfl : (t.1, shD t.2) = x :=
    Option.some.inj ((takeMasks_carries s.d t.2 s.idx _ t.1 ht).symm.trans (some_of_named hx))
  obtain rfl : msg = msg' := Option.some.inj (hmsg.symm.trans (some_of_named hm'))
  have hbd' := true_of_need hbd
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hbd'
  have hw : weightsB one.lin (linLayOmega cs one.lin) row.g = true :=
    weightsB_of_low one.lin _ _
      (hlow _ _ (layPile_low_admitted keysOf one s _ h1 _ ha)) hbd'.1 hbd'.2
  refine Prod.ext rfl ?_
  show BackSh.mk (rows.map rowSh) (pileB one.lin rows) msg.toList s.ids.toList
      (some ⟨noId, noId, noId, none, claimOfRow (claimSh one.lin.kCol (rows.map rowSh) _)⟩) true =
    BackSh.mk (rows.map rowSh) (pileB one.lin rows) msg.toList s.ids.toList
      (some ⟨noId, noId, noId, none, claimSh4 (memberClaim row)⟩)
      (weightsB one.lin (linLayOmega cs one.lin) row.g)
  rw [hw, claimSh4_member, hrow]

/-- The mark on the statement is kept: the library's `batt_keeps` at `groundQuiet_tidy`. -/
theorem batch_tidy (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat)
    (s s' : ChainState β) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s')
    (hT : stTidyB s.d.st = true) : stTidyB s'.d.st = true := by
  obtain ⟨rows, out, msg, rs', -, -, hb, rfl⟩ :=
    VerifiableInference.Desc.Key.seat_says keysOf one N sent s s' rs gs h
  exact tidy_mark (VerifiableInference.Desc.K13.batt_keeps
    VerifiableInference.Desc.Ground.groundQuiet_tidy _ _ _ _ _ _ _ out hb (tidy_of hT))

/-- **(B2)**: the guards return, the rounds fit the declared ones, the one named test on values
passes: the decision returns. -/
theorem batch_returns (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (cs : Codes) (N : Pieces)
    (sent : Nat) (s : ChainState β) (y : CoreSh × BackSh)
    (hg : gBatch one cs N sent (shD s.d) s.idx s.owed s.atEnd
      (keysB (Wf.matrixOf one.lin) one.ranges.lookups (keysOf s.base))
      (keysSlots (keysOf s.base)) (backSh one.lin cs s) = .ok y)
    (hv : keysSumB (Wf.matrixOf one.lin) one.ranges.lookups (keysOf s.base) = true)
    (rs : List Fmt.RoundView) (hr : roundsFit (battRounds (batchWhere one N sent)) rs = true)
    (gs : List (List (Nat × List UInt64))) :
    ∃ s', (batchTableRows (Cl := Cl) keysOf one N sent).decide s (rs.map noDigest) gs = .ok s' := by
  unfold gBatch gBatchA at hg
  obtain ⟨b₁, hb₁, hg⟩ := ok_of_bind hg
  obtain ⟨_, hend, hg⟩ := ok_of_bind hg
  obtain ⟨_, hready, hg⟩ := ok_of_bind hg
  obtain ⟨s₁, h1⟩ := pile_returns keysOf one cs s b₁ hb₁ hv
  obtain ⟨rfl, rows, rfl⟩ := pile_carries keysOf one cs s s₁ h1 _ b₁ hb₁
  have hend' : s.atEnd = false := by
    have := true_of_need hend
    cases e : s.atEnd with
    | false => rfl
    | true => rw [e] at this; cases this
  have hre : readySh (batchWhere one N sent)
      (partSh3 (partAt { s with pile := rows, atEnd := true })) = true := by
    rw [sh3_eq one.lin cs]
    exact true_of_need hready
  have key : ∀ (R : List Fmt.RoundView), R = rs.map noDigest → ∀ (r0 r2 : List Fmt.RoundView)
      (g0 g1 g2 : List (List (Nat × List UInt64))), ∃ s',
      (((VerifiableInference.Desc.K13.frontB (Cl := Cl) batchLens (batchWhere one N sent)).decide
          { s with pile := rows } r0 g0).bind fun a =>
        (VerifiableInference.Desc.K13.claimCombinationBlock (Cl := Cl) batchLens (batchWhere one N sent)).decide a
          R g1).bind (fun a =>
        (VerifiableInference.Desc.K13.quietB (Cl := Cl) batchLens (batchWhere one N sent)).decide a
          r2 g2) = .ok s' := by
    intro R hR r0 r2 g0 g1 g2
    subst hR
    obtain ⟨p₁, p₂, row, hrun, -⟩ := VerifiableInference.Desc.K13.Honest.m3_returns_at (Cl := Cl)
      batchLens (batchWhere one N sent)
      (fun t p p' hgt a b c d => VerifiableInference.Desc.Key.lens_get_set_same t p p' hgt a b c d)
      (t := { s with pile := rows }) (t₁ := { s with pile := rows, atEnd := true })
      ((VerifiableInference.Desc.Key.lens_enter _ _).2 ⟨hend', rfl⟩)
      ((VerifiableInference.Desc.Key.lens_get _ _).2 ⟨rfl, rfl⟩) hre rs hr r0 r2 g0 g1 g2
    exact ⟨_, hrun⟩
  have hlen : (rs.map noDigest).length = (battRounds (batchWhere one N sent)).length := by
    rw [List.length_map]
    exact VerifiableInference.Desc.K13.Law.roundsFit_length _ _ hr
  unfold batchTableRows
  dsimp only
  rw [VerifiableInference.Desc.decide_andThen, VerifiableInference.Desc.decide_andThen,
    VerifiableInference.Desc.decide_andThen]
  show ∃ s', ((((layPile keysOf one s).bind fun a => _).bind fun a => _).bind fun a => _) = .ok s'
  rw [h1]
  refine key _ ?_ _ _ _ _ _
  show ((rs.map noDigest).take (battRounds (batchWhere one N sent)).length).drop 0 = _
  rw [List.drop_zero, List.take_of_length_le (Nat.le_of_eq hlen)]

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.sh3_eq
#print axioms AtPublicFiles.AtFiles.claimSh4_member
#print axioms AtPublicFiles.AtFiles.batch_says
#print axioms AtPublicFiles.AtFiles.batch_carries
#print axioms AtPublicFiles.AtFiles.batch_tidy
#print axioms AtPublicFiles.AtFiles.batch_returns
