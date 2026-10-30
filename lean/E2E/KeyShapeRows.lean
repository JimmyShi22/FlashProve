-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeRows.lean: THE LAST STEP OF "w.1.send", THE KIND K13's SUB-PROTOCOL BEHIND W's
COMMITMENT (the own group and the row (Eval)), AT THE KEY FILE's FIRST CHAIN, ON THE ONE SHAPE OF
STATEMENT, BOOK AND ROOTS (Johnson/Desc/Ground/Shape/) AND THE CHAIN's BACK PART
(E2E/KeyShapeBack.lean): BOTH DIRECTIONS of Johnson/Desc/ProofFile/Honest/Thread/Shape.lean's cut.
Definitions, statements and proofs. A step of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

The step's text (`K13.rows`) is calls of the ground's functions in a row: a new group · the messages
of the claim's masks join it · W joins · the split's message, where one is needed · the row (Eval)
is added. On shapes these are Ground.lean's and More.lean's.

  `joinAllS`, `joinAll_carries`: messages join a group, one behind the other.
  **`rowsS`**: the step's text on the core's shape, the numbers sent with W and the claim's shape.
  **`rows_carries`**: where the text returns, `rowsS` returns what is laid, by its shape, and the
    core's shape behind.
  **`gRows`**: the sub-protocol on the core's shape and the back part.
  **`rowsB_carries`**: (B1) at the key file's lens; of the chain's other named values one may turn:
    a count of 0 rows that waits becomes none.
  `rowsB_tidy`: the mark on the statement is kept.
  `viewSt`, `viewSt_eq`, `sh4At`, `sh4At_eq`: the kind K13's own shape of the state, read off ours.
  **`readyS`**: the kind's two tests on its own shape, read off ours. **`rowsB_returns`**: (B2) at
    the key file's lens: Johnson/Desc/K13/Honest/PartM4Key.lean's `rowsB_returns_key`: CALLED. No
    test on values.

Limits.
- `gRows` does not ask `readyS`: whoever seats the step asks both. That `gRows` returns wherever
  `readyS` passes, or the other way round, is not shown.
- The three steps in front of it in "w.1.send" (what is announced; W's sending; the numbers sent)
  are not here.
- The file that is called for (B2), Johnson/Desc/K13/Honest/PartM4Key.lean, is not reviewed.


-/
import E2E.KeyShapeBack
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.K13.Law.M4Proof
import Johnson.Desc.K13.Law.TextIs
import Johnson.Desc.Third.Law.Sharp
import Johnson.Desc.K13.Keeps
import Johnson.Desc.Tidy.Stay
import Johnson.Desc.Ground.Shape.Marks
import Johnson.Desc.K13.Honest.PartM4Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Ground (joinP)
open VerifiableInference.Desc.Key (ChainState batchLens)
open VerifiableInference.Desc.K13 (St Where)
open VerifiableInference.Desc.K13.Honest (LaidSh laidSh ClaimSh claimSh4)
open VerifiableInference.Desc.K13.Law (bind_ok there_ok pure_ok)

variable {β Cl : Type}

/-- Messages join a group, one behind the other: on the shape. -/
def joinAllS (g : Nat) : List Nat → CoreSh → Option CoreSh
  | [], c => some c
  | o :: l, c => (joinS c g o false).bind (joinAllS g l)

theorem joinAll_carries (g : Nat) : ∀ (l : List Nat) (d d' : St),
    VerifiableInference.Desc.K13.joinAll g l d = .ok d' → joinAllS g l (shD d) = some (shD d')
  | [], d, d', h => by
    obtain rfl : d = d' := Except.ok.inj h
    rfl
  | o :: l, d, d', h => by
    unfold VerifiableInference.Desc.K13.joinAll at h
    simp only [bind_ok, there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    show (joinS (shD d) g o false).bind (joinAllS g l) = _
    rw [join_carries d d₁ g o false h1]
    exact joinAll_carries g l d₁ d' h2

/-- **The step's text on shapes.** ids: the numbers sent with W; cl: the claim's shape. -/
def rowsS (S : LinShape) (c : CoreSh) (ids : List Nat) (cl : ClaimSh) :
    Option (LaidSh × CoreSh) :=
  (ids[0]?).bind fun w =>
  (newGroupS c S.w.code S.ownMaskCode).bind fun b =>
  (joinAllS b.1 (listOfT (cl.slots.map (·.1))) b.2).bind fun c₁ =>
  (joinS c₁ b.1 w false).bind fun c₂ =>
  (if S.ownSplitNeeded then ids[1]? else some noId).bind fun split =>
  (if S.ownSplitNeeded then joinS c₂ b.1 split false else some c₂).bind fun c₃ =>
  (if S.masksAhead then ids.getLast?.map some else some none).bind fun mask =>
  (addRowsS c₃ b.1 [.plain]).map fun c₄ => (⟨w, split, b.1, mask, cl⟩, c₄)

/-- **Where the text returns, so does its text on shapes: with what is laid, by its shape, and the
core's shape behind.** -/
theorem rows_carries (S : LinShape) (claim : LinClaim) (ids : Array Nat) (d : St)
    (o : LinFirst × St) (h : VerifiableInference.Desc.K13.rows S claim ids d = .ok o) :
    rowsS S (shD d) ids.toList (claimSh4 claim) = some (laidSh o.1, shD o.2) := by
  simp only [VerifiableInference.Desc.K13.Law.rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, hw, b, hb, d₁, h1, d₂, h2, split, hsp, d₃, h3, mask, hmk, row, hr, d₄, h4, rfl⟩ := h
  have e0 : ids.toList[0]? = some w := by rw [Array.getElem?_toList]; exact hw
  have e1 := newGroup_carries d b.2 S.w.code S.ownMaskCode b.1 hb
  have e2 : joinAllS b.1 (listOfT ((claimSh4 claim).slots.map (·.1))) (shD b.2) =
      some (shD d₁) := by
    have : (claimSh4 claim).slots.map (·.1) = claim.masks.toList.map (·.oracle) := by
      unfold claimSh4
      rw [List.map_map]
      rfl
    rw [this]
    exact joinAll_carries _ _ _ _ h1
  have e3 := join_carries d₁ d₂ b.1 w false h2
  have e4 : (if S.ownSplitNeeded then ids.toList[1]? else some noId) = some split := by
    rw [Array.getElem?_toList]
    exact hsp
  have e5 : (if S.ownSplitNeeded then joinS (shD d₂) b.1 split false else some (shD d₂)) =
      some (shD d₃) := by
    split at h3
    · rename_i c
      rw [if_pos c]
      exact join_carries d₂ d₃ b.1 split false h3
    · rename_i c
      rw [if_neg c, Option.some.inj h3]
  have e6 : (if S.masksAhead then ids.toList.getLast?.map some else some none) = some mask := by
    have eb : ids.toList.getLast? = ids.back? := by simp
    rw [eb]
    exact hmk
  have hk : row.kind = .plain := by
    obtain ⟨-, rfl⟩ := Slice.linEvalRow_inv S claim w _ row hr
    exact VerifiableInference.Desc.Third.Law.addLaid_kind _ _ _ _
  have e7 : addRowsS (shD d₃) b.1 [.plain] = some (shD d₄) := by
    have := addRows_carries d₃ d₄ b.1 [row] h4
    rwa [List.map_cons, List.map_nil, hk] at this
  unfold rowsS
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, Option.bind_some, Option.map_some]
  rfl

/-- **The sub-protocol on the shape.** -/
def gRows (S : LinShape) (c : CoreSh) (b : BackSh) : Except String (CoreSh × BackSh) :=
  match b.lin with
  | none => .error "K13: no claim is laid"
  | some l =>
    match rowsS S c b.ids l.claim with
    | some x => .ok (x.2, { b with lin := some x.1 })
    | none => .error "K13: the own group and the row (Eval): a guard on the shape"

/-- **(B1), at the key file's lens.** -/
theorem rowsB_carries (P : Where) (cs : Codes) (s s' : ChainState β) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K13.rowsB (Cl := Cl) batchLens P).decide s rs gs = .ok s')
    (y : CoreSh × BackSh) (hg : gRows P.lin (shD s.d) (backSh P.lin cs s) = .ok y) :
    y = (shD s'.d, backSh P.lin cs s') ∧
      ∃ l d, s' = { s with owed := s.debt, lin := some l, d := d } := by
  obtain ⟨p, l, o, hp, hl, ho, rfl⟩ := VerifiableInference.Desc.K13.Law.rowsB_ok _ _ h
  obtain ⟨-, rfl⟩ := (VerifiableInference.Desc.Key.lens_get _ _).1 hp
  have hl' : s.lin = some l := hl
  rw [VerifiableInference.Desc.Key.lens_set]
  refine ⟨?_, _, _, rfl⟩
  have c := rows_carries P.lin l.claim s.ids s.d o ho
  obtain ⟨-, -, -, hcl, -⟩ := VerifiableInference.Desc.K13.Law.rows_ok ho
  unfold gRows at hg
  have hbl : (backSh P.lin cs s).lin = some (laidSh l) := by
    unfold backSh backOf
    rw [hl']
    rfl
  rw [hbl] at hg
  have c' : rowsS P.lin (shD s.d) (backSh P.lin cs s).ids (laidSh l).claim =
      some (laidSh o.1, shD o.2) := c
  simp only [c'] at hg
  obtain rfl := Except.ok.inj hg
  refine Prod.ext rfl ?_
  show BackSh.mk _ _ _ _ (some (laidSh o.1))
      (s.lin.all fun l => weightsB P.lin (linLayOmega cs P.lin) l.claim.g) =
    BackSh.mk _ _ _ _ (some (laidSh o.1))
      (weightsB P.lin (linLayOmega cs P.lin) o.1.claim.g)
  rw [hl', hcl]
  rfl

/-- The mark on the statement is kept: the library's `rows_keeps` at `groundQuiet_tidy`. -/
theorem rowsB_tidy (P : Where) (s s' : ChainState β) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K13.rowsB (Cl := Cl) batchLens P).decide s rs gs = .ok s')
    (hT : stTidyB s.d.st = true) : stTidyB s'.d.st = true := by
  obtain ⟨p, l, o, hp, hl, ho, rfl⟩ := VerifiableInference.Desc.K13.Law.rowsB_ok _ _ h
  obtain ⟨-, rfl⟩ := (VerifiableInference.Desc.Key.lens_get _ _).1 hp
  rw [VerifiableInference.Desc.Key.lens_set]
  exact tidy_mark (VerifiableInference.Desc.K13.rows_keeps
    VerifiableInference.Desc.Ground.groundQuiet_tidy _ _ _ _ o ho (tidy_of hT))

/-! ## (B2): by the kind's own shape -/

/-- The statement's shape, read as the kind K13's own shape of a statement. -/
def viewSt (a : StSh) : VerifiableInference.Desc.K13.Honest.StSh :=
  ⟨a.codes, (a.oracles.map fun o => ⟨o.shape, o.sampled, o.groups, o.pad⟩).toArray,
    (a.groups.map fun G =>
      ⟨G.code, G.maskCode, G.members.toArray, G.kept.toArray, G.kinds.length, G.inRun⟩).toArray⟩

theorem viewSt_eq (T : Statement) :
    viewSt (stSh T) = VerifiableInference.Desc.K13.Honest.stSh T := by
  have e1 : ((T.oracles.toList.map orcSh).map fun o =>
      (⟨o.shape, o.sampled, o.groups, o.pad⟩ : VerifiableInference.Desc.K13.Honest.Msg4)).toArray =
      T.oracles.map VerifiableInference.Desc.K13.Honest.msg4 := by
    apply Array.toList_inj.1
    rw [List.map_map, Array.toList_map]
    rfl
  have e2 : ((T.groups.toList.map grpSh).map fun G =>
      (⟨G.code, G.maskCode, G.members.toArray, G.kept.toArray, G.kinds.length, G.inRun⟩ :
        VerifiableInference.Desc.K13.Honest.GrpSh)).toArray =
      T.groups.map VerifiableInference.Desc.K13.Honest.grpSh := by
    apply Array.toList_inj.1
    rw [List.map_map, Array.toList_map]
    refine List.map_congr_left fun G _ => ?_
    show (⟨G.code, G.maskCode, G.members.toList.toArray, G.kept.toList.toArray,
      (G.rows.toList.map (·.kind)).length, G.inRun⟩ : VerifiableInference.Desc.K13.Honest.GrpSh) =
      ⟨G.code, G.maskCode, G.members, G.kept, G.rows.size, G.inRun⟩
    rw [List.length_map, Array.length_toList]
  exact congrArg₂ (fun m g => (⟨T.codes, m, g⟩ : VerifiableInference.Desc.K13.Honest.StSh)) e1 e2

/-- The kind's own shape of the state, read off the core's shape, the count that is owed and the
back part. -/
def sh4At (c : CoreSh) (owed : Option Nat) (b : BackSh) : VerifiableInference.Desc.K13.Honest.Sh4 :=
  ⟨true, b.ids.toArray, b.lin, owed, viewSt c.st⟩

theorem sh4At_eq (S : LinShape) (cs : Codes) (s : ChainState β) :
    sh4At (shD s.d) s.debt (backSh S cs s) =
      VerifiableInference.Desc.K13.Honest.partSh4
        (VerifiableInference.Desc.K13.Honest.batchPart s) := by
  show (⟨true, s.ids.toList.toArray, s.lin.map laidSh, s.debt, viewSt (stSh s.d.st)⟩ :
    VerifiableInference.Desc.K13.Honest.Sh4) = ⟨true, s.ids, s.lin.map laidSh, s.debt, _⟩
  rw [viewSt_eq]
  rfl

/-- **The kind's two tests on its own shape** (twelve clauses; two on pads), read off ours. -/
def readyS (S : LinShape) (c : CoreSh) (owed : Option Nat) (b : BackSh) : Bool :=
  VerifiableInference.Desc.K13.Honest.ready4 S (sh4At c owed b) &&
    VerifiableInference.Desc.K13.Honest.pads4 S (sh4At c owed b)

/-- **(B2) at the key file's lens**: the chain stands at its end and the two tests pass: the
sub-protocol's decision returns: Johnson/Desc/K13/Honest/PartM4Key.lean's `rowsB_returns_key`. -/
theorem rowsB_returns (P : Where) (cs : Codes) (s : ChainState β) (he : s.atEnd = true)
    (h : readyS P.lin (shD s.d) s.debt (backSh P.lin cs s) = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∃ s', (VerifiableInference.Desc.K13.rowsB (Cl := Cl) batchLens P).decide s rs gs = .ok s' := by
  unfold readyS at h
  rw [sh4At_eq, Bool.and_eq_true] at h
  obtain ⟨p', e, -⟩ :=
    VerifiableInference.Desc.K13.Honest.rowsB_returns_key (Cl := Cl) P he h.1 h.2 rs gs
  exact ⟨_, e⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.joinAll_carries
#print axioms AtPublicFiles.AtFiles.rows_carries
#print axioms AtPublicFiles.AtFiles.rowsB_carries
#print axioms AtPublicFiles.AtFiles.rowsB_tidy
#print axioms AtPublicFiles.AtFiles.viewSt_eq
#print axioms AtPublicFiles.AtFiles.sh4At_eq
#print axioms AtPublicFiles.AtFiles.rowsB_returns
