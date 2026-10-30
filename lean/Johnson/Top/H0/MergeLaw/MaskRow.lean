-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MaskRow.lean: the two readings of a segment's mask row are one; and the
merge's sentences read that row only where the two agree. Definitions and theorems with their
proofs.

Why. The law of the merge of the claims on the committed table reads the mask row of the head's
sub-proof off the witness at one member of the list of oracle messages (`vecBy`, Pin.lean). The
filling of the table of joints reads the same row as its sentences on linear forms do: through the
verifier's state: which oracle message holds the segment's mask rows, and where the state's book of
trees has it (`dataQ ... .mask`, Johnson/Desc/Sound/FormsQ.lean). "merged" comes out of the filling
in the second reading (`merged_at_table`, LateTie.lean); the law wants the first.

Main names:
  `entries_congr`, `mergedHere_congr`, `weightsHere_congr`: `MergedHere` and `WeightsHere`
    (Here.lean) read the mask row below the number of slots alone, and the index masks below their
    number alone.
  `posMask R`: the positions of a mask table's entries in the numbering in which the forms read
    them: entry j stands in row j % 2 ^ R at place j / 2 ^ R.
  `mask_readings`: THE EQUATION, below n: under four premises on the verifier's state's part and the
    list of members: the request's frame names the message o as the one that holds the segment's
    mask rows; the book gives o the member's place, among the segment's own; the first member of the
    list with that place is xM; R bits number the rows of o's mask table.
  `MaskAt`, `maskAtB`, `maskAt_of_test`: the three premises on the verifier's state, gathered; as a
    test with code; its yes gives them.
  `maskAt_behind`: the merge's accepting step leaves what `MaskAt` reads: so behind it the fact
    follows from the fact in front.
  `merged_at_member`: "merged" out of the table's own sentence on linear forms (`formsQ`), at the
    merge's reading of the mask row.
  `weights_at_forms`: "weights" at the merge's reading gives "weights" at the reading of the table's
    own forms.

Limits. `maskAtB` has been evaluated at no verifier's state; who makes it true along the chain is
not said. That xM is the first member of the list with its place is a closed fact on the list of
members, not shown. The two last theorems are in the form that the fields "merged" and "weights" of
`MergeFill` (TieThreeFour.lean) want at posM := `posMask R`; no filling is named here. Nothing on
soundness.
-/
import Johnson.Top.H0.MergeLaw.LateTie
import Johnson.Top.H0.MergeLaw.Pin
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.K9 (seatAt Readers RunOf)
open Johnson.Desc.First.ForkMerge (headMergeClaim)

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- The three readings as entries: they read the mask row below the number of slots alone, and the
index masks below their number alone. -/
theorem entries_congr {cell : ℕ → ℕ → GE} {mask mask' idx idx' : ℕ → GE}
    (hm : ∀ j, j < N.ns → mask j = mask' j) (hi : ∀ j, j < N.ni → idx j = idx' j) :
    K11Caller.entries N cell mask idx = K11Caller.entries N cell mask' idx' := by
  funext x
  rcases x with rc | j | j
  · rfl
  · exact hm j.val j.isLt
  · exact hi j.val j.isLt

/-- **"merged" reads the mask row below the number of slots alone.** -/
theorem mergedHere_congr {cell : ℕ → ℕ → GE} {mask mask' idx idx' : ℕ → GE} {s : S}
    (hm : ∀ j, j < N.ns → mask j = mask' j) (hi : ∀ j, j < N.ni → idx j = idx' j)
    (h : MergedHere N cell mask idx s) : MergedHere N cell mask' idx' s := by
  unfold MergedHere at h ⊢
  rw [← entries_congr N hm hi]
  exact h

/-- **"weights" reads the mask row at the slots of the claims' values alone.** -/
theorem weightsHere_congr {cell : ℕ → ℕ → GE} {mask mask' : ℕ → GE} {s : S}
    (hm : ∀ j, j < N.ns → mask j = mask' j) (h : WeightsHere N cell mask s) :
    WeightsHere N cell mask' s := by
  unfold WeightsHere K11Caller.WeightsSays at h ⊢
  intro a
  rw [← hm (N.sv a) (N.hsv a)]
  exact h a

section
variable (cs : OnBytes.Codes) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem)

/-- The positions of a mask table's entries, in the numbering in which the forms read them: entry j
stands in row j % 2 ^ R at place j / 2 ^ R. R: the bits that number the table's rows. -/
def posMask (R : ℕ) (j : ℕ) : Bool × ℕ × ℕ := (true, j % 2 ^ R, j / 2 ^ R)

/-- **THE TWO READINGS OF THE SEGMENT's MASK ROW ARE ONE, below n**: the reading of the table's own
forms (`dataQ ... .mask`, Johnson/Desc/Sound/FormsQ.lean) and the merge's (`vecBy`, Pin.lean), at
the member xM: where, in the verifier's state's part a9: the request's frame names the message o as
the one that holds the segment's mask rows; the book gives o the member's place, among the segment's
own; the first member of the list with that place is xM; and R bits number the rows of o's mask
table. -/
theorem mask_readings (own : List (ℕ × ℕ)) (a9 : K9.Part) (w : Wit Cells Tok MsgT) (xM : Mem)
    (o R n : ℕ) (ho : maskOracle a9.L.check.frame = some o)
    (hs : seatAt own a9.d.book o = some (seatOf xM))
    (hx : (ms.find? fun y => decide (seatOf y = seatOf xM)) = some xM)
    (hR : a9.d.st.rowBits o .mask = R) (j : ℕ) (hj : j < n) :
    (dataQ own a9 (seatTab cs arr ms w)).mask j = vecBy cs arr n (posMask R) xM w j := by
  unfold vecBy vecOf posMask
  rw [if_pos hj]
  show (match maskOracle a9.L.check.frame with
    | some o => tabQ own a9.d.st a9.d.book (seatTab cs arr ms w) o .mask j
    | none => 0) = _
  rw [ho]
  show tabQ own a9.d.st a9.d.book (seatTab cs arr ms w) o .mask j = _
  unfold tabQ
  rw [hs, hR]
  show seatTab cs arr ms w (seatOf xM) _ _ _ = _
  unfold seatTab
  rw [hx]
  rfl

/-- **What the equation asks of a verifier's state**, gathered: an open segment's part is there; its
request's frame names the message o as the one that holds the segment's mask rows; its book of trees
gives o the member's place, among the segment's own; R bits number the rows of o's mask table. -/
def MaskAt (own : List (ℕ × ℕ)) (xM : Mem) (R : ℕ) (s : S) : Prop :=
  ∃ a9 o, K9.segAt? s = some a9 ∧ maskOracle a9.L.check.frame = some o ∧
    seatAt own a9.d.book o = some (seatOf xM) ∧ a9.d.st.rowBits o .mask = R

/-- **The same as a test with code on the verifier's state.** x: the member's place. -/
def maskAtB (own : List (ℕ × ℕ)) (x : ℕ × ℕ) (R : ℕ) (s : S) : Bool :=
  (K9.segAt? s).any fun a9 => (maskOracle a9.L.check.frame).any fun o =>
    seatAt own a9.d.book o == some x && a9.d.st.rowBits o .mask == R

theorem maskAt_of_test {own : List (ℕ × ℕ)} {xM : Mem} {R : ℕ} {s : S}
    (h : maskAtB own (seatOf xM) R s = true) : MaskAt own xM R s := by
  unfold maskAtB at h
  cases e9 : K9.segAt? s with
  | none => simp [e9] at h
  | some a9 =>
    rw [e9] at h
    simp only [Option.any_some] at h
    cases eo : maskOracle a9.L.check.frame with
    | none => simp [eo] at h
    | some o =>
      rw [eo] at h
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨a9, o, e9, eo, h.1, h.2⟩

open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide) in
/-- **The merge's accepting step leaves what `MaskAt` reads**: the open segment's context, the
statement and the book of trees. -/
theorem maskAt_behind (P : HeadMergeP) {own : List (ℕ × ℕ)} {xM : Mem} {R : ℕ} {s s' : S}
    {rs : List Fmt.RoundView} (h : headMergeDecide P s rs = .ok s') (hM : MaskAt own xM R s) :
    MaskAt own xM R s' := by
  obtain ⟨a, a', ha, ha', e, ea, _⟩ := isLocal P s rs s' h
  obtain ⟨a9, o, e9, ho, hs, hR⟩ := hM
  unfold K9.segAt? at e9
  simp only [Option.bind_eq_bind, Option.pure_def] at e9
  obtain ⟨L, hL, e9⟩ := Option.bind_eq_some_iff.1 e9
  obtain ⟨F, hF, e9⟩ := Option.bind_eq_some_iff.1 e9
  obtain ⟨tl, htl, e9⟩ := Option.bind_eq_some_iff.1 e9
  obtain rfl := Option.some.inj e9
  have hop : a.opened = true := by
    unfold S.link? at hL
    rw [ha] at hL
    by_contra hn
    simp [hn] at hL
  have hop' : a'.opened = true := by rw [ea]; exact hop
  have hL' : s'.link? = some L := by
    unfold S.link? at hL ⊢
    rw [ha] at hL
    rw [ha']
    simp only [hop, hop', if_true] at hL ⊢
    rw [ea]
    exact hL
  have htl' : s'.tl? = some tl := by
    unfold S.tl? at htl ⊢
    rw [ha] at htl
    rw [ha']
    simp only [hop, hop', if_true] at htl ⊢
    rw [ea]
    exact htl
  have hF' : s'.fork? = some a'.F := by
    unfold S.fork?
    rw [ha']
    simp only [hop', if_true]
  have hst : s'.st = s.st := by rw [e]
  have hbk : s'.book = s.book := by rw [e]
  let a9' : K9.Part :=
    { owed := K9.owedOf s'
      used := (K9.usedOf s').getD 0
      laid := K9.laidOf tl
      L := L
      F := a'.F
      d := { st := s'.st, book := s'.book, roots := s'.roots, opened := [], loc := () } }
  refine ⟨a9', o, ?_, ho, ?_, ?_⟩
  · unfold K9.segAt?
    simp only [Option.bind_eq_bind, Option.pure_def, hL', hF', htl', Option.bind_some]
    rfl
  · show seatAt own s'.book o = _
    rw [hbk]
    exact hs
  · show s'.st.rowBits o .mask = R
    rw [hst]
    exact hR

/-- **"merged" out of the table's own sentence on linear forms, AT THE MERGE's READING of the mask
row.** -/
theorem merged_at_member (states : ℕ → List (RunOf S)) (own : List (ℕ × ℕ)) (piece : ℕ)
    (run name : String)
    (hst : ((states piece).find? fun r => r.1 == run) = some (name, headMergeClaim))
    {s : S} (hb : BehindOk N s) (w : Wit Cells Tok MsgT) (cell : ℕ → ℕ → GE) (idx : ℕ → GE)
    (xM : Mem) (R : ℕ) (hM : MaskAt own xM R s)
    (hx : (ms.find? fun y => decide (seatOf y = seatOf xM)) = some xM)
    (h : formsQ (Readers.ofStates states) own piece run s (seatTab cs arr ms w)) :
    MergedHere N cell (vecBy cs arr N.ns (posMask R) xM w) idx s := by
  obtain ⟨a9, e9, hm⟩ := merged_at_table N states own piece run name hst hb _ cell idx h
  obtain ⟨a9', o, e9', ho, hs, hR⟩ := hM
  obtain rfl : a9 = a9' := Option.some.inj (e9.symm.trans e9')
  exact mergedHere_congr N
    (fun j hj => mask_readings cs arr ms own a9 w xM o R N.ns ho hs hx hR j hj) (fun _ _ => rfl) hm

/-- **"weights" at the merge's reading gives "weights" at the reading of the table's own forms.**
mask: any reading that is the forms' at the open segment's part. -/
theorem weights_at_forms (own : List (ℕ × ℕ)) {s : S} (w : Wit Cells Tok MsgT)
    (cell : ℕ → ℕ → GE) (xM : Mem) (R : ℕ) (hM : MaskAt own xM R s)
    (hx : (ms.find? fun y => decide (seatOf y = seatOf xM)) = some xM) (mask : ℕ → GE)
    (hmask : ∀ a9, K9.segAt? s = some a9 →
      ∀ j, mask j = (dataQ own a9 (seatTab cs arr ms w)).mask j)
    (h : WeightsHere N cell (vecBy cs arr N.ns (posMask R) xM w) s) :
    WeightsHere N cell mask s := by
  obtain ⟨a9, o, e9, ho, hs, hR⟩ := hM
  exact weightsHere_congr N (fun j hj => by
    rw [hmask a9 e9 j, mask_readings cs arr ms own a9 w xM o R N.ns ho hs hx hR j hj]) h

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.maskAt_behind
#print axioms VerifiableInference.Desc.First.MergeLaw.maskAt_of_test
#print axioms VerifiableInference.Desc.First.MergeLaw.merged_at_member
#print axioms VerifiableInference.Desc.First.MergeLaw.weights_at_forms
#print axioms VerifiableInference.Desc.First.MergeLaw.mask_readings
#print axioms VerifiableInference.Desc.First.MergeLaw.mergedHere_congr
#print axioms VerifiableInference.Desc.First.MergeLaw.weightsHere_congr
