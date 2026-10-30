-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/Shape.lean: kind K13, the members' batching: THE SHAPE OF THE VERIFIER's
STATE THAT THE JOINED SUB-PROTOCOL's TESTS READ (`atM3`, Johnson/Desc/K13/AtS.lean): a projection of
the first chain's state onto flags, counts, lengths, numbers of oracle messages and of mask entries,
ledgers, shapes of oracle messages and codes: NO ELEMENT OF A FIELD, BY TYPE. And: the sub-protocol
accepts any elements in rounds of the kind's form WHEREVER A TEST WITH CODE ON THAT SHAPE ACCEPTS.
Definitions with code, and statements with their proofs. Local to this kind: no shape for all kinds
is defined here.
The types `RowSh`, `MsgSh`, `Sh` and the projection `rowSh` lie in ShapeDefs.lean of this folder,
which imports the library alone; the projection `shOf` lies here.
Main names:
  `RowSh`, `rowSh` (ShapeDefs.lean): of a row: two marks on its weights (it has none; each has v
    variables), NOT HOW MANY THERE ARE; how many coordinates its column point has; the slots that
    its mask form names. Not a coefficient, not a coordinate, not the target.
  `all_eq_mark`, `all_head_mark`, `head_of_mark`, `not_all_head`: what the library's two tests on a
    row's weights say, by the marks.
  `MsgSh`, `Sh` (ShapeDefs.lean), `shOf`: of an oracle message: its shape and its ledger; the
    state's shape.
  `fitSh`, `formSh`, `roomSh`, `readySh`: the nine tests, on the shape.
  `fitSh_eq`, `formSh_eq`: two of them are the library's tests on the state. `roomSh_eq`: a third is
    `leftAtC` (Room.lean of this folder), from which the verifier's taking of mask entries returns.
  `ready_of_shape`: where `readySh` accepts, the nine premises of `atM3_accepts_any` hold.
  `atM3_accepts_shape`: **so the decision returns, at any elements.**

What is not claimed. The converse: that the test accepts wherever the decision returns. What the
shape behind the sub-protocol is: no step of the shape is written here. That the shape at a state of
a run hangs on no sent value and on no coin: the type shuts out field elements; that a count or a
slot is not made of one along a run is a statement on every sub-protocol in front. Nothing on
soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.ShapeDefs
import Johnson.Desc.K13.Honest.AcceptsAny
import Johnson.Desc.K13.Honest.Ready
import Johnson.Desc.K13.Honest.Room
import Johnson.Desc.K13.Law.AtM3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

/-- "Each member is k", by the mark. -/
theorem all_eq_mark (k : Nat) : ∀ l : List Nat,
    l.all (· == k) = (l.isEmpty || varsMark l == some k)
  | [] => rfl
  | v :: t => by
    show (v == k && t.all (· == k)) = (false || (if t.all (· == v) then some v else none) == some k)
    by_cases hv : v = k
    · subst hv
      cases t.all (· == v) <;> simp
    · have e1 : (v == k) = false := beq_false_of_ne hv
      rw [e1]
      cases t.all (· == v) <;> simp [hv]

/-- "The list is not empty and each member is h", by the mark. -/
theorem all_head_mark (h : Nat) (l : List Nat) :
    (!l.isEmpty && l.all fun v => some v == some h) = (varsMark l == some h) := by
  have e : (l.all fun v => some v == some h) = l.all (· == h) :=
    List.all_congr rfl fun v => by simp
  rw [e, all_eq_mark]
  cases l with
  | nil => rfl
  | cons v t => rfl

/-- Where the mark is some h, the list's first member is h. -/
theorem head_of_mark {l : List Nat} {h : Nat} (e : varsMark l = some h) : l.head? = some h := by
  cases l with
  | nil => cases e
  | cons v t =>
    have e' : (if t.all (· == v) then some v else none) = some h := e
    split at e'
    · exact e'
    · cases e'

/-- Where the mark is none, "not empty, and each member is the first" fails. -/
theorem not_all_head {l : List Nat} (e : varsMark l = none) :
    (!l.isEmpty && l.all fun v => some v == l.head?) = false := by
  cases l with
  | nil => rfl
  | cons v t =>
    have h2 := all_head_mark v (v :: t)
    have h3 : varsMark (v :: t) = none := e
    rw [h3] at h2
    exact h2

/-- **The state's shape.** -/
def shOf (s : S) : Sh :=
  ⟨atFinC s, s.out.reply.isSome, s.noneWaits, s.out.indexMasks, s.out.pending.map rowSh, s.st.codes,
    s.st.oracles.map fun x => ⟨x.shape, x.ledger⟩⟩

/-- The pile and the index masks' message have the form that the table's shape asks. -/
def fitSh (L : LinShape) (h : Sh) : Bool :=
  match h.msgs[h.index]? with
  | none => false
  | some x =>
    x.shape.mainRows == 0 && decide (0 < x.shape.maskRows) && decide (0 < x.shape.answers) &&
    x.shape.maskCode == L.ownMaskCode &&
    !h.pile.isEmpty && decide (0 < L.kCol) &&
    h.pile.all fun r =>
      (r.slots.all fun m => m.oracle == h.index) && r.point == L.kCol &&
        (r.bare || r.vars == some L.kRow)

/-- The pile has a form that the batching allows. -/
def formSh (kCol : Nat) (pile : List RowSh) : Bool :=
  match pile with
  | [] => false
  | r :: _ =>
    decide (1 ≤ kCol) &&
    pile.all fun s =>
      s.point == kCol && !s.bare && (s.vars.isSome && s.vars == r.vars)

/-- The index masks' message has an open ledger with n entries left. -/
def roomSh (h : Sh) (n : Nat) : Bool :=
  match (h.msgs[h.index]?).bind (·.ledger) with
  | some l => !l.closed && decide (n ≤ l.left)
  | none => false

/-- **The nine tests, on the shape.** -/
def readySh (P : Where) (h : Sh) : Bool :=
  h.atFin && (!P.reply || h.reply) && h.pile.length == P.rows && fitSh P.lin h && h.quiet &&
    formSh P.lin.kCol h.pile && roomSh h (Batt.masksOf P.lin.kCol) && linOk h.codes P.lin &&
    (linMessageW P.lin).isSome

/-- At a state's shape that test is the library's `memberRowsFit` at the state. -/
theorem fitSh_eq (L : LinShape) (s : S) :
    fitSh L (shOf s) = memberRowsFit s.st L s.out.indexMasks s.out.pending := by
  unfold fitSh memberRowsFit shOf
  simp only [Array.getElem?_map]
  cases s.st.oracles[s.out.indexMasks]? with
  | none => rfl
  | some x =>
    simp only [Option.map_some, List.isEmpty_map, List.all_map, Function.comp_def, rowSh]
    have e : ∀ r : TensorRow, (r.g.isEmpty || varsMark (r.g.map Tensor.vars) == some L.kRow) =
        r.g.all (·.vars == L.kRow) := fun r => by
      rw [← List.isEmpty_map (f := Tensor.vars), ← all_eq_mark, List.all_map]
      rfl
    simp only [e]

/-- At a pile's rows' shapes that test is the library's `Batt.fits` at the pile. -/
theorem formSh_eq (kCol : Nat) (pile : List TensorRow) :
    formSh kCol (pile.map rowSh) = Batt.fits kCol pile := by
  cases pile with
  | nil => rfl
  | cons r l =>
    have row : ∀ (h : Nat) (s : TensorRow), r.g.head?.map Tensor.vars = some h →
        (!s.g.isEmpty && s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) =
          (varsMark (s.g.map Tensor.vars) == some h) := fun h s eh => by
      rw [eh, ← all_head_mark, List.isEmpty_map, List.all_map]
      rfl
    show (decide (1 ≤ kCol) && ((r :: l).map rowSh).all fun s =>
        s.point == kCol && !s.bare && (s.vars.isSome && s.vars == (rowSh r).vars)) =
      (decide (1 ≤ kCol) && (r :: l).all fun s =>
        s.psi.length == kCol && !s.g.isEmpty &&
          s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars)
    congr 1
    rw [List.all_map]
    cases hm : varsMark (r.g.map Tensor.vars) with
    | some h =>
      have eh : r.g.head?.map Tensor.vars = some h := by
        rw [← List.head?_map]
        exact head_of_mark hm
      refine List.all_congr rfl fun s => ?_
      show (s.psi.length == kCol && !s.g.isEmpty &&
          ((varsMark (s.g.map Tensor.vars)).isSome &&
            varsMark (s.g.map Tensor.vars) == varsMark (r.g.map Tensor.vars))) = _
      rw [Bool.and_assoc, Bool.and_assoc, row h s eh, hm]
      congr 1
      cases hs : varsMark (s.g.map Tensor.vars) with
      | none => simp
      | some w =>
        have hne : s.g.isEmpty = false := by
          cases hg : s.g with
          | nil =>
            rw [hg] at hs
            cases hs
          | cons _ _ => rfl
        rw [hne]
        simp
    | none =>
      have hL : ((r :: l).all ((fun s : RowSh => s.point == kCol && !s.bare &&
          (s.vars.isSome && s.vars == (rowSh r).vars)) ∘ rowSh)) = false := by
        rw [List.all_cons]
        have : ((fun s : RowSh => s.point == kCol && !s.bare &&
            (s.vars.isSome && s.vars == (rowSh r).vars)) ∘ rowSh) r = false := by
          show (r.psi.length == kCol && !r.g.isEmpty &&
            ((varsMark (r.g.map Tensor.vars)).isSome && _)) = false
          rw [hm]
          simp
        rw [this]
        rfl
      have hR : ((r :: l).all fun s => s.psi.length == kCol && !s.g.isEmpty &&
          s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) = false := by
        rw [List.all_cons]
        have h0 := not_all_head hm
        rw [List.isEmpty_map, List.all_map, List.head?_map] at h0
        have : (r.psi.length == kCol && !r.g.isEmpty &&
            r.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) = false := by
          rw [Bool.and_assoc]
          have h0' : (!r.g.isEmpty && r.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) =
              false := h0
          rw [h0']
          simp
        rw [this]
        rfl
      rw [hL, hR]

/-- At a state's shape that test is `leftAtC` (Room.lean of this folder) at the state. -/
theorem roomSh_eq (s : S) (n : Nat) : roomSh (shOf s) n = leftAtC s.st s.out.indexMasks n := by
  unfold roomSh leftAtC shOf
  simp only [Array.getElem?_map]
  cases s.st.oracles[s.out.indexMasks]? <;> rfl

/-- Where the test on the shape accepts, the nine premises hold. -/
theorem ready_of_shape {P : Where} {s : S} (h : readySh P (shOf s) = true) :
    ∃ (f : First.FinOwn) (t : List ℕ × St) (msg : Array OracleNotice),
      s.here = .fin f ∧ (!P.reply || s.out.reply.isSome) = true ∧
      s.out.pending.length = P.rows ∧
      memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true ∧ s.noneWaits = true ∧
      Batt.fits P.lin.kCol s.out.pending = true ∧
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linOk s.st.codes P.lin = true ∧ linMessageW P.lin = some msg := by
  unfold readySh at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  obtain ⟨f, hf⟩ := (atFinC_iff s).1 h1
  obtain ⟨msg, hm⟩ := Option.isSome_iff_exists.1 h9
  rw [roomSh_eq] at h7
  obtain ⟨t, ht⟩ := takeMasks_returns (d := dOf s) ((leftAtC_iff _ _ _).1 h7)
  rw [fitSh_eq] at h4
  have h6' : formSh P.lin.kCol (s.out.pending.map rowSh) = true := h6
  rw [formSh_eq] at h6'
  have h3' : (s.out.pending.map rowSh).length = P.rows := eq_of_beq h3
  rw [List.length_map] at h3'
  exact ⟨f, t, msg, hf, h2, h3', h4, h5, h6', ht, h8, hm⟩

variable {Cl : Type}

/-- **Where the test on the shape accepts, the joined sub-protocol accepts any elements in rounds of
the kind's form.** -/
theorem atM3_accepts_shape {P : Where} {s : S} (hsh : readySh P (shOf s) = true) (x : E)
    (h : Psc.Heard) (hl : h.rounds.length = P.lin.kCol) (h2 : ∀ p ∈ h.rounds, p.1.length = 2)
    (hv : h.values = []) (cols : List (List (Nat × List UInt64))) :
    ∃ s', (atM3 (Cl := Cl) P).decide s (roundsOf x h) cols = .ok s' := by
  obtain ⟨f, t, msg, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ready_of_shape hsh
  obtain ⟨row, hr⟩ := atM3_accepts_any (Cl := Cl) a1 a2 a3 a4 a5 a6 a7 a8 a9 x h hl h2 hv cols
  exact ⟨_, hr⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.all_eq_mark
#print axioms VerifiableInference.Desc.K13.Honest.all_head_mark
#print axioms VerifiableInference.Desc.K13.Honest.head_of_mark
#print axioms VerifiableInference.Desc.K13.Honest.not_all_head
#print axioms VerifiableInference.Desc.K13.Honest.fitSh_eq
#print axioms VerifiableInference.Desc.K13.Honest.formSh_eq
#print axioms VerifiableInference.Desc.K13.Honest.roomSh_eq
#print axioms VerifiableInference.Desc.K13.Honest.ready_of_shape
#print axioms VerifiableInference.Desc.K13.Honest.atM3_accepts_shape
