-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/FillLaws.lean: what OnBytes/Maker/Page/Fill.lean's way back gives at the plain
parts that the compiled verifier of a file writes into its chain queries.

The verifier runs the three chains one after the other and writes the plain part of a round of chain
c through `PB.left` and `PB.right` (OnBytes/TypedOracleCompiler/Joined/Cut.lean; OnBytes/TypedOracleCompiler/Joined/Verifier.lean:
`emb₁`, `emb₂`, `emb₃`). Here `partOf` is computed at these.

  `splitPB_left`, `splitPB_right`: `splitPB` undoes `PB.left` and `PB.right`.
  `in₁`, `in₂`, `in₃`: a plain part of chain 1's, chain 2's, chain 3's rounds as one of the file's.
  `partOf_front`, `partOf_join`, `partOf_seam`: at the three silent rounds' messages.
  `partOf_one`, `partOf_two`, `partOf_three`: at a plain part of a stretch: what `saidLo` or
    `saidSh` says there, at the typed round.
  `saidLo_head`, `saidLo_tail`, `saidSh_head`, `saidSh_tail`: how these two unfold at a first round.
    Nobody calls these four.
  `PartsLo a ds e`, `PartsSh a ds e`: e writes the plain parts of a stretch whose first round is the
    typed round a + 1 into the file's. `PartsLo.head`, `PartsLo.tail`, `PartsSh.head`,
    `PartsSh.tail`: at the first round: `.row (a + 1)` with that round's message and nonce; behind
    it the same at a + 1: so a statement on all rounds of a stretch can go by induction.
    `ofSaid_next`: a tool.
  `parts_one`, `parts_two`, `parts_three`: the three stretches of a file. Nobody calls `PartsLo`,
    `PartsSh`, their four laws or these three: the induction of OnBytes/Maker/Page/FillLine.lean
      goes
    at `partAt`.
  `rdAt_one`, `rdAt_two`, `rdAt_three`, `kindAt_of`, `workAt_of`: a written round's data, kind's
    number and bits of work at its typed round.

What is not claimed. Nothing on the interface's plain parts or on the read-back `rd`.


-/
import OnBytes.Maker.Page.Fill
import OnBytes.TypedOracleCompiler.Joined.Cut

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Joined Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ _root_.Compile.Joined

theorem splitPB_left : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (z : PlainPart s A),
    splitPB (PB.left (u := u) (B := B) z) = .inl z
  | [], _, _, _, z => nomatch z
  | _ :: _, _, (_, _), _, .inl _ => rfl
  | _ :: s, u, (a, A), B, .inr z => by
      show Sum.map (Sum.inr : PlainPart s A → (a.P0 ⊕ a.Pj) ⊕ PlainPart s A) id
        (splitPB (PB.left (u := u) (B := B) z)) = _
      rw [splitPB_left z]
      rfl

theorem splitPB_right : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (z : PlainPart u B),
    splitPB (PB.right (s := s) (A := A) z) = .inr z
  | [], _, _, _, _ => rfl
  | _ :: s, u, (a, A), B, z => by
      show Sum.map (Sum.inr : PlainPart s A → (a.P0 ⊕ a.Pj) ⊕ PlainPart s A) id
        (splitPB (PB.right (s := s) (A := A) z)) = _
      rw [splitPB_right z]
      rfl

section
variable (C : CK)

theorem saidLo_head (d : RDT) (ds : List RDT) (pl : (roundT C d).Plain) :
    saidLo C (d :: ds) (.inl (.inr pl)) = some (saidOf C d pl) := rfl

theorem saidLo_tail (d : RDT) (ds : List RDT) (w : PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds))) :
    saidLo C (d :: ds) (.inr w) = (saidLo C ds w).map Said.next := rfl

theorem saidSh_head (d : RDT) (ds : List RDT) (pl : (roundT C d).Plain) :
    saidSh C (d :: ds) (.inl (.inl pl)) = some (saidOf C d pl) := rfl

theorem saidSh_tail (d : RDT) (ds : List RDT)
    (w : PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))) :
    saidSh C (d :: ds) (.inr w) = (saidSh C ds w).map Said.next := rfl

variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- A plain part of chain 1's rounds, as one of the file's. -/
def in₁ (z : PlainPart (chainsOf C D tF tJ t3).c₁ (chainsOf C D tF tJ t3).A₁) :
    PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  PB.left (s := (chainsOf C D tF tJ t3).c₁)
    (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
    (A := (chainsOf C D tF tJ t3).A₁)
    (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z

/-- Of chain 2's. -/
def in₂ (z : PlainPart (chainsOf C D tF tJ t3).c₂ (chainsOf C D tF tJ t3).A₂) :
    PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  PB.right (s := (chainsOf C D tF tJ t3).c₁)
    (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
    (A := (chainsOf C D tF tJ t3).A₁)
    (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃)
    (PB.left (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
      (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z)

/-- Of chain 3's. -/
def in₃ (z : PlainPart (chainsOf C D tF tJ t3).c₃ (chainsOf C D tF tJ t3).A₃) :
    PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  PB.right (s := (chainsOf C D tF tJ t3).c₁)
    (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
    (A := (chainsOf C D tF tJ t3).A₁)
    (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃)
    (PB.right (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
      (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z)

theorem partOf_front (p : TF) :
    partOf C D tF tJ t3 (in₁ C D tF tJ t3 (.inl (.inr p))) = .front p := by
  unfold partOf in₁
  rw [splitPB_left]

theorem partOf_one (w : PlainPart (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁))) :
    partOf C D tF tJ t3 (in₁ C D tF tJ t3 (.inr w)) = PartJ.ofSaid 0 (saidLo C D.ds₁ w) := by
  unfold partOf in₁
  rw [splitPB_left]

theorem partOf_join (p : TJ) :
    partOf C D tF tJ t3 (in₂ C D tF tJ t3 (.inl (.inl p))) = .join p := by
  unfold partOf in₂
  rw [splitPB_right]
  simp only
  rw [splitPB_left]

theorem partOf_two (w : PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))) :
    partOf C D tF tJ t3 (in₂ C D tF tJ t3 (.inr w)) =
      PartJ.ofSaid (D.ds₁.length + 1) (saidSh C D.ds₂ w) := by
  unfold partOf in₂
  rw [splitPB_right]
  simp only
  rw [splitPB_left]

theorem partOf_seam (p : T3) :
    partOf C D tF tJ t3 (in₃ C D tF tJ t3 (.inl (.inr p))) = .seam p := by
  unfold partOf in₃
  rw [splitPB_right]
  simp only
  rw [splitPB_right]

theorem partOf_three (w : PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃))) :
    partOf C D tF tJ t3 (in₃ C D tF tJ t3 (.inr w)) =
      PartJ.ofSaid (D.ds₁.length + D.ds₂.length + 2) (saidLo C D.ds₃ w) := by
  unfold partOf in₃
  rw [splitPB_right]
  simp only
  rw [splitPB_right]

/-! ## Along a stretch, round by round -/

theorem ofSaid_next (a : ℕ) (s : Option Said) :
    (PartJ.ofSaid a (s.map Said.next) : PartJ TF TJ T3) = PartJ.ofSaid (a + 1) s := by
  cases s with
  | none => rfl
  | some s =>
    show PartJ.row (a + 1 + (s.k + 1)) s.msg s.nonce = PartJ.row (a + 1 + 1 + s.k) s.msg s.nonce
    rw [show a + 1 + (s.k + 1) = a + 1 + 1 + s.k by omega]

/-- e writes the plain parts of a stretch of local rounds, whose first round is the typed round
a + 1, into the file's. -/
def PartsLo (a : ℕ) (ds : List RDT)
    (e : PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds)) →
      PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) : Prop :=
  ∀ w, partOf C D tF tJ t3 (e w) = PartJ.ofSaid a (saidLo C ds w)

/-- The same for shared rounds. -/
def PartsSh (a : ℕ) (ds : List RDT)
    (e : PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) →
      PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) : Prop :=
  ∀ w, partOf C D tF tJ t3 (e w) = PartJ.ofSaid a (saidSh C ds w)

variable {C D tF tJ t3}

/-- **At the stretch's first round**: the typed round, the message and the nonce of that round's
plain part. -/
theorem PartsLo.head {a : ℕ} {d : RDT} {ds : List RDT}
    {e : PlainPart (uLT C (d :: ds)) (RoundSplits.allLocal (uLT C (d :: ds))) →
      PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann}
    (h : PartsLo C D tF tJ t3 a (d :: ds) e) (pl : (roundT C d).Plain) :
    partOf C D tF tJ t3 (e (.inl (.inr pl))) =
      .row (a + 1) (saidOf C d pl).msg (saidOf C d pl).nonce :=
  h (.inl (.inr pl))

theorem PartsLo.tail {a : ℕ} {d : RDT} {ds : List RDT}
    {e : PlainPart (uLT C (d :: ds)) (RoundSplits.allLocal (uLT C (d :: ds))) →
      PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann}
    (h : PartsLo C D tF tJ t3 a (d :: ds) e) :
    PartsLo C D tF tJ t3 (a + 1) ds fun w => e (.inr w) :=
  fun w => (h (.inr w)).trans (ofSaid_next a (saidLo C ds w))

theorem PartsSh.head {a : ℕ} {d : RDT} {ds : List RDT}
    {e : PlainPart (uLT C (d :: ds)) (RoundSplits.const (RAnn.ofShared .sh) (uLT C (d :: ds))) →
      PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann}
    (h : PartsSh C D tF tJ t3 a (d :: ds) e) (pl : (roundT C d).Plain) :
    partOf C D tF tJ t3 (e (.inl (.inl pl))) =
      .row (a + 1) (saidOf C d pl).msg (saidOf C d pl).nonce :=
  h (.inl (.inl pl))

theorem PartsSh.tail {a : ℕ} {d : RDT} {ds : List RDT}
    {e : PlainPart (uLT C (d :: ds)) (RoundSplits.const (RAnn.ofShared .sh) (uLT C (d :: ds))) →
      PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann}
    (h : PartsSh C D tF tJ t3 a (d :: ds) e) :
    PartsSh C D tF tJ t3 (a + 1) ds fun w => e (.inr w) :=
  fun w => (h (.inr w)).trans (ofSaid_next a (saidSh C ds w))

variable (C D tF tJ t3)

/-- **The three stretches of a file.** -/
theorem parts_one : PartsLo C D tF tJ t3 0 D.ds₁ fun w => in₁ C D tF tJ t3 (.inr w) :=
  partOf_one C D tF tJ t3

theorem parts_two :
    PartsSh C D tF tJ t3 (D.ds₁.length + 1) D.ds₂ fun w => in₂ C D tF tJ t3 (.inr w) :=
  partOf_two C D tF tJ t3

theorem parts_three :
    PartsLo C D tF tJ t3 (D.ds₁.length + D.ds₂.length + 2) D.ds₃ fun w =>
      in₃ C D tF tJ t3 (.inr w) :=
  partOf_three C D tF tJ t3

end

/-! ## A written round's data, by the typed round -/

section
variable (D : WholeD)

theorem rdAt_one (k : ℕ) (h : k < D.ds₁.length) : rdAt D (0 + 1 + k) = D.ds₁[k]? := by
  unfold rdAt
  rw [if_neg (by omega), if_pos (by omega), show 0 + 1 + k - 1 = k by omega]

theorem rdAt_two (k : ℕ) (h : k < D.ds₂.length) :
    rdAt D (D.ds₁.length + 1 + 1 + k) = D.ds₂[k]? := by
  unfold rdAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show D.ds₁.length + 1 + 1 + k - (D.ds₁.length + 2) = k by omega]

theorem rdAt_three (k : ℕ) :
    rdAt D (D.ds₁.length + D.ds₂.length + 2 + 1 + k) = D.ds₃[k]? := by
  unfold rdAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega),
    show D.ds₁.length + D.ds₂.length + 2 + 1 + k - (D.ds₁.length + D.ds₂.length + 3) = k by omega]

theorem kindAt_of {i : ℕ} {d : RDT} (h : rdAt D i = some d) : kindAt D i = d.kind.num := by
  unfold kindAt
  rw [h]
  rfl

theorem workAt_of {i : ℕ} {d : RDT} (h : rdAt D i = some d) : workAt D i = d.entry.work := by
  unfold workAt
  rw [h]
  rfl

end

end OnBytes.Maker.Page
