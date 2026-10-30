-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountTests.lean: THE TWO PROXIMITY TESTS OF A PROOF FILE's SHARED CHAIN (blocks number 9 and 10 of the table of
joints, Johnson/Desc/Shared/BordersShared.lean) AT THE CLAUSE OF THE ROW shared_joint_count's LEDGER (the head of EachPlainShOwn,
Johnson/Desc/Sound/SharedJointCountLedger.lean): WHAT THE CLAUSE ASKS THERE, OF WHOM. The table unfolded at these borders, one rule at letters, and
the rule at the table's three rows. WHY THESE TWO: with a split eight written rounds stand in front of the two tests (Johnson/Desc/K14/Text.lean: its own four, and
"the two rounds of the sending" twice): so, BY SUBTRACTION, NOT COUNTED AT THE LIST, 60 of the 68 rounds of the full size's written list of the shared chain are the tests' and the end's.

THE RULE (clause_of_test). A test closes classes of open rows (cls) and the pin of ONE message (laid: its extractor lays that message), and reads
the pins of the group's other members (kept). Letters: M: words · rg: a witness's words · Say s c m: every open row of the class c, as it lies
in the record s, says its claim of the words m · Cand mu v m: at the message mu the words m are A CANDIDATE at the acting part's value v: in the
list of mu's committed word, and with the answers of mu's sample as the record holds it · Same mu m m': two words agree at mu's tables.
THE DEBTS, EACH WITH ITS PAYER:
  law    THE KIND's LAW, for ONE statement, at the kind's own errors: but for these, at a yes THERE ARE WORDS m THAT ARE A CANDIDATE AT EVERY MEMBER,
         the kept ones too, and at which every closed class says its claim. (The kind's files; carried to the seat. "IN THE LIST" HOLDS ONLY IF THE
         LIST OF WHICH "NO COLLISION" SPEAKS REACHES AS FAR AS THE TEST's FIRST RADIUS: a comparison of the plan's numbers: found made in no file
         that was read for this; searched no further.)
  hdet   a member's pin binds: a candidate is, at that member, what every witness with the member's pin has.
  hlaid  the extractor lays the pinned message: where there is a candidate, the laid witness has the pin.
  hctx   the other members' pins come back past the block and past the extractor.
         (These three: PAID AT THE TABLE's FILLING, but for the riding back, in Johnson/Desc/Sound/SharedJointCountTestsFill.lean.)
  hrow   the filling of the table's letter row at the closed classes. hcong: a class reads the tables of the test's members (the laid message and the kept
         ones), and no other. (The files that lay the rows owe it.) BOTH ARE ASKED INSIDE THE PROMISE (at the
         record of a statement a with the condition at border k), AND hcong UNDER "the two words agree at the laid AND at every kept message": asked at
         EVERY record, and under agreement at the table's column "reads" alone, they are FALSE at a filling by "the rows as they lie in the record's
         groups": at an arbitrary record a row may name any message. The proof held the wider agreement all along (hsame).
  prom   for certain, at a yes: the shared promise behind. frames: for certain: the shared items that the row does not name ride.
A FIND BY READING, ON THE TABLE's ROW 9 WITH A SPLIT. (fold_u) reads o_sp, whose pin is context there, and the row closes no sample row of o_sp
("the sample rows of o_omega and o_sp lie untouched"). Of the rows that the table names for block 9 alone the clause WOULD NOT FOLLOW: beyond half
the distance the test's witness could hold another member of o_sp's list than the pinned one, with another kappa. IT FOLLOWS BECAUSE A TEST TAKES IN EACH
MEMBER's SAMPLE ROWS, which lie with the message and not with the group (runRows, OnBytes/Slice/BlkBegin.lean), and o_sp is a member of both
groups (joins, Johnson/Desc/K14/Text.lean): so law above asks a candidate at ALL members, kept ones too. A law of the kind that
concluded the group's own open rows alone would not pay.

  rowReads: the messages that the table names as read by a class (ItemS.reads). ins_nine_split … rides_ten: the table, unfolded, by evaluation.
  clause_nine_split · clause_nine_whole · clause_ten: the rule at the table's rows. With a split: 9 lays o_u, keeps o_sp, closes the sample's
  rows of o_u, (rec_gamma), (loc_x), (fold_u); four shared items ride. 10 lays o_sp, keeps o_omega, closes both samples' rows and (fold_omega); nothing
  rides. Without: 9 lays o_u, keeps o_omega, closes o_u's and o_omega's samples' rows, (rec_gamma), (loc_x), (fold); nothing rides.

NEAREST KIN, BY SHAPE: THE TABLE's LAW OF A BLOCK THAT CLOSES PINS (Johnson/Desc/Sound/WordsLaw.lean: TestGivesCand "the one row that is owed" ·
words_of_cand · goodIn_of_words; dec_of_cand by the library's sig_dec_good): in the form with witnesses (GoodIn), at its own filling, over ALL the oracles; its
candidates are those of the members whose pins the block CLOSES: what its letter ins asks of a kept member's tables is left to the payer. Here: the
plain coin, the ledger's clause to the letter, at the acting parts' values; the kept members have candidates too.
Kin, searched by name (clause_of | ClauseAt | insSh … 9 | 10):
clause_of_own | clause_of_sure (LedgerClause.lean): general in what is closed; here the extraction at a test is
taken apart. No file there speaks of borders 9 | 10 but open9_of_open8. Not every file of the library was searched.
Every "there is", walked. In law: the words m: no verifier reads them; they are the test's witness's.
Limits. RULES AT LETTERS: AS EMPTY AS THEIR PREMISES: NO MEMBER IS SHOWN. No block's text, no record is read. A block that refuses all meets the
clause. IT CLOSES NO ROW. NO SOUNDNESS. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountLedger
import Johnson.Desc.Sound.PointTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Doomed)
open VerifiableInference.Desc.Shared

/-! ## 1 The table, unfolded at the two tests -/

/-- The messages that the table names as read by a class of rows. -/
def rowReads (c : RowS) : List Msg2 :=
  (ItemS.row c).reads.filterMap fun x => match x with
    | .msg m => some m
    | _ => none

theorem ins_nine_split (i : ItemS) (h : insSh true 9 i) :
    i = .pin .oU ∨ (∃ ν ∈ [Msg2.oSp], i = .pin ν) ∨
      ∃ c ∈ [RowS.sample .oU, .recG, .loc, .foldU], i = .row c := by
  rw [insSh_eq] at h
  have h' : i ∈ insLSh true 9 := h
  have e : insLSh true 9 =
      [.row (.sample .oU), .row .recG, .row .loc, .pin .oU, .row .foldU, .pin .oSp] := by decide
  rw [e] at h'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inl ⟨_, by simp, rfl⟩)

theorem ins_nine_whole (i : ItemS) (h : insSh false 9 i) :
    i = .pin .oU ∨ (∃ ν ∈ [Msg2.oOmega], i = .pin ν) ∨
      ∃ c ∈ [RowS.sample .oU, .recG, .loc, .fold, .sample .oOmega], i = .row c := by
  rw [insSh_eq] at h
  have h' : i ∈ insLSh false 9 := h
  have e : insLSh false 9 = [.row (.sample .oU), .row .recG, .row .loc, .pin .oU, .row .fold,
      .row (.sample .oOmega), .pin .oOmega] := by decide
  rw [e] at h'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inl ⟨_, by simp, rfl⟩)

theorem ins_ten (i : ItemS) (h : insSh true 10 i) :
    i = .pin .oSp ∨ (∃ ν ∈ [Msg2.oOmega], i = .pin ν) ∨
      ∃ c ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega], i = .row c := by
  rw [insSh_eq] at h
  have h' : i ∈ insLSh true 10 := h
  have e : insLSh true 10 = [.row (.sample .oOmega), .row (.sample .oSp), .row .foldOmega, .pin .oSp,
      .pin .oOmega] := by decide
  rw [e] at h'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, by simp, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨_, by simp, rfl⟩)

/-- The pins that a test reads and does not close stand behind it. -/
theorem outs_nine_split : ∀ ν ∈ [Msg2.oSp], outsSh true 9 (.pin ν) := by
  intro ν hν
  rw [outsSh_eq]
  have e : ∀ μ ∈ [Msg2.oSp], ItemS.pin μ ∈ outsLSh true 9 := by decide
  exact e ν hν

theorem outs_nine_whole : ∀ ν ∈ [Msg2.oOmega], outsSh false 9 (.pin ν) := by
  intro ν hν
  rw [outsSh_eq]
  have e : ∀ μ ∈ [Msg2.oOmega], ItemS.pin μ ∈ outsLSh false 9 := by decide
  exact e ν hν

theorem outs_ten : ∀ ν ∈ [Msg2.oOmega], outsSh true 10 (.pin ν) := by
  intro ν hν
  rw [outsSh_eq]
  have e : ∀ μ ∈ [Msg2.oOmega], ItemS.pin μ ∈ outsLSh true 10 := by decide
  exact e ν hν

/-- **What rides past the test on G_u, with a split.** -/
theorem rides_nine_split (i : ItemS)
    (ho : openAfter (insSh true) (outsSh true) startSh 9 i) (hn : ¬ insSh true 9 i) :
    i ∈ [ItemS.pin .oOmega, .row (.sample .oOmega), .row (.sample .oSp), .row .foldOmega] := by
  have h1 := (openShL_iff true 9 i).1 ho
  rw [insSh_eq] at hn
  have h2 : i ∉ insLSh true 9 := hn
  have e : ∀ j ∈ openL (insLSh true) (outsLSh true) startLSh 9, j ∉ insLSh true 9 →
      j ∈ [ItemS.pin .oOmega, .row (.sample .oOmega), .row (.sample .oSp), .row .foldOmega] := by
    decide
  exact e i h1 h2

/-- Without a split nothing rides past the one test. -/
theorem rides_nine_whole (i : ItemS)
    (ho : openAfter (insSh false) (outsSh false) startSh 9 i) : insSh false 9 i := by
  have h1 := (openShL_iff false 9 i).1 ho
  rw [insSh_eq]
  have e : ∀ j ∈ openL (insLSh false) (outsLSh false) startLSh 9, j ∈ insLSh false 9 := by decide
  exact e i h1

/-- Nothing rides past the test on G_omega. -/
theorem rides_ten (i : ItemS)
    (ho : openAfter (insSh true) (outsSh true) startSh 10 i) : insSh true 10 i := by
  have h1 := (openShL_iff true 10 i).1 ho
  rw [insSh_eq]
  have e : ∀ j ∈ openL (insLSh true) (outsLSh true) startLSh 10, j ∈ insLSh true 10 := by decide
  exact e i h1

/-- The promise at the three borders. -/
theorem promsAt_tests :
    promsAt true 9 = [.tablePromise, .shape 9, .noColl .oU, .noColl .oOmega, .noColl .oSp] ∧
      promsAt true 10 = [.tablePromise, .shape 10, .noColl .oOmega, .noColl .oSp] ∧
      promsAt true 11 = [.tablePromise, .shape 11, .noColl .oOmega] ∧
      promsAt false 9 = [.tablePromise, .shape 9, .noColl .oU, .noColl .oOmega] ∧
      promsAt false 10 = [.tablePromise, .shape 10, .noColl .oOmega] := by
  decide

/-! ## 2 The rule -/

section
variable {P₁ S₂ Cl Wt M : Type} {C : CK} {Fr : Frame} (Ns : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (e₀ : ℕ → ActV S₂ Fr → Wt → Wt)
  (rg : Wt → M) (Say : S₂ → RowS → M → Prop) (Cand : Msg2 → ActV S₂ Fr → M → Prop)
  (Same : Msg2 → M → M → Prop)

/-- **What the kind's law is to lead to, at the statement in front**: there are words that are a candidate at every member and
at which every closed class says its claim. -/
def TestSays (k : ℕ) (laid : Msg2) (kept : List Msg2) (cls : List RowS)
    (a : (P₁ × S₂) × Fr.E.Str) : Prop :=
  ∃ m : M, (∀ μ, μ = laid ∨ μ ∈ kept → Cand μ ((actQ Ns p l k).2 a) m) ∧ ∀ c ∈ cls, Say a.1.2 c m

/-- **A proximity test at the ledger's clause.** -/
theorem clause_of_test (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds))
    (laid : Msg2) (kept : List Msg2) (cls : List RowS)
    (hins : ∀ i, insSh split k i →
      i = .pin laid ∨ (∃ ν ∈ kept, i = .pin ν) ∨ ∃ c ∈ cls, i = .row c)
    (houts : ∀ ν ∈ kept, outsSh split k (.pin ν))
    (law : x.ior.red.Leads (onQ₂ Ns Pm Oc split p l k)
      (fun a _ => TestSays Ns p l Say Cand k laid kept cls a) ε)
    (hdet : ∀ μ, μ = laid ∨ μ ∈ kept → ∀ a m w, onQ₂ Ns Pm Oc split p l k a →
      Cand μ ((actQ Ns p l k).2 a) m →
      muQ Ns Mg p l (.pin μ) k ((actQ Ns p l k).2 a) w → Same μ m (rg w))
    (hlaid : ∀ a m w, onQ₂ Ns Pm Oc split p l k a → Cand laid ((actQ Ns p l k).2 a) m →
      muQ Ns Mg p l (.pin laid) k ((actQ Ns p l k).2 a) (e₀ k ((actQ Ns p l k).2 a) w))
    (hctx : ∀ ν ∈ kept, ∀ a τ b w, onQ₂ Ns Pm Oc split p l k a → x.ior.red.out a τ = some b →
      muQ Ns Mg p l (.pin ν) (k + 1) ((actQ Ns p l (k + 1)).2 b) w →
      muQ Ns Mg p l (.pin ν) k ((actQ Ns p l k).2 a) (e₀ k ((actQ Ns p l k).2 a) w))
    (hrow : ∀ c ∈ cls, ∀ a, onQ₂ Ns Pm Oc split p l k a → ∀ w,
      Say a.1.2 c (rg w) → Mg.row c a.1.2 w)
    (hcong : ∀ c ∈ cls, ∀ a, onQ₂ Ns Pm Oc split p l k a → ∀ m m',
      (∀ μ, μ = laid ∨ μ ∈ kept → Same μ m m') → Say a.1.2 c m → Say a.1.2 c m')
    (prom : ∀ a τ b, onQ₂ Ns Pm Oc split p l k a → x.ior.red.out a τ = some b →
      promQ Ns Pm split p l (k + 1) ((actQ Ns p l (k + 1)).2 b))
    (frames : ∀ a τ b w i, onQ₂ Ns Pm Oc split p l k a → x.ior.red.out a τ = some b →
      openAfter (insSh split) (outsSh split) startSh k i → ¬ insSh split k i →
      muQ Ns Mg p l i (k + 1) ((actQ Ns p l (k + 1)).2 b) w →
      muQ Ns Mg p l i k ((actQ Ns p l k).2 a) (e₀ k ((actQ Ns p l k).2 a) w)) :
    x.ior.red.Leads (onQ₂ Ns Pm Oc split p l k)
      (fun a b => stepV Ns Mg Pm split p l e₀ k ((actQ Ns p l k).2 a) ((actQ Ns p l (k + 1)).2 b))
      ε := by
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ b hb => ?_) (law a ha)
  obtain ⟨m, hs, hc⟩ := hτ b hb
  refine ⟨prom a τ b ha hb, fun w h i hi => ?_⟩
  by_cases hI : insSh split k i
  · have hp0 := hlaid a m w ha (hs laid (Or.inl rfl))
    have hpk : ∀ ν ∈ kept,
        muQ Ns Mg p l (.pin ν) k ((actQ Ns p l k).2 a) (e₀ k ((actQ Ns p l k).2 a) w) :=
      fun ν hν => hctx ν hν a τ b w ha hb (h _ (Or.inr (houts ν hν)))
    have hsame : ∀ μ, μ = laid ∨ μ ∈ kept → Same μ m (rg (e₀ k ((actQ Ns p l k).2 a) w)) := by
      intro μ hμ
      refine hdet μ hμ a m _ ha (hs μ hμ) ?_
      rcases hμ with rfl | hμ
      · exact hp0
      · exact hpk μ hμ
    rcases hins i hI with rfl | ⟨ν, hν, rfl⟩ | ⟨c, hc', rfl⟩
    · exact hp0
    · exact hpk ν hν
    · exact hrow c hc' a ha _ (hcong c hc' a ha m _ hsame (hc c hc'))
  · exact frames a τ b w i ha hb hi hI (h i (Or.inl ⟨hi, hI⟩))

/-! ## 3 The rule at the table's rows -/

/-- **Block 9, with a split: the test on G_u.** -/
theorem clause_nine_split (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds))
    (law : x.ior.red.Leads (onQ₂ Ns Pm Oc true p l 9)
      (fun a _ => TestSays Ns p l Say Cand 9 .oU [.oSp] [.sample .oU, .recG, .loc, .foldU] a) ε)
    (hdet : ∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oSp] → ∀ a m w, onQ₂ Ns Pm Oc true p l 9 a →
      Cand μ ((actQ Ns p l 9).2 a) m →
      muQ Ns Mg p l (.pin μ) 9 ((actQ Ns p l 9).2 a) w → Same μ m (rg w))
    (hlaid : ∀ a m w, onQ₂ Ns Pm Oc true p l 9 a → Cand .oU ((actQ Ns p l 9).2 a) m →
      muQ Ns Mg p l (.pin .oU) 9 ((actQ Ns p l 9).2 a) (e₀ 9 ((actQ Ns p l 9).2 a) w))
    (hctx : ∀ ν ∈ [Msg2.oSp], ∀ a τ b w, onQ₂ Ns Pm Oc true p l 9 a →
      x.ior.red.out a τ = some b → muQ Ns Mg p l (.pin ν) 10 ((actQ Ns p l 10).2 b) w →
      muQ Ns Mg p l (.pin ν) 9 ((actQ Ns p l 9).2 a) (e₀ 9 ((actQ Ns p l 9).2 a) w))
    (hrow : ∀ c ∈ [RowS.sample .oU, .recG, .loc, .foldU], ∀ a, onQ₂ Ns Pm Oc true p l 9 a → ∀ w,
      Say a.1.2 c (rg w) → Mg.row c a.1.2 w)
    (hcong : ∀ c ∈ [RowS.sample .oU, .recG, .loc, .foldU], ∀ a, onQ₂ Ns Pm Oc true p l 9 a → ∀ m m',
      (∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oSp] → Same μ m m') → Say a.1.2 c m → Say a.1.2 c m')
    (prom : ∀ a τ b, onQ₂ Ns Pm Oc true p l 9 a → x.ior.red.out a τ = some b →
      promQ Ns Pm true p l 10 ((actQ Ns p l 10).2 b))
    (frames : ∀ i ∈ [ItemS.pin .oOmega, .row (.sample .oOmega), .row (.sample .oSp),
        .row .foldOmega], ∀ a τ b w, onQ₂ Ns Pm Oc true p l 9 a → x.ior.red.out a τ = some b →
      muQ Ns Mg p l i 10 ((actQ Ns p l 10).2 b) w →
      muQ Ns Mg p l i 9 ((actQ Ns p l 9).2 a) (e₀ 9 ((actQ Ns p l 9).2 a) w)) :
    x.ior.red.Leads (onQ₂ Ns Pm Oc true p l 9)
      (fun a b => stepV Ns Mg Pm true p l e₀ 9 ((actQ Ns p l 9).2 a) ((actQ Ns p l 10).2 b)) ε :=
  clause_of_test Ns Mg Pm Oc true p l e₀ rg Say Cand Same 9 x ε .oU [.oSp]
    [.sample .oU, .recG, .loc, .foldU] ins_nine_split outs_nine_split law hdet hlaid
    hctx hrow hcong prom
    (fun a τ b w i ha hb ho hn hm => frames i (rides_nine_split i ho hn) a τ b w ha hb hm)

/-- **Block 9, without a split: the one test.** -/
theorem clause_nine_whole (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds))
    (law : x.ior.red.Leads (onQ₂ Ns Pm Oc false p l 9)
      (fun a _ => TestSays Ns p l Say Cand 9 .oU [.oOmega]
        [.sample .oU, .recG, .loc, .fold, .sample .oOmega] a) ε)
    (hdet : ∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oOmega] → ∀ a m w, onQ₂ Ns Pm Oc false p l 9 a →
      Cand μ ((actQ Ns p l 9).2 a) m →
      muQ Ns Mg p l (.pin μ) 9 ((actQ Ns p l 9).2 a) w → Same μ m (rg w))
    (hlaid : ∀ a m w, onQ₂ Ns Pm Oc false p l 9 a → Cand .oU ((actQ Ns p l 9).2 a) m →
      muQ Ns Mg p l (.pin .oU) 9 ((actQ Ns p l 9).2 a) (e₀ 9 ((actQ Ns p l 9).2 a) w))
    (hctx : ∀ ν ∈ [Msg2.oOmega], ∀ a τ b w, onQ₂ Ns Pm Oc false p l 9 a →
      x.ior.red.out a τ = some b → muQ Ns Mg p l (.pin ν) 10 ((actQ Ns p l 10).2 b) w →
      muQ Ns Mg p l (.pin ν) 9 ((actQ Ns p l 9).2 a) (e₀ 9 ((actQ Ns p l 9).2 a) w))
    (hrow : ∀ c ∈ [RowS.sample .oU, .recG, .loc, .fold, .sample .oOmega], ∀ a, onQ₂ Ns Pm Oc false p l 9 a → ∀ w,
      Say a.1.2 c (rg w) → Mg.row c a.1.2 w)
    (hcong : ∀ c ∈ [RowS.sample .oU, .recG, .loc, .fold, .sample .oOmega], ∀ a, onQ₂ Ns Pm Oc false p l 9 a → ∀ m m',
      (∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oOmega] → Same μ m m') → Say a.1.2 c m → Say a.1.2 c m')
    (prom : ∀ a τ b, onQ₂ Ns Pm Oc false p l 9 a → x.ior.red.out a τ = some b →
      promQ Ns Pm false p l 10 ((actQ Ns p l 10).2 b)) :
    x.ior.red.Leads (onQ₂ Ns Pm Oc false p l 9)
      (fun a b => stepV Ns Mg Pm false p l e₀ 9 ((actQ Ns p l 9).2 a) ((actQ Ns p l 10).2 b)) ε :=
  clause_of_test Ns Mg Pm Oc false p l e₀ rg Say Cand Same 9 x ε .oU [.oOmega]
    [.sample .oU, .recG, .loc, .fold, .sample .oOmega] ins_nine_whole outs_nine_whole
    law hdet hlaid hctx hrow hcong prom
    (fun _ _ _ _ i _ _ ho hn _ => absurd (rides_nine_whole i ho) hn)

/-- **Block 10: the test on G_omega.** -/
theorem clause_ten (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds))
    (law : x.ior.red.Leads (onQ₂ Ns Pm Oc true p l 10)
      (fun a _ => TestSays Ns p l Say Cand 10 .oSp [.oOmega]
        [.sample .oOmega, .sample .oSp, .foldOmega] a) ε)
    (hdet : ∀ μ, μ = Msg2.oSp ∨ μ ∈ [Msg2.oOmega] → ∀ a m w, onQ₂ Ns Pm Oc true p l 10 a →
      Cand μ ((actQ Ns p l 10).2 a) m →
      muQ Ns Mg p l (.pin μ) 10 ((actQ Ns p l 10).2 a) w → Same μ m (rg w))
    (hlaid : ∀ a m w, onQ₂ Ns Pm Oc true p l 10 a → Cand .oSp ((actQ Ns p l 10).2 a) m →
      muQ Ns Mg p l (.pin .oSp) 10 ((actQ Ns p l 10).2 a) (e₀ 10 ((actQ Ns p l 10).2 a) w))
    (hctx : ∀ ν ∈ [Msg2.oOmega], ∀ a τ b w, onQ₂ Ns Pm Oc true p l 10 a →
      x.ior.red.out a τ = some b → muQ Ns Mg p l (.pin ν) 11 ((actQ Ns p l 11).2 b) w →
      muQ Ns Mg p l (.pin ν) 10 ((actQ Ns p l 10).2 a) (e₀ 10 ((actQ Ns p l 10).2 a) w))
    (hrow : ∀ c ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega], ∀ a, onQ₂ Ns Pm Oc true p l 10 a → ∀ w,
      Say a.1.2 c (rg w) → Mg.row c a.1.2 w)
    (hcong : ∀ c ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega], ∀ a, onQ₂ Ns Pm Oc true p l 10 a → ∀ m m',
      (∀ μ, μ = Msg2.oSp ∨ μ ∈ [Msg2.oOmega] → Same μ m m') → Say a.1.2 c m → Say a.1.2 c m')
    (prom : ∀ a τ b, onQ₂ Ns Pm Oc true p l 10 a → x.ior.red.out a τ = some b →
      promQ Ns Pm true p l 11 ((actQ Ns p l 11).2 b)) :
    x.ior.red.Leads (onQ₂ Ns Pm Oc true p l 10)
      (fun a b => stepV Ns Mg Pm true p l e₀ 10 ((actQ Ns p l 10).2 a) ((actQ Ns p l 11).2 b))
      ε :=
  clause_of_test Ns Mg Pm Oc true p l e₀ rg Say Cand Same 10 x ε .oSp [.oOmega]
    [.sample .oOmega, .sample .oSp, .foldOmega] ins_ten outs_ten law hdet hlaid hctx
    hrow hcong prom (fun _ _ _ _ i _ _ ho hn _ => absurd (rides_ten i ho) hn)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.clause_of_test
#print axioms VerifiableInference.Desc.Sound.clause_nine_split
#print axioms VerifiableInference.Desc.Sound.clause_nine_whole
#print axioms VerifiableInference.Desc.Sound.clause_ten
#print axioms VerifiableInference.Desc.Sound.promsAt_tests
