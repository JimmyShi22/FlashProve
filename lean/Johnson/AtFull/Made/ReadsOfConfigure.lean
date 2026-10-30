-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ReadsOfConfigure.lean: where the planner returns, the readers of a key's and of
a proof's three chains return on the planner's own parameter bytes, and at which values.

`Params.configure` (OnBytes/Params/Configure.lean) spells the parameter bytes of seven chains.
`Model.Verify.chainsOf` (OnBytes/Model/VerifyChains.lean) reads them back at once and refuses if a
reader does. The two main laws here say that `KeyChains.read` and `ProofChains.read` return there,
under tests with code on the plans and on the values that were spelled, and under a bound on each
item's length. What they return is written out: `keyOf`, `proofOf`. Each chain holds the plan, the
digest and the items that were spelled, and each item's value is the value that was spelled. For the
entry's chain the library has such a law at the full-size lines (`Tie.configure_record_read`,
OnBytes/Tie/EntryAtCfgRecord.lean).

No byte is laid or compared. The laws on the items are general
(Johnson/HB/LLHARD/KB9/ItemsBack.lean, Johnson/AtFull/Made/ItemsBackMore.lean), and so is the law on
the bytes around them (`Given.read_spelled`, OnBytes/Params/ToyDescriptions.lean).

  `givenAt P cfg I`: what `Given.read` returns on the bytes spelled from P, cfg and I.
  `planB`: the plan fits the format's words, is in order, and all its names are the format's.
  `Short`: each item's value has fewer than 2 ^ 64 bytes. `sameWords`: two plans have the same six
    settings. `noSample`: the plan has no entry for a table's own sample.
  `given_read`; `shared_read_spelled`, `second_read_spelled`, `oneTime_read_spelled`,
    `first_read_spelled`: one chain's reader on spelled bytes.
  `firstTests_of`, `threeTests_of`, `sameSetting_at`, `sameItem_key`, `sameItem_proof`: the readers'
    closing tests.
  **`key_read_of_configure`, `proof_read_of_configure`**: the two main laws.

Limits. That the planner returns is a premise. So are the tests' yes, the bound on the lengths, the
digest's 32 bytes, and that the layout has one entry for each link. None is shown here at any
values. Nothing where a premise fails. Nothing on soundness.
-/
import Johnson.AtFull.Made.ReadOf
import Johnson.AtFull.Made.ItemsBackMore
import Johnson.G.MadeSpelled
import OnBytes.Model.ReadBackMade
import OnBytes.Params.ToyDescriptions
import OnBytes.Params.ReadBackAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.KB9

/-! ## The bytes around the items -/

/-- What `Given.read` returns on the bytes that are spelled from a plan, a digest and items. -/
def givenAt (P : Fmt.Plan) (cfg : ByteArray) (I : List (String × ByteArray)) : Given :=
  ⟨Fmt.paramsBytes P cfg I, P, cfg, I⟩

/-- The plan fits the format's words, is in order, and every entry's name is one of the format's. -/
def planB (P : Fmt.Plan) : Bool := P.fit && (P.ok && namesKnown P)

/-- Each item's value has fewer than 2 ^ 64 bytes. -/
def Short (I : List (String × ByteArray)) : Prop := ∀ y ∈ I, y.2.size < 2 ^ 64

theorem given_read {P : Fmt.Plan} {cfg : ByteArray} {I : List (String × ByteArray)}
    (hP : planB P = true) (h32 : cfg.size = 32) (hn : ∀ y ∈ I, Fmt.nameFit y.1 = true)
    (hs : Short I) : Given.read (Fmt.paramsBytes P cfg I) = some (givenAt P cfg I) := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hP
  refine Given.read_spelled P cfg I (fit_of h1 h32 (List.all_eq_true.2 fun y hy => ?_)) h2
  exact Bool.and_eq_true_iff.2 ⟨hn y hy, decide_eq_true (hs y hy)⟩

/-! ## The items' names -/

theorem fit_oneTime (z : Plan.KeySized) : ∀ y ∈ Plan.oneTimeItems z, Fmt.nameFit y.1 = true := by
  intro y hy
  simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

theorem fit_lin (C : Codes) (S : LinShape) : ∀ y ∈ madeLinItems C S, Fmt.nameFit y.1 = true := by
  intro y hy
  simp only [madeLinItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> dsimp only <;> decide

theorem fit_first (l : Lines) (x : Shapes) (z : Sized) :
    ∀ y ∈ madeFirstItems l x z, Fmt.nameFit y.1 = true := by
  intro y hy
  simp only [madeFirstItems, madeLinItems, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hy
  rcases hy with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-! ## One chain's reader on spelled bytes -/

theorem shared_read_spelled {P : Fmt.Plan} {cfg : ByteArray} {C : Codes} {S : LinShape}
    (hP : planB P = true) (h32 : cfg.size = 32) (hs : Short (madeLinItems C S))
    (hC : codesB C = true) (hS : linB S = true) :
    Shared.read (Fmt.paramsBytes P cfg (madeLinItems C S)) =
      some ⟨givenAt P cfg (madeLinItems C S), C, S⟩ :=
  shared_read_of (given_read hP h32 (fit_lin C S) hs) rfl (readCodes_spell hC) (readLin_spell hS)

theorem second_read_spelled {P : Fmt.Plan} {cfg : ByteArray} (hP : planB P = true)
    (h32 : cfg.size = 32) : Second.read (Fmt.paramsBytes P cfg []) = some ⟨givenAt P cfg []⟩ :=
  second_read_of (given_read hP h32 (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil)) rfl

theorem oneTime_read_spelled {P : Fmt.Plan} {cfg : ByteArray} {z : Plan.KeySized}
    (hP : planB P = true) (h32 : cfg.size = 32) (hs : Short (Plan.oneTimeItems z))
    (hi : itemsB z = true) :
    OneTime.read (Fmt.paramsBytes P cfg (Plan.oneTimeItems z)) =
      some ⟨givenAt P cfg (Plan.oneTimeItems z), z.once.input, z.ranges.x, z.binding, z.codes,
        z.once.shape⟩ := by
  simp only [itemsB, Bool.and_eq_true] at hi
  obtain ⟨⟨⟨⟨i1, i2⟩, i3⟩, i4⟩, i5⟩ := hi
  exact oneTime_read_of (given_read hP h32 (fit_oneTime z) hs) rfl (readNotice_spell i1)
    (readRanges_spell i2) (readBinding_spell i3) (readCodes_spell i4) (readLin_spell i5)

theorem first_read_spelled {P : Fmt.Plan} {cfg : ByteArray} {l : Lines} {x : Shapes} {z : Sized}
    (hP : planB P = true) (h32 : cfg.size = 32) (hs : Short (madeFirstItems l x z))
    (hC : codesB z.proof.codes = true) (hL : linB z.proof.batch.shape = true)
    (hR : reqB z.proof.request = true) (hY : layoutB x.layout = true)
    (hI : wordsB x.identifiers = true) (hN : wB x.sub.pendingRows = true)
    (hB : bindingB ⟨clog2 l.slots, z.set.saltBytes⟩ = true)
    (ht : firstTests (givenAt P cfg (madeFirstItems l x z)) z.proof.request x.layout x.identifiers
      x.sub.pendingRows = true) :
    First.read (Fmt.paramsBytes P cfg (madeFirstItems l x z)) =
      some ⟨givenAt P cfg (madeFirstItems l x z), z.proof.codes, z.proof.batch.shape,
        z.proof.request, x.layout, x.identifiers, x.sub.pendingRows,
        ⟨clog2 l.slots, z.set.saltBytes⟩, []⟩ :=
  first_read_of (given_read hP h32 (fit_first l x z) hs) rfl (readCodes_spell hC)
    (readLin_spell hL) (readReq_spell hR) (readLayout_spell hY) (readWords_spell hI)
    (readWord_spell hN) (readBinding_spell hB) ht

/-! ## The closing tests -/

/-- Two plans have the same field, bytes of a salt, of a nonce and of a listed position, answers to
a sample, and word "saved". -/
def sameWords (P Q : Fmt.Plan) : Bool :=
  P.field == Q.field && P.salt == Q.salt && P.nonce == Q.nonce && P.posB == Q.posB &&
    P.samples == Q.samples && P.saved == Q.saved

/-- The plan has no entry for a table's own sample. -/
def noSample (P : Fmt.Plan) : Bool := (P.entries.find? fun e => e.name == recordName).isNone

theorem sameSetting_at {P Q : Fmt.Plan} {cfg : ByteArray} {I J : List (String × ByteArray)}
    (h : sameWords P Q = true) : sameSetting (givenAt P cfg I) (givenAt Q cfg J) = true := by
  show (sameWords P Q && cfg == cfg) = true
  rw [h, beq_self_bytes]
  rfl

/-- The items "codes" and "the test on the table" have the same bytes in a key's first two chains as
the planner spells them. -/
theorem sameItem_key (P Q : Fmt.Plan) (cfg : ByteArray) (z : Plan.KeySized) :
    sameItem (givenAt P cfg (Plan.oneTimeItems z))
        (givenAt Q cfg (madeLinItems z.codes z.once.shape)) "codes" = true ∧
      sameItem (givenAt P cfg (Plan.oneTimeItems z))
        (givenAt Q cfg (madeLinItems z.codes z.once.shape)) "the test on the table" = true := by
  constructor <;>
    simp [sameItem, Given.item, givenAt, Plan.oneTimeItems, madeLinItems, beq_self_bytes]

/-- The same for a proof's first two chains. -/
theorem sameItem_proof (P Q : Fmt.Plan) (cfg : ByteArray) (l : Lines) (x : Shapes) (z : Sized) :
    sameItem (givenAt P cfg (madeFirstItems l x z))
        (givenAt Q cfg (madeLinItems z.proof.codes z.proof.batch.shape)) "codes" = true ∧
      sameItem (givenAt P cfg (madeFirstItems l x z))
        (givenAt Q cfg (madeLinItems z.proof.codes z.proof.batch.shape))
        "the test on the table" = true := by
  constructor <;>
    simp [sameItem, Given.item, givenAt, madeFirstItems, madeLinItems, beq_self_bytes]

theorem threeTests_of {a b c : Given} (s1 : sameSetting a b = true) (s2 : sameSetting a c = true)
    (i1 : sameItem a b "codes" = true) (i2 : sameItem a b "the test on the table" = true)
    (r1 : b.record.isNone = true) (r2 : c.record.isNone = true) : threeTests a b c = true := by
  unfold threeTests
  rw [s1, s2, i1, i2, r1, r2]
  rfl

/-- The six tests at the end of `First.read`, from the four conditions that the planner asks itself,
one entry of the layout for each link, and a plan without an entry for a table's own sample. -/
theorem firstTests_of {g : Given} {s : ReqShape} {y : ReqLayout} {ids : List Nat} {n : Nat}
    (hk : ¬ (ids.length != s.link.length || s.atStart.length != 1 || n == 0 ||
      s.link.map (·.plain) != List.replicate (s.link.length - 1) 0 ++ [1]) = true)
    (hl : y.link.length = s.link.length) (hr : g.record.isNone = true) :
    firstTests g s y ids n = true := by
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq, not_or, ne_eq, not_not] at hk
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hk
  simp only [firstTests, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨k2, k4⟩, k1⟩, hl⟩, by omega⟩, hr⟩

/-! ## The values -/

/-- A key's three chains as they are read back: from the digest, the key's sizes and the three
plans. -/
def keyOf (cfg : ByteArray) (z : Plan.KeySized) (P1 P2 P3 : Fmt.Plan) : KeyChains :=
  ⟨⟨givenAt P1 cfg (Plan.oneTimeItems z), z.once.input, z.ranges.x, z.binding, z.codes,
      z.once.shape⟩,
    ⟨givenAt P2 cfg (madeLinItems z.codes z.once.shape), z.codes, z.once.shape⟩,
    ⟨givenAt P3 cfg []⟩⟩

/-- A proof's three chains as they are read back: from the digest, the lines, the shapes, the sizes
and the three plans. -/
def proofOf (cfg : ByteArray) (l : Lines) (x : Shapes) (z : Sized) (F S2 S3 : Fmt.Plan) :
    ProofChains :=
  ⟨⟨givenAt F cfg (madeFirstItems l x z), z.proof.codes, z.proof.batch.shape, z.proof.request,
      x.layout, x.identifiers, x.sub.pendingRows, ⟨clog2 l.slots, z.set.saltBytes⟩, []⟩,
    ⟨givenAt S2 cfg (madeLinItems z.proof.codes z.proof.batch.shape), z.proof.codes,
      z.proof.batch.shape⟩,
    ⟨givenAt S3 cfg []⟩⟩

/-! ## The two main laws -/

/-- **Where the planner returns, the reader of a key's three chains returns `keyOf`.** -/
theorem key_read_of_configure {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hc : configure l x cfg bits = .ok made) {P1 P2 P3 : Planned}
    (hk : made.key = [P1, P2, P3]) (h32 : cfg.size = 32) (p1 : planB P1.plan = true)
    (p2 : planB P2.plan = true) (p3 : planB P3.plan = true) (hi : itemsB made.sized.key = true)
    (hs : Short (Plan.oneTimeItems made.sized.key)) (w2 : sameWords P1.plan P2.plan = true)
    (w3 : sameWords P1.plan P3.plan = true) (n2 : noSample P2.plan = true)
    (n3 : noSample P3.plan = true) :
    KeyChains.read made.keyOneTime made.keyShared made.keySecond =
      some (keyOf cfg made.sized.key P1.plan P2.plan P3.plan) := by
  obtain ⟨Q1, Q2, Q3, _, _, _, hq, _, e1, e2, e3, _, _, _, _⟩ := configure_bytes hc
  rw [hk] at hq
  obtain ⟨rfl, rfl, rfl⟩ : P1 = Q1 ∧ P2 = Q2 ∧ P3 = Q3 := by
    simpa using hq
  have hs2 : Short (madeLinItems made.sized.key.codes made.sized.key.once.shape) := by
    intro y hy
    apply hs
    simp only [madeLinItems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> simp [Plan.oneTimeItems]
  have i := hi
  simp only [itemsB, Bool.and_eq_true] at i
  obtain ⟨t1, t2⟩ := sameItem_key P1.plan P2.plan cfg made.sized.key
  rw [e1, e2, e3]
  exact keyChains_read_of (oneTime_read_spelled p1 h32 hs hi)
    (shared_read_spelled p2 h32 hs2 i.1.2 i.2) (second_read_spelled p3 h32)
    (threeTests_of (sameSetting_at w2) (sameSetting_at w3) t1 t2 n2 n3)

/-- **Where the planner returns, the reader of a proof's three chains returns `proofOf`.** -/
theorem proof_read_of_configure {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hc : configure l x cfg bits = .ok made) {F S2 S3 : Planned}
    (hp : made.proof = [F, S2, S3]) (h32 : cfg.size = 32) (p1 : planB F.plan = true)
    (p2 : planB S2.plan = true) (p3 : planB S3.plan = true)
    (hC : codesB made.sized.proof.codes = true) (hL : linB made.sized.proof.batch.shape = true)
    (hR : reqB made.sized.proof.request = true) (hY : layoutB x.layout = true)
    (hI : wordsB x.identifiers = true) (hN : wB x.sub.pendingRows = true)
    (hB : bindingB ⟨clog2 l.slots, made.sized.set.saltBytes⟩ = true)
    (hs : Short (madeFirstItems l x made.sized))
    (hl : x.layout.link.length = made.sized.proof.request.link.length)
    (w2 : sameWords F.plan S2.plan = true) (w3 : sameWords F.plan S3.plan = true)
    (n1 : noSample F.plan = true) (n2 : noSample S2.plan = true) (n3 : noSample S3.plan = true) :
    ProofChains.read made.first made.shared made.second =
      some (proofOf cfg l x made.sized F.plan S2.plan S3.plan) := by
  obtain ⟨_, _, _, Q1, Q2, Q3, _, hq, _, _, _, _, e1, e2, e3⟩ := configure_bytes hc
  rw [hp] at hq
  obtain ⟨rfl, rfl, rfl⟩ : F = Q1 ∧ S2 = Q2 ∧ S3 = Q3 := by
    simpa using hq
  have hs2 : Short (madeLinItems made.sized.proof.codes made.sized.proof.batch.shape) := by
    intro y hy
    apply hs
    unfold madeFirstItems
    exact List.mem_append_left _ hy
  obtain ⟨t1, t2⟩ := sameItem_proof F.plan S2.plan cfg l x made.sized
  rw [e1, e2, e3]
  exact proofChains_read_of
    (first_read_spelled p1 h32 hs hC hL hR hY hI hN hB
      (firstTests_of (Johnson.G.MadeFree.configure_kept hc) hl n1))
    (shared_read_spelled p2 h32 hs2 hC hL) (second_read_spelled p3 h32)
    (threeTests_of (sameSetting_at w2) (sameSetting_at w3) t1 t2 n2 n3)

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.given_read
#print axioms Johnson.AtFull.Made.fit_oneTime
#print axioms Johnson.AtFull.Made.fit_lin
#print axioms Johnson.AtFull.Made.fit_first
#print axioms Johnson.AtFull.Made.shared_read_spelled
#print axioms Johnson.AtFull.Made.second_read_spelled
#print axioms Johnson.AtFull.Made.oneTime_read_spelled
#print axioms Johnson.AtFull.Made.first_read_spelled
#print axioms Johnson.AtFull.Made.sameSetting_at
#print axioms Johnson.AtFull.Made.sameItem_key
#print axioms Johnson.AtFull.Made.sameItem_proof
#print axioms Johnson.AtFull.Made.threeTests_of
#print axioms Johnson.AtFull.Made.firstTests_of
#print axioms Johnson.AtFull.Made.key_read_of_configure
#print axioms Johnson.AtFull.Made.proof_read_of_configure
