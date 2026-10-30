-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/LedgerKeeps.lean: what lies under a filled slot stays there across the seat: the
form of a law that every block of a link owes, and its small rules. Definitions of Props and
theorems; no definition that a run uses.

Why. A block lays the sub-proof's ledger into the carried record and the next block takes it out.
The laws on what lies under a slot (Johnson/Desc/Part/MaskedSumLedger.lean;
OnBytes/Tie/Pv/Psc/PscForm.lean) speak of "any later ledger": that the link's LAST ledger is later
than the one behind a write has to be a law of every block between.
  LedgerKeeps ledger b     : whatever record b's decide returns, its ledger is later (in the sense
                             of OnBytes.PscRun.Later) than the one in the record that it was handed.
                             ledger is ONE function for the whole link, fixed once for the link.
  LedgerKeepsRuns ledger b : the same of b's runs of claims and of its runs behind the batching.
                             (Some runs write: see WHO MAKES A ROW LATE.)
  LedgerKeepsAt ledger? b  : the same where the record holds a ledger only inside a link: if the
                             record in front holds one, so does the record behind, and a later one.
  ledgerKeeps_of_same      : a block that leaves the ledger as it is has it.
  LedgerKeeps.at           : the first form gives the third.
  LedgerKeeps.two, Ran, LedgerKeeps.ran, LedgerKeepsAt.ran : two blocks in a row; any row of blocks.
ROOM, AND STRETCHES THAT ARE OWED (the notions: OnBytes/Tie/Pv/Psc/PscRoom.lean). Later keeps
neither: a later ledger may fill any free slot. So three forms more, at the reading that holds a
ledger only inside a link:
  LedgerTakes ledger? b t     : the block takes AT MOST t slots: from room for t and m more it
                                gives back room for m. t is a count off the plan. A CEILING: a
                                block that takes fewer has it too (LedgerTakes.mono).
  LedgerWritesAbove ledger? b : it turns no mark below the next slot of the ledger in front.
  LedgerKeepsOwed ledger? b a n : it keeps the stretch of n slots from a on owed (taken, not yet
                                written): for the blocks between a hearing and its late row.
  LedgerTakesRuns, LedgerWritesAboveRuns, LedgerKeepsOwedRuns : the same of a block's runs.
  LedgerWritesAbove.keepsOwed, ledgerKeepsOwed_of_along, ledgerTakes_of_same : who has them: a block
                                that writes above; a block whose yes can be cut into steps each of
                                which spares the stretch; a block that leaves the ledger as it is.
  LedgerKeepsOwed.ran, LedgerTakes.ran : any row of blocks: the stretch stays owed; one room in
                                front and a sum of counts.
  deaf_takes, greedy_fails, squatter_fails, squatter_writes_below, dropper_fails : at silly members:
                                no to all; one that takes a slot; one that fills an owed slot;
                                one that drops the ledger. taker_takes: a member at t = 1.
WHO MAKES A ROW LATE. Reported of other files, not read here: the lookup's
sumcheck over the leaves and the merge of the claims on the committed weights hold a sumcheck's own
slots back at the hearing and write them at a run of claims. The attention's and the head's kinds
write them at the hearing's own ledger: they owe LedgerTakes, and nothing of LedgerKeepsOwed for
their own sumchecks.
WALKS. Between such a hearing and its row lie decisions and runs, of several blocks, in an order
that the general fold sets. The rule is for EVERY order: the fold is not read.
  LedgerKeepsAtRuns : Later, of a block's runs, at that reading.
  decides, stepsOf  : a block's steps as relations from record to record: its decision at any
                      rounds; each run of claims at ANY number, whatever claims it hands out; each
                      run behind the batching.
  Walked st N       : N steps, in any order, each one of the list st. Length 0: nothing has turned.
  StepKeeps ledger? a n r : what one step owes for one stretch.
  walked_keeps      : along any walk the ledger is there, later, and the stretch still owed.
  stepsOf_keep      : a block's four forms give the law for every one of its steps.
  walked_of_ran     : a row of decisions is a walk.
  squatter_run_fails : the run that fills the stretch, left in the list: the law fails.
THE RUN THAT MAKES THE ROW IS NOT IN THE WALK: its block has not LedgerKeepsOwedRuns at its own
stretch: so the caller hands the list of steps WITHOUT that run, and shows StepKeeps of that block's
other steps one by one.
WHY "keeps owed" AND NOT "spares": sparing is a relation of two ledgers and is not kept under one
step after another; a block's yes is many steps. What a fold can carry is that the stretch is still
owed.
A LIMIT, LOUD: LedgerKeepsOwed HAS THE STRETCH AS A LETTER. In a frame it must be asked FOR EVERY
SUMCHECK THAT IS STILL OPEN IN THE CARRIED RECORD: that form wants the record's own type and is not
typed here.
A SECOND LIMIT, LOUDER: StepKeeps AND LedgerKeepsOwedRuns SPEAK OF
ALL RECORDS, with no promise on the record but that the stretch is owed. A RUN THAT WRITES AT AN
ADDRESS READ OFF THE RECORD HAS THEM AT NO STRETCH OF ONE SLOT OR MORE (late_writer_fails): among
all records there is one whose address lies in the stretch; the slots there are free because they
are owed; the write returns; the stretch is owed no more. No theorem here is false by that. But
where ANOTHER late writer's run stands in the walk, the premise of walked_keeps and of stepsOf_keep
cannot be met, and they are TRUE AND SAY NOTHING. So are the laws that lean on them:
late_row_returns_walked (Johnson/Desc/Part/MaskedSumLate.lean [not in this library]); claimRun_keeps
and owed_at_run (Johnson/Desc/Part/LedgerFoldClaims.lean [not in this library]). They serve steps
that write above the next slot or not at all, and links with one late writer, that writer's own run
left out.
STEPS UNDER A PROMISE, the cure:
  StepKeepsUnder Inv ledger? a n r : the same law, asked only at records that meet Inv, and the step
                      HANDS Inv ON to the record behind.
  stepKeeps_iff_under : StepKeeps is StepKeepsUnder at the promise that always holds.
  StepKeeps.under     : a step with StepKeeps has StepKeepsUnder under every promise that it hands
                      on; it may hand it on WITH THE STRETCH's BOUND AT HAND (a hearing does: it
                      lays the next slot as an address, and the stretch lies below the next slot).
  walked_keeps_under  : along any walk FROM A RECORD THAT MEETS Inv: Inv, the ledger, later, owed.
  lateWriter, owedLedger, LateApart, late_writer_fails, late_writer_keeps_under : a run that writes
                      one slot at the address in the record: it fails StepKeeps at every stretch of
                      one slot or more; it has StepKeepsUnder at the promise LateApart: "the arrays
                      have their size and the address lies apart from the stretch".
  late_writer_fails_sized : under the first half of that promise alone it still fails: the second
                      half does the work.
  late_writer_meets   : the promise is met by a record at which the stretch is owed and the write
                      returns.
  lateHearer, late_hearer_keeps_under : a hearing that takes slots and lays their first number as
                      the address has the law under the same promise.
  late_mover_fails    : a step that lays the stretch's own first slot as the address has it not.
  late_pair_walks     : a walk of two steps, the hearing and then the write, from a record that
                      meets the promise: the write fills its slot and the stretch is still owed.
  stepKeepsUnder_false : AT A PROMISE THAT NO RECORD MEETS EVERY STEP HAS THE LAW, the squatter too,
                      and walked_keeps_under says nothing.
THAT Inv HOLDS AT THE WALK's FIRST RECORD IS THE CALLER's TO SHOW, and with it that some record
meets Inv at all. Inv is the kind's to name: for late writers, that the stretches still open in the
record lie apart. No kind's Inv is typed here.
FIVE LIMITS OF THE CURE:
  Inv MUST BE HANDED ON FROM EVERY RECORD THAT MEETS IT, at any rounds, any number of claims, in any
  order and any number of times: not only from records that a fold reaches. A promise that is true
  of reachable records alone makes the premise unmeetable again.
  THE STRETCH's OWN WRITER. (a, n) are letters: that the run which makes the row writes AT a can
  only come out of Inv at the last record. With that pin in Inv the writer's own HEARING cannot
  stand in the list (it moves the address): the caller leaves out that writer's run AND its hearing,
  or shows that the hearing refuses at every record that meets Inv.
  A WRITER THAT IS NOT YET HEARD: Inv speaks of its address field at the first record too: an idle
  value must lie apart, or the run must refuse.
  NOT CARRIED UP: stepsOf_keep has no twin under a promise; claimRun_keeps and owed_at_run
  lean on walked_keeps. late_row_returns_walked has a twin under a promise beside it
  (late_row_returns_walked_under, Johnson/Desc/Part/MaskedSumLate.lean).
  NO MEMBER SHOWS THE PIN: the toys below have ONE address: the stretch (a, n) has no writer of its
  own in them; two addresses and the pin are shown by no member here.
At n = 0 every ledger owes the stretch (0, 0): walked_keeps_under then carries a bare promise along
a walk.
A part that blocks call is no block and owes its own share: that each of its functions that takes a
ledger hands back a later one (for the masked sumcheck: hear_keeps, row_keeps,
Johnson/Desc/Part/MaskedSumLedger.lean; whole_keeps, Johnson/Desc/Part/MaskedSumKeeps.lean).
At silly members: deaf_keeps: a block that says no to all MEETS the law, emptily: it is an
invariant, and needs a returning half beside it. fresh_fails: a block that lays a fresh ledger in
mid-link does NOT meet it.
STRICTLY BETWEEN THE LAYING AND THE CLEARING. Not due at the block that lays the link's ledger:
there a new stretch begins. And the forms at the reading ledger? all end in "the record behind holds
a ledger": the block that clears the link has none of them and stands in no row or walk.
What is not claimed. That any block of the description has it. Nothing on soundness, on an honest
prover or on hiding.
-/
import Johnson.Desc.Block
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part
open OnBytes OnBytes.Model
open OnBytes.PscRun (LedgerRoom WritesAbove SlotsOwed SparesAlong owed_of_writesAbove owed_along)

variable {S Cl : Type}

/-- **The block's yes leads to a later ledger.** -/
def LedgerKeeps {S Cl : Type} (ledger : S → Fork) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → OnBytes.PscRun.Later (ledger s) (ledger s')

/-- The same of the block's runs of claims and of its runs behind the batching. -/
def LedgerKeepsRuns (ledger : S → Fork) (b : Block S Cl) : Prop :=
  (∀ x ∈ b.claims, ∀ n s l s', x.2 n s = .ok (l, s') →
    OnBytes.PscRun.Later (ledger s) (ledger s')) ∧
    ∀ x ∈ b.after, ∀ s s', x.2 s = .ok s' → OnBytes.PscRun.Later (ledger s) (ledger s')

/-- The same where the record holds a ledger only inside a link. -/
def LedgerKeepsAt (ledger? : S → Option Fork) (b : Block S Cl) : Prop :=
  ∀ s rs gs s' F, b.decide s rs gs = .ok s' → ledger? s = some F →
    ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F'

/-- A block that leaves the ledger as it is. -/
theorem ledgerKeeps_of_same (ledger : S → Fork) (b : Block S Cl)
    (h : ∀ s rs gs s', b.decide s rs gs = .ok s' → ledger s' = ledger s) :
    LedgerKeeps ledger b := by
  intro s rs gs s' hd
  rw [h s rs gs s' hd]
  exact OnBytes.PscRun.Later.refl _

/-- The first form gives the third, at the reading that always holds a ledger. -/
theorem LedgerKeeps.at {ledger : S → Fork} {b : Block S Cl} (h : LedgerKeeps ledger b) :
    LedgerKeepsAt (fun s => some (ledger s)) b := by
  intro s rs gs s' F hd hF
  have e : ledger s = F := Option.some.inj hF
  exact ⟨ledger s', rfl, e ▸ h s rs gs s' hd⟩

/-- Two blocks in a row. -/
theorem LedgerKeeps.two {ledger : S → Fork} {b c : Block S Cl} (hb : LedgerKeeps ledger b)
    (hc : LedgerKeeps ledger c) {s t u : S} {rs rs' : List Fmt.RoundView}
    {gs gs' : List (List (Nat × List UInt64))} (h1 : b.decide s rs gs = .ok t)
    (h2 : c.decide t rs' gs' = .ok u) : OnBytes.PscRun.Later (ledger s) (ledger u) :=
  (hb _ _ _ _ h1).trans (hc _ _ _ _ h2)

/-- The blocks have said yes one behind the other, each at some rounds and columns, from s to s'. -/
def Ran : List (Block S Cl) → S → S → Prop
  | [], s, s' => s' = s
  | b :: bs, s, s' => ∃ rs gs t, b.decide s rs gs = .ok t ∧ Ran bs t s'

/-- **Any row of blocks.** -/
theorem LedgerKeeps.ran {ledger : S → Fork} : ∀ (bs : List (Block S Cl)),
    (∀ b ∈ bs, LedgerKeeps ledger b) → ∀ s s', Ran bs s s' →
      OnBytes.PscRun.Later (ledger s) (ledger s')
  | [], _, s, s', h => by
    have e : s' = s := h
    rw [e]
    exact OnBytes.PscRun.Later.refl _
  | b :: bs, hk, s, s', h => by
    obtain ⟨rs, gs, t, h1, h2⟩ := h
    exact (hk b (by simp) _ _ _ _ h1).trans
      (LedgerKeeps.ran bs (fun c hc => hk c (List.mem_cons_of_mem _ hc)) t s' h2)

/-- Any row of blocks, where the record holds a ledger only inside a link. -/
theorem LedgerKeepsAt.ran {ledger? : S → Option Fork} : ∀ (bs : List (Block S Cl)),
    (∀ b ∈ bs, LedgerKeepsAt ledger? b) → ∀ s s' F, Ran bs s s' → ledger? s = some F →
      ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F'
  | [], _, s, s', F, h, hF => by
    have e : s' = s := h
    rw [e]
    exact ⟨F, hF, OnBytes.PscRun.Later.refl _⟩
  | b :: bs, hk, s, s', F, h, hF => by
    obtain ⟨rs, gs, t, h1, h2⟩ := h
    obtain ⟨F1, g1, l1⟩ := hk b (by simp) s rs gs t F h1 hF
    obtain ⟨F2, g2, l2⟩ :=
      LedgerKeepsAt.ran bs (fun c hc => hk c (List.mem_cons_of_mem _ hc)) t s' F1 h2 g1
    exact ⟨F2, g2, l1.trans l2⟩

/-- A block that says no to all meets it, emptily. -/
theorem deaf_keeps (ledger : S → Fork) :
    LedgerKeeps ledger ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun _ _ _ => .error "no" } : Block S Cl) := by
  intro s rs gs s' h
  cases h

/-- **A block that lays a fresh ledger in mid-link does not meet it.** -/
theorem fresh_fails :
    ¬ LedgerKeeps (fun F : Fork => F) ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun F _ _ => .ok (F.slots F.ns) } : Block Fork Unit) := by
  intro H
  have h0 := (H { ns := 1, vp := #[zeroE], mf := #[zeroE], LS := #[zeroE], gotF := #[true] } [] [] _
    rfl).keep 0 rfl
  have h1 : (Array.replicate 1 false).getD 0 false = true := h0.1
  simp [Array.getD_eq_getD_getElem?] at h1

/-! ## Room, and stretches that are owed -/

/-- **The block takes at most t slots**: from room for t and m more it gives back room for m. -/
def LedgerTakes (ledger? : S → Option Fork) (b : Block S Cl) (t : Nat) : Prop :=
  ∀ s rs gs s' F m, b.decide s rs gs = .ok s' → ledger? s = some F → LedgerRoom F (t + m) →
    ∃ F', ledger? s' = some F' ∧ LedgerRoom F' m

/-- **The block writes above**: it turns no mark below the next slot of the ledger in front. -/
def LedgerWritesAbove (ledger? : S → Option Fork) (b : Block S Cl) : Prop :=
  ∀ s rs gs s' F, b.decide s rs gs = .ok s' → ledger? s = some F →
    ∃ F', ledger? s' = some F' ∧ WritesAbove F F'

/-- **The block keeps the stretch of n slots from a on owed.** The stretch is a letter: a block that
makes another sumcheck's late row has this at every stretch apart from that one. -/
def LedgerKeepsOwed (ledger? : S → Option Fork) (b : Block S Cl) (a n : Nat) : Prop :=
  ∀ s rs gs s' F, b.decide s rs gs = .ok s' → ledger? s = some F → SlotsOwed F a n →
    ∃ F', ledger? s' = some F' ∧ SlotsOwed F' a n

/-- The block's runs of claims and its runs behind the batching take no slot. -/
def LedgerTakesRuns (ledger? : S → Option Fork) (b : Block S Cl) : Prop :=
  (∀ x ∈ b.claims, ∀ i s l s' F m, x.2 i s = .ok (l, s') → ledger? s = some F → LedgerRoom F m →
    ∃ F', ledger? s' = some F' ∧ LedgerRoom F' m) ∧
    ∀ x ∈ b.after, ∀ s s' F m, x.2 s = .ok s' → ledger? s = some F → LedgerRoom F m →
      ∃ F', ledger? s' = some F' ∧ LedgerRoom F' m

/-- The block's runs write above. (A run that makes a late row does not.) -/
def LedgerWritesAboveRuns (ledger? : S → Option Fork) (b : Block S Cl) : Prop :=
  (∀ x ∈ b.claims, ∀ i s l s' F, x.2 i s = .ok (l, s') → ledger? s = some F →
    ∃ F', ledger? s' = some F' ∧ WritesAbove F F') ∧
    ∀ x ∈ b.after, ∀ s s' F, x.2 s = .ok s' → ledger? s = some F →
      ∃ F', ledger? s' = some F' ∧ WritesAbove F F'

/-- The block's runs keep the stretch owed. -/
def LedgerKeepsOwedRuns (ledger? : S → Option Fork) (b : Block S Cl) (a n : Nat) : Prop :=
  (∀ x ∈ b.claims, ∀ i s l s' F, x.2 i s = .ok (l, s') → ledger? s = some F → SlotsOwed F a n →
    ∃ F', ledger? s' = some F' ∧ SlotsOwed F' a n) ∧
    ∀ x ∈ b.after, ∀ s s' F, x.2 s = .ok s' → ledger? s = some F → SlotsOwed F a n →
      ∃ F', ledger? s' = some F' ∧ SlotsOwed F' a n

/-- A block that writes above keeps every stretch owed. -/
theorem LedgerWritesAbove.keepsOwed {ledger? : S → Option Fork} {b : Block S Cl}
    (h : LedgerWritesAbove ledger? b) (a n : Nat) : LedgerKeepsOwed ledger? b a n := by
  intro s rs gs s' F hd hF ho
  obtain ⟨F', g, w⟩ := h s rs gs s' F hd hF
  exact ⟨F', g, owed_of_writesAbove ho w⟩

/-- **The bridge**: a block whose yes can be cut into a row of ledgers, each step of which spares
the stretch, keeps it owed. The row is the block's files' own, inside their proof: no fold sees it.
-/
theorem ledgerKeepsOwed_of_along {ledger? : S → Option Fork} {b : Block S Cl} {a n : Nat}
    (h : ∀ s rs gs s' F, b.decide s rs gs = .ok s' → ledger? s = some F →
      ∃ l : List Fork, SparesAlong a n F l ∧ ledger? s' = some (l.getLastD F)) :
    LedgerKeepsOwed ledger? b a n := by
  intro s rs gs s' F hd hF ho
  obtain ⟨l, h1, h2⟩ := h s rs gs s' F hd hF
  exact ⟨_, h2, owed_along l F ho h1⟩

/-- A block that leaves the ledger as it is takes no slot, writes above and keeps every stretch
owed. -/
theorem ledgerTakes_of_same {ledger? : S → Option Fork} {b : Block S Cl}
    (h : ∀ s rs gs s', b.decide s rs gs = .ok s' → ledger? s' = ledger? s) :
    LedgerTakes ledger? b 0 ∧ LedgerWritesAbove ledger? b ∧
      ∀ a n, LedgerKeepsOwed ledger? b a n := by
  refine ⟨?_, ?_, ?_⟩
  · intro s rs gs s' F m hd hF hR
    exact ⟨F, by rw [h s rs gs s' hd]; exact hF, hR.mono (Nat.le_add_left _ _)⟩
  · intro s rs gs s' F hd hF
    exact ⟨F, by rw [h s rs gs s' hd]; exact hF, OnBytes.PscRun.WritesAbove.refl F⟩
  · intro a n s rs gs s' F hd hF ho
    exact ⟨F, by rw [h s rs gs s' hd]; exact hF, ho⟩

/-- **Any row of blocks: the stretch stays owed.** -/
theorem LedgerKeepsOwed.ran {ledger? : S → Option Fork} {a n : Nat} : ∀ (bs : List (Block S Cl)),
    (∀ b ∈ bs, LedgerKeepsOwed ledger? b a n) → ∀ s s' F, Ran bs s s' → ledger? s = some F →
      SlotsOwed F a n → ∃ F', ledger? s' = some F' ∧ SlotsOwed F' a n
  | [], _, s, s', F, h, hF, ho => by
    have e : s' = s := h
    rw [e]
    exact ⟨F, hF, ho⟩
  | b :: bs, hk, s, s', F, h, hF, ho => by
    obtain ⟨rs, gs, t, h1, h2⟩ := h
    obtain ⟨F1, g1, o1⟩ := hk b (by simp) s rs gs t F h1 hF ho
    exact LedgerKeepsOwed.ran bs (fun c hc => hk c (List.mem_cons_of_mem _ hc)) t s' F1 h2 g1 o1

/-- **Any row of blocks, each with its count: one room in front, and a sum.** -/
theorem LedgerTakes.ran {ledger? : S → Option Fork} {m : Nat} :
    ∀ (bs : List (Block S Cl × Nat)), (∀ x ∈ bs, LedgerTakes ledger? x.1 x.2) → ∀ s s' F,
      Ran (bs.map (·.1)) s s' → ledger? s = some F → LedgerRoom F ((bs.map (·.2)).sum + m) →
      ∃ F', ledger? s' = some F' ∧ LedgerRoom F' m
  | [], _, s, s', F, h, hF, hR => by
    have e : s' = s := h
    rw [e]
    exact ⟨F, hF, hR.mono (Nat.le_add_left _ _)⟩
  | x :: bs, hk, s, s', F, h, hF, hR => by
    obtain ⟨rs, gs, t, h1, h2⟩ := h
    have hR' : LedgerRoom F (x.2 + ((bs.map (·.2)).sum + m)) :=
      hR.mono (by simp only [List.map_cons, List.sum_cons]; omega)
    obtain ⟨F1, g1, r1⟩ := hk x (by simp) s rs gs t F _ h1 hF hR'
    exact LedgerTakes.ran bs (fun c hc => hk c (List.mem_cons_of_mem _ hc)) t s' F1 h2 g1 r1

/-- A block that says no to all has the first two, emptily; so the third too
(LedgerWritesAbove.keepsOwed). -/
theorem deaf_takes (ledger? : S → Option Fork) (t : Nat) :
    LedgerTakes ledger? ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun _ _ _ => .error "no" } : Block S Cl) t ∧
    LedgerWritesAbove ledger? ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun _ _ _ => .error "no" } : Block S Cl) := by
  constructor
  · intro s rs gs s' F m h
    cases h
  · intro s rs gs s' F h
    cases h

/-- **A block that takes a slot has not "takes none".** -/
theorem greedy_fails :
    ¬ LedgerTakes (fun F : Fork => some F) ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun F _ _ => .ok { F with next := F.next + 1 } } : Block Fork Unit) 0 := by
  intro H
  obtain ⟨F', e, hR⟩ := H (({} : Fork).slots 0) [] [] _ (({} : Fork).slots 0) 0 rfl rfl
    (OnBytes.PscRun.ledgerRoom_slots 0)
  have e' := Option.some.inj e
  rw [← e'] at hR
  have h2 : 0 + 1 + 0 ≤ 0 := hR.fits
  omega

/-- **A block that fills an owed slot does not keep it owed.** -/
theorem squatter_fails :
    ¬ LedgerKeepsOwed (fun F : Fork => some F) ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun F _ _ => .ok { F with gotF := F.gotF.set! 0 true } } : Block Fork Unit)
      0 1 := by
  intro H
  have ho : SlotsOwed ({ (({} : Fork).slots 1) with next := 1 } : Fork) 0 1 := by
    refine ⟨Nat.le_refl _, fun j _ hj hf => ?_⟩
    have e : j = 0 := by omega
    subst e
    have hf' : (Array.replicate 1 false).getD 0 false = true := hf
    simp [Array.getD_eq_getD_getElem?] at hf'
  obtain ⟨F', e, o⟩ := H _ [] [] _ _ rfl rfl ho
  have e' := Option.some.inj e
  rw [← e'] at o
  exact o.2 0 (Nat.le_refl _) Nat.one_pos rfl

/-- A ceiling: what takes at most t takes at most any more. -/
theorem LedgerTakes.mono {ledger? : S → Option Fork} {b : Block S Cl} {t t' : Nat}
    (h : LedgerTakes ledger? b t) (ht : t ≤ t') : LedgerTakes ledger? b t' := by
  intro s rs gs s' F m hd hF hR
  exact h s rs gs s' F m hd hF (hR.mono (Nat.add_le_add_right ht m))

/-- **A member at t = 1**: a block that takes one slot. -/
theorem taker_takes :
    LedgerTakes (fun F : Fork => some F) ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun F _ _ => .ok { F with next := F.next + 1 } } : Block Fork Unit) 1 := by
  intro s rs gs s' F m hd hF hR
  have e1 : s = F := Option.some.inj hF
  have e2 := Except.ok.inj hd
  refine ⟨s', rfl, ?_⟩
  rw [← e2, e1]
  have h2 : F.next + (1 + m) ≤ F.ns := hR.fits
  refine ⟨hR.sized, ?_, fun j hj => hR.free j ?_⟩
  · show F.next + 1 + m ≤ F.ns
    omega
  · have h3 : F.next + 1 ≤ j := hj
    omega

/-- A block that fills a slot below the next one does not write above. -/
theorem squatter_writes_below :
    ¬ LedgerWritesAbove (fun F : Fork => some F) ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun F _ _ => .ok { F with gotF := F.gotF.set! 0 true } } : Block Fork Unit) :=
  fun H => squatter_fails (H.keepsOwed 0 1)

/-- **A block that drops the ledger has none of the forms.** The record is a ledger or none. -/
theorem dropper_fails :
    ¬ LedgerKeepsAt (fun s : Option Fork => s) ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [], after := [],
      decide := fun _ _ _ => .ok none } : Block (Option Fork) Unit) := by
  intro H
  obtain ⟨F', e, _⟩ := H (some {}) [] [] none {} rfl rfl
  cases e

/-! ## Walks: decisions and runs, in any order -/

/-- Later, of a block's runs, where the record holds a ledger only inside a link. -/
def LedgerKeepsAtRuns (ledger? : S → Option Fork) (b : Block S Cl) : Prop :=
  (∀ x ∈ b.claims, ∀ i s l s' F, x.2 i s = .ok (l, s') → ledger? s = some F →
    ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F') ∧
    ∀ x ∈ b.after, ∀ s s' F, x.2 s = .ok s' → ledger? s = some F →
      ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F'

/-- The block's decision as a step from record to record: at some rounds and columns. -/
def decides (b : Block S Cl) : S → S → Prop := fun s s' => ∃ rs gs, b.decide s rs gs = .ok s'

/-- **The steps of a block**: its decision; each of its runs of claims, at any number and whatever
claims it hands out; each of its runs behind the batching. -/
def stepsOf (b : Block S Cl) : List (S → S → Prop) :=
  decides b :: ((b.claims.map fun x => fun s s' => ∃ i l, x.2 i s = .ok (l, s')) ++
    b.after.map fun x => fun s s' => x.2 s = .ok s')

/-- **N steps, in any order, each one of the list.** -/
def Walked (st : List (S → S → Prop)) : Nat → S → S → Prop
  | 0, s, s' => s' = s
  | N + 1, s, s' => ∃ r ∈ st, ∃ t, r s t ∧ Walked st N t s'

/-- **What one step owes for one stretch**: the ledger is still there, is later, and the stretch is
still owed. -/
def StepKeeps (ledger? : S → Option Fork) (a n : Nat) (r : S → S → Prop) : Prop :=
  ∀ s s' F, r s s' → ledger? s = some F → SlotsOwed F a n →
    ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F' ∧ SlotsOwed F' a n

/-- **Along any walk.** -/
theorem walked_keeps {ledger? : S → Option Fork} {a n : Nat} {st : List (S → S → Prop)}
    (hk : ∀ r ∈ st, StepKeeps ledger? a n r) : ∀ (N : Nat) (s s' : S) (F : Fork),
    Walked st N s s' → ledger? s = some F → SlotsOwed F a n →
      ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F' ∧ SlotsOwed F' a n
  | 0, s, s', F, h, hF, ho => by
    have e : s' = s := h
    rw [e]
    exact ⟨F, hF, OnBytes.PscRun.Later.refl F, ho⟩
  | N + 1, s, s', F, h, hF, ho => by
    obtain ⟨r, hr, t, h1, h2⟩ := h
    obtain ⟨F1, g1, l1, o1⟩ := hk r hr s t F h1 hF ho
    obtain ⟨F2, g2, l2, o2⟩ := walked_keeps hk N t s' F1 h2 g1 o1
    exact ⟨F2, g2, l1.trans l2, o2⟩

/-- The two halves of a step's law, said of one record behind, are one. -/
theorem stepKeeps_join {ledger? : S → Option Fork} {s' : S} {F : Fork} {a n : Nat}
    (h1 : ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F')
    (h2 : ∃ F', ledger? s' = some F' ∧ SlotsOwed F' a n) :
    ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F' ∧ SlotsOwed F' a n := by
  obtain ⟨F1, g1, l1⟩ := h1
  obtain ⟨F2, g2, o2⟩ := h2
  have e : F2 = F1 := by
    rw [g1] at g2
    exact (Option.some.inj g2).symm
  rw [e] at o2
  exact ⟨F1, g1, l1, o2⟩

/-- **The four forms of a block give the law for every one of its steps.** -/
theorem stepsOf_keep {ledger? : S → Option Fork} {b : Block S Cl} {a n : Nat}
    (h1 : LedgerKeepsAt ledger? b) (h2 : LedgerKeepsAtRuns ledger? b)
    (h3 : LedgerKeepsOwed ledger? b a n) (h4 : LedgerKeepsOwedRuns ledger? b a n) :
    ∀ r ∈ stepsOf b, StepKeeps ledger? a n r := by
  intro r hr s s' F hs hF ho
  cases List.mem_cons.1 hr with
  | inl e =>
    rw [e] at hs
    obtain ⟨rs, gs, hd⟩ := hs
    exact stepKeeps_join (h1 s rs gs s' F hd hF) (h3 s rs gs s' F hd hF ho)
  | inr hr' =>
    cases List.mem_append.1 hr' with
    | inl hc =>
      obtain ⟨x, hx, e⟩ := List.mem_map.1 hc
      rw [← e] at hs
      obtain ⟨i, l, hd⟩ := hs
      exact stepKeeps_join (h2.1 x hx i s l s' F hd hF) (h4.1 x hx i s l s' F hd hF ho)
    | inr ha =>
      obtain ⟨x, hx, e⟩ := List.mem_map.1 ha
      rw [← e] at hs
      exact stepKeeps_join (h2.2 x hx s s' F hs hF) (h4.2 x hx s s' F hs hF ho)

/-- A row of decisions is a walk. -/
theorem walked_of_ran {st : List (S → S → Prop)} : ∀ (bs : List (Block S Cl)),
    (∀ b ∈ bs, decides b ∈ st) → ∀ s s', Ran bs s s' → Walked st bs.length s s'
  | [], _, _, _, h => h
  | b :: bs, hm, s, s', h => by
    obtain ⟨rs, gs, t, h1, h2⟩ := h
    exact ⟨decides b, hm b (by simp), t, ⟨rs, gs, h1⟩,
      walked_of_ran bs (fun c hc => hm c (List.mem_cons_of_mem _ hc)) t s' h2⟩

/-- **The run that fills the stretch, left in the list: the law fails.** The block's decision leaves
the ledger as it is; its one run of claims fills slot 0. -/
theorem squatter_run_fails :
    ¬ ∀ r ∈ stepsOf ({
      name := "", place := default, planOk := true, rounds := [], oracles := [], before := [],
      claims := [("", fun _ F => .ok ([], { F with gotF := F.gotF.set! 0 true }))], after := [],
      decide := fun F _ _ => .ok F } : Block Fork Unit),
      StepKeeps (fun F : Fork => some F) 0 1 r := by
  intro H
  have ho : SlotsOwed ({ (({} : Fork).slots 1) with next := 1 } : Fork) 0 1 := by
    refine ⟨Nat.le_refl _, fun j _ hj hf => ?_⟩
    have e : j = 0 := by omega
    subst e
    have hf' : (Array.replicate 1 false).getD 0 false = true := hf
    simp [Array.getD_eq_getD_getElem?] at hf'
  obtain ⟨F', e, _, o⟩ := H _
    (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem List.mem_cons_self)))
    _ _ _ ⟨0, [], rfl⟩ rfl ho
  have e' := Option.some.inj e
  rw [← e'] at o
  exact o.2 0 (Nat.le_refl _) Nat.one_pos rfl

/-! ## Steps under a promise on the record -/

/-- **What one step owes for one stretch, under a promise on the record**, which it hands on. -/
def StepKeepsUnder (Inv : S → Prop) (ledger? : S → Option Fork) (a n : Nat) (r : S → S → Prop) :
    Prop :=
  ∀ s s' F, Inv s → r s s' → ledger? s = some F → SlotsOwed F a n →
    Inv s' ∧ ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F' ∧ SlotsOwed F' a n

/-- StepKeeps is StepKeepsUnder at the promise that always holds. -/
theorem stepKeeps_iff_under {ledger? : S → Option Fork} {a n : Nat} {r : S → S → Prop} :
    StepKeeps ledger? a n r ↔ StepKeepsUnder (fun _ => True) ledger? a n r :=
  ⟨fun h s s' F _ hr hF ho => ⟨trivial, h s s' F hr hF ho⟩,
    fun h s s' F hr hF ho => (h s s' F trivial hr hF ho).2⟩

/-- A step with StepKeeps has StepKeepsUnder under every promise that it hands on. -/
theorem StepKeeps.under {Inv : S → Prop} {ledger? : S → Option Fork} {a n : Nat}
    {r : S → S → Prop} (h : StepKeeps ledger? a n r)
    (hi : ∀ s s' F, Inv s → r s s' → ledger? s = some F → SlotsOwed F a n → Inv s') :
    StepKeepsUnder Inv ledger? a n r :=
  fun s s' F hI hr hF ho => ⟨hi s s' F hI hr hF ho, h s s' F hr hF ho⟩

/-- **Along any walk from a record that meets the promise.** -/
theorem walked_keeps_under {Inv : S → Prop} {ledger? : S → Option Fork} {a n : Nat}
    {st : List (S → S → Prop)} (hk : ∀ r ∈ st, StepKeepsUnder Inv ledger? a n r) :
    ∀ (N : Nat) (s s' : S) (F : Fork), Inv s → Walked st N s s' → ledger? s = some F →
      SlotsOwed F a n →
      Inv s' ∧ ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F' ∧ SlotsOwed F' a n
  | 0, s, s', F, hI, h, hF, ho => by
    have e : s' = s := h
    rw [e]
    exact ⟨hI, F, hF, OnBytes.PscRun.Later.refl F, ho⟩
  | N + 1, s, s', F, hI, h, hF, ho => by
    obtain ⟨r, hr, t, h1, h2⟩ := h
    obtain ⟨i1, F1, g1, l1, o1⟩ := hk r hr s t F hI h1 hF ho
    obtain ⟨i2, F2, g2, l2, o2⟩ := walked_keeps_under hk N t s' F1 i1 h2 g1 o1
    exact ⟨i2, F2, g2, l1.trans l2, o2⟩

/-- **At a promise that no record meets every step has the law**: it then says nothing. -/
theorem stepKeepsUnder_false (ledger? : S → Option Fork) (a n : Nat) (r : S → S → Prop) :
    StepKeepsUnder (fun _ => False) ledger? a n r :=
  fun _ _ _ hI => hI.elim

/-- A run that writes one slot at the address in the record. The record: an address and a ledger. -/
def lateWriter : Nat × Fork → Nat × Fork → Prop :=
  fun s s' => s'.1 = s.1 ∧ s.2.hide s.1 zeroE (subE zeroE oneE) = some s'.2

/-- A ledger of a + n slots, all taken, none filled. -/
def owedLedger (a n : Nat) : Fork := { (({} : Fork).slots (a + n)) with next := a + n }

theorem owedLedger_free (a n j : Nat) : ¬ OnBytes.PscRun.Filled (owedLedger a n) j :=
  OnBytes.PscRun.freeAbove_slots (a + n) j (Nat.zero_le _)

theorem owedLedger_sized (a n : Nat) : OnBytes.PscRun.Sized (owedLedger a n) :=
  OnBytes.PscRun.slots_sized ({} : Fork) (a + n)

/-- The promise: the arrays have their size, and the address lies apart from the stretch. -/
def LateApart (a n : Nat) (s : Nat × Fork) : Prop :=
  OnBytes.PscRun.Sized s.2 ∧ (s.1 < a ∨ a + n ≤ s.1)

/-- **Under the promise's first half alone the run fails**, at every stretch of one slot or more. -/
theorem late_writer_fails_sized (a n : Nat) (hn : 1 ≤ n) :
    ¬ StepKeepsUnder (fun s : Nat × Fork => OnBytes.PscRun.Sized s.2)
      (fun s : Nat × Fork => some s.2) a n lateWriter := by
  intro H
  have ho : SlotsOwed (owedLedger a n) a n :=
    ⟨Nat.le_refl _, fun j _ _ => owedLedger_free a n j⟩
  have hs : (owedLedger a n).gotF.size = (owedLedger a n).ns := (owedLedger_sized a n).2.2
  have hj : a < (owedLedger a n).ns := by
    show a < a + n
    omega
  obtain ⟨G, hG⟩ : ∃ G, (owedLedger a n).hide a zeroE (subE zeroE oneE) = some G :=
    ⟨_, OnBytes.PscRun.hide_returns (F := owedLedger a n) (j := a) zeroE (subE zeroE oneE) hs hj
      (owedLedger_free a n a)⟩
  obtain ⟨_, F', e, _, o⟩ := H (a, owedLedger a n) (a, G) (owedLedger a n) (owedLedger_sized a n)
    ⟨rfl, hG⟩ rfl ho
  have e' : G = F' := Option.some.inj e
  rw [← e'] at o
  exact o.2 a (Nat.le_refl _) (by omega)
    (OnBytes.PscRun.hide_ok _ G _ _ _ (owedLedger_sized a n) hG).2.2.2.2.1

/-- **A run that writes where the record says has StepKeeps at no stretch of one slot or
more.** -/
theorem late_writer_fails (a n : Nat) (hn : 1 ≤ n) :
    ¬ StepKeeps (fun s : Nat × Fork => some s.2) a n lateWriter :=
  fun H => late_writer_fails_sized a n hn
    (H.under fun _ _ _ hI hr _ _ => OnBytes.PscRun.hide_sized hI hr.2)

/-- **It has the law under the promise.** -/
theorem late_writer_keeps_under (a n : Nat) :
    StepKeepsUnder (LateApart a n) (fun s : Nat × Fork => some s.2) a n lateWriter := by
  intro s s' F hI hr hF ho
  obtain ⟨hsz, hap⟩ := hI
  obtain ⟨h1, h2⟩ := hr
  have eF : s.2 = F := Option.some.inj hF
  obtain ⟨_, _, b3, b4, _, _, _, b8⟩ := OnBytes.PscRun.hide_ok _ _ _ _ _ hsz h2
  rw [← eF] at ho
  refine ⟨⟨b4, by rw [h1]; exact hap⟩, s'.2, rfl, ?_, ?_⟩
  · rw [← eF]
    exact OnBytes.PscRun.hide_keeps h2
  · exact ⟨by rw [b3.next]; exact ho.1,
      fun j x y hf => ho.2 j x y ((b8 j (by omega)).2.2.1 hf)⟩

/-- **The promise is met**, at a record at which the stretch is owed and the write returns. -/
theorem late_writer_meets (a n : Nat) :
    ∃ s s' : Nat × Fork, LateApart a n s ∧ SlotsOwed s.2 a n ∧ lateWriter s s' := by
  have hj : a + n < (owedLedger a (n + 1)).ns := by
    show a + n < a + (n + 1)
    omega
  obtain ⟨G, hG⟩ : ∃ G, (owedLedger a (n + 1)).hide (a + n) zeroE (subE zeroE oneE) = some G :=
    ⟨_, OnBytes.PscRun.hide_returns (F := owedLedger a (n + 1)) (j := a + n) zeroE
      (subE zeroE oneE) (owedLedger_sized a (n + 1)).2.2 hj (owedLedger_free a (n + 1) (a + n))⟩
  refine ⟨(a + n, owedLedger a (n + 1)), (a + n, G),
    ⟨owedLedger_sized a (n + 1), Or.inr (Nat.le_refl _)⟩,
    ⟨?_, fun j _ _ => owedLedger_free a (n + 1) j⟩, rfl, hG⟩
  show a + n ≤ a + (n + 1)
  omega

/-- A hearing that takes m slots and lays their first number into the record. -/
def lateHearer (m : Nat) : Nat × Fork → Nat × Fork → Prop :=
  fun s s' => s'.1 = s.2.next ∧ s'.2 = OnBytes.PscRun.took s.2 m

/-- **The hearing has the law under the same promise**: it hands the promise on by the stretch's own
bound. -/
theorem late_hearer_keeps_under (a n m : Nat) :
    StepKeepsUnder (LateApart a n) (fun s : Nat × Fork => some s.2) a n (lateHearer m) := by
  intro s s' F hI hr hF ho
  obtain ⟨hsz, _⟩ := hI
  obtain ⟨h1, h2⟩ := hr
  have eF : s.2 = F := Option.some.inj hF
  rw [← eF] at ho
  refine ⟨⟨by rw [h2]; exact OnBytes.PscRun.took_sized m hsz, Or.inr (by rw [h1]; exact ho.1)⟩,
    s'.2, rfl, ?_, ?_⟩
  · rw [← eF, h2]
    exact OnBytes.PscRun.took_later s.2 m
  · rw [h2]
    exact ⟨Nat.le_trans ho.1 (Nat.le_add_right _ _), ho.2⟩

/-- **A step that lays the stretch's own first slot as the address does not hand the promise
on.** -/
theorem late_mover_fails (a n : Nat) (hn : 1 ≤ n) :
    ¬ StepKeepsUnder (LateApart a n) (fun s : Nat × Fork => some s.2) a n
      (fun s s' => s' = (a, s.2)) := by
  intro H
  obtain ⟨⟨_, hap⟩, _⟩ := H (a + n, owedLedger a n) (a, owedLedger a n) (owedLedger a n)
    ⟨owedLedger_sized a n, Or.inr (Nat.le_refl _)⟩ rfl rfl
    ⟨Nat.le_refl _, fun j _ _ => owedLedger_free a n j⟩
  have hap' : a < a ∨ a + n ≤ a := hap
  omega

/-- A ledger of a + n + 1 slots, a + n of them taken, none filled. -/
def lateLedger (a n : Nat) : Fork := { (({} : Fork).slots (a + n + 1)) with next := a + n }

/-- **A walk of two steps under the promise**: the hearing takes a slot, the write fills it, and the
stretch is still owed. -/
theorem late_pair_walks (a n : Nat) :
    ∃ s s' : Nat × Fork, LateApart a n s ∧ SlotsOwed s.2 a n ∧
      Walked [lateHearer 1, lateWriter] 2 s s' ∧ OnBytes.PscRun.Filled s'.2 (a + n) ∧
      SlotsOwed s'.2 a n := by
  have hfree : ∀ j, ¬ OnBytes.PscRun.Filled (lateLedger a n) j :=
    fun j => OnBytes.PscRun.freeAbove_slots (a + n + 1) j (Nat.zero_le _)
  have hsz : OnBytes.PscRun.Sized (lateLedger a n) :=
    OnBytes.PscRun.slots_sized ({} : Fork) (a + n + 1)
  have ho : SlotsOwed (lateLedger a n) a n := ⟨Nat.le_refl _, fun j _ _ => hfree j⟩
  have hI : LateApart a n (a + n, lateLedger a n) := ⟨hsz, Or.inr (Nat.le_refl _)⟩
  obtain ⟨G, hG⟩ : ∃ G, (OnBytes.PscRun.took (lateLedger a n) 1).hide (a + n) zeroE
      (subE zeroE oneE) = some G :=
    ⟨_, OnBytes.PscRun.hide_returns (F := OnBytes.PscRun.took (lateLedger a n) 1) (j := a + n) zeroE
      (subE zeroE oneE) hsz.2.2 (Nat.lt_succ_self (a + n)) (hfree (a + n))⟩
  have hw : Walked [lateHearer 1, lateWriter] 2 (a + n, lateLedger a n) (a + n, G) :=
    ⟨lateHearer 1, by simp, (a + n, OnBytes.PscRun.took (lateLedger a n) 1), ⟨rfl, rfl⟩,
      lateWriter, by simp, (a + n, G), ⟨rfl, hG⟩, rfl⟩
  have hk : ∀ r ∈ [lateHearer 1, lateWriter],
      StepKeepsUnder (LateApart a n) (fun s : Nat × Fork => some s.2) a n r := by
    intro r hr
    rcases List.mem_cons.1 hr with e | hr'
    · rw [e]
      exact late_hearer_keeps_under a n 1
    · rw [List.mem_singleton.1 hr']
      exact late_writer_keeps_under a n
  obtain ⟨_, F', e, _, o⟩ := walked_keeps_under hk 2 _ _ _ hI hw rfl ho
  have e' : G = F' := Option.some.inj e
  rw [← e'] at o
  exact ⟨_, _, hI, ho, hw,
    (OnBytes.PscRun.hide_ok _ G _ _ _ (OnBytes.PscRun.took_sized 1 hsz) hG).2.2.2.2.1, o⟩

end VerifiableInference.Desc.Part

