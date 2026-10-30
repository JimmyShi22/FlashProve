-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameFieldsBack.lean: THE EIGHT SENTENCES, ONE A FIELD OF THE MEANING, AT THE
COMPOSED MEANING ITSELF (`mgAll 𝔇 Mg`, Johnson/Desc/Sound/MgAll.lean): `FieldsBack`
(Johnson/Desc/Sound/ItemsRide.lean) over the relation that the frame's ties hand to their payer
(`StepRel`, FrameItemsBack.lean), at the frame's steps: the chain's front and "laid", which leave
the verifier's state as it is, and an accepting "cleared".

What is said.
  `SameRead s t`: what the eight sentences read of the verifier's state in front (s) is what they
    read behind (t): no mark; the book; the codes; the groups; the oracle messages but their
    ledgers; every row on the table in front is on the table behind; a claim of the test on the
    table in front stands behind.
  `says_same`, `words_same`, `classRows_same`: what a row says of words, the witness's words and a
    class's rows are functions of that alone.
  `RelReads low R`: what is asked of a relation R between two statements: the committed table's
    cells stay; every column of a tree that has `low` stays; `SameRead`.
  `ParamsRead 𝔇 low R`: WHAT IS ASKED OF 𝔇's PARAMETERS, FOUR NAMED PREMISES: over R the reader of
    the request (𝔇.H.req), the decoder of the committed table (𝔇.decT) and, at the members of 𝔇.ms
    in a tree that has `low`, the reader of the OOD samples (𝔇.smp) answer alike at the two
    statements; the carried word's sentence (𝔇.cr1, a parameter with the field's very type) goes
    back.
  `ownAt X`: the parts of which nothing is said: "every digit lies in the digits' table", and
    every part at the output head's segment (there the sentence is a parameter).
  `fieldsBack_mgAll`: **`FieldsBack (mgAll 𝔇 Mg) (ownAt X) low R` from `RelReads`, `ParamsRead`.**
  `fieldsBack_same`: at a step that leaves the state ONE premise is left: 𝔇.cr1 goes back.
  `fieldsBack_front`, `fieldsBack_laid`: so at the yes of the chain's front and of "laid".
  `sameRead_cleared`: an accepting "cleared" (`clearWith`, at whatever counts) gives `SameRead`.
  `fieldsBack_cleared`: so at "cleared" `ParamsRead` is left.
  `clearedRec_not_sameRead`: `ClearedRec` alone does not give `SameRead`: two states.
  `Kept s t`, `ReadKept 𝔇 base`: THREE OF THE FOUR AS SENTENCES ON THE PARAMETERS ALONE: each reads
    of the verifier's state nothing but what "cleared" keeps. `CarryBack`: the fourth, over the
    step's own relation. `readKept_made`: `ReadKept` can be met (made-up parameters).
    `not_readKept_pile`: it can fail.
  `fieldsBack_cleared_kept`, `fieldsBack_clear_row`: **`FieldsBack` at the yes of every "cleared",
    and of the "cleared" of a row of `framesOf`, under `ReadKept` and `CarryBack`.**

Limits. `ParamsRead`, `ReadKept` and `CarryBack` are premises on parameters that are letters:
they are owed by whoever fills 𝔇; THAT ANY REAL FILLING HAS THEM IS NOT SHOWN HERE.
Nothing is said of the parts that `ownAt X` names, nor of the seven fields that an item with a part
of a segment of its own reads. The step's own yes is spent at "cleared" (a fork is open in front):
the rows on the table are read through where the state stands. It goes backward, from the statement
behind to the one in front. No soundness statement.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.ConstrRides
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Top.H0.Walk.FrameItemsBack
import Johnson.Top.H0.Walk.FrameTiedRec
import Johnson.Top.H0.Walk.FrameRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open OnBytes.Means (Words Says AllSay value onTable tableSize)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Meaning Numbers RowClass classRows)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.K13.Law (linAt RowsTrue WRow rwBook_same)
open VerifiableInference.OnPublicFiles (headLink)

/-! ### what the eight sentences read of the verifier's state -/

/-- **What the eight sentences read of the state in front (s) is what they read behind (t).** -/
structure SameRead (s t : S) : Prop where
  mark : t.failed = none → s.failed = none
  book : t.book = s.book
  codes : t.st.codes = s.st.codes
  groups : t.st.groups = s.st.groups
  size : t.st.oracles.size = s.st.oracles.size
  /-- the oracle messages but their ledgers -/
  msgs : ∀ i : Nat, (t.st.oracles[i]?).map (fun (x : Oracle) => { x with ledger := none }) =
    (s.st.oracles[i]?).map fun (x : Oracle) => { x with ledger := none }
  /-- every row on the table in front is on the table behind -/
  rows : ∀ r ∈ s.rows, r ∈ t.rows
  /-- a claim of the test on the table in front stands behind -/
  lin : ∀ l, linAt s = some l → linAt t = some l

theorem SameRead.refl (s : S) : SameRead s s :=
  ⟨id, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ h => h, fun _ h => h⟩

theorem SameRead.shape {s t : S} (h : SameRead s t) (o : Nat) :
    (t.st.oracles[o]?).map (fun a : Oracle => a.shape) =
      (s.st.oracles[o]?).map (fun a : Oracle => a.shape) := by
  have h1 := congrArg (Option.map fun a : Oracle => a.shape) (h.msgs o)
  rw [Option.map_map, Option.map_map] at h1
  exact h1

theorem SameRead.samples {s t : S} (h : SameRead s t) (o : Nat) :
    (t.st.oracles[o]?).map (fun a : Oracle => a.sampleRows.toList) =
      (s.st.oracles[o]?).map (fun a : Oracle => a.sampleRows.toList) := by
  have h1 := congrArg (Option.map fun a : Oracle => a.sampleRows.toList) (h.msgs o)
  rw [Option.map_map, Option.map_map] at h1
  exact h1

/-- A table's size hangs on the message's shape and the code table alone. -/
theorem tableSize_same {st st' : Statement} (o : Nat) (part : OnBytes.Part)
    (hcs : st'.codes = st.codes)
    (h : (st'.oracles[o]?).map (fun a : Oracle => a.shape) =
      (st.oracles[o]?).map (fun a : Oracle => a.shape)) :
    tableSize st' o part = tableSize st o part := by
  unfold tableSize Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  rw [hcs]
  cases h1 : st.oracles[o]? with
  | none =>
    rw [h1, Option.map_none, Option.map_eq_none_iff] at h
    rw [h]
  | some a =>
    rw [h1, Option.map_some] at h
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 h
    rw [hb]
    simp only [e]

/-- What a row says of words reads of the statement the code table, the number of the oracle
messages and their shapes alone. -/
theorem says_same {K : Type} [CommRing K] (ρ : Reading K) {st st' : Statement}
    (hcs : st'.codes = st.codes) (hsz : st'.oracles.size = st.oracles.size)
    (hsh : ∀ o : Nat, (st'.oracles[o]?).map (fun a : Oracle => a.shape) =
      (st.oracles[o]?).map (fun a : Oracle => a.shape)) (r : Row) (m : Words K) :
    Says ρ st' r m ↔ Says ρ st r m := by
  have e : value ρ st' r m = value ρ st r m := by
    unfold value onTable
    rw [hsz]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [tableSize_same o .main hcs (hsh o), tableSize_same o .mask hcs (hsh o)]
  unfold Says
  rw [e]

/-- The witness's words, read through the book in the verifier's state. -/
theorem words_same {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) {s t : S} (h : SameRead s t)
    (w : VerifiableInference.Desc.Wit Cells Tok MsgT) :
    wordsFirst arr t.st t.book w = wordsFirst arr s.st s.book w := by
  funext o part i
  unfold wordsFirst
  rw [h.book]
  exact wordsBy_congr arr _ _ s.st t.st w o o h.codes rfl (h.shape o) part i

/-- The rows of a class of a segment, as they lie in the verifier's state. -/
theorem classRows_same (N : Numbers) (m : Nat) (c : RowClass) {s t : S} (h : SameRead s t) :
    classRows N m c t = classRows N m c s := by
  cases c <;> simp only [classRows, h.size, h.book, h.groups, h.samples]

/-! ### the eight sentences at the composed meaning, over a relation that is a letter -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- The parts of a segment's relation of which nothing is said here. -/
def ownAt (X : OnBytes.Model.Verify.Public) : Nat → VerifiableInference.Desc.First.Part → Bool :=
  fun m p => p == .lookDigits || m == headLink X

/-- **What is asked of the relation between the two statements.** -/
structure RelReads (low : Nat → Prop) (R : P × S → Strs → P × S → Strs → Prop) : Prop where
  cell : ∀ a y b y', R a y b y' → ∀ x, y'.cell x = y.cell x
  col : ∀ a y b y', R a y b y' → ∀ j, low j → ∀ x, y'.col j x = y.col j x
  state : ∀ a y b y', R a y b y' → SameRead a.2 b.2

/-- **What is asked of the composed meaning's parameters.** -/
structure ParamsRead (low : Nat → Prop) (R : P × S → Strs → P × S → Strs → Prop) : Prop where
  /-- the reader of the request answers alike at the two statements -/
  req : ∀ a y b y', R a y b y' → 𝔇.H.req a = 𝔇.H.req b
  /-- the decoder of the committed table answers alike -/
  dec : ∀ a y b y', R a y b y' → ∀ c, 𝔇.decT c a = 𝔇.decT c b
  /-- the reader of the OOD samples answers alike, at the members in a tree that has `low` -/
  smp : ∀ a y b y', R a y b y' → ∀ x ∈ 𝔇.ms, low (x.1.seat x.2).1 →
    𝔇.smp a x.1 x.2 = 𝔇.smp b x.1 x.2
  /-- the carried word's sentence, a parameter, goes back -/
  carry : ∀ m, GoesBack R (𝔇.cr1 m)

/-- **THE EIGHT SENTENCES AT THE COMPOSED MEANING.** -/
theorem fieldsBack_mgAll (low : Nat → Prop) (R : P × S → Strs → P × S → Strs → Prop)
    (hR : RelReads low R) (hP : ParamsRead 𝔇 low R) :
    FieldsBack (mgAll 𝔇 Mg) (ownAt X) low R where
  constr m p ho := by
    rw [mgAll_constr]
    have h1 : p ≠ .lookDigits := by
      intro e
      subst e
      simp [ownAt] at ho
    have h2 : m ≠ headLink X := by
      intro e
      subst e
      simp [ownAt] at ho
    refine constrQAt_back (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart m p h1 h2
      R (fun a y b y' h => hP.req a y b y' h) fun a y b y' h => ?_
    show 𝔇.decT y.cell a = 𝔇.decT y'.cell b
    rw [show y'.cell = y.cell from funext (hR.cell a y b y' h)]
    exact hP.dec a y b y' h _
  pin j t hj := by
    rw [mgAll_pin]
    intro a y b y' w h hp
    have hp' := pinJT_col 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms j t b y' y w
      (fun x => (hR.col a y b y' h j hj x).symm) hp
    refine ⟨hp'.1, fun x hx hs => ?_⟩
    obtain ⟨z, hz, h2, h3⟩ := hp'.2 x hx hs
    have hs' : x.1.seat x.2 = (j, t) := hs
    refine ⟨z, ?_, h2, h3⟩
    show 𝔇.smp a x.1 x.2 = some z
    rw [hP.smp a y b y' h x hx (by rw [hs']; exact hj)]
    exact hz
  pinW := by
    rw [mgAll_pinW]
    intro a y b y' w h hp
    show 𝔇.decT y.cell a = some w.cells
    rw [hP.dec a y b y' h, ← show y'.cell = y.cell from funext (hR.cell a y b y' h)]
    exact hp
  row m c := by
    rw [mgAll_row]
    intro a y b y' w h hp
    have hS := hR.state a y b y' h
    have hp' : AllSay OnBytes.Slice.rdE b.2.st (classRows 𝔇.N m c b.2)
        (wordsFirst 𝔇.arr b.2.st b.2.book w) := hp
    rw [classRows_same 𝔇.N m c hS, words_same 𝔇.arr hS w] at hp'
    show AllSay OnBytes.Slice.rdE a.2.st (classRows 𝔇.N m c a.2)
      (wordsFirst 𝔇.arr a.2.st a.2.book w)
    exact fun r hr => (says_same _ hS.codes hS.size hS.shape r _).1 (hp' r hr)
  carry m := by
    rw [mgAll_carry]
    exact hP.carry m
  pile := by
    rw [mgAll_pile]
    intro a y b y' w h hp
    have hS := hR.state a y b y' h
    have hp' : RowsTrue (𝔇.rw13 b) b.2 w := hp
    have e : 𝔇.rw13 b w = 𝔇.rw13 a w := rwBook_same 𝔇.arr 𝔇.mat13 a b hS.book hS.codes hS.shape w
    show RowsTrue (𝔇.rw13 a) a.2 w
    intro r hr
    have h1 := hp' r (hS.rows r hr)
    rw [e] at h1
    exact h1
  pileOne := by
    rw [mgAll_pileOne]
    intro a y b y' w h hp
    have hS := hR.state a y b y' h
    have hp' : RowsTrue (𝔇.rw13 b) b.2 w := hp
    have e : 𝔇.rw13 b w = 𝔇.rw13 a w := rwBook_same 𝔇.arr 𝔇.mat13 a b hS.book hS.codes hS.shape w
    show RowsTrue (𝔇.rw13 a) a.2 w
    intro r hr
    have h1 := hp' r (hS.rows r hr)
    rw [e] at h1
    exact h1
  wrow := by
    rw [mgAll_wrow]
    intro a y b y' w h hp
    have hS := hR.state a y b y' h
    have hp' : WRow 𝔇.P13 b.2 (𝔇.rdW b w) := hp
    have e : 𝔇.rdW b w = 𝔇.rdW a w := words_same 𝔇.arr hS w
    show WRow 𝔇.P13 a.2 (𝔇.rdW a w)
    intro l r hl hr
    have h1 := hp' l r (hS.lin l hl) (by rw [hS.codes]; exact hr)
    rw [e] at h1
    exact (says_same _ hS.codes hS.size hS.shape r _).1 h1
  mark a y b y' h := (hR.state a y b y' h).mark

/-! ### at the relation that the frame's ties hand to their payer -/

/-- `StepRel` has what is asked of the relation, where the step gives `SameRead`. -/
theorem relReads_step (rel : S → S → Prop) (base : Nat) (In : P × S → Strs → Prop)
    (h : ∀ s t, rel s t → SameRead s t) :
    RelReads (fun j => j < base) (StepRel rel base In) where
  cell _ _ _ _ h' := h'.2.2.1.1
  col _ _ _ _ h' j hj x := h'.2.2.1.2 j x hj
  state _ _ _ _ h' := h _ _ h'.2.1

/-- **At a step that leaves the verifier's state**: one premise. -/
theorem fieldsBack_same (rel : S → S → Prop) (hrel : ∀ s t, rel s t → t = s) (base : Nat)
    (In : P × S → Strs → Prop) (hc : ∀ m, GoesBack (StepRel rel base In) (𝔇.cr1 m)) :
    FieldsBack (mgAll 𝔇 Mg) (ownAt X) (fun j => j < base) (StepRel rel base In) := by
  have hb : ∀ (a : P × S) (y : Strs) (b : P × S) (y' : Strs),
      StepRel rel base In a y b y' → b = a := fun a y b y' h => Prod.ext h.1 (hrel _ _ h.2.1)
  refine fieldsBack_mgAll 𝔇 Mg _ _
    (relReads_step _ base In fun s t e => by rw [hrel s t e]; exact SameRead.refl s)
    ⟨?_, ?_, ?_, hc⟩
  · intro a y b y' h
    rw [hb a y b y' h]
  · intro a y b y' h c
    rw [hb a y b y' h]
  · intro a y b y' h x _ _
    rw [hb a y b y' h]

/-- The chain's front: the sub-protocol that asks nothing. -/
theorem fieldsBack_front (base : Nat) (In : P × S → Strs → Prop)
    (hc : ∀ m, GoesBack (StepRel (Yes .ok) base In) (𝔇.cr1 m)) :
    FieldsBack (mgAll 𝔇 Mg) (ownAt X) (fun j => j < base) (StepRel (Yes .ok) base In) :=
  fieldsBack_same 𝔇 Mg _ (fun _ _ h => (Except.ok.inj h).symm) base In hc

/-- "link m: laid". -/
theorem fieldsBack_laid (m : Nat) (base : Nat) (In : P × S → Strs → Prop)
    (hc : ∀ k, GoesBack (StepRel (Yes (layFront m)) base In) (𝔇.cr1 k)) :
    FieldsBack (mgAll 𝔇 Mg) (ownAt X) (fun j => j < base) (StepRel (Yes (layFront m)) base In) :=
  fieldsBack_same 𝔇 Mg _ (fun s t h => (laidAdds m s t h).1) base In hc

/-! ### «cleared» -/

/-- In front of an accepting "cleared" a fork is open. -/
theorem fork_of_clear {L : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : RowFn} {s t : S}
    (h : clearWith L counts left row s = .ok t) : ∃ F, s.fork? = some F := by
  unfold clearWith at h
  split at h
  · rename_i C F h1 h2
    exact ⟨F, h2⟩
  · cases h

/-- Where a fork is open the rows on the table are the pile, and no claim of the test on the table
stands. -/
theorem pile_of_fork {s : S} {F : Fork} (h : s.fork? = some F) :
    s.rows = s.out.pending ∧ linAt s = none := by
  cases hh : s.here <;> simp [S.fork?, S.rows, linAt, hh] at h ⊢

/-- Between two links the rows on the table are the pile. -/
theorem pile_of_between {t : S} (h : t.atBetween = true) : t.rows = t.out.pending := by
  cases hh : t.here <;> simp [S.atBetween, S.rows, hh] at h ⊢

/-- **An accepting "cleared" gives `SameRead`.** -/
theorem sameRead_cleared (L : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (s t : S)
    (h : clearWith L counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    SameRead s t := by
  obtain ⟨hb, -, -, hbook, -, -, hfail, -, hcodes, hgroups, hsize, hmsgs, -, -, hF, hT⟩ :=
    clearedGives L counts left lay lin s t h
  obtain ⟨F, hfork⟩ := fork_of_clear h
  obtain ⟨hrows, hlin⟩ := pile_of_fork hfork
  refine ⟨fun e => by rw [← hfail]; exact e, hbook, hcodes, hgroups, hsize, hmsgs, ?_, ?_⟩
  · intro r hr
    rw [hrows] at hr
    rw [pile_of_between hb]
    cases hv : L.fv with
    | false =>
      rw [(hF hv).1]
      exact hr
    | true =>
      obtain ⟨r', -, e⟩ := hT hv
      rw [e]
      exact List.mem_append_left _ hr
  · intro l hl
    rw [hlin] at hl
    cases hl

/-- **At an accepting "cleared"**: what is asked of the parameters is left. -/
theorem fieldsBack_cleared (L : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (base : Nat)
    (In : P × S → Strs → Prop)
    (hP : ParamsRead 𝔇 (fun j => j < base) (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In)) :
    FieldsBack (mgAll 𝔇 Mg) (ownAt X) (fun j => j < base) (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In) :=
  fieldsBack_mgAll 𝔇 Mg _ _
    (relReads_step _ base In fun s t h => sameRead_cleared L counts left lay lin s t h) hP

/-- **`ClearedRec` alone does not give `SameRead`**: it says nothing of where the state in front
stands. At a state in front that stands at the chain's end, with a claim of the test on the table
and an empty pile: the row read off the claim is on the table in front and not behind. -/
theorem clearedRec_not_sameRead (L : LinkPub) (hv : L.fv = false) (left : S → Option WsForkOut)
    (lay : WsLay) (lin : Params.LinShape) (s₀ : S) (l : LinFirst) :
    ∃ s t, ClearedRec L left lay lin s t ∧ ¬ SameRead s t := by
  refine ⟨{ s₀ with here := .mem ⟨#[], #[], some l⟩, out := { s₀.out with pending := [] } },
    { s₀ with here := .between, out := { s₀.out with pending := [] } },
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl,
      fun _ => ⟨rfl, rfl⟩, fun h => by rw [hv] at h; cases h⟩, fun H => ?_⟩
  have h1 := H.rows (VerifiableInference.Desc.First.rowOfClaim l.claim) (by simp [S.rows])
  simp [S.rows] at h1

/-! ### the premises as sentences on the parameters alone -/

/-- **What an accepting "cleared" keeps of the verifier's state.** -/
structure Kept (s t : S) : Prop where
  live : t.live = s.live
  book : t.book = s.book
  roots : t.roots = s.roots
  rowsOwed : t.rowsOwed = s.rowsOwed
  failed : t.failed = s.failed
  req : t.req = s.req
  codes : t.st.codes = s.st.codes
  groups : t.st.groups = s.st.groups
  size : t.st.oracles.size = s.st.oracles.size
  /-- the oracle messages but their ledgers -/
  msgs : ∀ i : Nat, (t.st.oracles[i]?).map (fun (x : Oracle) => { x with ledger := none }) =
    (s.st.oracles[i]?).map fun (x : Oracle) => { x with ledger := none }
  reply : t.out.reply = s.out.reply
  indexMasks : t.out.indexMasks = s.out.indexMasks

theorem Kept.refl (s : S) : Kept s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩

theorem kept_cleared (L : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (s t : S)
    (h : clearWith L counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    Kept s t := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -⟩ :=
    clearedGives L counts left lay lin s t h
  exact ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- **THREE SENTENCES ON 𝔇's PARAMETERS ALONE: each reads of the verifier's state nothing but what
"cleared" keeps** (so: of the statement's oracle messages all but their ledgers; not the pile; not
where the chain stands). No step, no link and no promise is named. -/
structure ReadKept (base : Nat) : Prop where
  req : ∀ p s t, Kept s t → 𝔇.H.req (p, s) = 𝔇.H.req (p, t)
  dec : ∀ p s t c, Kept s t → 𝔇.decT c (p, s) = 𝔇.decT c (p, t)
  smp : ∀ p s t, Kept s t → ∀ x ∈ 𝔇.ms, (x.1.seat x.2).1 < base →
    𝔇.smp (p, s) x.1 x.2 = 𝔇.smp (p, t) x.1 x.2

/-- The fourth premise: the carried word's sentence goes back over the step's own relation. (NOT
asked over every pair that `Kept` relates: a filling of 𝔇.cr1 may read where the chain stands.) -/
def CarryBack (rel : S → S → Prop) (base : Nat) (In : P × S → Strs → Prop) : Prop :=
  ∀ m, GoesBack (StepRel rel base In) (𝔇.cr1 m)

theorem paramsRead_of_kept (rel : S → S → Prop) (hrel : ∀ s t, rel s t → Kept s t) (base : Nat)
    (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base) (hc : CarryBack 𝔇 rel base In) :
    ParamsRead 𝔇 (fun j => j < base) (StepRel rel base In) where
  req a y b y' h := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    exact H.req p' s t (hrel _ _ h.2.1)
  dec a y b y' h c := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    exact H.dec p' s t c (hrel _ _ h.2.1)
  smp a y b y' h x hx hl := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    exact H.smp p' s t (hrel _ _ h.2.1) x hx hl
  carry := hc

/-- **`ReadKept` can be met**: at made-up parameters that read nothing of the state. It says nothing
of any real filling. -/
theorem readKept_made (s₀ : S) (base : Nat) :
    ReadKept { 𝔇 with
      smp := fun _ _ _ => none
      decT := fun _ _ => none
      H := { 𝔇.H with req := fun a => 𝔇.H.req (a.1, s₀) } } base :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- **It can fail**: at a decoder of the committed table that reads the pile. -/
theorem not_readKept_pile (p : P) (s₀ : S) (r : TensorRow) (M : CellsQ rows cols) (base : Nat) :
    ¬ ReadKept { 𝔇 with
      decT := fun _ a => if a.2.out.pending = [] then some M else none } base := fun H => by
  have h1 := H.dec p { s₀ with out := { s₀.out with pending := [] } }
    { s₀ with out := { s₀.out with pending := [r] } } (fun _ => none)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  simp at h1

/-- **At an accepting "cleared", under `ReadKept` and `CarryBack`.** -/
theorem fieldsBack_cleared_kept (L : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (base : Nat)
    (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base)
    (hc : CarryBack 𝔇 (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In) :
    FieldsBack (mgAll 𝔇 Mg) (ownAt X) (fun j => j < base) (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In) :=
  fieldsBack_cleared 𝔇 Mg L counts left lay lin base In
    (paramsRead_of_kept 𝔇 _ (fun s t h => kept_cleared L counts left lay lin s t h) base In H hc)

/-- **At the "cleared" of a row of the frame's own list** (`framesOf`, FrameLot.lean). -/
theorem fieldsBack_clear_row {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List Seat.LinkFrame} {f : Seat.LinkFrame} {l : Nat}
    (h : Seat.framesOf built first W = .ok fs) (hf : fs[l]? = some f) (base : Nat)
    (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base) (hc : CarryBack 𝔇 (Yes f.clear) base In) :
    FieldsBack (mgAll 𝔇 Mg) (ownAt X) (fun j => j < base) (StepRel (Yes f.clear) base In) := by
  obtain ⟨L, counts, left, e⟩ : ∃ L counts left,
      f.clear = clearWith L counts left (Seat.rowOf W first) := by
    rcases Seat.framesOf_arms h hf with ⟨Y, -, -, e⟩ | ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩ |
      ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩ | ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩
    · subst e
      exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, e⟩
    · exact ⟨_, _, _, e⟩
    · exact ⟨_, _, _, e⟩
  rw [e] at hc ⊢
  exact fieldsBack_cleared_kept 𝔇 Mg L counts left W.layers.wsLay first.lin base In H hc

end

#print axioms fieldsBack_mgAll
#print axioms fieldsBack_same
#print axioms fieldsBack_front
#print axioms fieldsBack_laid
#print axioms sameRead_cleared
#print axioms fieldsBack_cleared
#print axioms clearedRec_not_sameRead
#print axioms kept_cleared
#print axioms paramsRead_of_kept
#print axioms readKept_made
#print axioms not_readKept_pile
#print axioms fieldsBack_cleared_kept
#print axioms fieldsBack_clear_row

end Johnson.Desc.First.Walk.Tied
