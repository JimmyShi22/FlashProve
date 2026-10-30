-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerOne.lean: THE FIVE BLOCKS OF A PROOF FILE's SHARED CHAIN THAT SEND
NOTHING ("(rec_gamma)", "LOC", the joinings, "LIN zeta", "SPLIT": blocks 3, 4, 6, 7, 8), AT THE
LEDGER, AT ONE FILLING OF THE TABLE's LETTERS, at blocks that decide as the kind's own, in the wrap
in which a description's pieces hold them. Each is what a kind's files owe at that block (ClauseAt,
Johnson/Desc/Sound/LedgerClause.lean).

THE ONE FILLING. mgI: nearU, recRow, omU as the table's files fill them at "LIN point" (NearAt,
RecAll, OmU at a reader uR of the record) · the rows' classes as slices of the two groups' lists as
they lie in the record ((rec_gamma), (loc_x): RowsUL, said at a statement that has grown out of the
record's; (fold_u), (fold_omega): RowsU, RowsO; (fold): FoldAt) · a message's own sample's rows:
still the letter Mg₀'s. pmI: tablePromise := "the stored table decodes with the record" (decodesOf
decT₂, as the table's files fill it at "LIN point") · shape k := shapeK for 2 ≤ k ≤ 9, else the
letter Pm₀'s · nothingLeft := the end's own test. Around both: the table's files' meaningSigS,
promSigS, extS; in promSigS's slot for the book (a field that stands in no clause of the
promise): bkR ∘ (·.book), bkR an idle letter.
  DecidesAs       a block at another type of claims that decides as one of the kind's eight (over
                  the one base a description holds b.retype); heldW_decide: in the wrap the two
                  decide alike.
  heldW, held_yes the wrap; a yes of a piece that holds heldW b is a yes of b.
  QuietStep       a step onward that leaves the small record, the messages and the book.
  SmpReads, SampleRides   two premises on letters, as named terms; SmpSay, smpSay_rides: a filling
                  that meets the second.
  uRK, uRK_seated, uRK_next   the reader of the record, as a term, with what is asked of it.
  layX, layX_codes, layX_grows   a test beside the book-keeping: o_omega's layout at the record's
                  codes is the plan's; it is handed on wherever the codes stand. besX: it and a
                  letter X. omWK: the witness's Omega as o_omega's words at the plan's layout. codX:
                  an offer: the record's codes are the plan's.
  tab_rides       the stored table's promise rides where the record's key stays.
  other_back      the shared items that are no pins ride back over a quiet step.
  three_at … eight_at   **the five clauses** (three_at, four_at, six_at, seven_at, eight_at).
WHAT STAYS, AND WHOSE. SmpReads (the letter smp₂ reads the record through its messages and its book:
whoever fills smp₂) · hdk (the decoder reads the record's key alone: the table's files' own
premise at "LIN point") · SampleRides (K1's | K12's files) · huR (paid at uRK) · SentBefore
(numbers: the plan's and the tiling's) · the written rounds' data (the plan's) · the members at
o_u's and o_omega's seats.
What is not claimed. NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerEnd
import Johnson.Desc.Sound.LedgerBeside
import Johnson.Desc.K1.Law.LedgerHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription Grows)
open VerifiableInference.Desc.ChainEnd (untestedL)
open VerifiableInference.Desc.K1 (SameMsgs size_of_same)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

/-- The wrap in which a description's pieces hold the shared chain's blocks. -/
abbrev heldW {U Cl : Type} (b : Block St Cl) : Block (U × St) Cl :=
  Block.lift Prod.snd (fun x s => (x.1, s)) (below b)

/-- A block at another type of claims that decides as a block does: so a block carried to a
description's type of claims (Block.retype: by rfl). -/
def DecidesAs {Cl Cl' : Type} (c : Block St Cl) (b : Block St Cl') : Prop :=
  ∀ d rs gs, c.decide d rs gs = b.decide d rs gs

/-- In the wrap the two decide alike. -/
theorem heldW_decide {U Cl Cl' : Type} (c : Block St Cl) (b : Block St Cl') (h : DecidesAs c b)
    (t : U × St) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    (heldW (U := U) c).decide t rs gs = (heldW (U := U) b).decide t rs gs := by
  have e : (below c).decide t.2 rs gs = (below b).decide t.2 rs gs := by
    show (if _ then c.decide t.2 rs gs else _) = (if _ then b.decide t.2 rs gs else _)
    rw [h]
  show ((below c).decide t.2 rs gs).map _ = ((below b).decide t.2 rs gs).map _
  rw [e]

/-- A yes of a piece that holds a block in the wrap is a yes of the block. -/
theorem held_yes {U Cl W : Type} {Fr : Frame} (x : Piece (ckP .two) Fr (U × St) Cl W)
    (b : Block St Cl) (hx : x.b = heldW b) (a : (U × St) × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (c : (U × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some c) : ∃ rs gs, b.decide a.1.2 rs gs = .ok c.1.2 := by
  obtain ⟨_, gs, hd⟩ := piece_yes x a τ c hout
  rw [hx] at hd
  exact ⟨_, gs, (wrap_decide b a.1 c.1 _ gs hd).1⟩

/-- A step onward that leaves the small record, the messages and the book. -/
structure QuietStep (a b : St) : Prop where
  on : Onward a b
  loc : b.loc = a.loc
  msgs : SameMsgs a.st b.st
  book : b.book = a.book

/-- The letter smp₂ reads the record through its messages and its book. -/
def SmpReads {σ : Type} (smp₂ : St → σ) : Prop :=
  ∀ s s' : St, SameMsgs s.st s'.st → s'.book = s.book → smp₂ s' = smp₂ s

/-- The letter for a message's own sample's rows reads the record through the statement's growth and
through that message's shape, mark and sample rows: it rides back where the statement has grown and
these three stay. num: the messages' numbers in the chain's own statement, by the plan. -/
def SampleRides {P₁ Wt : Type} (Mg₀ : MeaningS St P₁ Wt) (num : Msg2 → ℕ) : Prop :=
  ∀ (m : Msg2) (s s' : St) (w : Wt), Grows s.st s'.st →
    (s'.st.oracles[num m]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (s.st.oracles[num m]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) →
    Mg₀.row (.sample m) s' w → Mg₀.row (.sample m) s w

/-- A FILLING THAT MEETS IT: the message is there, and its sample rows, as the record holds them,
    say
their claims of the words at a statement that has grown out of the record's. -/
def SmpSay (o : ℕ) (s : St) (m : Words GE) : Prop :=
  ∃ x T, s.st.oracles[o]? = some x ∧ Grows s.st T ∧
    Means.AllSay OnBytes.Model.Reading.gl T x.sampleRows.toList m

theorem smpSay_rides (o : ℕ) (s s' : St) (m : Words GE) (g : Grows s.st s'.st)
    (e : (s'.st.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (s.st.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)))
    (h : SmpSay o s' m) : SmpSay o s m := by
  obtain ⟨x', T, hx', gT, hs⟩ := h
  rw [hx'] at e
  obtain ⟨x, hx, e'⟩ := Option.map_eq_some_iff.1 e.symm
  have e3 : x.sampleRows = x'.sampleRows := (Prod.mk.inj (Prod.mk.inj e').2).2
  exact ⟨x, T, hx, g.trans gT, by rw [e3]; exact hs⟩

/-- **The reader of the record at which "near", RecRow and "Omega is what u gives" are said**: the
record itself where o_u is seated; else the record with o_u noted as the message to come. -/
def uRK (P : Par) (s : St) : St := if seatedUB P s = true then s else withNext P s

theorem uRK_seated (P : Par) (s : St) (h : seatedUB P s = true) : uRK P s = s := if_pos h

/-- In front of o_u's sending, where the chain's statement has no message yet. -/
theorem uRK_next (P : Par) (s : St) (h : s.st.oracles.size = 0) : uRK P s = withNext P s := by
  refine if_neg fun hs => ?_
  have := noted_of_seatedUB P s hs
  omega

/-- What "Omega is what u gives" reads of the record. -/
theorem omU_of_same {Wt : Type} (P : Par) (uR : St → St) (rg : Wt → Words GE) (omW : Wt → ℕ → GE)
    (s s' : St) (w : Wt) (hp : s'.loc.psiSh = s.loc.psiSh) (hu : (uR s').loc.oU = (uR s).loc.oU)
    (h : OmU P uR rg omW s' w) : OmU P uR rg omW s w := by
  unfold OmU uOf at h ⊢
  rw [hp, hu] at h
  exact h

/-- The four blocks without a sending that leave the small record, at a yes. -/
theorem quiet_at (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.S.sharedSplitNeeded = true) :
    ∀ b ∈ [b3, b4, b6, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' → QuietStep d d' := by
  intro b hb d rs gs d' h
  have hm : b ∈ [b1, b3, b4, b6, b7, b8] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
    tauto
  have h1 := msgs_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS b hm d rs gs d' h
  have h2 := (book_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS b hm d rs gs d' h).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · have k := (quiet_of_blocks Q b1 b2 _ b4 b5 b6 b7 b8 hbl).1 d rs gs d' h
    exact ⟨(onward_laysRec _ d d' rs k).1, (onward_laysRec _ d d' rs k).2, h1, h2⟩
  · have k := loc_of_blocks Q b1 b2 b3 _ b5 b6 b7 b8 hbl d rs gs d' h
    obtain ⟨r, cols, rfl, rfl⟩ := loc_one _ _ _ _ _ k
    exact ⟨(onward_loc _ d d' r cols k).1, (onward_loc _ d d' r cols k).2, h1, h2⟩
  · have k := (quiet_of_blocks Q b1 b2 b3 b4 b5 _ b7 b8 hbl).2 d rs gs d' h
    exact ⟨(onward_joins _ d d' rs k).1, (onward_joins _ d d' rs k).2, h1, h2⟩
  · have k := decidesBySplit_of_blocks Q b1 b2 b3 b4 b5 b6 b7 _ hbl d rs gs d' h
    obtain ⟨r, rfl⟩ := split_one _ _ _ _ hS k
    exact ⟨(onward_split _ d d' r hS k).1, (onward_split _ d d' r hS k).2, h1, h2⟩

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
  (bkR : TreeBook → TreeBook)
  (N : NumbersS) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St)
  (Oc : P₁ → Strs → Prop)
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (P : Par) (uR : St → St) (omW : Wit Cells Tok MsgT → ℕ → GE) (e' n nU nO : ℕ) (num : Msg2 → ℕ)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- **The kind's letters of the items' meaning, filled.** -/
def mgI : MeaningS St P₁ (Wit Cells Tok MsgT) :=
  { Mg₀ with
    nearU := fun s y w => NearAt OnBytes.Model.Reading.gl P (uR s) (rgOf cs arr mem rd w)
      (colsOf y.cell) e'
    recRow := fun s w => RecAll OnBytes.Model.Reading.gl P (uR s) (rgOf cs arr mem rd w)
    omU := OmU P uR (rgOf cs arr mem rd) omW
    row := fun c => match c with
      | .recG => fun s w => RowsUL OnBytes.Model.Reading.gl 0 P.S.fold.index.answers s
          (rgOf cs arr mem rd w)
      | .loc => fun s w => RowsUL OnBytes.Model.Reading.gl P.S.fold.index.answers n s
          (rgOf cs arr mem rd w)
      | .fold => fun s w => FoldAt OnBytes.Model.Reading.gl P.S s (rgOf cs arr mem rd w)
      | .foldU => fun s w => RowsU OnBytes.Model.Reading.gl (P.S.fold.index.answers + n) 1 s
          (rgOf cs arr mem rd w)
      | .foldOmega => fun s w => RowsO OnBytes.Model.Reading.gl 0 1 s (rgOf cs arr mem rd w)
      | .sample m => Mg₀.row (.sample m) }

/-- **The kind's letters of the promise's meaning, filled.** -/
def pmI : PromMeaning St :=
  { Pm₀ with
    tablePromise := decodesOf decT₂
    shape := fun k => if 2 ≤ k ∧ k ≤ 9 then shapeK P nU nO n k else Pm₀.shape k
    nothingLeft := fun s => (untestedL s.st).all (·.2) }

/-- The filling's book-keeping between 2 and 9 is shapeK. -/
theorem pmI_shape0 (k : ℕ) (h : 2 ≤ k ∧ k ≤ 9) :
    (pmI decT₂ Pm₀ P n nU nO).shape k = shapeK P nU nO n k := if_pos h

/-- A TEST BESIDE THE BOOK-KEEPING: o_omega's layout at the record's codes is the plan's. (Nothing
    in
shapeK pins the record's codes; "the witness's Omega is read off o_omega's words" wants it.) -/
def layX (Q : P14) : ℕ → St → Bool := fun _ s =>
  decide (linLayOmega s.st.codes Q.par.S = linLayOmega Q.codes Q.par.S)

/-- It is handed on wherever the record's codes stand. -/
theorem layX_codes (Q : P14) (j k : ℕ) (a b : St) (hc : b.st.codes = a.st.codes)
    (h : layX Q j a = true) : layX Q k b = true := by
  unfold layX at h ⊢
  rw [hc]
  exact h

/-- So wherever the statement grows. -/
theorem layX_grows (Q : P14) (j k : ℕ) (a b : St) (g : Grows a.st b.st)
    (h : layX Q j a = true) : layX Q k b = true := layX_codes Q j k a b g.1 h

/-- AN OFFER, LAID NOWHERE HERE: "the record's codes are the plan's", as a test with code. It gives
layX; it is handed on wherever the codes stand. Whoever reads a witness's words at the record's
codes (the tie of the two readers, Johnson/Desc/K14/Law/LedgerReader.lean) lays it beside shapeK
(clause_beside, each_beside). -/
def codX (Q : P14) : ℕ → St → Bool := fun _ s => decide (s.st.codes = Q.codes)

theorem codX_iff (Q : P14) (k : ℕ) (s : St) : codX Q k s = true ↔ s.st.codes = Q.codes :=
  decide_eq_true_iff

theorem codX_codes (Q : P14) (j k : ℕ) (a b : St) (hc : b.st.codes = a.st.codes)
    (h : codX Q j a = true) : codX Q k b = true :=
  (codX_iff Q k b).2 (hc.trans ((codX_iff Q j a).1 h))

theorem layX_of_codX (Q : P14) (j k : ℕ) (s : St) (h : codX Q j s = true) : layX Q k s = true := by
  unfold layX
  rw [(codX_iff Q j s).1 h]
  exact decide_eq_true rfl

/-- **What stands beside shapeK in the promise**, at every border: the layout's test, and A LETTER X
for whatever else of the record another file's clause wants (the book in order, its places, the
groups' members): our clauses hand it on and spend nothing of it. -/
def besX (Q : P14) (X : ℕ → St → Bool) : ℕ → St → Bool := fun k s => layX Q k s && X k s

/-- **The witness's Omega**: o_omega's words, at the plan's number and layout. -/
def omWK (Q : P14) : Wit Cells Tok MsgT → ℕ → GE := fun w y =>
  rgOf cs arr mem rd w nO .main ((linLayOmega Q.codes Q.par.S).index y)

variable (Q : P14)


/-- The stored table's promise rides where the record's key stays. -/
theorem tab_rides (hdk : ∀ c (s s' : St), s'.loc.key = s.loc.key → decT₂ c s' = decT₂ c s)
    (k : ℕ) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (a b : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (hout : x.ior.red.out a τ = some b) (hk : b.1.2.loc.key = a.1.2.loc.key)
    (h : decodesOf decT₂ a.1.2 (strsOfAct Fr ((actQ N p l k).2 a))) :
    decodesOf decT₂ b.1.2 (strsOfAct Fr ((actQ N p l (k + 1)).2 b)) := by
  unfold decodesOf at h ⊢
  rw [← cells_stay N p l k x a b τ hout, hdk _ a.1.2 b.1.2 hk]
  exact h

/-- **The shared items that are no pins ride back over a quiet step**, where o_u is seated and the
rows of "(rec_gamma)" and "LOC" lie in front. -/
theorem other_back (hsr : SampleRides Mg₀ num) (huR : ∀ s, seatedUB P s = true → uR s = s)
    (a b : St) (q : QuietStep a b) (sA : seatedUB P a = true)
    (w : Wit Cells Tok MsgT) :
    ((mgI cs arr Mg₀ mem rd P uR omW e' n).omU b w →
      (mgI cs arr Mg₀ mem rd P uR omW e' n).omU a w) ∧
    (P.S.fold.index.answers ≤ (rowsOn a a.loc.gU).length →
      (mgI cs arr Mg₀ mem rd P uR omW e' n).row .recG b w →
      (mgI cs arr Mg₀ mem rd P uR omW e' n).row .recG a w) ∧
    (P.S.fold.index.answers + n ≤ (rowsOn a a.loc.gU).length →
      (mgI cs arr Mg₀ mem rd P uR omW e' n).row .loc b w →
      (mgI cs arr Mg₀ mem rd P uR omW e' n).row .loc a w) ∧
    ∀ m, (mgI cs arr Mg₀ mem rd P uR omW e' n).row (.sample m) b w →
      (mgI cs arr Mg₀ mem rd P uR omW e' n).row (.sample m) a w := by
  have sB := seatedUB_onward P a b q.on q.loc sA
  refine ⟨fun h => omU_ride P uR _ omW a b w q.loc (huR _ sA) (huR _ sB) h, fun hl h => ?_,
    fun hl h => ?_, fun m h => hsr m a b w q.on.grows (q.msgs.2 _) h⟩
  · exact rowsUL_back OnBytes.Model.Reading.gl 0 P.S.fold.index.answers a b _ q.on
      (by rw [q.loc]) (by rw [Nat.zero_add]; exact hl) h
  · exact rowsUL_back OnBytes.Model.Reading.gl P.S.fold.index.answers n a b _ q.on
      (by rw [q.loc]) hl h

/-- The filling's book-keeping between 2 and 9 is shapeK. -/
theorem pmI_shape (k : ℕ) (h : 2 ≤ k ∧ k ≤ 9) : ((promSigS cs G smp₂ ms (fun s : St => s.st) (fun s
    : St => bkR s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO))).shape k = shapeK Q.par nU nO n k := by
  show (if 2 ≤ k ∧ k ≤ 9 then shapeK Q.par nU nO n k else Pm₀.shape k) = _
  exact if_pos h

theorem smp_of_quiet (hsm : SmpReads smp₂) {a b : St} (q : QuietStep a b) : smp₂ b = smp₂ a :=
  hsm a b q.msgs q.book

/-- What the book-keeping at 6, 7, 8 gives. -/
theorem shapeO_of_on (k : ℕ) (hk : k = 6 ∨ k = 7 ∨ k = 8) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂
        Pm₀ (P14.par Q) n nU nO)) Oc true p l k a) :
    shapeO Q.par nU nO (Q.par.S.fold.index.answers + n) 0 a.1.2 = true := by
  have h1 : ((promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
      (P14.par Q) n nU nO))).shape k a.1.2 = true := ha.1 (.shape k) (by simp [promsAt])
  rw [pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q k (by omega)] at h1
  rcases hk with rfl | rfl | rfl <;> exact h1

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hS : Q.S.sharedSplitNeeded = true)
  (hsm : SmpReads smp₂)
  (hdk : ∀ c (s s' : St), s'.loc.key = s.loc.key → decT₂ c s' = decT₂ c s)
  (hsr : SampleRides Mg₀ num) (huR : ∀ s, seatedUB Q.par s = true → uR s = s)
include hbl hS hsm hdk hsr huR

/-- **"(rec_gamma)": the clause at block 3.** -/
theorem three_at (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (ε : Err (uLT (ckP .two) x.ds)) (c3 : Block St Cl) (h3 : DecidesAs c3 b3) (hx : x.b = heldW c3)
        (hB : SentBefore N p l 3 x .oU) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO)) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N true k v.1
        (strsOfAct Fr v) w) 3 x ε := by
  have hq : ∀ a τ c, x.ior.red.out a τ = some c → QuietStep a.1.2 c.1.2 := fun a τ c hout => by
    obtain ⟨rs, gs, hd⟩ := held_yes x c3 hx a τ c hout
    rw [h3] at hd
    exact quiet_at Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS b3 (by simp) _ rs gs _ hd
  refine rec_filled N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW
      e' n)) (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
      (P14.par Q) n nU nO)) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N true k v.1
      (strsOfAct Fr v) w) Q.par (rgOf cs arr mem rd) uR omW e' nU nO x ε ?_
    (fun v w => extS_id cs G arr smp₂ ms decT₂ c₀ N true 3 rfl _ _ w) huR rfl rfl rfl rfl
    (pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 3 (by decide))
    (pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 4 (by decide)) ?_ ?_ ?_
  · intro t rs gs t' h
    rw [hx] at h
    exact (quiet_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl).1 _ _ gs _ ((h3 _ _ _).symm.trans
        (wrap_decide c3 t t' rs gs h).1)
  · intro c hc a τ b _ hout h
    rcases hc with rfl | rfl
    · exact tab_rides decT₂ N p l hdk 3 x a b τ hout (by rw [(hq a τ b hout).loc]) h
    · exact noColl_rides cs G smp₂ ms _ _ N _ p l 3 x .oU hB a b τ hout
        (fun _ _ => by rw [smp_of_quiet cs smp₂ hsm (hq a τ b hout)]) h
  · exact fun a τ b w _ hout h => pin_rides cs G arr smp₂ ms decT₂ N _ p l 3 x .oU hB a b τ hout
      (fun _ _ => by rw [smp_of_quiet cs smp₂ hsm (hq a τ b hout)]) w h
  · exact fun a τ b w _ hout h => hsr .oU a.1.2 b.1.2 w (hq a τ b hout).on.grows
      ((hq a τ b hout).msgs.2 _) h

/-- **"LOC": the clause at block 4.** -/
theorem four_at (xU : Mem) (hU : mem nU = some xU) (mU : xU ∈ ms)
    (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2) (c4 : Block St Cl) (h4 : DecidesAs c4 b4)
        (base : ℕ) (d : RDT) (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wit Cells
        Tok MsgT → Wit Cells Tok MsgT) (er : Err (uLT (ckP .two) [d])) {ns : ℕ}
    (hd : SendsDraws (toRD d) ns 0 n Q.par.S.fold.index.code.logN) (ho : d.opens = []) (e : ℕ)
    (he : (2 ^ Q.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e)
    (hB : SentBefore N p l 4 (⟨heldW c4, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) .oU) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO)) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N true k v.1
        (strsOfAct Fr v) w) 4 (⟨heldW c4, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      ((posMaps d Q.par.S.fold.index.code.logN n).err ((e, ()) : ℕ × Unit)) := by
  have hq : ∀ a τ c, (⟨heldW c4, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)).ior.red.out a τ = some c →
      QuietStep a.1.2 c.1.2 := fun a τ c hout => by
    obtain ⟨rs, gs, hd⟩ := held_yes (⟨heldW c4, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) c4 rfl a τ c hout
    rw [h4] at hd
    exact quiet_at Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS b4 (by simp) _ rs gs _ hd
  refine loc_filled N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW
      e' n)) (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
      (P14.par Q) n nU nO)) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N true k v.1
      (strsOfAct Fr v) w) Q.par (rgOf cs arr mem rd) uR omW nU nO (heldW c4) base d ex er hd ho e' e
    he ?_ (fun v w => extS_id cs G arr smp₂ ms decT₂ c₀ N true 4 rfl _ _ w) huR rfl rfl rfl rfl
    (pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 4 (by decide))
    (pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 5 (by decide)) ?_ ?_ ?_ ?_
  · intro t rs gs t' h
    exact loc_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ ((h4 _ _ _).symm.trans (wrap_decide
        c4 t t' rs gs h).1)
  · intro c hc a τ b _ hout h
    rcases hc with rfl | rfl
    · exact tab_rides decT₂ N p l hdk 4 (⟨heldW c4, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) a b τ hout (by rw [(hq a τ b
          hout).loc]) h
    · exact noColl_rides cs G smp₂ ms _ _ N _ p l 4 (⟨heldW c4, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) .oU hB a b τ hout
        (fun _ _ => by rw [smp_of_quiet cs smp₂ hsm (hq a τ b hout)]) h
  · exact fun a τ b w _ hout h => pin_rides cs G arr smp₂ ms decT₂ N _ p l 4
      (⟨heldW c4, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) .oU hB a b τ hout
      (fun _ _ => by rw [smp_of_quiet cs smp₂ hsm (hq a τ b hout)]) w h
  · exact fun a w w' _ h h' => agreeOn_of_pinJT cs G arr smp₂ mem rd ms _ _ _ _ w w' nU xU hU mU sU
      h h'
  · exact fun a τ b w _ hout h => hsr .oU a.1.2 b.1.2 w (hq a τ b hout).on.grows
      ((hq a τ b hout).msgs.2 _) h

/-- **The joinings: the clause at block 6.** -/
theorem six_at (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (ε : Err (uLT (ckP .two) x.ds)) (c6 : Block St Cl) (h6c : DecidesAs c6 b6) (hx : x.b = heldW c6)
    (hB : ∀ m, SentBefore N p l 6 x m) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO)) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N true k v.1
        (strsOfAct Fr v) w) 6 x ε := by
  have hq : ∀ a τ c, x.ior.red.out a τ = some c → QuietStep a.1.2 c.1.2 := fun a τ c hout => by
    obtain ⟨rs, gs, hd⟩ := held_yes x c6 hx a τ c hout
    rw [h6c] at hd
    exact quiet_at Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS b6 (by simp) _ rs gs _ hd
  refine joins_filled cs G arr smp₂ ms decT₂ c₀ _ _ N _ _ Oc p l true Q.par nU nO
    (Q.par.S.fold.index.answers + n) 0 x ε ?_ (fun m _ => hB m) (fun m _ => hB m)
    (fun a τ b _ hout => smp_of_quiet cs smp₂ hsm (hq a τ b hout))
    (fun a τ b _ hout h => tab_rides decT₂ N p l hdk 6 x a b τ hout
      (by rw [(hq a τ b hout).loc]) h) ?_
    (pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 6 (by decide))
    (pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 7 (by decide))
  · intro t rs gs t' h
    rw [hx] at h
    exact (quiet_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl).2 _ _ gs _ ((h6c _ _ _).symm.trans
        (wrap_decide c6 t t' rs gs h).1)
  · intro a τ b w i ha hout ho _ hp hm
    have hO := shapeO_of_on cs G smp₂ ms decT₂ bkR N Pm₀ Oc n nU nO p l Q 6 (Or.inl rfl) a ha
    have hUU := (shapeU_iff Q.par nU _ a.1.2).1 ((shapeO_iff Q.par nU nO _ 0 a.1.2).1 hO).1
    obtain ⟨o1, o2, o3, o4⟩ := other_back cs arr Mg₀ mem rd Q.par uR omW e' n num hsr huR a.1.2
        b.1.2
      (hq a τ b hout) hUU.2.1 w
    have h6 : ∀ j ∈ openL (insLSh true) (outsLSh true) startLSh 6, j = ItemS.omU ∨ j = .row .recG ∨
        j = .row .loc ∨ j = .row (.sample .oU) ∨ j = .row (.sample .oOmega) ∨
        j = .row (.sample .oSp) ∨ j = .pin .oU ∨ j = .pin .oOmega ∨ j = .pin .oSp := by decide
    rcases h6 i ((openSh_iff true 6 i).1 ho) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact o1 hm
    · exact o2 (by rw [hUU.2.2.2]; omega) hm
    · exact o3 (by rw [hUU.2.2.2]) hm
    · exact o4 _ hm
    · exact o4 _ hm
    · exact o4 _ hm
    · exact absurd rfl (hp _)
    · exact absurd rfl (hp _)
    · exact absurd rfl (hp _)

/-- **"LIN zeta": the clause at block 7**, at the promise with the layout's test beside the
book-keeping, and at the witness's Omega as o_omega's words. -/
theorem seven_at (X : ℕ → St → Bool)
    (hX7 : ∀ (s : St) z, X 7 s = true → X 8 { s with loc := { s.loc with zFd := z } } = true)
    (homW : omW = omWK cs arr mem rd nO Q) (xU xO : Mem) (hU : mem nU = some xU)
    (hO : mem nO = some xO) (mU : xU ∈ ms)
    (mO : xO ∈ ms) (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
    (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2) (c7 : Block St Cl) (h7 : DecidesAs c7
        b7) (base : ℕ) (d : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er : Err (uLT (ckP .two) [d])) {ns a0 : ℕ} (hd : SendsDraws (toRD d) ns Q.par.S.kRow 0 a0)
    (e : ℕ) (he : Q.par.S.kRow * Fintype.card GE ^ (Q.par.S.kRow - 1) ≤ e)
    (hB : ∀ m, SentBefore N p l 7 (⟨heldW c7, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) m) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
      (besideP (pmI decT₂ Pm₀ Q.par n nU nO) (besX Q X))) Oc true p l (fun k v w => extS cs G arr
          smp₂ ms decT₂ c₀ N true k v.1 (strsOfAct Fr v) w) 7
      (⟨heldW c7, base, [d], [], ex, er⟩ :
        Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      ((vecMaps d Q.par.S.kRow).err ((e, ()) : ℕ × Unit)) := by
  have e7 := pmI_shape0 decT₂ Pm₀ Q.par n nU nO 7 (by decide)
  have e8 := pmI_shape0 decT₂ Pm₀ Q.par n nU nO 8 (by decide)
  have hsh : ∀ x, onQ₂ N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
      (besideP (pmI decT₂ Pm₀ Q.par n nU nO) (besX Q X))) Oc true p l 7 x →
      shapeO Q.par nU nO (Q.par.S.fold.index.answers + n) 0 x.1.2 = true ∧
        layX Q 7 x.1.2 = true := by
    intro x hx
    have h1 : ((pmI decT₂ Pm₀ Q.par n nU nO).shape 7 x.1.2 && (layX Q 7 x.1.2 && X 7 x.1.2)) = true
        :=
      hx.1 (.shape 7) (by simp [promsAt])
    rw [e7] at h1
    exact ⟨(Bool.and_eq_true_iff.1 h1).1,
      (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h1).2).1⟩
  refine zeta_at_sig cs G arr smp₂ ms decT₂ c₀ _ _ N _ _ Oc true p l Q.par.S mem rd nU nO xU xO hU
      hO
    mU mO sU sO (heldW c7) base d ex er hd e he
    (zeta_wrapped Q b1 b2 b3 b4 b5 b6 b7 b8 hbl c7 h7) (fun m _ => hB m)
    (fun m _ => hB m) (fun s z => hsm s _ (same_refl _) rfl) ?_
    (fun _ _ _ h => h) ?_ ?_ ?_ ?_
  · intro x w hx h
    obtain ⟨hs, hl⟩ := hsh x hx
    obtain ⟨hsU, _, eO, _⟩ := (shapeO_iff Q.par nU nO _ 0 x.1.2).1 hs
    have hseat := ((shapeU_iff Q.par nU _ x.1.2).1 hsU).2.1
    show OmU Q.par uR (rgOf cs arr mem rd) omW x.1.2 w
    intro y hy
    have h0 := h y hy
    unfold omegaOf at h0
    rw [eO, of_decide_eq_true hl] at h0
    rw [huR x.1.2 hseat, homW]
    exact h0
  · intro x hx
    obtain ⟨hsU, _, eO, _⟩ := (shapeO_iff Q.par nU nO _ 0 x.1.2).1 (hsh x hx).1
    exact ⟨((shapeU_iff Q.par nU _ x.1.2).1 hsU).2.2.1, eO⟩
  · intro s z h
    have h' : ((pmI decT₂ Pm₀ Q.par n nU nO).shape 7 s && (layX Q 7 s && X 7 s)) = true := h
    show ((pmI decT₂ Pm₀ Q.par n nU nO).shape 8 _ && (layX Q 8 _ && X 8 _)) = true
    rw [e7] at h'
    rw [e8]
    obtain ⟨a1, a2⟩ := Bool.and_eq_true_iff.1 h'
    obtain ⟨a3, a4⟩ := Bool.and_eq_true_iff.1 a2
    exact Bool.and_eq_true_iff.2 ⟨a1, Bool.and_eq_true_iff.2 ⟨a3, hX7 s z a4⟩⟩
  · intro s z y y' hc h
    have h' : decodesOf decT₂ s y := h
    show decodesOf decT₂ _ y'
    unfold decodesOf at h' ⊢
    rw [hc, hdk y.cell s { s with loc := { s.loc with zFd := z } } rfl]
    exact h'
  · intro x τ y w i _ hout ho hi hp hm
    obtain ⟨c, rfl, hc⟩ := open7_other true i ho hi hp
    obtain ⟨rs, gs, hdd⟩ := held_yes (⟨heldW c7, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) c7 rfl x τ y hout
    rw [h7] at hdd
    have k7 := zeta_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hdd
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k7
    rw [hr] at k7
    have e7' := linZeta_inv x.1.2 y.1.2 r7 k7
    have hm' : (mgI cs arr Mg₀ mem rd Q.par uR omW e' n).row c y.1.2 w := hm
    show (mgI cs arr Mg₀ mem rd Q.par uR omW e' n).row c x.1.2 w
    rw [e7'] at hm'
    cases c with
    | sample m =>
      exact hsr m x.1.2 { x.1.2 with loc := { x.1.2.loc with zFd := drawn r7 } } w (Grows.refl _)
        rfl hm'
    | recG => exact hm'
    | loc => exact hm'
    | fold => exact absurd rfl hc
    | foldU => exact hm'
    | foldOmega => exact hm'

/-- **"SPLIT": the clause at block 8.** -/
theorem eight_at (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (ε : Err (uLT (ckP .two) x.ds)) (c8 : Block St Cl) (h8c : DecidesAs c8 b8) (hx : x.b = heldW c8)
    (hB : ∀ m, SentBefore N p l 8 x m) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO)) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N true k v.1
        (strsOfAct Fr v) w) 8 x ε := by
  have hq : ∀ a τ c, x.ior.red.out a τ = some c → QuietStep a.1.2 c.1.2 := fun a τ c hout => by
    obtain ⟨rs, gs, hd⟩ := held_yes x c8 hx a τ c hout
    rw [h8c] at hd
    exact quiet_at Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS b8 (by simp) _ rs gs _ hd
  refine split_filled cs G arr smp₂ ms decT₂ c₀ _ _ N _ _ Oc p l Q.par (rgOf cs arr mem rd) nU nO
    (Q.par.S.fold.index.answers + n) 0 x ε ?_ (fun m _ => hB m) (fun m _ => hB m)
    (fun a τ b _ hout => smp_of_quiet cs smp₂ hsm (hq a τ b hout))
    (fun a τ b _ hout h => tab_rides decT₂ N p l hdk 8 x a b τ hout
      (by rw [(hq a τ b hout).loc]) h) ?_ rfl rfl rfl
    (pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 8 (by decide))
    (pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 9 (by decide))
  · rw [hx]
    exact split_wrapped Q b1 b2 b3 b4 b5 b6 b7 b8 hbl c8 h8c
  · intro a τ b w i ha hout ho hi hp hm
    have hO := shapeO_of_on cs G smp₂ ms decT₂ bkR N Pm₀ Oc n nU nO p l Q 8 (Or.inr (Or.inr rfl)) a
        ha
    have hUU := (shapeU_iff Q.par nU _ a.1.2).1 ((shapeO_iff Q.par nU nO _ 0 a.1.2).1 hO).1
    obtain ⟨_, o2, o3, o4⟩ := other_back cs arr Mg₀ mem rd Q.par uR omW e' n num hsr huR a.1.2 b.1.2
      (hq a τ b hout) hUU.2.1 w
    have h8 : ∀ j ∈ openL (insLSh true) (outsLSh true) startLSh 8, j = ItemS.row .fold ∨ j = .row .recG ∨
        j = .row .loc ∨ j = .row (.sample .oU) ∨ j = .row (.sample .oOmega) ∨
        j = .row (.sample .oSp) ∨ j = .pin .oU ∨ j = .pin .oOmega ∨ j = .pin .oSp := by decide
    rcases h8 i ((openSh_iff true 8 i).1 ho) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd ((ins8 _).2 (Or.inl rfl)) hi
    · exact o2 (by rw [hUU.2.2.2]; omega) hm
    · exact o3 (by rw [hUU.2.2.2]) hm
    · exact o4 _ hm
    · exact o4 _ hm
    · exact o4 _ hm
    · exact absurd rfl (hp _)
    · exact absurd rfl (hp _)
    · exact absurd rfl (hp _)

end Desc.K14.Law
