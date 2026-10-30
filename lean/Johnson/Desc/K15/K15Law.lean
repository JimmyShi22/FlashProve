-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/K15Law.lean: K15's LAW, (L2) «HANDS ON», AT THE FOLD: its proof.

WHAT IT SAYS (`k15_ran`; the statement as a definition of its own: `HandsOnFold`,
Johnson/Desc/K15/K15Says.lean). Where the format's own fold
(`foldBlocks 0`, Johnson/Desc/Block.lean) over the link's
blocks 0 to 5 (the front · LINK point · the sending ·
(rec_gamma), twice · LINK · LINK phi: Johnson/Desc/Link/LinkDescWithGroundSend.lean; the front alone:
Johnson/Desc/Link/LinkDesc.lean) says yes from a carried
record d on rounds rs and columns cols, leaving
d', rest, cols': there are X and D with the library's record of facts on a link's five rounds,
`LinkRanR P.S key0 key1 (ctxOf es d rs cols) (ctxOf (es.drop 5) d' rest cols') X D`
(OnBytes/Slice/BlkLinkRanRec.lean): the five rounds
and what each shows; the statement behind IN CLOSED FORM (`linkStR`); the book; the group's rows by
the library's own pure row
functions (foldeqRecordRow · columnRows · linkEqualityRow · Send.form); `RowChecked` of every row;
the columns taken, as
`viewColumns` of the two tables' lists. X's group and mask are the carried record's.
WHY THAT RECORD. The library's proved soundness of a link's five rounds (`core_peelR`,
OnBytes/Slice/CorePeelRec.lean) is tied to a decision
on views through this record and no other; `linkSteps_invR` has it from a run of `verify-on-bytes`
alone. Here it
is had of the description's own text. NO RUN OF `verify-on-bytes` STANDS IN A STATEMENT OR A PROOF
OF THESE FILES: no linkStepsVerify, no
linkVerify, no value of the type Blk, no «Yields». WHAT THEY DO TAKE from the library's files whose
names begin with Blk (OnBytes/Slice/
BlkLinkRanRec · BlkLinkRan · BlkLinkRun · BlkCalls · BlkSendRun · BlkStLaws) are definitions and
lemmas ON DATA: LinkRanR · linkStR · columnRows ·
storedList · withMessageInGroup · withRow | withRows · admitted · stSent · RowChecked and their laws;
viewColumns (OnBytes/Iop/OpenLaws.lean); and one pure
test in the namespace Blk (Blk.placeOk, which the plain ground's rowL calls). The type Ctx is used
as a record of data (`ctxOf`). `verify-on-bytes`'s PURE functions on rows,
tensors, codes and shapes stay, as on K14's and K15's pages.
THE THREE PREMISES, ALL NAMED (over Block.lean).
(1) P.set.samples = 1: one answer to a
sample (the library's record is stated so). PUBLIC. (2) entries P =
some es5: the five rounds can be said. PUBLIC; at the decision the tests on the plan pay it
(`entries_of_planOk`). (3) key0.item = 0,
key1.item = 1: at the decision the test on the instance pays it. NOT A PREMISE: every position
drawn in round 3 is below 2 ^ logN: K15's
`link`, as Block.step's groupsOf, takes a position modulo 2 ^ logN; Block.lean's roundsFit
asks the range in front of it,
so the fold's yes gives it (`fit_one`), and behind it the modulus is the
identity (`map_mod_self`).
NOT A PREMISE: viewWordsBelowPrime (the words below the prime): the record says nothing that needs it; whoever
reads the words as field elements does.
THE TWO SILLY MEMBERS (Johnson/Desc/K15/K15Run.lean). «Yes to all»: a list of blocks that says yes
and takes nothing FAILS the conclusion: `silly_yes`,
`ran_not_idle`: proved. «No to all»: MEETS the law, as every law «a yes gives …» must. So its worth
hangs on the premises being met
where it runs: evaluated at two stored sets (synthetic weights), outside this library: a run,
no theorem.
HOW PROVED. `k15_steps`: the fold's yes, block by block (Johnson/Desc/K15/FoldInv.lean: general),
down to each of K15's five functions' yes and what roundsFit
has asked. `point_inv` · `send_inv` (Johnson/Desc/K15/K15Send.lean) · `laysRec_inv` · `link_ran`
(Johnson/Desc/K15/K15Cols.lean) · `phi_inv`: each function's yes, by the plain
ground's inversions (Johnson/Desc/K15/GroundInv.lean: general in the carried record) and the two
equations of Johnson/Desc/K15/K15Rows.lean (K14's recGamma | locX ARE the
library's row functions under the clauses in front of them). The tail follows the proof of
linkSteps_invR.
LIMITS. Nothing on soundness by itself: it is the tie («hands on»), not the count. What the rows
MEAN (IsRowsR; the typed statement st4R) is
the library's next step, from this record. The proximity test and the chain's end are other kinds'.
Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K15.K15Says
import Johnson.Desc.K15.K15Rows
import Johnson.Desc.K15.K15Send
import Johnson.Desc.K15.FoldInv
import Johnson.Desc.K15.K15Cols
import OnBytes.Slice.BlkLinkRanRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block foldBlocks roundsFit groupsOf noDigest OpenedColumn)

theorem entries_inv (P : P15) (es : List Fmt.Entry) (h : entries P = some es) :
    ∃ lay, layTrees P.codes (sent P) = some lay ∧ es = fiveOf P := by
  unfold entries at h
  cases hl : layTrees P.codes (sent P) with
  | none => simp [hl] at h
  | some lay =>
    simp [hl] at h
    exact ⟨lay, rfl, h.symm⟩

/-! ## What each of K15's five functions' yes says -/

theorem point_inv (p : Par15) (d d' : St) (r : Fmt.RoundView) (h : point p d [r] = some d') :
    d' = { d with st := OnBytes.Slice.withGroup d.st p.S.code p.S.maskCode
                  loc := { d.loc with gamma := Desc.K14.drawn r, g := d.st.groups.size } } := by
  unfold point at h
  simp only [Option.bind_eq_bind] at h
  cases hg : VerifiableInference.Desc.Ground.newGroupP d p.S.code p.S.maskCode with
  | none => rw [hg] at h; simp at h
  | some x =>
    obtain ⟨g, d₁⟩ := x
    obtain ⟨rfl, rfl⟩ := newGroupP_inv d d₁ _ _ g hg
    rw [hg] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    exact h.symm

theorem phi_inv (p : Par15) (d d' : St) (r : Fmt.RoundView) (h : phi p d [r] = some d') :
    ∃ rE, linkEqualityRow p.S (Desc.K14.drawn r) d.loc.o0 d.loc.o1 p.S.cut = some rE ∧
      RowChecked d.st rE ∧ d' = { d with st := withRow d.st d.loc.g rE } := by
  unfold phi at h
  simp only [Option.bind_eq_bind] at h
  cases he : eqPhi p.S (Desc.K14.drawn r) d.loc.o0 d.loc.o1 with
  | none => rw [he] at h; simp at h
  | some rE =>
    rw [he] at h
    simp only [Option.bind_some] at h
    obtain ⟨hk, rfl⟩ := addRowP_inv d d' _ _ h
    refine ⟨rE, ?_, (rowL_checked _ _ _ hk).2, rfl⟩
    rw [← he]
    unfold linkEqualityRow eqPhi
    by_cases hl : (Desc.K14.drawn r).length = p.S.entryBits
    · simp [hl, guard]
    · simp [hl, guard] at he ⊢

theorem send_inv (p : Par15) (hs : p.samples = 1) (d d' : St) (r2 r3 : Fmt.RoundView)
    (h : send p d [r2, r3] = some d') :
    ∃ ids lay beta y0 y1 row0 row1 places d₂,
      SentP p.S 0 d d₂ ids lay beta y0 y1 row0 row1 places r2 r3 ∧
      d' = { d₂ with loc := { d₂.loc with
        o0 := ⟨d.st.oracles.size, vectorLay d.st.codes (rowShape p.S) p.S.rowsHigh⟩
        o1 := ⟨d.st.oracles.size + 1, vectorLay d.st.codes (rowShape p.S) p.S.rowsHigh⟩
        firstMask := if p.S.masksAhead = true then some (d.st.oracles.size + 2) else none } } := by
  unfold send at h
  rw [hs] at h
  simp only [Option.bind_eq_bind] at h
  cases hq : sendP groundG p.gp true d (linkMessage p.S 1) r2 r3 with
  | none => rw [hq] at h; simp at h
  | some x =>
    obtain ⟨ids, sd, an, need, d₂⟩ := x
    obtain ⟨lay, beta, y0, y1, row0, row1, places, Q⟩ := sendLink_inv p.S p.gp d d₂ r2 r3 ids sd an
        need hq
    rw [hq] at h
    simp only [Option.bind_some] at h
    unfold behind at h
    rw [hs] at h
    simp only [Option.bind_eq_bind] at h
    obtain ⟨i0, i1, i2⟩ := linkSent_at p.S d.st.oracles.size
    rw [Q.numbers, i0, i1, i2] at h
    have hc : d₂.st.codes = d.st.codes := by rw [Q.out]; rfl
    refine ⟨ids, lay, beta, y0, y1, row0, row1, places, d₂, Q, ?_⟩
    cases hm : p.S.masksAhead <;> simp [hm, hc] at h ⊢ <;> exact h.symm

theorem mapM_congr_mem {α β : Type} {f g : α → Option β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) →
    l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons]
    rw [h a (List.mem_cons_self ..), mapM_congr_mem l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- One table's share of the step without a round. -/
theorem laysOne_inv (p : Par15) (further : Bool) (d d' : St) (key : TableKey) (o : FoldedRow)
    (hf : key.fits p.S.table = true) (hg : d.loc.gamma.length = p.S.table.v)
    (h : laysOne p d key o = some d') :
    ∃ G l, d.st.groups[d.loc.g]? = some G ∧
      recRowsR (p.S.side further 1) key (foldeqWeights d.loc.gamma) o = some l ∧
      (∀ r ∈ l, RowChecked (withMessageInGroup d.st d.loc.g o.oracle false G) r) ∧
      d' = { d with st := withRows (withMessageInGroup d.st d.loc.g o.oracle false G) d.loc.g l } := by
  unfold laysOne at h
  simp only [Option.bind_eq_bind] at h
  cases hj : VerifiableInference.Desc.Ground.joinP d d.loc.g o.oracle false with
  | none => rw [hj] at h; simp at h
  | some d₁ =>
    obtain ⟨G, hG, rfl⟩ := joinP_inv d d₁ _ _ _ hj
    rw [hj] at h
    simp only [Option.bind_some] at h
    have hrows : (key.seeds.zipIdx.mapM fun x =>
        Desc.K14.recGamma p.S.table x.1 x.2 (weights d.loc) key.record o) =
        recRowsR (p.S.side further 1) key (foldeqWeights d.loc.gamma) o := by
      unfold recRowsR
      apply mapM_congr_mem
      intro x hx
      unfold TableKey.fits at hf
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hf
      obtain ⟨⟨h1, h2⟩, h3⟩ := hf
      obtain ⟨a, i⟩ := x
      have hm := List.mem_zipIdx_iff_getElem?.1 hx
      have hi : i < key.seeds.length := (List.getElem?_eq_some_iff.1 hm).1
      exact recGamma_eq (p.S.side further 1) a i (weights d.loc) key.record o
        (h3 a (List.mem_of_getElem? hm)) h1
        (by
          show p.S.table.rows ≤ (eqTable d.loc.gamma).size
          rw [size_eqTable, hg]
          exact Nat.le_refl _)
        (by
          show i < p.S.table.answers
          rw [← h2]
          exact hi)
    rw [hrows] at h
    cases hr : recRowsR (p.S.side further 1) key (foldeqWeights d.loc.gamma) o with
    | none => rw [hr] at h; simp at h
    | some l =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      obtain ⟨hc, rfl⟩ := addRowsP_inv _ d' _ _ h
      exact ⟨G, l, hG, rfl, fun r hr => (hc r hr).2, rfl⟩

/-- The step without a round, whole. -/
theorem laysRec_inv (p : Par15) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    d.loc.key0.fits p.S.table = true ∧ d.loc.key1.fits p.S.table = true ∧
    (d.loc.key0.seeds.all fun s => !isZeroE s.beta) = true ∧
    (d.loc.key1.seeds.all fun s => !isZeroE s.beta) = true ∧ d.loc.gamma.length = p.S.table.v ∧
    ∃ G0 G1 rec0 rec1, d.st.groups[d.loc.g]? = some G0 ∧
      recRowsR (p.S.side false 1) d.loc.key0 (foldeqWeights d.loc.gamma) d.loc.o0 = some rec0 ∧
      (∀ r ∈ rec0, RowChecked (withMessageInGroup d.st d.loc.g d.loc.o0.oracle false G0) r) ∧
      (withRows (withMessageInGroup d.st d.loc.g d.loc.o0.oracle false G0) d.loc.g rec0).groups[d.loc.g]? = some
          G1 ∧
      recRowsR (p.S.side true 1) d.loc.key1 (foldeqWeights d.loc.gamma) d.loc.o1 = some rec1 ∧
      (∀ r ∈ rec1, RowChecked (withMessageInGroup (withRows (withMessageInGroup d.st d.loc.g d.loc.o0.oracle false G0)
                      d.loc.g rec0)
        d.loc.g d.loc.o1.oracle false G1) r) ∧
      d' = { d with st := withRows (withMessageInGroup (withRows (withMessageInGroup d.st d.loc.g d.loc.o0.oracle false G0)
                    d.loc.g rec0) d.loc.g d.loc.o1.oracle false G1) d.loc.g rec1 } := by
  unfold laysRec at h
  simp only [Option.bind_eq_bind, guard] at h
  split at h
  · rename_i hk
    simp only [Option.pure_def, Option.bind_some] at h
    unfold VerifiableInference.Desc.Ground.ok laysRecL keyL at hk
    simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, beq_iff_eq] at hk
    obtain ⟨f0, z0, hg, f1, z1, _⟩ := hk
    cases h0 : laysOne p d d.loc.key0 d.loc.o0 with
    | none => rw [h0] at h; simp at h
    | some d₁ =>
      rw [h0] at h
      simp only [Option.bind_some] at h
      obtain ⟨G0, rec0, hG0, hr0, hc0, rfl⟩ := laysOne_inv p false d d₁ _ _ f0 hg h0
      obtain ⟨G1, rec1, hG1, hr1, hc1, rfl⟩ := laysOne_inv p true
        { d with st := withRows (withMessageInGroup d.st d.loc.g d.loc.o0.oracle false G0) d.loc.g rec0 } d' _ _
            f1 hg h
      exact ⟨f0, f1, z0, z1, hg, G0, G1, rec0, rec1, hG0, hr0, hc0, hG1, hr1, hc1, rfl⟩
  · simp at h

/-- One table's share of "LINK". -/
theorem locOne_inv (p : Par15) (d d' : St) (further : Bool) (draws : List Nat)
    (cols : List (Nat × List UInt64)) (o : FoldedRow) (h : locOne p d further draws cols o = some
        d') :
    ∃ rows, (draws.mapM fun x => do
        Desc.K14.locX (p.S.side further p.samples) x (weights d.loc) ((← cols.lookup x).toArray) o)
            = some rows ∧
      (∀ r ∈ rows, RowChecked d.st r) ∧ d' = { d with st := withRows d.st d.loc.g rows } := by
  unfold locOne at h
  simp only [Option.bind_eq_bind] at h
  cases hr : (draws.mapM fun x => do
      Desc.K14.locX (p.S.side further p.samples) x (weights d.loc) ((← cols.lookup x).toArray) o)
          with
  | none => simp only [Option.bind_eq_bind] at hr; rw [hr] at h; simp at h
  | some rows =>
    simp only [Option.bind_eq_bind] at hr
    rw [hr] at h
    simp only [Option.bind_some] at h
    obtain ⟨hc, rfl⟩ := addRowsP_inv d d' _ _ h
    exact ⟨rows, rfl, fun r hr => (hc r hr).2, rfl⟩

theorem why_ok (l : VerifiableInference.Desc.Ground.Clauses) (x : Option St) (d : St)
    (h : why l x = .ok d) :
    x = some d := by
  unfold why at h
  cases x with
  | none => cases h
  | some y => injection h with h; rw [h]

theorem take_one {α : Type} (l : List α) (h : (l.take 1).length = 1) : ∃ a t, l = a :: t := by
  cases l with
  | nil => simp at h
  | cons a t => exact ⟨a, t, rfl⟩

theorem take_two {α : Type} (l : List α) (h : (l.take 2).length = 2) : ∃ a b t, l = a :: b :: t :=
    by
  match l, h with
  | [], h => simp at h
  | [_], h => simp at h
  | a :: b :: t, _ => exact ⟨a, b, t, rfl⟩

/-- An item's kind list that is empty: no item. -/
theorem vals_nil (r : Fmt.RoundView) (h : r.vals.map VerifiableInference.Desc.itemOf = []) : r.vals = [] :=
    by
  simpa using h

/-- What the format's reading of one round has asked. -/
theorem fit_one (x : Fmt.DeclaredRound) (r : Fmt.RoundView) (h : roundsFit [x] [r] = true) :
    r.vals.map VerifiableInference.Desc.itemOf = x.entry.cut.filter (· != .root) ∧
      r.drawn.elems.length = x.entry.drawE ∧ r.drawn.poss.length = x.entry.poss ∧
      ∀ y ∈ r.drawn.poss, y < 2 ^ x.entry.logN := by
  unfold roundsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.2⟩

/-! ## The five blocks by name -/

def bPoint (P : P15) (es : List Fmt.Entry) : Block St Unit :=
  { name := "LINK point", place := ⟨1, none, 1, .K15⟩, planOk := true
    rounds := ((es.drop 0).take 1).map fun e => { entry := e }
    oracles := [[]], before := [], decide := fun d rs _ => why [] (point P.par d rs)
    claims := [], after := [] }

def bSend (P : P15) (es : List Fmt.Entry) : Block St Unit :=
  { name := "send o_0, o_1", place := ⟨1, none, 2, .K1⟩, planOk := true
    rounds := ((es.drop 1).take 2).map fun e => { entry := e }
    oracles := [Desc.K14.oraclesOf P.codes (sent P) ([[0], [0]] ++ if P.S.masksAhead then [[]] else
        []), []]
    before := [], decide := fun d rs _ => why [] (send P.par d rs), claims := [], after := [] }

def bRec (P : P15) (es : List Fmt.Entry) : Block St Unit :=
  { name := "(rec_gamma), twice", place := ⟨1, none, 3, .K15⟩, planOk := true
    rounds := ((es.drop 0).take 0).map fun e => { entry := e }
    oracles := [], before := [], decide := fun d rs _ =>
      why (laysRecL P.par d.loc) (laysRec P.par d rs)
    claims := [], after := [] }

def bLink (P : P15) (es : List Fmt.Entry) : Block St Unit :=
  { name := "LINK", place := ⟨1, none, 4, .K15⟩, planOk := true
    rounds := ((es.drop 3).take 1).map fun e => { entry := e, stored := readsAtLink P.S }
    oracles := [[]], before := [(1, 0)], decide := fun d rs gs => why [] (link P.par d rs gs)
    claims := [], after := [] }

def bPhi (P : P15) (es : List Fmt.Entry) : Block St Unit :=
  { name := "LINK phi", place := ⟨1, none, 5, .K15⟩, planOk := true
    rounds := ((es.drop 4).take 1).map fun e => { entry := e }
    oracles := [[]], before := [(1, 0)], decide := fun d rs _ => why [] (phi P.par d rs)
    claims := [], after := [] }

/-- The description's five blocks in front of the test are these. -/
theorem blocks_eq (P : P15) (es : List Fmt.Entry) (he : entries P = some es) :
    blocksOr P = [bPoint P es, bSend P es, bRec P es, bLink P es, bPhi P es] := by
  unfold blocksOr blocks
  simp only [he, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.getD_some]
  rfl

/-- **The fold's yes over the link's blocks 0 to 5, taken apart**: the five rounds; what the
format's own reading of a round has
asked of them; each of K15's functions' yes at the rounds without the sealed digest; the columns
that were handed. -/
theorem k15_steps (P : P15) (es5 : List Fmt.Entry) (he : entries P = some es5) (d d' : St)
    (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn)
    (h : foldBlocks 0 (frontBlock P :: blocksOr P) d rs cols = .ok (d', rest, cols')) :
    ∃ r1 r2 r3 r4 r5 d1 d2 d3 d4 e4 k, rs = r1 :: r2 :: r3 :: r4 :: r5 :: rest ∧
      r1.vals = [] ∧ r1.drawn.elems.length = P.S.table.v ∧ point P.par d [noDigest r1] = some d1 ∧
      send P.par d1 [noDigest r2, noDigest r3] = some d2 ∧ laysRec P.par d2 [] = some d3 ∧
      r4.vals = [] ∧ r4.drawn.poss.length = P.S.columnsFirst + P.S.columnsFurther ∧
      (∀ y ∈ r4.drawn.poss, y < 2 ^ P.S.table.code.logN) ∧
      k = ((groupsOf 0 [⟨e4, readsAtLink P.S, []⟩] [r4.drawn]).flatMap id).length ∧
      (cols.take k).map (fun c => (c.1, c.2.1, c.2.2.length)) =
        (groupsOf 0 [⟨e4, readsAtLink P.S, []⟩] [r4.drawn]).flatMap id ∧
      link P.par d3 [noDigest r4]
        (VerifiableInference.Desc.regroup ((groupsOf 0 [⟨e4, readsAtLink P.S, []⟩] [r4.drawn]).map
            (·.length))
          (cols.take k)) = some d4 ∧
      cols' = cols.drop k ∧
      r5.vals = [] ∧ r5.drawn.elems.length = P.S.entryBits ∧ phi P.par d4 [noDigest r5] = some d' :=
          by
  rw [blocks_eq P es5 he] at h
  obtain ⟨lay, _, rfl⟩ := entries_inv P es5 he
  -- the front
  obtain ⟨s0, k0, _, t0, h⟩ := VerifiableInference.Desc.foldBlocks_cons _ _ _ _ _ _ _ h
  have hr0 : (frontBlock P).rounds = [] := rfl
  obtain ⟨_, rfl, q0⟩ := VerifiableInference.Desc.step_quiet 0 (frontBlock P)
    (by intro x hx; rw [hr0] at hx; cases hx) _ _ _ _ _ t0
  change Except.ok d = Except.ok s0 at q0
  injection q0 with q0
  subst q0
  rw [hr0] at h
  simp only [List.length_nil, List.drop_zero] at h
  -- LINK point
  obtain ⟨s1, k1, l1, t1, h⟩ := VerifiableInference.Desc.foldBlocks_cons _ _ _ _ _ _ _ h
  have hr1 : (bPoint P (fiveOf P)).rounds = [{ entry := (fiveOf P)[0]! }] := rfl
  rw [hr1] at l1 t1 h
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at l1 t1 h
  obtain ⟨r1, rs1, rfl⟩ := take_one _ l1
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at t1 h
  obtain ⟨f1, rfl, q1⟩ := VerifiableInference.Desc.step_quiet 0 (bPoint P (fiveOf P))
    (by intro x hx; rw [hr1] at hx; simp at hx; subst hx; exact ⟨rfl, rfl⟩) _ _ _ _ _ t1
  have w1 := why_ok _ _ _ q1
  clear q1
  rw [hr1] at f1
  obtain ⟨v1, e1, _, _⟩ := fit_one _ _ f1
  have v1 : r1.vals = [] := vals_nil _ (v1.trans (by simp [fiveOf, rounds, entryOf, Fmt.Entry.cut]))
  have e1 : r1.drawn.elems.length = P.S.table.v := e1
  simp only [List.drop_zero] at h
  -- the sending
  obtain ⟨s2, k2, l2, t2, h⟩ := VerifiableInference.Desc.foldBlocks_cons _ _ _ _ _ _ _ h
  have hr2 : (bSend P (fiveOf P)).rounds =
      [{ entry := (fiveOf P)[1]! }, { entry := (fiveOf P)[2]! }] := rfl
  rw [hr2] at l2 t2 h
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at l2 t2 h
  obtain ⟨r2, r3, rs3, rfl⟩ := take_two _ l2
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at t2 h
  obtain ⟨_, rfl, q2⟩ := VerifiableInference.Desc.step_quiet 0 (bSend P (fiveOf P))
    (by
      intro x hx; rw [hr2] at hx; simp at hx; rcases hx with rfl | rfl <;> exact
          ⟨rfl, rfl⟩) _ _ _ _ _ t2
  have w2 := why_ok _ _ _ q2
  clear q2
  simp only [List.drop_zero] at h
  -- the step without a round
  obtain ⟨s3, k3, _, t3, h⟩ := VerifiableInference.Desc.foldBlocks_cons _ _ _ _ _ _ _ h
  have hr3 : (bRec P (fiveOf P)).rounds = [] := rfl
  obtain ⟨_, rfl, q3⟩ := VerifiableInference.Desc.step_quiet 0 (bRec P (fiveOf P))
    (by intro x hx; rw [hr3] at hx; cases hx) _ _ _ _ _ t3
  have w3 := why_ok _ _ _ q3
  clear q3
  rw [hr3] at w3 h
  simp only [List.length_nil, List.take_zero, List.drop_zero, List.map_nil] at w3 h
  -- LINK
  obtain ⟨s4, k4, l4, t4, h⟩ := VerifiableInference.Desc.foldBlocks_cons _ _ _ _ _ _ _ h
  have hr4 : (bLink P (fiveOf P)).rounds = [⟨(fiveOf P)[3]!, readsAtLink P.S, []⟩] := rfl
  rw [hr4] at l4 t4 h
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at l4 t4 h
  obtain ⟨r4, rs4, rfl⟩ := take_one _ l4
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at t4 h
  obtain ⟨f4, hk4, hc4, q4⟩ := VerifiableInference.Desc.step_inv 0 (bLink P (fiveOf P)) _ _ _ _ _ t4
  have w4 := why_ok _ _ _ q4
  clear q4
  rw [hr4] at f4 hk4 hc4 w4
  obtain ⟨v4, _, p4, b4⟩ := fit_one _ _ f4
  have b4 : ∀ y ∈ r4.drawn.poss, y < 2 ^ P.S.table.code.logN := b4
  have v4 : r4.vals = [] := vals_nil _ (v4.trans (by simp [fiveOf, rounds, entryOf, Fmt.Entry.cut]))
  have p4 : r4.drawn.poss.length = P.S.columnsFirst + P.S.columnsFurther := p4
  -- LINK phi
  obtain ⟨s5, k5, l5, t5, h⟩ := VerifiableInference.Desc.foldBlocks_cons _ _ _ _ _ _ _ h
  have hr5 : (bPhi P (fiveOf P)).rounds = [{ entry := (fiveOf P)[4]! }] := rfl
  rw [hr5] at l5 t5 h
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at l5 t5 h
  obtain ⟨r5, rs5, rfl⟩ := take_one _ l5
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at t5 h
  obtain ⟨f5, rfl, q5⟩ := VerifiableInference.Desc.step_quiet 0 (bPhi P (fiveOf P))
    (by intro x hx; rw [hr5] at hx; simp at hx; subst hx; exact ⟨rfl, rfl⟩) _ _ _ _ _ t5
  have w5 := why_ok _ _ _ q5
  clear q5
  rw [hr5] at f5
  obtain ⟨v5, e5, _, _⟩ := fit_one _ _ f5
  have v5 : r5.vals = [] := vals_nil _ (v5.trans (by simp [fiveOf, rounds, entryOf, Fmt.Entry.cut]))
  have e5 : r5.drawn.elems.length = P.S.entryBits := e5
  have h := VerifiableInference.Desc.foldBlocks_nil _ _ _ _ _ h
  simp only [List.drop_zero, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  simp only [List.map_cons, List.map_nil] at w1 w2 w4 w5 hk4 hc4
  exact ⟨r1, r2, r3, r4, r5, s1, s2, s3, s4, _, k4, rfl, v1, e1, w1, w2, w3, v4, p4, b4, hk4, hc4,
      w4, rfl, v5, e5, w5⟩

theorem map_mod_self (n : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x < n) → l.map (· % n) = l
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons]
    rw [Nat.mod_eq_of_lt (h a (List.mem_cons_self ..)), map_mod_self n l fun x hx =>
      h x (List.mem_cons_of_mem _ hx)]

/-- **"LINK", taken apart**: the columns that Block.step has matched and handed are the library's
viewColumns of the two tables'
lists; K15's rows are the library's columnRows. UNDER: every drawn position is below 2 ^ logN. -/
theorem link_ran (p : Par15) (hs : p.samples = 1) (d3 d4 : St) (e4 : Fmt.Entry) (r4 : Fmt.RoundView)
    (cols : List OpenedColumn)
    (k : Nat) (key0 key1 : TableKey) (hi0 : key0.item = 0) (hi1 : key1.item = 1)
    (hp : ∀ x ∈ r4.drawn.poss, x < 2 ^ p.S.table.code.logN) (hg : d3.loc.gamma.length = p.S.table.v)
    (hk : k = ((groupsOf 0 [⟨e4, readsAtLink p.S, []⟩] [r4.drawn]).flatMap id).length)
    (hc : (cols.take k).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      (groupsOf 0 [⟨e4, readsAtLink p.S, []⟩] [r4.drawn]).flatMap id)
    (w4 : link p d3 [noDigest r4]
      (VerifiableInference.Desc.regroup ((groupsOf 0 [⟨e4, readsAtLink p.S, []⟩] [r4.drawn]).map
          (·.length))
        (cols.take k)) = some d4) :
    ∃ cols0 cols1 rows0 rows1,
      cols0.size = (storedList (linkStored p.S key0 false)
        (Positions.ofDraws p.S.table.code.logN r4.drawn.poss)).toArray.size ∧
      columnRows (p.S.side false 1) (foldeqWeights d3.loc.gamma)
        (Positions.ofDraws p.S.table.code.logN r4.drawn.poss) 0 d3.loc.o0
        (storedList (linkStored p.S key0 false)
          (Positions.ofDraws p.S.table.code.logN r4.drawn.poss)).toArray cols0 = some rows0 ∧
      cols1.size = (storedList (linkStored p.S key1 true)
        (Positions.ofDraws p.S.table.code.logN r4.drawn.poss)).toArray.size ∧
      columnRows (p.S.side true 1) (foldeqWeights d3.loc.gamma)
        (Positions.ofDraws p.S.table.code.logN r4.drawn.poss) p.S.columnsFirst d3.loc.o1
        (storedList (linkStored p.S key1 true)
          (Positions.ofDraws p.S.table.code.logN r4.drawn.poss)).toArray cols1 = some rows1 ∧
      cols = viewColumns (Fmt.storedKey key0.item) (storedList (linkStored p.S key0 false)
          (Positions.ofDraws p.S.table.code.logN r4.drawn.poss)).toArray cols0 ++
        (viewColumns (Fmt.storedKey key1.item) (storedList (linkStored p.S key1 true)
          (Positions.ofDraws p.S.table.code.logN r4.drawn.poss)).toArray cols1 ++ cols.drop k) ∧
      (∀ r ∈ rows0, RowChecked d3.st r) ∧ (∀ r ∈ rows1, RowChecked (withRows d3.st d3.loc.g rows0)
          r) ∧
      d4 = { d3 with st := withRows (withRows d3.st d3.loc.g rows0) d3.loc.g rows1 } := by
  have hG : groupsOf 0 [⟨e4, readsAtLink p.S, []⟩] [r4.drawn] =
      [(storedList (linkStored p.S key0 false) (Positions.ofDraws p.S.table.code.logN
          r4.drawn.poss)).map
          (fun x => (Fmt.storedKey key0.item, x, p.S.table.rows)),
       (storedList (linkStored p.S key1 true) (Positions.ofDraws p.S.table.code.logN
           r4.drawn.poss)).map
          (fun x => (Fmt.storedKey key1.item, x, p.S.table.rows))] := by
    rw [hi0, hi1]
    simp [groupsOf, readsAtLink, storedList, linkStored, Positions.ofDraws, Fmt.partOf,
        IndexShape.tree]
  rw [hG] at hk hc w4
  clear hG
  generalize storedList (linkStored p.S key0 false) (Positions.ofDraws p.S.table.code.logN
      r4.drawn.poss) = xs0
    at hk hc w4 ⊢
  generalize storedList (linkStored p.S key1 true) (Positions.ofDraws p.S.table.code.logN
      r4.drawn.poss) = xs1
    at hk hc w4 ⊢
  simp only [List.flatMap_cons, List.flatMap_nil, id, List.append_nil, List.length_append,
      List.length_map,
    List.map_cons, List.map_nil, VerifiableInference.Desc.regroup] at hk hc w4
  generalize hgot : cols.take k = got at hc w4
  have hlen : got.length = xs0.length + xs1.length := by
    have := congrArg List.length hc
    simpa using this
  have h0 : (got.take xs0.length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      xs0.map (fun x => (Fmt.storedKey key0.item, x, p.S.table.rows)) := by
    rw [List.map_take, hc, List.take_left' (by simp)]
  have h1 : ((got.drop xs0.length).take xs1.length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      xs1.map (fun x => (Fmt.storedKey key1.item, x, p.S.table.rows)) := by
    rw [List.map_take, List.map_drop, hc, List.drop_left' (by
      simp), List.take_of_length_le (by simp)]
  have hW : (weights d3.loc).size ≤ p.S.table.rows := by
    show (eqTable d3.loc.gamma).size ≤ 2 ^ p.S.table.v
    rw [size_eqTable, hg]
  have hq : (noDigest r4).drawn.poss.map (· % 2 ^ p.S.table.code.logN) = r4.drawn.poss :=
    map_mod_self _ _ hp
  simp only [link, hq, Option.bind_eq_bind] at w4
  cases ha : locOne p d3 false (r4.drawn.poss.take p.S.columnsFirst)
      ((got.take xs0.length).map fun c => (c.2.1, c.2.2)) d3.loc.o0 with
  | none => rw [ha] at w4; simp at w4
  | some d₁ =>
    rw [ha] at w4
    simp only [Option.bind_some] at w4
    obtain ⟨rows0, m0, c0, rfl⟩ := locOne_inv p d3 d₁ _ _ _ _ ha
    obtain ⟨rows1, m1, c1, rfl⟩ := locOne_inv p _ d4 _ _ _ _ w4
    rw [hs] at m0 m1
    rw [locRows_eq _ _ _ _ _ _ _ _ h0 hW] at m0
    rw [locRows_eq _ _ _ _ _ _ _ _ h1 hW] at m1
    refine ⟨wordsOf (got.take xs0.length), wordsOf ((got.drop xs0.length).take xs1.length), rows0,
        rows1,
      ?_, ?_, ?_, ?_, ?_, c0, c1, rfl⟩
    · have := congrArg List.length h0
      simpa [wordsOf] using this
    · unfold columnRows
      simpa [Positions.ofDraws] using m0
    · have := congrArg List.length h1
      simpa [wordsOf] using this
    · unfold columnRows
      simpa [Positions.ofDraws] using m1
    · rw [← view_of_fit _ _ _ _ h0, ← view_of_fit _ _ _ _ h1, ← List.append_assoc,
        List.take_of_length_le (l := got.drop xs0.length) (by
          simp [hlen]), List.take_append_drop, ← hgot,
        List.take_append_drop]

theorem upRows {S : Statement} {r : Row} (g : Nat) (l : List Row) (h : RowChecked S r) :
    RowChecked (withRows S g l) r := h.congr (withRows_oracles g l S).1 (withRows_oracles g l S).2

theorem upRow {S : Statement} {r : Row} (g : Nat) (x : Row) (h : RowChecked S r) :
    RowChecked (withRow S g x) r := h.congr (withRow_oracles S g x).1 (withRow_oracles S g x).2

/-- **K15's LAW, (L2) «HANDS ON».** WHERE THE FORMAT's OWN FOLD OVER THE LINK's BLOCKS 0 TO 5 (the
front · LINK point · the sending ·
(rec_gamma), twice · LINK · LINK phi) SAYS YES, THE LIBRARY's RECORD OF FACTS ON A LINK's FIVE
ROUNDS HOLDS AT THE CARRIED RECORDS
IN FRONT AND BEHIND: LinkRanR (OnBytes/Slice/BlkLinkRanRec.lean): the statement behind in closed
form (linkStR), the book, the rows
by the library's own row functions, the columns taken. -/
theorem k15_ran (P : P15) (hs : P.set.samples = 1) (es5 : List Fmt.Entry)
    (he : entries P = some es5)
    (es : List Fmt.Entry) (d d' : St) (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn)
    (hi0 : d.loc.key0.item = 0) (hi1 : d.loc.key1.item = 1) (kok : linkOk d.st.codes P.S 1 = true)
    (h : foldBlocks 0 (frontBlock P :: blocksOr P) d rs cols = .ok (d', rest, cols')) :
    ∃ X D, LinkRanR P.S d.loc.key0 d.loc.key1 (ctxOf es d rs cols) (ctxOf (es.drop 5) d' rest cols')
        X D ∧
      X.group = d'.loc.g ∧ X.mask = d'.loc.firstMask := by
  obtain ⟨r1, r2, r3, r4, r5, d1, d2, d3, d4, e4, k, rfl, v1, e1, w1, w2, w3, v4, p4, b4, hk, hc,
      w4, rfl, v5, e5,
    w5⟩ := k15_steps P es5 he d d' rs rest cols cols' h
  have hs' : P.par.samples = 1 := hs
  obtain rfl := point_inv P.par d d1 _ w1
  clear w1
  obtain ⟨ids, lay, beta, y0, y1, row0, row1, places, d₂, Q, rfl⟩ := send_inv P.par hs' _ d2 _ _ w2
  clear w2
  obtain ⟨Qlaid, Qnum, Qv2, Qfac, Qnz, Qv3, Qf0, Qf1, Qpad, rfl, Qpl⟩ := Q
  dsimp only at Qlaid Qnum Qfac Qf0 Qf1 Qpad Qpl w3
  obtain ⟨f0, f1, z0, z1, hg, G0, G1, rec0, rec1, j1, kr0, chr0, j3, kr1, chr1, rfl⟩ :=
    laysRec_inv P.par _ d3 _ w3
  clear w3
  dsimp only at f0 f1 z0 z1 hg j1 kr0 chr0 j3 kr1 chr1 w4
  obtain ⟨cols0, cols1, rows0, rows1, sz0, t0, sz1, t1, hop, chk0, chk1, rfl⟩ :=
    link_ran P.par hs' _ d4 e4 r4 cols k d.loc.key0 d.loc.key1 hi0 hi1 b4 (by exact hg) hk hc w4
  clear w4
  dsimp only at t0 t1 chk0 chk1 w5
  obtain ⟨rE, krE, chkE, rfl⟩ := phi_inv P.par _ d' _ w5
  clear w5
  dsimp only at krE chkE
  clear h
  have hG0 : G0 = linkGrp0 P.S := by
    rw [(admitted_groups _ _ _ _ _).1, (admitted_groups _ _ _ _ _).1, (stSent_groups _ _).1,
      withGroup_group] at j1
    exact (Option.some.inj j1).symm
  have hG1 : G1.members = (linkGrp1 P.S d.st.oracles.size).members := by
    rw [withRows_group _ _ _ _ (joined_group _ _ _ _ _ j1), hG0] at j3
    rw [← Option.some.inj j3]
    rfl
  refine ⟨⟨Desc.K14.drawn (noDigest r1), Desc.K14.drawn (noDigest r5),
      ⟨d.st.oracles.size, vectorLay d.st.codes (rowShape P.S) P.S.rowsHigh⟩,
      ⟨d.st.oracles.size + 1, vectorLay d.st.codes (rowShape P.S) P.S.rowsHigh⟩, d.st.groups.size,
      if P.S.masksAhead = true then some (d.st.oracles.size + 2) else none⟩,
    ⟨⟨r1, r2, r3, r4, r5, rest, lay, beta, y0, y1, row0, row1, places,
      Positions.ofDraws P.S.table.code.logN r4.drawn.poss, cols0, cols1, rows0, rows1, rE⟩, rec0,
          rec1⟩,
    ?_, rfl, rfl⟩
  exact
    { ok := kok
      fits0 := f0
      fits1 := f1
      nz0 := z0
      nz1 := z1
      pending := rfl
      left := rfl
      vals1 := v1
      gamma := rfl
      gammaLen := hg
      vals2 := Qv2
      factor := Qfac
      nz := Qnz
      vals3 := Qv3
      vals4 := v4
      pos := rfl
      draws := by
        show (Positions.ofDraws P.S.table.code.logN r4.drawn.poss).draws.size = _
        simpa [Positions.ofDraws] using p4
      vals5 := v5
      phi := rfl
      phiLen := (List.length_map ..).trans e5
      uFirst := rfl
      uFurther := rfl
      group := rfl
      mask := rfl
      form0 := Qf0
      form1 := Qf1
      pad := Qpad
      rec0 := kr0
      rec1 := kr1
      size0 := sz0
      rows0 := t0
      size1 := sz1
      rows1 := t1
      eqRow := krE
      checked := by
        intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · exact upRow _ _ chkE
        · rcases List.mem_append.1 hr with hr | hr
          · exact upRow _ _ (upRows _ _ (upRows _ _ (upRows _ _
                ((upRows _ _ (chr0 r hr)).joinedR _ _ _ _))))
          · rcases List.mem_append.1 hr with hr | hr
            · exact upRow _ _ (upRows _ _ (upRows _ _ (upRows _ _ (chr1 r hr))))
            · rcases List.mem_append.1 hr with hr | hr
              · exact upRow _ _ (upRows _ _ (upRows _ _ (chk0 r hr)))
              · exact upRow _ _ (upRows _ _ (chk1 r hr))
      st := by
        show withRow (withRows (withRows (withRows (withMessageInGroup
            (withRows (withMessageInGroup _ _ _ _ G0) _ rec0) _ _ _ G1) _ rec1)
          _ rows0) _ rows1) _ rE = _
        rw [joined_withRows, joined_members _ _ _ _ hG1, hG0]
        unfold linkStR linkSt
        rw [withRows_append, withRows_append]
        rfl
      laid := Qlaid
      book := rfl
      opened := hop
      entries := rfl
      dry := rfl
      failed := rfl
      firstTree := rfl
      samples := rfl
      roots := rfl
      placed := Qpl }

end Desc.K15

#print axioms Desc.K15.k15_steps
#print axioms Desc.K15.link_ran
#print axioms Desc.K15.k15_ran
