-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/WantAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS
REACH IN FRONT OF A SEGMENT's BATCHING, AT ALL 25 SEGMENTS: EACH PIECE THAT THE VERIFIER's SECOND
COMPUTATION EXPECTS IS THE PLAN's PIECE OF ITS CALL: NINE OF THE ELEVEN FIELDS OF `PieceFront`
(Johnson/Desc/K8/Honest/PieceWhole.lean), THOSE THAT READ NOTHING THAT THE LOOKUP HAS HEARD; AND ITS
ROWS LIE IN THE DIGITS' ARRAY OF THE STATE's LEDGER. UNDER THE SCOPE, THE FILES READ, IM.Open AND
THE DESCRIPTION's TEST ON ITS PLAN. A structure, a definition and lemmas; none of the library's
goals. No prover stands in them; nothing on completeness, soundness or hiding. Why. In scope there
are 128 combinations (`drawn_at_batch`, Johnson/P1K8R/DrawAtBatch.lean): so the second computation's
list is a written list of two, and each call has one piece, which holds all rows.

  `PiecePlanned tl w`, `pieceFront_of_planned`, `piecePlanned_view`   the nine fields and "the
      piece lies in the digits' array"; `PieceFront` from them and the two fields left; they read
      `piecesView` (Johnson/P1K8R/PublicAtBatch.lean) alone
  `want128`, **`wants_128`**   the list at 128 combinations
  `single_of_keys`, `rows_of_single`, `planned_call`   one key, one piece; it holds all 128 rows:
      DgP.TailOK's pc and rows (OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean); one call's expected
      piece
  **`planned_of_tests`**   on plain data, from tests on public numbers: `piecesLaid`
      (Johnson/Desc/K8/Honest/PiecesLaid.lean), `piecesFit` (GoodOf.lean), DgP.TailOK, Fo.PieceOK
      (OnBytes/Tie/Pv/Lookup/Ends/FoTailKf.lean), "the two counts of blocks agree", 0 < mz
  `mz_pos`, `matrix_there`   there is a matrix, so the digits' array has a column: planOk_iff
      (Johnson/Desc/First/K8/HearMeans.lean), Keeps.planOk_blocks (Johnson/Desc/PlanPasses.lean);
      `colsFacts_of` (Johnson/Desc/K8/Honest/TiesLaidOf.lean)
  **`want_at_batch`**   `tests_at_built`, `static_at_built` (Johnson/P1K8R/StaticAtBuilt.lean) at
      the built segment; `public_at_batch`, `apart_at_batch`, `sizes_at_batch` (PublicAtBatch.lean,
      ApartAtBatch.lean, TiesAtBatch.lean) at the state; LinkJoin.planned_at_batch
      (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean) between the two
  **`rows_at_batch`**   Fo.ZTests' t10 at the built segment; the state's ledger has its looks:
      `looks_at_batch` (Johnson/P1K8R/StaticAtBatch.lean), LinkJoin.looks_array, frame_of_looks
      (OkJoin.lean, FullFour.lean)
Limits. The two fields of `PieceFront` on what the lookup has heard (size, e) are not touched. At
128 combinations alone. Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.DrawAtBatch
import Johnson.P1K8R.StaticAtBuilt
import Johnson.P1K8R.StaticAtBatch
import Johnson.P1K8R.PublicAtBatch
import Johnson.P1K8R.TiesAtBatch
import Johnson.Desc.K8.Honest.PieceWhole
import Johnson.Desc.K8.Honest.SecondFew
import Johnson.Desc.First.Link.Law.FullFour
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.PlanPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Road.K4 (reach_pred)

/-- **The nine fields of `PieceFront` (Johnson/Desc/K8/Honest/PieceWhole.lean) that read nothing
that the lookup has heard, and one more**: the expected piece w is the plan's piece of its call and
index; that piece lies in the digits' array. -/
structure PiecePlanned (tl : HTailF2) (w : Want) : Prop where
  mem : (w.call, (tl.zOf w.call).pieces.getD w.i {}) ∈ joinPairs tl
  tree : ((tl.zOf w.call).pieces.getD w.i {}).tree = tl.ix.ZZ
  row : w.row = ((tl.zOf w.call).pieces.getD w.i {}).row
  r0 : w.r0 = ((tl.zOf w.call).pieces.getD w.i {}).r0
  Rp : w.Rp = ((tl.zOf w.call).pieces.getD w.i {}).Rp
  c0 : w.c0 = ((tl.zOf w.call).pieces.getD w.i {}).c0
  Cp : w.Cp = ((tl.zOf w.call).pieces.getD w.i {}).Cp
  pos : 0 < ((tl.zOf w.call).pieces.getD w.i {}).Cp
  ok : Fo.PieceOK tl w.call (tl.zOf w.call).call.n ((tl.zOf w.call).pieces.getD w.i {})
  n63 : (tl.zOf w.call).call.n - ((tl.zOf w.call).pieces.getD w.i {}).b ≤ 63

/-- `PieceFront` from it and the two fields on what the lookup has heard. -/
theorem pieceFront_of_planned {tl : HTailF2} {g : Forest.Heard} {w : Want} (k : PiecePlanned tl w)
    (h1 : (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n)
    (h2 : g.e.getD w.call zeroE = callWeightAgain g w.call) : PieceFront tl g w :=
  ⟨k.mem, k.row, k.r0, k.Rp, k.c0, k.Cp, k.pos, k.ok, h1, k.n63, h2⟩

/-- It reads the six fields of `piecesView` (Johnson/P1K8R/PublicAtBatch.lean) alone. -/
theorem piecePlanned_view {a b : HTailF2} (h : piecesView a = piecesView b) {w : Want}
    (k : PiecePlanned b w) : PiecePlanned a w := by
  simp only [piecesView, Prod.mk.injEq] at h
  obtain ⟨h1, -, h3, h4, h5, -⟩ := h
  have ez : a.zOf = b.zOf := by
    funext q
    unfold HTailF2.zOf
    rw [h3, h4]
  have ej : joinPairs a = joinPairs b := by
    unfold joinPairs
    rw [ez]
  refine ⟨by rw [ez, ej]; exact k.mem, by rw [ez, h1]; exact k.tree, by rw [ez]; exact k.row,
    by rw [ez]; exact k.r0, by rw [ez]; exact k.Rp, by rw [ez]; exact k.c0,
    by rw [ez]; exact k.Cp, by rw [ez]; exact k.pos, ?_, by rw [ez]; exact k.n63⟩
  rw [ez]
  exact ⟨by rw [h1]; exact k.ok.tree, by rw [h5]; exact k.ok.c0, k.ok.le, k.ok.pw, k.ok.rp, k.ok.b,
    k.ok.bn, k.ok.dvd, k.ok.fit⟩

/-- The expected piece of call q where there are 128 combinations. -/
def want128 (tl : HTailF2) (q : ℕ) : Want :=
  { call := q, i := 0, row := q, r0 := 0, Rp := 128, c0 := q * tl.mz, Cp := tl.mz }

/-- **At 128 combinations the second computation expects one block of rows, and one piece a
call.** -/
theorem wants_128 {tl : HTailF2} (h : tl.tau = 128) :
    tl.wants = some (1, [want128 tl 0, want128 tl 1]) := by
  have h7 : Nat.log2 128 = 7 := by
    rw [show (128 : ℕ) = 2 ^ 7 by norm_num, Nat.log2_two_pow]
  simp [HTailF2.wants, want128, h, h7]

/-- A list of pieces with one key has one piece. -/
theorem single_of_keys {ps : Array OnBytes.Model.Piece} {k : Nat × Nat × Nat × Nat}
    (h : ps.toList.map pieceKey = [k]) :
    ∃ p, ps.toList = [p] ∧ pieceKey p = k ∧ ps.getD 0 {} = p := by
  cases hl : ps.toList with
  | nil =>
    rw [hl] at h
    exact absurd h (by simp)
  | cons p t =>
    rw [hl] at h
    cases t with
    | nil =>
      refine ⟨p, rfl, by simpa using h, ?_⟩
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hl]
      rfl
    | cons _ _ => exact absurd h (by simp)

/-- **A call's one piece holds all 128 rows**: every combination lies in a piece, and a piece ends
at or before the last. -/
theorem rows_of_single {tl : HTailF2} {q : ℕ} {p : OnBytes.Model.Piece}
    (hp : DgP.piecesL tl q = [p]) (T : DgP.TailOK tl) (hq : q < 2) (h : tl.tau = 128) :
    p.r0 = 0 ∧ p.Rp = 128 := by
  have hq' : q < tl.f9.NC := by
    rw [T.nc]
    exact hq
  obtain ⟨-, -, -, -, c5⟩ := T.pc q hq' p (by rw [hp]; exact List.mem_singleton.2 rfl)
  have a0 := T.rows q hq' 0 (by rw [h]; norm_num)
  have a1 := T.rows q hq' 127 (by rw [h]; norm_num)
  unfold DgP.pieceAt at a0 a1
  rw [hp, List.find?_isSome] at a0 a1
  rw [h] at c5
  obtain ⟨x, hx, b0⟩ := a0
  obtain ⟨y, hy, b1⟩ := a1
  rw [List.mem_singleton.1 hx] at b0
  rw [List.mem_singleton.1 hy] at b1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at b0 b1
  omega

/-- One call's expected piece. -/
theorem planned_call {tl : HTailF2} {q : ℕ} (hq : q < 2) {p : OnBytes.Model.Piece}
    (hl : (tl.zOf q).pieces.toList = [p]) (hg : (tl.zOf q).pieces.getD 0 {} = p)
    (hk : pieceKey p = (tl.ix.ZZ, q, q * tl.mz, tl.mz)) (hr : p.r0 = 0 ∧ p.Rp = 128)
    (hF : piecesFit tl = true)
    (h2 : ∀ x ∈ DgP.piecesL tl q, Fo.PieceOK tl q (tl.zOf q).call.n x) (hz : 0 < tl.mz) :
    PiecePlanned tl (want128 tl q) := by
  have hin : p ∈ (tl.zOf q).pieces.toList := by
    rw [hl]
    exact List.mem_singleton.2 rfl
  have hmem : (q, p) ∈ joinPairs tl := by
    unfold joinPairs
    refine List.mem_flatMap.2 ⟨q, ?_, List.mem_map.2 ⟨p, hin, rfl⟩⟩
    have hc : q = 0 ∨ q = 1 := by omega
    rcases hc with rfl | rfl <;> simp
  simp only [pieceKey, Prod.mk.injEq] at hk
  obtain ⟨k1, k2, k3, k4⟩ := hk
  unfold piecesFit at hF
  have hfit := List.all_eq_true.1 hF (q, p) hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (q, (tl.zOf q).pieces.getD 0 {}) ∈ joinPairs tl
    rw [hg]
    exact hmem
  · show ((tl.zOf q).pieces.getD 0 {}).tree = tl.ix.ZZ
    rw [hg]
    exact k1
  · show q = ((tl.zOf q).pieces.getD 0 {}).row
    rw [hg]
    exact k2.symm
  · show 0 = ((tl.zOf q).pieces.getD 0 {}).r0
    rw [hg]
    exact hr.1.symm
  · show 128 = ((tl.zOf q).pieces.getD 0 {}).Rp
    rw [hg]
    exact hr.2.symm
  · show q * tl.mz = ((tl.zOf q).pieces.getD 0 {}).c0
    rw [hg]
    exact k3.symm
  · show tl.mz = ((tl.zOf q).pieces.getD 0 {}).Cp
    rw [hg]
    exact k4.symm
  · show 0 < ((tl.zOf q).pieces.getD 0 {}).Cp
    rw [hg, k4]
    exact hz
  · show Fo.PieceOK tl q (tl.zOf q).call.n ((tl.zOf q).pieces.getD 0 {})
    rw [hg]
    exact h2 p hin
  · show (tl.zOf q).call.n - ((tl.zOf q).pieces.getD 0 {}).b ≤ 63
    rw [hg]
    exact hfit.1.1.1.2

/-- **ON PLAIN DATA: AT 128 COMBINATIONS, FROM TESTS ON PUBLIC NUMBERS: `PiecePlanned` AT EVERY
EXPECTED PIECE.** -/
theorem planned_of_tests {tl : HTailF2} (h : tl.tau = 128)
    (hB : tl.wants.map (·.1) = some tl.zzBlocks) (hL : piecesLaid tl = true)
    (hF : piecesFit tl = true) (T : DgP.TailOK tl)
    (h2 : ∀ q, q < 2 → ∀ x ∈ DgP.piecesL tl q, Fo.PieceOK tl q (tl.zOf q).call.n x)
    (hz : 0 < tl.mz) :
    ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W, PiecePlanned tl w := by
  intro nbW W hw w hm
  have hw' := wants_128 h
  have hb1 : tl.zzBlocks = 1 := by
    rw [hw'] at hB
    exact (Option.some.inj hB).symm
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj (hw'.symm.trans hw))
  unfold piecesLaid at hL
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, hb1] at hL
  obtain ⟨p0, l0, k0, g0⟩ := single_of_keys (k := (tl.ix.ZZ, 0, 0, tl.mz)) hL.1
  obtain ⟨p1, l1, k1, g1⟩ := single_of_keys (k := (tl.ix.ZZ, 1 + 0, tl.mz, tl.mz)) hL.2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact planned_call (q := 0) (by norm_num) l0 g0 (by rw [k0]; simp)
      (rows_of_single (tl := tl) (q := 0) l0 T (by norm_num) h) hF (h2 0 (by norm_num)) hz
  · exact planned_call (q := 1) (by norm_num) l1 g1 (by rw [k1]; simp)
      (rows_of_single (tl := tl) (q := 1) l1 T (by norm_num) h) hF (h2 1 (by norm_num)) hz

/-- Where there is a matrix the digits' array has a column: the last matrix ends at mz, and has a
row of cells. -/
theorem mz_pos {tl : HTailF2} (hN : 0 < tl.NM) (hC : DgP.colsTest tl = true)
    (hZ : sizesB tl = true) : 0 < tl.mz := by
  unfold sizesB at hZ
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hZ
  obtain ⟨h1, -⟩ := hZ
  have C := colsFacts_of tl hC (fun mu hmu => (h1 mu hmu).2) fun h0 => absurd h0 (by omega)
  have e := C.next (tl.NM - 1) (by omega)
  rw [if_neg (by omega)] at e
  have p := C.pos (tl.NM - 1) (by omega)
  omega

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At every state reached in front of a segment's batching there is a matrix**, where the
description passes its test on its plan: the draw's block's own test on the plan asks one, and its
yes ties the data's number of matrices to the place's list. The walk is that of `drawn_at_batch`
(Johnson/P1K8R/DrawAtBatch.lean), whose lines stand here a further time: its statement does not hand
the number of matrices. -/
theorem matrix_there {Q : Type} {start : Q → S} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {z : Q} {s : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ 0 < tl.NM := by
  obtain ⟨tl, hts, -, -⟩ := drawn_at_batch hS hR O hl h
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨Lk, b8, Xl, -, -, hf8, -, -, -, hLike, hstep⟩ := P1K8S.sitsAt_open hS hR O _ hp
  have hq : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
    have e := O.desc
    subst e
    exact (Keeps.planOk_blocks _ hOk).1
  have h8 := hq b8 (List.mem_of_getElem? hf8)
  rw [hLike.planOk] at h8
  have hks := ((planOk_iff atS _).1 h8).1
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  rw [← e] at h
  obtain ⟨s₇, h7, e7⟩ := view_back hS hR O hx h
  obtain ⟨z', s₆, t₇, b, e', -, hb, R, cs, -, hst⟩ :=
    reach_pred (k := 14 * l + (if l = 24 then 5 else 4) + 2) h7
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
  obtain rfl : b8 = b := Option.some.inj (hf8.symm.trans hb)
  obtain ⟨r, -, -, hm, -, -⟩ := (hstep 0 _ _ _ _ _).1 hst
  obtain ⟨tl₆, h6, -, -, -, hN, -, -, -, -, e6⟩ := hm
  have ht := putTl_tl s₆ tl₆
    { tl₆ with cfF := r.drawn.trits.toArray
               cfFirst := firstColumns (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar } h6
  rw [← e6] at ht
  have ev := LinkJoin.of_readTl (e7.trans (LinkJoin.read_of_tl ht)) tl hts
  have eN : tl.NM = tl₆.NM := congrArg (·.2.2.1) ev
  refine ⟨tl, hts, ?_⟩
  rw [eN, hN]
  exact List.length_pos_of_ne_nil hks

/-- **AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING, AT ALL 25 SEGMENTS: `PiecePlanned` AT
EVERY EXPECTED PIECE.** -/
theorem want_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) :
    ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W, PiecePlanned tl w := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have v : piecesView tl = piecesView Xl.tl :=
    LinkJoin.of_readTl (LinkJoin.planned_at_batch planned_pieces hS hR O hx e3 (z, s) h') tl ht
  obtain ⟨t1, a1, hLaid, hFit, hKey⟩ := public_at_batch hS hR O hl h
  rw [Option.some.inj (a1.symm.trans ht)] at hLaid hFit hKey
  obtain ⟨t2, a2, -, hT⟩ := drawn_at_batch hS hR O hl h
  rw [Option.some.inj (a2.symm.trans ht)] at hT
  obtain ⟨t3, a3, -, hC⟩ := apart_at_batch hS hR O hl h
  rw [Option.some.inj (a3.symm.trans ht)] at hC
  obtain ⟨t4, a4, hZ⟩ := sizes_at_batch hS hR O hl h
  rw [Option.some.inj (a4.symm.trans ht)] at hZ
  obtain ⟨t5, a5, hN⟩ := matrix_there hS hR O hOk hl h
  rw [Option.some.inj (a5.symm.trans ht)] at hN
  have hz := mz_pos hN hC hZ
  have hTX : Xl.tl.tau = 128 := IM.k8_tau_128 hS hR O (by omega) e3
  have hpub : publicB Xl.tl = true := by
    rw [← tests_view v]
    exact publicB_of ⟨hLaid, hFit, hKey⟩
  unfold publicB at hpub
  rw [Bool.and_eq_true, Bool.and_eq_true] at hpub
  have v5 : tl.mz = Xl.tl.mz := congrArg (·.2.2.2.2.1) v
  have T := tests_at_built hS O hl e3
  have R := planned_of_tests hTX (static_at_built hS O hl e3).blocks hpub.1.1 hpub.1.2
    (DgP.tailOK_of_test T.t1) (fun q hq => Fo.pieceOK_of_test (T.t2 q hq))
    (by rw [← v5]; exact hz)
  intro nbW W hw w hm
  have ew : tl.wants = Xl.tl.wants := wants_same (hT.trans hTX.symm) v5
  rw [ew] at hw
  exact piecePlanned_view v (R nbW W hw w hm)

/-- **AND THE EXPECTED PIECES' ROWS LIE IN THE DIGITS' ARRAY OF THE STATE's LEDGER.** -/
theorem rows_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
      w.r0 + w.Rp ≤ (G.trees.getD tl.ix.ZZ {}).R := by
  intro nbW W hw w hm
  have k := want_at_batch hS hR O hOk hl e3 h ht nbW W hw w hm
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have v : piecesView tl = piecesView Xl.tl :=
    LinkJoin.of_readTl (LinkJoin.planned_at_batch planned_pieces hS hR O hx e3 (z, s) h') tl ht
  have ej : joinPairs tl = Fo.allPieces Xl.tl := by
    rw [← joinPairs_all]
    simp only [piecesView, Prod.mk.injEq] at v
    unfold joinPairs HTailF2.zOf
    rw [v.2.2.1, v.2.2.2.1]
  have fr : Fo.Frame Xl.Fp G :=
    LinkJoin.frame_of_looks (LinkJoin.looks_array (looks_at_batch hS hR O hl e3 h hG))
  have t10 := (tests_at_built hS O hl e3).t10 _ (ej ▸ k.mem)
  rw [k.r0, k.Rp, ← k.tree, (fr.2 _).1]
  exact t10

end

end P1K8

#print axioms P1K8.pieceFront_of_planned
#print axioms P1K8.piecePlanned_view
#print axioms P1K8.wants_128
#print axioms P1K8.single_of_keys
#print axioms P1K8.rows_of_single
#print axioms P1K8.planned_call
#print axioms P1K8.planned_of_tests
#print axioms P1K8.mz_pos
#print axioms P1K8.matrix_there
#print axioms P1K8.want_at_batch
#print axioms P1K8.rows_at_batch
