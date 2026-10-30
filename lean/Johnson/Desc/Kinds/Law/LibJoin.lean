-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibJoin.lean: FROM THE OUTPUT HEAD's RELATION ON CELLS (HeadLaw.lean: CellRel) TO THE HEAD's OWN CLAUSES OF THE LIBRARY's FIELD RELATION OF THE HEAD WITH THE COST LEDGER (Policy/Rel/LedgerHead.lean: RF). **PORTED, BY PROGRAM, FROM A TEXT OF THIS PROJECT (IN THE VERSION THAT STOOD WHEN THIS WAS PORTED) THAT IS NOT IN THIS REPOSITORY:
EVERY DEFINITION, STATEMENT AND PROOF BELOW IS THAT TEXT's, TO THE LETTER,** but for the module's path, the namespace and one import: the records of letters that it reads of that import stand here, to the
letter: Same and rc_eq, Wide (two files that are not in this library), in the form that was ported.
  cellsOf c X · weightsOf c · Same Y · Wide · More Y · HeadOwn | NormOwn np H Y t (the clauses of RF, cut in the head's own and the final normalisation's) · rf_of_own (no clause is lost)
  rhoC_eq · rho_eq · hid_eq · sB2_int · sB3_int · dB4_int · ex_eq · dZ_int · K1_eq · K2_eq · lg_eq · top_eq   IDENTITIES BETWEEN INTEGERS: the library's expression at cellsOf c X is the kind's.
  key_cast · headOwn_of_castRel · JoinStatement · join   ONE DIRECTION: the tests on the plan and the request · the next token is a token · Same · Wide · More · the kind's table is the library's EX on 16 bits · CellRel c tab ⇒ HeadOwn at cellsOf c X, over the field in which the program's elements are read.
WHAT IT DOES NOT SAY (that text's own list). The converse. NormOwn (Law/LibJoinNorm.lean). That a verifier's yes gives CellRel. That the premises hold of a description: that its sizes are Wide's; that its request and policy are Y's; that its table is EX. THE CASE WITH PADDING (JV > V) IS OUTSIDE Wide: there the two texts lay the matrix wide out differently. That some cells have CellRel.
The relation over the base field: Johnson/Road/HeadDown.lean leads there from the whole of RF. A TOOL: it holds of all cells and names no description. The two ported files call no name of that text's Kit | Policy | Clip | Table but Same, rc_eq, Wide. WHAT BEARS ON WHAT IS
TAKEN: Y IS A LETTER: that Same (Req.of pol x) holds at a description's request and policy is paid at the seat by Law/LibAtSeat.lean's same_at, but for the record's two words; win, sh, JVa (More) STAY LETTERS · Wide.blocks and Wide.JV follow from its other clauses: harmless · JV = V
FOLLOWS FROM NO TEST THAT THE KIND's planOk NAMES (at ls = 7 planOk passes and JV > V) · sh = 8 likewise (the ranges admit sh = 7, where the library's 2^8 and R23 are the wrong numbers). No chance in it.

-/
import Johnson.Desc.Kinds.Law.Values
import Policy.Rel.LedgerHeadInt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.HeadJoin

open Finset
open VerifiableInference.Desc.Kinds VerifiableInference.Desc.Kinds.Head
open Inst.Model (NormPar)

section Letters
variable [Head.Sizes] [Head.Policy] [Head.Request]

/-- The running text's letters are the relation's numbers. -/
structure Same (y : Inst.Model.Head.Req) : Prop where
  T : Norm.T = 1024
  r : y.r = r
  e : y.e = e
  C : y.pol.C = C
  theta : y.pol.theta = theta
  cap : y.pol.cap = cap

theorem rc_eq {y : Inst.Model.Head.Req} (S : Same y) : RC = y.NB := by
  unfold RC Inst.Model.Head.Req.NB
  rw [S.T, S.r, S.e]

/-- The sizes at which the two layouts of the matrix wide agree. -/
structure Wide : Prop where
  d : Norm.d = 5120
  V : Head.V = 202048
  JV : Head.JV = 202048
  F : Head.F = 24
  blocks : Norm.S2 ∣ 64

end Letters

/-- The library's record of cells, of the kind's. X: the stream's cells. -/
def cellsOf (c : Law.Cells) (X : ℕ → ℕ → ℤ) : Inst.Model.Head.Cells ℤ :=
  ⟨c.cell .wide, c.cell .act, c.cell .row, X⟩

/-- The head's weights, in the field. -/
def weightsOf (c : Law.Cells) : ℕ → ℕ → Law.K := fun j v => ((c.Wh j v : ℤ) : Law.K)

/-- The head's own clauses of the field relation. -/
structure HeadOwn (np : NormPar) (H : ℕ → ℕ → Law.K) (Y : Inst.Model.Head.Req)
    (t : Inst.Model.Head.Cells ℤ) : Prop where
  small : ∀ i < Inst.Model.Head.nT,
    (∀ φ < Inst.Model.Head.nFeat .hf, |t.hf φ i| < 2 ^ 18) ∧
    (∀ φ < Inst.Model.Head.nFeat .hd, |t.hd φ i| < 2 ^ 18) ∧
    ∀ φ < Inst.Model.Head.nFeat .hr, |t.hr φ i| < 2 ^ 18
  keys : ∀ s : Inst.Model.Head.Fam, s ∈ [.HD0, .HD1, .HD2, .HE0, .HE1] → ∀ x i,
    x < Inst.Model.Head.len s → i < Inst.Model.Head.nT →
    Inst.Model.Head.InLut (Policy.LedgerHead.tableOf s)
      (Policy.LedgerHead.key np (t.cast Law.K) H Y s x i)
  row : ∀ n i, 99 ≤ n → n < 120 → i < Inst.Model.Head.nT →
    Inst.Model.Head.InLut (Policy.LedgerHead.tableOf .ROW)
      (Policy.LedgerHead.key np (t.cast Law.K) H Y .ROW n i)
  jc : ∀ i < Inst.Model.Head.nT, Inst.Model.Head.dB4 (t.cast Law.K) Y i = 0 ∧
    Inst.Model.Head.dZ (t.cast Law.K) Y i = 0
  sums : Inst.Model.Head.sB2 (t.cast Law.K) Y = 0 ∧ Inst.Model.Head.sB3 (t.cast Law.K) Y = 0

/-- The other clauses: the final normalisation's. -/
structure NormOwn (np : NormPar) (H : ℕ → ℕ → Law.K) (Y : Inst.Model.Head.Req)
    (t : Inst.Model.Head.Cells ℤ) : Prop where
  small : ∀ i < Inst.Model.Head.nT, ∀ φ < Inst.Model.Head.nFeat .x, |t.x φ i| < 2 ^ 18
  keys : ∀ s : Inst.Model.Head.Fam, s ∈ [.NF, .NFH, .CNF] → ∀ x i,
    x < Inst.Model.Head.len s → i < Inst.Model.Head.nT →
    Inst.Model.Head.InLut (Policy.LedgerHead.tableOf s)
      (Policy.LedgerHead.key np (t.cast Law.K) H Y s x i)
  row : ∀ n i, n < 99 → i < Inst.Model.Head.nT →
    Inst.Model.Head.InLut (Policy.LedgerHead.tableOf .ROW)
      (Policy.LedgerHead.key np (t.cast Law.K) H Y .ROW n i)
  idns : ∀ i < Inst.Model.Head.nT, ∀ k < 17, Inst.Model.Head.N.idn np (t.cast Law.K) i k = 0

/-- **No clause is lost.** -/
theorem rf_of_own {np : NormPar} {H : ℕ → ℕ → Law.K} {Y : Inst.Model.Head.Req}
    {t : Inst.Model.Head.Cells ℤ} (h : HeadOwn np H Y t) (n : NormOwn np H Y t) :
    Policy.LedgerHead.RF np H Y t where
  small := fun i hi => ⟨(h.small i hi).1, (h.small i hi).2.1, (h.small i hi).2.2, n.small i hi⟩
  keys := fun s x i hx hi => by
    cases s
    · exact n.keys .NF (by simp) x i hx hi
    · exact n.keys .NFH (by simp) x i hx hi
    · exact h.keys .HD0 (by simp) x i hx hi
    · exact h.keys .HD1 (by simp) x i hx hi
    · by_cases h99 : x < 99
      · exact n.row x i h99 hi
      · exact h.row x i (by omega) hx hi
    · exact h.keys .HD2 (by simp) x i hx hi
    · exact h.keys .HE0 (by simp) x i hx hi
    · exact h.keys .HE1 (by simp) x i hx hi
    · exact n.keys .CNF (by simp) x i hx hi
  idns := n.idns
  jc := h.jc
  sums := h.sums

/-- The letters that the keys read besides. -/
structure More [Head.Sizes] [Head.Request] [Head.Token] (Y : Inst.Model.Head.Req) :
    Prop where
  sh : Head.sh = 8
  JVa : Head.JVa = 131072
  win : ∀ t, Y.win t = Head.win t

/-- **From the kind's relation on cells to the head's own clauses of the library's.** -/
def JoinStatement : Prop :=
  ∀ [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] (np : NormPar) (sT : ℕ)
    (tab : ℕ → ℕ) (c : Law.Cells) (X : ℕ → ℕ → ℤ) (Y : Inst.Model.Head.Req),
    planOk sT = true → Request.ok = true → Token.y < Head.V → Same Y → Wide → More Y →
    (∀ u, u < 2 ^ 16 → (tab u : ℤ) = Inst.Model.EX u) → Law.CellRel c tab →
    HeadOwn np (weightsOf c) Y (cellsOf c X)

/-! ## The letters -/

section Ints
variable [Head.Sizes] [Head.Policy] [Head.Request] {c : Law.Cells}
  {X : ℕ → ℕ → ℤ} {Y : Inst.Model.Head.Req}

/-- The relation's indicator of the counted positions is the kind's. -/
theorem rhoC_eq (S : Same Y) (i : ℕ) : Y.rhoC i = if costed i = true then 1 else 0 := by
  unfold Inst.Model.Head.Req.rhoC costed checked
  rw [S.T, S.r, S.e]
  by_cases h : r ≤ i ∧ i < min e 1023
  · have h1 : (decide (r ≤ i) && decide (i < e) && decide (i + 1 < 1024)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [if_pos h, if_pos h1]
  · have h1 : ¬ (decide (r ≤ i) && decide (i < e) && decide (i + 1 < 1024)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [if_neg h, if_neg h1]

/-- The relation's indicator of the covered positions is the kind's. -/
theorem rho_eq (S : Same Y) (i : ℕ) : Y.rho i = if checked i = true then 1 else 0 := by
  unfold Inst.Model.Head.Req.rho checked
  rw [S.r, S.e]
  by_cases h : r ≤ i ∧ i < e
  · have h1 : (decide (r ≤ i) && decide (i < e)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact h
    rw [if_pos h, if_pos h1]
  · have h1 : ¬ (decide (r ≤ i) && decide (i < e)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact h
    rw [if_neg h, if_neg h1]

omit [Head.Sizes] [Head.Policy] [Head.Request] in
/-- A hidden number in the two texts. -/
theorem hid_eq (n : Number) (i : ℕ) :
    Inst.Model.Ledger.b256 (fun m => Inst.Model.Head.Dv (cellsOf c X) m i) (99 + n.digits.1)
      n.digits.2 = Law.numZ c n i := by
  unfold Inst.Model.Ledger.b256 Inst.Model.Head.Dv Law.numZ cellsOf
  refine Finset.sum_congr rfl fun l _ => ?_
  show (256 : ℤ) ^ l * (128 + c.cell .row (99 + n.digits.1 + l) i) =
    256 ^ l * (c.cell .row (99 + n.digits.1 + l) i + 128)
  rw [add_comm]

/-! ## The four lines, in integers -/

/-- (B2). -/
theorem sB2_int (S : Same Y) : Inst.Model.Head.sB2 (cellsOf c X) Y =
    (Finset.range Norm.T).sum (fun t => if costed t = true then
      Law.numZ c .paid t + (C : ℤ) * Law.numZ c .over t + Law.numZ c .slackMean t else 0) -
      (theta : ℤ) * (RC : ℤ) := by
  unfold Inst.Model.Head.sB2
  rw [S.T, rc_eq S, ← S.C, ← S.theta]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun i _ => ?_) rfl
  rw [show Inst.Model.Head.hidC (cellsOf c X) i = Law.numZ c .paid i from hid_eq .paid i,
    show Inst.Model.Head.hidB (cellsOf c X) i = Law.numZ c .over i from hid_eq .over i,
    show Inst.Model.Head.hidU (cellsOf c X) i = Law.numZ c .slackMean i from hid_eq .slackMean i,
    Int.cast_id, rhoC_eq S]
  split_ifs <;> simp

/-- (B3). -/
theorem sB3_int (S : Same Y) : Inst.Model.Head.sB3 (cellsOf c X) Y =
    (Finset.range Norm.T).sum (fun t => if costed t = true then
      Law.numZ c .over t + Law.numZ c .slackCap t else 0) -
      (((if RC > 0 then cap else 0 : ℕ) : ℤ)) := by
  unfold Inst.Model.Head.sB3
  rw [S.T, rc_eq S, ← S.cap]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun i _ => ?_) (by split_ifs <;> simp)
  rw [show Inst.Model.Head.hidB (cellsOf c X) i = Law.numZ c .over i from hid_eq .over i,
    show Inst.Model.Head.hidZ (cellsOf c X) i = Law.numZ c .slackCap i from hid_eq .slackCap i,
    Int.cast_id, rhoC_eq S]
  split_ifs <;> simp

/-- (B4). -/
theorem dB4_int (S : Same Y) (i : ℕ) : Inst.Model.Head.dB4 (cellsOf c X) Y i =
    if costed i = true then Law.numZ c .paid i + Law.numZ c .slackClip i - (C : ℤ) else 0 := by
  unfold Inst.Model.Head.dB4
  rw [show Inst.Model.Head.hidC (cellsOf c X) i = Law.numZ c .paid i from hid_eq .paid i,
    show Inst.Model.Head.hidK (cellsOf c X) i = Law.numZ c .slackClip i from hid_eq .slackClip i,
    Int.cast_id, rhoC_eq S, ← S.C]
  split_ifs <;> simp

omit [Head.Policy] [Head.Request] in
/-- A table value in the two texts. -/
theorem ex_eq (Wd : Wide) (v i : ℕ) :
    Inst.Model.Head.ex (cellsOf c X) v i = Law.tvZ c v i := by
  unfold Inst.Model.Head.ex Inst.Model.Head.rd Law.tvZ cellsOf Inst.Model.Head.fEx
  rw [Wd.d, Wd.JV]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun l _ => ?_)
  show (256 : ℤ) ^ l * c.cell .wide (626624 + 202048 * l + v) i =
    256 ^ l * c.cell .wide (4 * 5120 + (3 + l) * 202048 + v) i
  rw [show 626624 + 202048 * l + v = 4 * 5120 + (3 + l) * 202048 + v by ring]

/-- (Z). -/
theorem dZ_int (S : Same Y) (Wd : Wide) (i : ℕ) : Inst.Model.Head.dZ (cellsOf c X) Y i =
    if costed i = true then Law.numZ c .slackTable i +
      (Finset.range JV).sum (fun x => Law.tvZ c x i) - ((JV - V + 1 : ℕ) : ℤ) * 2 ^ Head.F
    else 0 := by
  unfold Inst.Model.Head.dZ
  rw [show Inst.Model.Head.hidS (cellsOf c X) i = Law.numZ c .slackTable i from
      hid_eq .slackTable i, Int.cast_id, rhoC_eq S, Wd.JV, Wd.V, Wd.F]
  simp only [ex_eq Wd]
  split_ifs
  · rw [one_mul]
    rfl
  · rw [zero_mul]

/-- The middle digit. -/
theorem K1_eq (S : Same Y) (Wd : Wide) {v : ℕ} (hv : v < 202048) (i : ℕ) :
    Inst.Model.Head.K1 (cellsOf c X) Y v i = Law.midZ c v i := by
  unfold Inst.Model.Head.K1 Inst.Model.Head.d1 Inst.Model.Head.rd Law.midZ cellsOf
    Inst.Model.Head.fD1
  rw [Wd.d, Wd.JV, Wd.V, Int.cast_id, rho_eq S, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  show 0 + (256 : ℤ) ^ 0 * c.cell .wide (20480 + 202048 * 0 + v) i +
      256 ^ 1 * c.cell .wide (20480 + 202048 * 1 + v) i + 32896 * _ =
    _ + (c.cell .wide (4 * 5120 + v) i + 256 * c.cell .wide (4 * 5120 + 202048 + v) i)
  by_cases hc : checked i = true
  · rw [if_pos hc, if_pos ⟨hv, hc⟩]
    unfold off2
    push_cast
    ring
  · rw [if_neg hc, if_neg fun h => hc h.2]
    ring

/-- The low digit. -/
theorem K2_eq (S : Same Y) (Wd : Wide) {v : ℕ} (hv : v < 202048) (i : ℕ) :
    Inst.Model.Head.K2 (cellsOf c X) Y v i = Law.lowZ c v i := by
  unfold Inst.Model.Head.K2 Inst.Model.Head.d2 Law.lowZ cellsOf Inst.Model.Head.fD2
  rw [Wd.d, Wd.JV, Wd.V, Int.cast_id, rho_eq S]
  show c.cell .wide (424576 + v) i + 128 * _ = _ + c.cell .wide (4 * 5120 + 2 * 202048 + v) i
  by_cases hc : checked i = true
  · rw [if_pos hc, if_pos ⟨hv, hc⟩]
    unfold off1
    push_cast
    ring
  · rw [if_neg hc, if_neg fun h => hc h.2]
    ring

omit [Head.Policy] [Head.Request] in
/-- A logit. -/
theorem lg_eq (Wd : Wide) (i v : ℕ) :
    Inst.Model.Head.lg (cellsOf c X) c.Wh i v = Law.logit c i v := by
  unfold Inst.Model.Head.lg Law.logit
  rw [Law.sumZ_eq, Wd.d]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Inst.Model.Head.nrm Inst.Model.Head.rd Law.act cellsOf Inst.Model.Head.fNrm
  rw [Wd.d, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  show (0 + (256 : ℤ) ^ 0 * c.cell .act (5120 * 0 + j) i +
    256 ^ 1 * c.cell .act (5120 * 1 + j) i) * _ = _
  ring_nf

variable [Head.Token]

/-- What is left of a margin above its two lower digits. -/
theorem top_eq (S : Same Y) (Wd : Wide) (M : More Y) {v : ℕ} (hv : v < 202048) (i : ℕ) :
    Inst.Model.Head.mg (cellsOf c X) c.Wh Y v i - 2 ^ 8 * Inst.Model.Head.K1 (cellsOf c X) Y v i -
      Inst.Model.Head.K2 (cellsOf c X) Y v i = Law.topNum c v i := by
  rw [K1_eq S Wd hv, K2_eq S Wd hv]
  unfold Inst.Model.Head.mg Law.topNum Law.liftZ
  rw [lg_eq Wd, lg_eq Wd, M.win, M.sh, Wd.V, Int.cast_id, Int.cast_id, rho_eq S, rhoC_eq S,
    show Inst.Model.Head.hidC (cellsOf c X) i = Law.numZ c .paid i from hid_eq .paid i,
    show Inst.Model.Head.hidB (cellsOf c X) i = Law.numZ c .over i from hid_eq .over i]
  unfold BIG
  by_cases hc : checked i = true <;> by_cases hk : costed i = true <;>
    by_cases hw : v < win i <;>
    first
      | (simp [hc, hk, hw, hv]; done)
      | (simp [hc, hk, hw, hv]; ring)

/-! ## From integers to the field -/

omit [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] in
/-- A key on integer cells, read in the field. -/
theorem key_cast (np : NormPar) (t : Inst.Model.Head.Cells ℤ) (s : Inst.Model.Head.Fam)
    (x i : ℕ) : Policy.LedgerHead.key np (t.cast Law.K) (weightsOf c) Y s x i =
      ((Policy.LedgerHead.key np t c.Wh Y s x i : ℤ) : Law.K) :=
  (Policy.LedgerHead.map_key (Int.castRingHom Law.K) np t c.Wh Y s x i).symm

/-- **From equalities of casts to the head's own clauses.** -/
theorem headOwn_of_castRel (np : NormPar) {tab : ℕ → ℕ} (S : Same Y) (Wd : Wide) (M : More Y)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : ℤ) = Inst.Model.EX u) (h : Law.CastRel c tab) :
    HeadOwn np (weightsOf c) Y (cellsOf c X) where
  small := fun i _ => by
    have hs : ∀ m f, |c.cell m f i| < 2 ^ 18 := fun m f => by
      have := h.small m f i
      rw [Int.abs_eq_natAbs]
      exact_mod_cast this
    exact ⟨fun φ _ => hs .wide φ, fun φ _ => hs .act φ, fun φ _ => hs .row φ⟩
  keys := fun s hs x i hx hi => by
    have hi' : i < Norm.T := by rw [S.T]; exact hi
    rw [key_cast]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · have hx' : x < 202048 := hx
      obtain ⟨n, hn, e⟩ := h.top i hi' x (by rw [Wd.JV]; exact hx')
      refine ⟨n, hn, ?_⟩
      show ((Inst.Model.Head.mg (cellsOf c X) c.Wh Y x i -
        2 ^ 8 * Inst.Model.Head.K1 (cellsOf c X) Y x i -
        Inst.Model.Head.K2 (cellsOf c X) Y x i : ℤ) : Law.K) = ((2 ^ 23 * (n : ℤ) : ℤ) : Law.K)
      rw [top_eq S Wd M hx', e, M.sh]
    · have hx' : x < 202048 := hx
      obtain ⟨n, hn, e⟩ := h.mid i hi' x (by rw [Wd.JV]; exact hx')
      refine ⟨n, hn, ?_⟩
      show ((Inst.Model.Head.K1 (cellsOf c X) Y x i : ℤ) : Law.K) = (((n : ℕ) : ℤ) : Law.K)
      rw [K1_eq S Wd hx', e]
    · have hx' : x < 202048 := hx
      obtain ⟨n, hn, e⟩ := h.low i hi' x (by rw [Wd.JV]; exact hx')
      refine ⟨n, hn, ?_⟩
      show ((Inst.Model.Head.K2 (cellsOf c X) Y x i : ℤ) : Law.K) = (((n : ℕ) : ℤ) : Law.K)
      rw [K2_eq S Wd hx', e]
    · have hx0 : x < 131072 := hx
      have hx' : x < 202048 := by omega
      obtain ⟨u, hu, e⟩ := h.row i hi' x (by rw [Wd.JV]; exact hx')
      refine ⟨u, hu, ?_⟩
      show ((Inst.Model.Head.K1 (cellsOf c X) Y x i +
        2 ^ 16 * Inst.Model.Head.ex (cellsOf c X) x i : ℤ) : Law.K) =
        (((u : ℤ) + 2 ^ 16 * Inst.Model.EX u : ℤ) : Law.K)
      rw [K1_eq S Wd hx', ex_eq Wd, e, htab u hu]
    · have hx0 : x < 70976 := hx
      have hx' : 131072 + x < 202048 := by omega
      obtain ⟨u, hu, e⟩ := h.row i hi' (131072 + x) (by rw [Wd.JV]; exact hx')
      refine ⟨u, hu, ?_⟩
      show ((Inst.Model.Head.K1 (cellsOf c X) Y (131072 + x) i +
        2 ^ 16 * Inst.Model.Head.ex (cellsOf c X) (131072 + x) i : ℤ) : Law.K) =
        (((u : ℤ) + 2 ^ 16 * Inst.Model.EX u : ℤ) : Law.K)
      rw [K1_eq S Wd hx', ex_eq Wd, e, htab u hu]
  row := fun n i h99 hn hi => by
    have hi' : i < Norm.T := by rw [S.T]; exact hi
    obtain ⟨b0, b1⟩ := h.bytes i hi' (n - 99) (by omega)
    have en : NR + (n - 99) = n := by unfold NR; omega
    rw [en] at b0 b1
    rw [key_cast]
    refine ⟨(c.cell .row n i + 128).toNat, ?_, ?_⟩
    · show (c.cell .row n i + 128).toNat < 2 ^ 8
      omega
    · have hmu : Inst.Model.Ledger.mu n = 1 := by
        unfold Inst.Model.Ledger.mu
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
      refine congrArg (fun z : ℤ => (z : Law.K)) ?_
      show ((Inst.Model.Ledger.mu n : ℤ) : ℤ) * (128 + c.cell .row n i) =
        (((c.cell .row n i + 128).toNat : ℕ) : ℤ)
      rw [hmu, one_mul, Int.toNat_of_nonneg b0, add_comm]
  jc := fun i hi => by
    have hi' : i < Norm.T := by rw [S.T]; exact hi
    have e1 : Inst.Model.Head.dB4 ((cellsOf c X).cast Law.K) Y i =
        ((Inst.Model.Head.dB4 (cellsOf c X) Y i : ℤ) : Law.K) :=
      (Inst.Model.Head.map_dB4 (Int.castRingHom Law.K) (cellsOf c X) Y i).symm
    have e2 : Inst.Model.Head.dZ ((cellsOf c X).cast Law.K) Y i =
        ((Inst.Model.Head.dZ (cellsOf c X) Y i : ℤ) : Law.K) :=
      (Inst.Model.Head.map_dZ (Int.castRingHom Law.K) (cellsOf c X) Y i).symm
    rw [e1, e2, dB4_int S, dZ_int S Wd]
    by_cases hk : costed i = true
    · rw [if_pos hk, if_pos hk, Int.cast_sub, Int.cast_sub, h.clip i hi' hk, h.table i hi' hk]
      exact ⟨sub_self _, sub_self _⟩
    · rw [if_neg hk, if_neg hk]
      exact ⟨Int.cast_zero, Int.cast_zero⟩
  sums := by
    have e1 : Inst.Model.Head.sB2 ((cellsOf c X).cast Law.K) Y =
        ((Inst.Model.Head.sB2 (cellsOf c X) Y : ℤ) : Law.K) :=
      (Inst.Model.Head.map_sB2 (Int.castRingHom Law.K) (cellsOf c X) Y).symm
    have e2 : Inst.Model.Head.sB3 ((cellsOf c X).cast Law.K) Y =
        ((Inst.Model.Head.sB3 (cellsOf c X) Y : ℤ) : Law.K) :=
      (Inst.Model.Head.map_sB3 (Int.castRingHom Law.K) (cellsOf c X) Y).symm
    rw [e1, e2, sB2_int S, sB3_int S, Int.cast_sub, Int.cast_sub, h.mean, h.count]
    exact ⟨sub_self _, sub_self _⟩

end Ints

/-- **The statement holds.** -/
theorem join : JoinStatement := fun np _ _ _ _ _ hplan hreq hy S Wd M htab h =>
  headOwn_of_castRel np S Wd M htab (Law.castRel_of_cellRel (Law.planFacts hplan) hreq hy h)

end VerifiableInference.Desc.Kinds.HeadJoin

#print axioms VerifiableInference.Desc.Kinds.HeadJoin.rf_of_own
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.rhoC_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.rho_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.hid_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.sB2_int
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.sB3_int
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.dB4_int
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.ex_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.dZ_int
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.K1_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.K2_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.lg_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.top_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.key_cast
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.headOwn_of_castRel
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.join
