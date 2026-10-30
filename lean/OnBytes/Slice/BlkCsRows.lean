-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsRows.lean: the rows that the program's code switch makes, in the field.

The program's code switch (OnBytes/Iop/Cs.lean) moves a claim on three folded rows to rows on a new
oracle message: the old claim, carried over, and three rows of generator matrices for each drawn
position. It writes these rows in short forms: tensors, runs of coefficients at equal distances,
boxes of a table's index. This file reads each row's coefficient on each entry of the new message's
two tables as an element of the field `GE` (`coefAt`). The results are the closed forms of
OnBytes/Slice/SimCs.lean for the format's own code switch, Fmt/M1Cs.lean (`cut`, `moved`, `wM`,
`wT`).

The case that is treated: a switch into a stage of a proximity test. There is no kept member, there
are two mask rows, the main row's message is in the new main table from index 0 on, and the rest
(the mask rows' messages and all tails) is in the new mask table side by side from index 0 on.
`FrameOK` says this of the record that the program computes once for a switch. `frame_ok` and
`make_flat` get it from conditions on the statement, the old rows and the target.

Main definitions: `pieceStep`, `messageTensor`, `FrameOK`, `genMain`, `genMask`, `carriedRow`,
`symAtB`.
Main theorems.
 `switchPieces_flat`: a stretch whose entries are side by side is one piece.
 `coefAt_restE`, `coefAt_restF`: what coefficients on such a stretch add to a row.
 `get_flat`, `make_flat`: entry i of the rest is at the index i, before the pad.
 `pick_block`, `formAt_switchLift`, `switchBox_some`, `readE_switchOnBox`: vectors that are carried
   to a block of a table.
 `cut_generatorTail`, `cut_generatorMessage`, `cut_messageTensor`: the program's rows of a generator
   matrix are the format's.
 `gen_main`, `gen_mask`, `gen_target`: the three rows of a draw.
 `carried_main`, `carried_mask`: the carried claim.
 `switchRows_eq`: which rows there are, and in which order.

Not claimed. Nothing on the run of the block, on the sample's row or on the batching. Nothing on an
index beyond a table's index bits. Nothing on a switch with kept members, or with a pad among the
entries of the rest.
-/
import OnBytes.Iop.Cs
import OnBytes.Slice.BlkRow
import OnBytes.Slice.SimCs
import OnBytes.Slice.ProgCodes
import OnBytes.Slice.BlkTens

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## A stretch without a gap is one piece -/

/-- One step of the loop of `switchPieces`: entry number i of the stretch goes on with the open
piece or begins a new one. -/
def pieceStep (places : SwitchPlaces) (first : ℕ) (s : List SwitchPiece × Option OpenPiece)
    (i : ℕ) : List SwitchPiece × Option OpenPiece :=
  let p := places.get (first + i)
  match s.2 with
  | none => (s.1, some ⟨i, p, none, p⟩)
  | some o =>
    match o.step with
    | none => (s.1, some { o with step := some (p - o.first), last := p })
    | some d =>
      if p == o.last + d then (s.1, some { o with last := p })
      else (o.close i :: s.1, some ⟨i, p, none, p⟩)

/-- `switchPieces` is that loop, and then the open piece is closed. -/
theorem switchPieces_eq (places : SwitchPlaces) (first count : ℕ) :
    switchPieces places first count
      = match ((List.range count).foldl (pieceStep places first) ([], none)).2 with
        | none => []
        | some o => (o.close count ::
            ((List.range count).foldl (pieceStep places first) ([], none)).1).reverse :=
  rfl

/-- The loop after the first two entries of a stretch whose entries are side by side from place a
on: one piece is open, with the step 1. -/
theorem pieces_loop (places : SwitchPlaces) (first a : ℕ) : ∀ n : ℕ,
    (∀ e, e < n + 2 → places.get (first + e) = a + e) →
    (List.range (n + 2)).foldl (pieceStep places first) ([], none)
      = ([], some ⟨0, a, some 1, a + (n + 1)⟩)
  | 0, h => by
    have h0 : places.get (first + 0) = a := h 0 (by omega)
    have h1 : places.get (first + 1) = a + 1 := h 1 (by omega)
    show pieceStep places first (pieceStep places first ([], none) 0) 1 = _
    unfold pieceStep
    rw [h0, h1]
    show (([] : List SwitchPiece), some (⟨0, a, some (a + 1 - a), a + 1⟩ : OpenPiece)) = _
    rw [Nat.add_sub_cancel_left]
  | n + 1, h => by
    have hn : places.get (first + (n + 2)) = a + (n + 1) + 1 := h (n + 2) (by omega)
    rw [List.range_succ, List.foldl_append, pieces_loop places first a n fun e he => h e (by omega)]
    show pieceStep places first ([], some ⟨0, a, some 1, a + (n + 1)⟩) (n + 2) = _
    unfold pieceStep
    rw [hn]
    show (if (a + (n + 1) + 1 == a + (n + 1) + 1) = true then
      (([] : List SwitchPiece), some (⟨0, a, some 1, a + (n + 1) + 1⟩ : OpenPiece)) else _) = _
    rw [if_pos (beq_self_eq_true _)]
    rfl

/-- A stretch whose entries are side by side from place a on is one piece. -/
theorem switchPieces_flat (places : SwitchPlaces) (first count a : ℕ) (hc : 0 < count)
    (h : ∀ e, e < count → places.get (first + e) = a + e) :
    switchPieces places first count = [⟨0, count, a, 1⟩] := by
  rw [switchPieces_eq]
  obtain rfl | ⟨n, rfl⟩ : count = 1 ∨ ∃ n, count = n + 2 := by
    rcases count with _ | _ | n
    · omega
    · exact Or.inl rfl
    · exact Or.inr ⟨n, rfl⟩
  · have h0 : places.get (first + 0) = a := h 0 (by omega)
    have e : (List.range 1).foldl (pieceStep places first) ([], none)
        = ([], some ⟨0, a, none, a⟩) := by
      show pieceStep places first ([], none) 0 = _
      unfold pieceStep
      rw [h0]
    rw [e]
    rfl
  · rw [pieces_loop places first a n h]
    rfl

/-- A stretch without an entry has no piece. -/
theorem switchPieces_zero (places : SwitchPlaces) (first : ℕ) :
    switchPieces places first 0 = [] := rfl

/-! ## What a run without a gap gives -/

/-- A run with the step 1 from place a on gives its coefficients, moved up by a places. -/
theorem runAt_unit (g : ℕ) (part : Part) (a : ℕ) (c : Coeffs)
    (hz : ∀ j, c.size ≤ j → readE (c.get j) = 0) (o : ℕ) (part' : Part) (i : ℕ) :
    runAt ⟨g, part, a, 1, c⟩ o part' i
      = if g == o && part == part' then moved a (fun j => readE (c.get j)) i else 0 := by
  unfold runAt runHits moved
  simp only [Nat.div_one, Nat.mod_one]
  by_cases h1 : (g == o && part == part') = true
  · by_cases h2 : a ≤ i
    · by_cases h3 : i - a < c.size
      · simp [h1, h2, h3]
      · simp [h1, h2, h3, hz (i - a) (by omega)]
    · simp [h1, h2]
  · simp [h1]

/-- The first count entries of an array, read in the field, are the array's reading cut at count. -/
theorem readV_extract (coeff : Array E) (count : ℕ) :
    readV (coeff.extract 0 count) = cut count (readV coeff) := by
  funext j
  by_cases h : j < count
  · rw [cut_of_lt h, readV_eq_readL, readV_eq_readL, Array.toList_extract,
      List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
    unfold readL
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]
  · rw [cut_of_le (by omega), readV_of_le _ _ (by rw [Array.size_extract]; omega)]

/-- A run of coefficients over the extension field, side by side from place a on. -/
theorem runAt_own (g : ℕ) (part : Part) (a count : ℕ) (coeff : Array E) (o : ℕ) (part' : Part)
    (i : ℕ) :
    runAt ⟨g, part, a, 1, .own (coeff.extract 0 count)⟩ o part' i
      = if g == o && part == part' then moved a (cut count (readV coeff)) i else 0 := by
  rw [runAt_unit g part a (.own (coeff.extract 0 count))
    (fun j hj => readV_of_le (coeff.extract 0 count) j hj), ← readV_extract]
  rfl

/-- A run of coefficients over the base field, side by side from place a on. -/
theorem runAt_stretch (g : ℕ) (part : Part) (a count : ℕ) (coeff : Array F) (o : ℕ) (part' : Part)
    (i : ℕ) :
    runAt ⟨g, part, a, 1, .stretch coeff 0 (count - 0)⟩ o part' i
      = if g == o && part == part' then
          moved a (cut count fun j => algebraMap GF GE (toF (coeff.getD j 0))) i else 0 := by
  have hget : (fun j => readE ((Coeffs.stretch coeff 0 (count - 0)).get j))
      = cut count fun j => algebraMap GF GE (toF (coeff.getD j 0)) := by
    funext j
    show readE (if j < count - 0 then OnBytes.ofF (coeff.getD (0 + j) 0) else zeroE) = _
    rw [Nat.sub_zero, Nat.zero_add]
    by_cases h : j < count
    · rw [if_pos h, cut_of_lt h, readE_ofF]
    · rw [if_neg h, cut_of_le (by omega), readE_zero]
  rw [runAt_unit g part a _ fun j hj => ?_, hget]
  have h : ¬ j < count - 0 := Nat.not_lt.2 hj
  show readE (if j < count - 0 then OnBytes.ofF (coeff.getD (0 + j) 0) else zeroE) = 0
  rw [if_neg h, readE_zero]

/-! ## Coefficients on a stretch of the rest -/

/-- Coefficients over the extension field on a stretch whose entries are side by side from place
a on. -/
theorem coefAt_restE (row : Row) (g : ℕ) (part : Part) (places : SwitchPlaces) (first count a : ℕ)
    (h : ∀ e, e < count → places.get (first + e) = a + e) (coeff : Array E) (o : ℕ) (part' : Part)
    (i : ℕ) :
    coefAt (switchAddRestE row g part (switchPieces places first count) coeff) o part' i
      = coefAt row o part' i
        + if g == o && part == part' then moved a (cut count (readV coeff)) i else 0 := by
  rcases Nat.eq_zero_or_pos count with rfl | hc
  · have hz : moved a (cut 0 (readV coeff)) i = 0 := by
      unfold moved cut
      simp
    rw [switchPieces_zero, hz, ite_self, add_zero]
    rfl
  · rw [switchPieces_flat places first count a hc h]
    show coefAt (row.addRun g part a 1 (.own (coeff.extract 0 count))) o part' i = _
    rw [coefAt_addRun, runAt_own]

/-- The same for coefficients over the base field. -/
theorem coefAt_restF (row : Row) (g : ℕ) (part : Part) (places : SwitchPlaces) (first count a : ℕ)
    (h : ∀ e, e < count → places.get (first + e) = a + e) (coeff : Array F) (o : ℕ) (part' : Part)
    (i : ℕ) :
    coefAt (switchAddRestF row g part (switchPieces places first count) coeff) o part' i
      = coefAt row o part' i + if g == o && part == part' then
          moved a (cut count fun j => algebraMap GF GE (toF (coeff.getD j 0))) i else 0 := by
  rcases Nat.eq_zero_or_pos count with rfl | hc
  · have hz : moved a (cut 0 fun j => algebraMap GF GE (toF (coeff.getD j 0))) i = 0 := by
      unfold moved cut
      simp
    rw [switchPieces_zero, hz, ite_self, add_zero]
    rfl
  · rw [switchPieces_flat places first count a hc h]
    show coefAt (row.addRun g part a 1 (.stretch coeff 0 (count - 0))) o part' i = _
    rw [coefAt_addRun, runAt_stretch]

/-! ## The places of the rest, before the pad -/

/-- Stepping over pad entries that all come later changes nothing. -/
theorem foldl_pad (i : ℕ) : ∀ pad : List ℕ, (∀ p ∈ pad, i < p) →
    pad.foldl (fun j p => if p ≤ j then j + 1 else j) i = i
  | [], _ => rfl
  | p :: pad, h => by
    have hp : ¬ p ≤ i := Nat.not_le.2 (h p List.mem_cons_self)
    rw [List.foldl_cons, if_neg hp]
    exact foldl_pad i pad fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- If the block of the rest is a whole table, entry i of the rest is at the index i, as
long as the pad's entries come later. -/
theorem get_flat (P : SwitchPlaces) (h0 : P.cut.firstRow = 0) (hb : P.cut.bits = P.rowBits) (i : ℕ)
    (hp : ∀ p ∈ P.pad, i < p) : P.get i = i := by
  unfold SwitchPlaces.get cutIndex
  rw [foldl_pad i P.pad hp, h0, hb, Nat.zero_add]
  exact Nat.mod_add_div' i (2 ^ P.rowBits)

/-! ## Variables that pick a block -/

/-- No inserted variable: nothing changes. -/
theorem pick_none (F : ℕ → GE) (pos value J : ℕ) :
    (if J / 2 ^ pos % 2 ^ 0 = value % 2 ^ 0 then 1 else 0) * F (unshift pos 0 J) = F J := by
  have hu : unshift pos 0 J = J := by
    unfold unshift
    rw [Nat.add_zero]
    exact Nat.mod_add_div J (2 ^ pos)
  rw [pow_zero, Nat.mod_one, Nat.mod_one, if_pos rfl, one_mul, hu]

/-- Variables above a vector of 2^vars entries that pick the block number value: the vector
is in that block, and 0 in all others. -/
theorem pick_block (F : ℕ → GE) (vars cnt value J : ℕ) (hJ : J < 2 ^ (vars + cnt))
    (hv : value < 2 ^ cnt) :
    (if J / 2 ^ vars % 2 ^ cnt = value % 2 ^ cnt then 1 else 0) * F (unshift vars cnt J)
      = moved (value * 2 ^ vars) (cut (2 ^ vars) F) J := by
  have hm : 0 < 2 ^ vars := Nat.two_pow_pos vars
  have hq : J / 2 ^ vars < 2 ^ cnt := Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hJ)
  have hu : unshift vars cnt J = J % 2 ^ vars := by
    unfold unshift
    rw [Nat.div_eq_of_lt hJ, Nat.mul_zero, Nat.add_zero]
  rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hv, hu]
  rcases Nat.lt_trichotomy (J / 2 ^ vars) value with h | h | h
  · rw [if_neg (Nat.ne_of_lt h), zero_mul, moved_of_lt ((Nat.div_lt_iff_lt_mul hm).1 h)]
  · have hJ' : value * 2 ^ vars + J % 2 ^ vars = J := by
      rw [← h, Nat.mul_comm]
      exact Nat.div_add_mod J (2 ^ vars)
    have hle : value * 2 ^ vars ≤ J := by omega
    have hsub : J - value * 2 ^ vars = J % 2 ^ vars := by omega
    rw [if_pos h, one_mul, moved_of_le hle, hsub, cut_of_lt (Nat.mod_lt J hm)]
  · have h1 : (value + 1) * 2 ^ vars ≤ J := (Nat.le_div_iff_mul_le hm).1 h
    rw [Nat.succ_mul] at h1
    rw [if_neg (Nat.ne_of_gt h), zero_mul, moved_of_le (by omega), cut_of_le (by omega)]

/-- A vector on the old main row's message, carried to the new main table, if the block of the
message is the whole table: the vector from index 0 on, and then 0. -/
theorem formAt_switchLift (c : Form) (vars k tb : ℕ) (hc : ∀ v ∈ c.tensors, v.vars = vars)
    (hk : k ≤ vars) (hv : vars ≤ tb) (J : ℕ) (hJ : J < 2 ^ tb) :
    formAt (switchLift c vars ⟨.main, k, 0⟩ k tb) J = cut (2 ^ vars) (formAt c) J := by
  have h1 : ∀ v ∈ c.tensors, k ≤ v.vars := fun v hv' => by rw [hc v hv']; exact hk
  have h2 : ∀ v ∈ (c.insertChoice k (k - k) (0 / 2 ^ k)).tensors, vars + (k - k) ≤ v.vars := by
    intro v hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv'
    rw [vars_insertChoice u _ _ _ (h1 u hu), hc u hu]
  show readE (((c.insertChoice k (k - k) (0 / 2 ^ k)).insertChoice (vars + (k - k))
    (tb - (vars + (k - k))) 0).entry J) = _
  refine (Form.entry_insertChoice rdE _ _ _ _ J h2).trans ?_
  have hin : ∀ i, rdE.val ((c.insertChoice k (k - k) (0 / 2 ^ k)).entry i) = formAt c i := by
    intro i
    refine (Form.entry_insertChoice rdE c _ _ _ i h1).trans ?_
    rw [Nat.sub_self]
    exact pick_none (formAt c) k _ i
  rw [hin, Nat.sub_self, Nat.add_zero,
    pick_block (formAt c) vars (tb - vars) 0 J (by rw [Nat.add_sub_cancel' hv]; exact hJ)
      (Nat.two_pow_pos _), Nat.zero_mul, moved_zero]

/-! ## The box of a mask row's message -/

/-- If a stretch whose entries are side by side from place first on has a box, the box has the
distance 1 and begins at first, which is a multiple of the stretch's length. -/
theorem switchBox_some (places : SwitchPlaces) (first vars : ℕ) (b : SwitchBox)
    (hflat : ∀ e, e < 2 ^ vars → places.get (first + e) = first + e)
    (h : switchBox places first vars = some b) :
    b = ⟨0, first⟩ ∧ first % 2 ^ vars = 0 := by
  unfold switchBox at h
  by_cases hv : vars = 0
  · simp [hv] at h
  · have h0 : places.get first = first := hflat 0 (Nat.two_pow_pos vars)
    have h1 : places.get (first + 1) = first + 1 := hflat 1 (Nat.one_lt_two_pow hv)
    simp only [h0, h1, Nat.add_sub_cancel_left, Nat.div_one] at h
    split_ifs at h with c1 c2 c3 c4
    have hb : b = ⟨ceilLog2 1, first⟩ := (Option.some.inj h).symm
    refine ⟨hb, ?_⟩
    simpa using c4

/-- A tensor on a box with the distance 1: the tensor's entries from the box's first index on, and
0 elsewhere. -/
theorem readE_switchOnBox (v : Tensor) (vars tb first J : ℕ) (hvv : v.vars = vars)
    (hd : first % 2 ^ vars = 0) (hle : vars ≤ tb) (hf : first < 2 ^ tb) (hJ : J < 2 ^ tb) :
    readE ((switchOnBox ⟨0, first⟩ v vars tb).entry J)
      = moved first (cut (2 ^ vars) fun j => readE (v.entry j)) J := by
  have hpow : 2 ^ vars * 2 ^ (tb - vars) = 2 ^ tb := by rw [← pow_add, Nat.add_sub_cancel' hle]
  have hin : ∀ i, rdE.val ((v.insertChoice 0 0 (first % 2 ^ 0)).entry i) = readE (v.entry i) := by
    intro i
    refine (Tensor.entry_insertChoice rdE v 0 0 _ i (Nat.zero_le _)).trans ?_
    exact pick_none (fun j => readE (v.entry j)) 0 _ i
  show readE (((v.insertChoice 0 0 (first % 2 ^ 0)).insertChoice (0 + vars) (tb - 0 - vars)
    (first / 2 ^ (0 + vars))).entry J) = _
  refine (Tensor.entry_insertChoice rdE _ _ _ _ J
    (by rw [vars_insertChoice v 0 0 _ (Nat.zero_le _), hvv]; omega)).trans ?_
  rw [hin, Nat.zero_add, Nat.sub_zero,
    pick_block (fun j => readE (v.entry j)) vars (tb - vars) (first / 2 ^ vars) J
      (by rw [Nat.add_sub_cancel' hle]; exact hJ)
      (Nat.div_lt_of_lt_mul (by rw [hpow]; exact hf)),
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)]

/-! ## The generator's rows, at the format's points -/

/-- The program's row of the generator on the tail is the format's (`wT`), if logN ≤ 32 and
x < 2^logN. -/
theorem cut_generatorTail (c : OnBytes.Code) (x : ℕ) (ha : c.logN ≤ 32) (hx : x < 2 ^ c.logN) :
    (cut c.r fun j => algebraMap GF GE (toF ((generatorTail c x).getD j 0))) = wT (codeOf c) x := by
  funext j
  show (if j < c.r then algebraMap GF GE (toF ((generatorTail c x).getD j 0)) else 0)
    = if j < c.r then algebraMap GF GE (toF (Fmt.M1.point c.logN x) ^ j) else 0
  by_cases h : j < c.r
  · rw [if_pos h, if_pos h, toF_generatorTail c x j h, toF_codePoint c.logN x ha hx]
  · rw [if_neg h, if_neg h]

/-- The program's row of the generator on the message, written out, is the format's (`wM`), if
logN ≤ 32 and x < 2^logN. -/
theorem cut_generatorMessage (c : OnBytes.Code) (x : ℕ) (ha : c.logN ≤ 32)
    (hx : x < 2 ^ c.logN) :
    (cut c.ell fun j => algebraMap GF GE (toF ((generatorMessage c x).getD j 0)))
      = wM (codeOf c) x := by
  funext j
  show (if j < c.ell then algebraMap GF GE (toF ((generatorMessage c x).getD j 0)) else 0)
    = if j < c.ell then algebraMap GF GE (toF (Fmt.M1.point c.logN x) ^ (c.r + j)) else 0
  by_cases h : j < c.ell
  · rw [if_pos h, if_pos h, toF_generatorMessage c x j h, toF_codePoint c.logN x ha hx]
  · rw [if_neg h, if_neg h]

/-- The tensor of the generator's row on a message whose length is a power of two. -/
def messageTensor (c : OnBytes.Code) (x : ℕ) : Tensor :=
  Tensor.product ((generatorAt c x).f.take c.logEll) (OnBytes.ofF (generatorAt c x).messageScale)

/-- With a message whose length is a power of two, the message has no more index bits than message
and tail together. -/
theorem logEll_le_logDim (c : OnBytes.Code) (hpow : c.ell = 2 ^ c.logEll) :
    c.logEll ≤ c.logDim :=
  (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (hpow ▸ ell_le_logDim c)

/-- That tensor has a variable for each index bit of the message. -/
theorem vars_messageTensor (c : OnBytes.Code) (x : ℕ) (hpow : c.ell = 2 ^ c.logEll) :
    (messageTensor c x).vars = c.logEll := by
  unfold messageTensor Tensor.vars Tensor.product
  rw [List.length_map, List.length_take, generatorAt_f, length_squaresOf]
  exact Nat.min_eq_left (logEll_le_logDim c hpow)

/-- The same row as a tensor is the format's, under the same conditions, if the message's length
is a power of two. -/
theorem cut_messageTensor (c : OnBytes.Code) (x : ℕ) (ha : c.logN ≤ 32) (hx : x < 2 ^ c.logN)
    (hpow : c.ell = 2 ^ c.logEll) :
    (cut (2 ^ c.logEll) fun j => readE ((messageTensor c x).entry j)) = wM (codeOf c) x := by
  have hpos : 0 < c.ell := hpow ▸ Nat.two_pow_pos _
  funext j
  rw [← hpow]
  show (if j < c.ell then readE ((messageTensor c x).entry j) else 0)
    = if j < c.ell then algebraMap GF GE (toF (Fmt.M1.point c.logN x) ^ (c.r + j)) else 0
  by_cases h : j < c.ell
  · have hj : j < 2 ^ min c.logEll c.logDim := by
      rw [Nat.min_eq_left (logEll_le_logDim c hpow), ← hpow]
      exact h
    rw [if_pos h, if_pos h]
    unfold messageTensor
    rw [readE_product, readE_ofF, toF_messageScale c x hpos, generatorAt_f, take_squaresOf,
      toF_productIndex_squares, Nat.mod_eq_of_lt hj, ← map_mul, ← pow_add,
      toF_codePoint c.logN x ha hx]
  · rw [if_neg h, if_neg h]

/-! ## The frame of a switch into a stage -/

/-- What is asked of the frame of a switch. There is no kept member. The block of the main row's
message is all rows of the new main table, so the message is there from index 0 on. The rest is in
the new mask table, side by side from index 0 on: two mask rows' messages, the main row's tail, two
mask rows' tails. The main code's message length is a power of two, the messages are within their
tables' index bits, and both old codes have logN ≤ 32. -/
structure FrameOK (W : SwitchFrame) : Prop where
  rest : W.restPart = .mask
  cut : W.mainCut = ⟨.main, W.rowBits, 0⟩
  kept : W.kept = []
  at0 : W.parts.maskAt.getD 0 0 = 0
  at1 : W.parts.maskAt.getD 1 0 = W.zk.ell
  mainTail : W.mainTail = switchPieces W.places (2 * W.zk.ell) W.code.r
  tail0 : W.maskTail.getD 0 [] = switchPieces W.places (2 * W.zk.ell + W.code.r) W.zk.r
  tail1 : W.maskTail.getD 1 []
    = switchPieces W.places (2 * W.zk.ell + W.code.r + W.zk.r) W.zk.r
  box : ∀ j b, W.box.getD j none = some b →
    switchBox W.places (W.parts.maskAt.getD j 0) W.zk.logEll = some b ∧ W.zk.ell = 2 ^ W.zk.logEll
  msg : ∀ j, j < 2 → W.box.getD j none = none →
    W.maskMessage.getD j [] = switchPieces W.places (W.parts.maskAt.getD j 0) W.zk.ell
  flat : ∀ i, i < 2 * W.zk.ell + W.code.r + 2 * W.zk.r → W.places.get i = i
  powC : W.code.ell = 2 ^ W.code.logEll
  rowBits : W.rowBits ≤ W.code.logEll
  tableBits : W.code.logEll ≤ W.tableBits
  restBits : 2 * W.zk.ell ≤ 2 ^ W.restBits
  logC : W.code.logN ≤ 32
  logZ : W.zk.logN ≤ 32

/-- The row of the generator of the old main code at the position x, with the target t. -/
def genMain (W : SwitchFrame) (x : ℕ) (t : E) : Row :=
  { switchAddRestF
      (({} : Row).addForm W.g (switchLift (Form.ofTensor (messageTensor W.code x)) W.code.logEll
        W.mainCut W.rowBits W.tableBits))
      W.g W.restPart W.mainTail (generatorTail W.code x) with
    kind := .generator, target := t }

/-- The row of the generator of the old mask code for mask row number j, at the position x of the
main code, with the target t. -/
def genMask (W : SwitchFrame) (x j : ℕ) (t : E) : Row :=
  { switchAddRestF
      (match W.box.getD j none with
        | some b =>
          ({} : Row).add W.g W.restPart
            (switchOnBox b (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits)
        | none =>
          switchAddRestF {} W.g W.restPart (W.maskMessage.getD j [])
            (generatorMessage W.zk (shortPosition W.zk.logN x)))
      W.g W.restPart (W.maskTail.getD j []) (generatorTail W.zk (shortPosition W.zk.logN x)) with
    kind := .generator, target := t }

/-- Without a kept member and with two mask rows, a draw gives three rows. -/
theorem switchGenerators_eq (W : SwitchFrame) (old : SingleRows) (x : ℕ) (sy : ℕ → E)
    (hk : W.kept = []) (hm : old.masks = 2) :
    switchGenerators W old x sy
      = [genMain W x (sy 0), genMask W x 0 (sy (old.maskRow 0)),
          genMask W x 1 (sy (old.maskRow 1))] := by
  unfold switchGenerators
  simp only [hk, hm]
  rfl

/-! ## The rows of one draw, entry by entry -/

section
variable {W : SwitchFrame} (hW : FrameOK W)
include hW

/-- The entries of a stretch of the rest are side by side from its own first place on. -/
theorem FrameOK.side (first count : ℕ)
    (h : first + count ≤ 2 * W.zk.ell + W.code.r + 2 * W.zk.r) :
    ∀ e, e < count → W.places.get (first + e) = first + e :=
  fun e he => hW.flat (first + e) (by omega)

/-- The main code's row on the new main table. -/
theorem genMain_main (x : ℕ) (hx : x < 2 ^ W.code.logN) (t : E) (i : ℕ)
    (hi : i < 2 ^ W.tableBits) :
    coefAt (genMain W x t) W.g .main i = wM (codeOf W.code) x i := by
  show coefAt (switchAddRestF (({} : Row).addForm W.g (switchLift
    (Form.ofTensor (messageTensor W.code x)) W.code.logEll W.mainCut W.rowBits W.tableBits))
    W.g W.restPart W.mainTail (generatorTail W.code x)) W.g .main i = _
  rw [hW.mainTail, coefAt_restF _ _ _ _ _ _ _ (hW.side _ _ (by omega)), coefAt_addForm,
    coefAt_empty, hW.rest, hW.cut,
    formAt_switchLift _ _ _ _ (fun v hv => by
      rw [List.mem_singleton.1 hv]
      exact vars_messageTensor W.code x hW.powC) hW.rowBits hW.tableBits i hi,
    show formAt (Form.ofTensor (messageTensor W.code x))
      = fun j => readE ((messageTensor W.code x).entry j) from funext (formAt_ofTensor _),
    cut_messageTensor W.code x hW.logC hx hW.powC]
  simp

/-- The main code's row on the new mask table: on the main row's tail. -/
theorem genMain_mask (x : ℕ) (hx : x < 2 ^ W.code.logN) (t : E) (i : ℕ) :
    coefAt (genMain W x t) W.g .mask i = moved (2 * W.zk.ell) (wT (codeOf W.code) x) i := by
  show coefAt (switchAddRestF (({} : Row).addForm W.g (switchLift
    (Form.ofTensor (messageTensor W.code x)) W.code.logEll W.mainCut W.rowBits W.tableBits))
    W.g W.restPart W.mainTail (generatorTail W.code x)) W.g .mask i = _
  rw [hW.mainTail, coefAt_restF _ _ _ _ _ _ _ (hW.side _ _ (by omega)), coefAt_addForm,
    coefAt_empty, hW.rest, cut_generatorTail W.code x hW.logC hx]
  simp

/-- A mask row's part on its message, on the new mask table. -/
theorem onMask_mask (x j : ℕ) (hj2 : j < 2)
    (hj : W.parts.maskAt.getD j 0 + W.zk.ell ≤ 2 * W.zk.ell) (i : ℕ) (hi : i < 2 ^ W.restBits) :
    coefAt (match W.box.getD j none with
        | some b =>
          ({} : Row).add W.g W.restPart
            (switchOnBox b (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits)
        | none =>
          switchAddRestF {} W.g W.restPart (W.maskMessage.getD j [])
            (generatorMessage W.zk (shortPosition W.zk.logN x))) W.g .mask i
      = moved (W.parts.maskAt.getD j 0) (wM (codeOf W.zk) (Fmt.M1.cp (codeOf W.zk) x)) i := by
  have hx' : shortPosition W.zk.logN x < 2 ^ W.zk.logN := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [← shortPosition_eq]
  cases hb : W.box.getD j none with
  | none =>
    show coefAt (switchAddRestF {} W.g W.restPart (W.maskMessage.getD j [])
      (generatorMessage W.zk (shortPosition W.zk.logN x))) W.g .mask i = _
    rw [hW.msg j hj2 hb, coefAt_restF _ _ _ _ _ _ _ (hW.side _ _ (by omega)), coefAt_empty,
      hW.rest, cut_generatorMessage W.zk _ hW.logZ hx']
    simp
  | some b =>
    obtain ⟨hbox, hpow⟩ := hW.box j b hb
    obtain ⟨rfl, hd⟩ := switchBox_some _ _ _ b
      (hW.side _ _ (by rw [← hpow]; omega)) hbox
    have hrest := hW.restBits
    have hle : W.zk.logEll ≤ W.restBits :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (by rw [← hpow]; omega)
    have hpos : 0 < W.zk.ell := hpow ▸ Nat.two_pow_pos _
    show coefAt (({} : Row).add W.g W.restPart (switchOnBox ⟨0, W.parts.maskAt.getD j 0⟩
      (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits)) W.g .mask i = _
    rw [coefAt_add, coefAt_empty, hW.rest,
      readE_switchOnBox _ _ _ _ _ (vars_messageTensor W.zk _ hpow) hd hle (by omega) hi,
      cut_messageTensor W.zk _ hW.logZ hx' hpow]
    simp

/-- A mask row's part on its message reads nothing of the new main table. -/
theorem onMask_main (x j : ℕ) (hj2 : j < 2)
    (hj : W.parts.maskAt.getD j 0 + W.zk.ell ≤ 2 * W.zk.ell) (i : ℕ) :
    coefAt (match W.box.getD j none with
        | some b =>
          ({} : Row).add W.g W.restPart
            (switchOnBox b (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits)
        | none =>
          switchAddRestF {} W.g W.restPart (W.maskMessage.getD j [])
            (generatorMessage W.zk (shortPosition W.zk.logN x))) W.g .main i = 0 := by
  cases hb : W.box.getD j none with
  | none =>
    show coefAt (switchAddRestF {} W.g W.restPart (W.maskMessage.getD j [])
      (generatorMessage W.zk (shortPosition W.zk.logN x))) W.g .main i = _
    rw [hW.msg j hj2 hb, coefAt_restF _ _ _ _ _ _ _ (hW.side _ _ (by omega)), coefAt_empty,
      hW.rest]
    simp
  | some b =>
    show coefAt (({} : Row).add W.g W.restPart (switchOnBox b
      (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits)) W.g .main i = _
    rw [coefAt_add, coefAt_empty, hW.rest]
    simp

/-- The row of mask row number j on the new mask table, if the mask row's tail begins at place
a. -/
theorem genMask_mask (x j a : ℕ) (hj2 : j < 2)
    (hj : W.parts.maskAt.getD j 0 + W.zk.ell ≤ 2 * W.zk.ell)
    (ht : W.maskTail.getD j [] = switchPieces W.places a W.zk.r)
    (ha : a + W.zk.r ≤ 2 * W.zk.ell + W.code.r + 2 * W.zk.r) (t : E) (i : ℕ)
    (hi : i < 2 ^ W.restBits) :
    coefAt (genMask W x j t) W.g .mask i
      = moved (W.parts.maskAt.getD j 0) (wM (codeOf W.zk) (Fmt.M1.cp (codeOf W.zk) x)) i
        + moved a (wT (codeOf W.zk) (Fmt.M1.cp (codeOf W.zk) x)) i := by
  have hx' : shortPosition W.zk.logN x < 2 ^ W.zk.logN := Nat.mod_lt _ (Nat.two_pow_pos _)
  show coefAt (switchAddRestF _ W.g W.restPart (W.maskTail.getD j [])
    (generatorTail W.zk (shortPosition W.zk.logN x))) W.g .mask i = _
  rw [ht, coefAt_restF _ _ _ _ _ _ _ (hW.side _ _ ha), onMask_mask hW x j hj2 hj i hi, hW.rest,
    cut_generatorTail W.zk _ hW.logZ hx', shortPosition_eq]
  simp

/-- The row of a mask row reads nothing of the new main table. -/
theorem genMask_main (x j a : ℕ) (hj2 : j < 2)
    (hj : W.parts.maskAt.getD j 0 + W.zk.ell ≤ 2 * W.zk.ell)
    (ht : W.maskTail.getD j [] = switchPieces W.places a W.zk.r)
    (ha : a + W.zk.r ≤ 2 * W.zk.ell + W.code.r + 2 * W.zk.r) (t : E) (i : ℕ) :
    coefAt (genMask W x j t) W.g .main i = 0 := by
  show coefAt (switchAddRestF _ W.g W.restPart (W.maskTail.getD j [])
    (generatorTail W.zk (shortPosition W.zk.logN x))) W.g .main i = _
  rw [ht, coefAt_restF _ _ _ _ _ _ _ (hW.side _ _ ha), onMask_main hW x j hj2 hj i, hW.rest]
  simp

end

/-! ## The carried claim -/

/-- The old claim on the new tables, without a kept member and with two mask rows. -/
def carriedRow (W : SwitchFrame) (old : SingleRows) : Row :=
  { switchAddRestE
      (switchAddRestE
        (({} : Row).addForm W.g (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits))
        W.g W.restPart (switchPieces W.places (W.parts.maskAt.getD 0 0) (old.d.getD 0 #[]).size)
        (old.d.getD 0 #[]))
      W.g W.restPart (switchPieces W.places (W.parts.maskAt.getD 1 0) (old.d.getD 1 #[]).size)
      (old.d.getD 1 #[]) with
    target := old.target }

/-- Coefficients on a stretch leave a row's kind as it was. -/
theorem kind_restE (g : ℕ) (part : Part) (coeff : Array E) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestE row g part pieces coeff).kind = row.kind
  | [], _ => rfl
  | p :: pieces, row =>
    kind_restE g part coeff pieces
      (row.addRun g part p.first p.step (.own (coeff.extract p.start p.stop)))

/-- The carried claim is a plain row. -/
theorem kind_carriedRow (W : SwitchFrame) (old : SingleRows) :
    (carriedRow W old).kind = .plain := by
  show (switchAddRestE (switchAddRestE _ _ _ _ _) _ _ _ _).kind = _
  rw [kind_restE, kind_restE]
  rfl

/-- The main code's row is a row of a generator matrix. -/
theorem kind_genMain (W : SwitchFrame) (x : ℕ) (t : E) : (genMain W x t).kind = .generator := rfl

/-- A mask code's row is a row of a generator matrix. -/
theorem kind_genMask (W : SwitchFrame) (x j : ℕ) (t : E) :
    (genMask W x j t).kind = .generator := rfl

/-- The carried claim has the old claim's target. -/
theorem target_carriedRow (W : SwitchFrame) (old : SingleRows) :
    (carriedRow W old).target = old.target := rfl

/-- The program's carried claim is that row. -/
theorem switchCarried_eq (W : SwitchFrame) (old : SingleRows) (hk : old.kept = #[])
    (hm : old.masks = 2) : switchCarried W old = some (carriedRow W old) := by
  unfold switchCarried
  simp only [hk, hm, Array.foldlM_empty]
  rfl

section
variable {W : SwitchFrame} (hW : FrameOK W) (old : SingleRows)
  (hd0 : (old.d.getD 0 #[]).size = W.zk.ell) (hd1 : (old.d.getD 1 #[]).size = W.zk.ell)
include hW hd0 hd1

/-- The carried claim on the new main table. -/
theorem carried_main (hc : ∀ v ∈ old.c.tensors, v.vars = W.code.logEll) (i : ℕ)
    (hi : i < 2 ^ W.tableBits) :
    coefAt (carriedRow W old) W.g .main i = cut W.code.ell (formAt old.c) i := by
  show coefAt (switchAddRestE (switchAddRestE (({} : Row).addForm W.g (switchLift old.c
    W.code.logEll W.mainCut W.rowBits W.tableBits)) W.g W.restPart _ _) W.g W.restPart _ _)
    W.g .main i = _
  rw [hd0, hd1, hW.at0, hW.at1, coefAt_restE _ _ _ _ _ _ _ (hW.side _ _ (by omega)),
    coefAt_restE _ _ _ _ _ _ _ (hW.side _ _ (by omega)), coefAt_addForm, coefAt_empty, hW.rest,
    hW.cut, formAt_switchLift _ _ _ _ hc hW.rowBits hW.tableBits i hi, ← hW.powC]
  simp

/-- The carried claim on the new mask table. -/
theorem carried_mask (i : ℕ) :
    coefAt (carriedRow W old) W.g .mask i
      = cut W.zk.ell (readV (old.d.getD 0 #[])) i
        + moved W.zk.ell (cut W.zk.ell (readV (old.d.getD 1 #[]))) i := by
  show coefAt (switchAddRestE (switchAddRestE (({} : Row).addForm W.g (switchLift old.c
    W.code.logEll W.mainCut W.rowBits W.tableBits)) W.g W.restPart _ _) W.g W.restPart _ _)
    W.g .mask i = _
  rw [hd0, hd1, hW.at0, hW.at1, coefAt_restE _ _ _ _ _ _ _ (hW.side _ _ (by omega)),
    coefAt_restE _ _ _ _ _ _ _ (hW.side _ _ (by omega)), coefAt_addForm, coefAt_empty, hW.rest,
    moved_zero]
  simp

end

/-! ## The three rows of a draw, side by side -/

section
variable {W : SwitchFrame} (hW : FrameOK W) (x : ℕ) (t0 t1 t2 : E)
include hW

/-- One draw's three rows on the new main table. -/
theorem gen_main (hx : x < 2 ^ W.code.logN) (i : ℕ) (hi : i < 2 ^ W.tableBits) :
    [genMain W x t0, genMask W x 0 t1, genMask W x 1 t2].map (fun R => coefAt R W.g .main i)
      = [wM (codeOf W.code) x i, 0, 0] := by
  have h0 := hW.at0
  have h1 := hW.at1
  show [coefAt (genMain W x t0) W.g .main i, coefAt (genMask W x 0 t1) W.g .main i,
    coefAt (genMask W x 1 t2) W.g .main i] = _
  rw [genMain_main hW x hx t0 i hi,
    genMask_main hW x 0 _ (by decide) (by omega) hW.tail0 (by omega) t1 i,
    genMask_main hW x 1 _ (by decide) (by omega) hW.tail1 (by omega) t2 i]

/-- One draw's three rows on the new mask table. -/
theorem gen_mask (hx : x < 2 ^ W.code.logN) (i : ℕ) (hi : i < 2 ^ W.restBits) :
    [genMain W x t0, genMask W x 0 t1, genMask W x 1 t2].map (fun R => coefAt R W.g .mask i)
      = [moved (2 * W.zk.ell) (wT (codeOf W.code) x) i,
         wM (codeOf W.zk) (Fmt.M1.cp (codeOf W.zk) x) i
           + moved (2 * W.zk.ell + W.code.r) (wT (codeOf W.zk) (Fmt.M1.cp (codeOf W.zk) x)) i,
         moved W.zk.ell (wM (codeOf W.zk) (Fmt.M1.cp (codeOf W.zk) x)) i
           + moved (2 * W.zk.ell + W.code.r + W.zk.r)
               (wT (codeOf W.zk) (Fmt.M1.cp (codeOf W.zk) x)) i] := by
  have h0 := hW.at0
  have h1 := hW.at1
  show [coefAt (genMain W x t0) W.g .mask i, coefAt (genMask W x 0 t1) W.g .mask i,
    coefAt (genMask W x 1 t2) W.g .mask i] = _
  rw [genMain_mask hW x hx t0 i,
    genMask_mask hW x 0 _ (by decide) (by omega) hW.tail0 (by omega) t1 i hi,
    genMask_mask hW x 1 _ (by decide) (by omega) hW.tail1 (by omega) t2 i hi, h0, h1, moved_zero]

omit hW in
/-- One draw's three targets. -/
theorem gen_target :
    [genMain W x t0, genMask W x 0 t1, genMask W x 1 t2].map (fun R => readE R.target)
      = [readE t0, readE t1, readE t2] :=
  rfl

end

/-! ## All rows of a switch -/

/-- What a loop over the draws gives, if it succeeds: each draw with its number in the list of
positions. -/
theorem mapM_index {β : Type} (idx : ℕ → Option ℕ) (G : ℕ → ℕ → β) :
    ∀ (l : List ℕ) (r : List β),
      l.mapM (fun x => (idx x).bind fun i => some (G x i)) = some r →
      r = l.map fun x => G x ((idx x).getD 0)
  | [], r, h => by
    rw [List.mapM_nil] at h
    exact (Option.some.inj h).symm
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ⟨i, hi, rfl⟩, as, has, rfl⟩ := h
    rw [List.map_cons, hi, ← mapM_index idx G l as has]
    rfl

/-- Without a kept member there is no old sample row. -/
theorem switchOldSamples_nil (S : Statement) (W : SwitchFrame) (hk : W.kept = []) :
    switchOldSamples S W = some [] := by
  unfold switchOldSamples
  rw [hk]
  rfl

/-- The symbol number row that was read at the position x. A position that is not in the list
counts as the first of the list. -/
def symAtB (old : SingleRows) (pos : Positions) (y : Array E) (x row : ℕ) : E :=
  y.getD ((pos.indexOf x).getD 0 * old.rows + row) zeroE

/-- The rows of a switch without a kept member and with two mask rows: first the old claim on the
new tables, then each draw's three rows of generator matrices, the draws in the order drawn. -/
theorem switchRows_eq (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (pos : Positions) (y : Array E) (rows : List Row) (hk : old.kept = #[]) (hm : old.masks = 2)
    (hK : ∀ W, switchFrame S old T g #[] = some W → W.kept = [])
    (h : switchRows S old T g #[] pos y = some rows) :
    ∃ W, switchFrame S old T g #[] = some W ∧
      rows = carriedRow W old :: pos.draws.toList.flatMap fun x =>
        [genMain W x (symAtB old pos y x 0), genMask W x 0 (symAtB old pos y x (old.maskRow 0)),
          genMask W x 1 (symAtB old pos y x (old.maskRow 1))] := by
  unfold switchRows at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨-, -, W, hW, c, hc, sm, hs, gs, hg, rfl⟩ := h
  have hkW := hK W hW
  rw [switchCarried_eq W old hk hm] at hc
  rw [switchOldSamples_nil S W hkW] at hs
  obtain rfl := Option.some.inj hc
  obtain rfl := Option.some.inj hs
  have hgs := mapM_index pos.indexOf
    (fun x i => switchGenerators W old x fun row => y.getD (i * old.rows + row) zeroE) _ _ hg
  refine ⟨W, hW, ?_⟩
  rw [hgs, List.flatMap_def]
  refine congrArg (fun l => carriedRow W old :: List.flatten l) (List.map_congr_left fun x _ => ?_)
  exact switchGenerators_eq W old x _ hkW hm

/-! ## The frame, from the statement and the target -/

/-- An entry of an array that is made from the numbers below n. -/
theorem getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (d : α) (j : ℕ) :
    ((Array.range n).map f).getD j d = if j < n then f j else d := by
  by_cases h : j < n
  · simp [Array.getD, h]
  · simp [Array.getD, h]

/-- A number n that passes the program's test `powerOfTwo` is 2^(ceilLog2 n). -/
theorem eq_of_powerOfTwo (n : ℕ) (h : powerOfTwo n = true) : n = 2 ^ ceilLog2 n := by
  unfold powerOfTwo at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2.symm

/-- Where the parts of the rest begin, without a kept member and with two mask rows. -/
theorem switchParts_eq (S : Statement) (old : SingleRows) (code zk : OnBytes.Code)
    (hc : S.codes.base[old.code]? = some code) (hz : S.codes.mask[old.maskCode]? = some zk)
    (hK : switchKept old = #[]) (hm : old.masks = 2) (hkr : old.keptRows = 0) :
    switchParts S old = ⟨startsFrom 0 zk.ell 2, 2 * zk.ell,
      startsFrom (2 * zk.ell + code.r) code.r 0,
      startsFrom (2 * zk.ell + code.r + 0 * code.r) zk.r 2, #[],
      2 * zk.ell + code.r + 0 * code.r + 2 * zk.r⟩ := by
  have g1 : S.codes.base.getD old.code default = code := by
    rw [Array.getD_eq_getD_getElem?, hc]
    rfl
  have g2 : S.codes.mask.getD old.maskCode default = zk := by
    rw [Array.getD_eq_getD_getElem?, hz]
    rfl
  unfold switchParts
  simp only [g1, g2, hK, hm, hkr]
  rfl

/-- The fields of a frame, one by one. -/
theorem switchFrame_fields (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (W : SwitchFrame) (h : switchFrame S old T g #[] = some W) :
    S.codes.base[old.code]? = some W.code ∧ S.codes.mask[old.maskCode]? = some W.zk ∧
    W.g = g ∧ W.restPart = T.rest.part ∧ W.mainCut = T.main ∧
    W.rowBits = switchRowBits T .main ∧ W.places = SwitchPlaces.make S.codes T ∧
    W.parts = switchParts S old ∧ W.kept.length = (switchKept old).size ∧
    W.mainTail = switchPieces W.places W.parts.mainTailAt W.code.r ∧
    W.maskTail = W.parts.maskTailAt.map (fun a => switchPieces W.places a W.zk.r) ∧
    W.box = (Array.range old.masks).map (fun j =>
      if powerOfTwo W.zk.ell then switchBox W.places (W.parts.maskAt.getD j 0) (ceilLog2 W.zk.ell)
      else none) ∧
    W.maskMessage = (Array.range old.masks).map (fun j =>
      if (W.box.getD j none).isSome then []
      else switchPieces W.places (W.parts.maskAt.getD j 0) W.zk.ell) := by
  unfold switchFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨code, hc, zk, hz, nc, -, -, -, rfl⟩ := h
  exact ⟨hc, hz, rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl, rfl, rfl, rfl⟩

/-- The frame of a switch into a stage is as asked, from conditions on the statement, the old
rows and the target. -/
theorem frame_ok (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ) (W : SwitchFrame)
    (h : switchFrame S old T g #[] = some W) (hK : switchKept old = #[]) (hm : old.masks = 2)
    (hkr : old.keptRows = 0) (hrest : T.rest.part = .mask)
    (hmain : T.main = ⟨.main, switchRowBits T .main, 0⟩)
    (hflat : ∀ i, i < 2 * W.zk.ell + W.code.r + 2 * W.zk.r →
      (SwitchPlaces.make S.codes T).get i = i)
    (hpow : W.code.ell = 2 ^ W.code.logEll) (hrb : W.rowBits ≤ W.code.logEll)
    (htb : W.code.logEll ≤ W.tableBits) (hre : 2 * W.zk.ell ≤ 2 ^ W.restBits)
    (hC : W.code.logN ≤ 32) (hZ : W.zk.logN ≤ 32) : FrameOK W := by
  obtain ⟨hc, hz, -, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := switchFrame_fields S old T g W h
  have hP := f5.trans (switchParts_eq S old W.code W.zk hc hz hK hm hkr)
  have hat : ∀ j, j < 2 → W.parts.maskAt.getD j 0 = 0 + W.zk.ell * j := fun j hj => by
    rw [hP]
    show (startsFrom 0 W.zk.ell 2).getD j 0 = _
    unfold startsFrom
    rw [getD_map_range, if_pos hj]
  have htl : ∀ j, j < 2 → W.maskTail.getD j []
      = switchPieces W.places (2 * W.zk.ell + W.code.r + 0 * W.code.r + W.zk.r * j) W.zk.r :=
    fun j hj => by
      rw [f8, hP]
      show ((startsFrom (2 * W.zk.ell + W.code.r + 0 * W.code.r) W.zk.r 2).map fun a =>
        switchPieces W.places a W.zk.r).getD j [] = _
      unfold startsFrom
      rw [Array.map_map, getD_map_range, if_pos hj]
      rfl
  refine ⟨f1.trans hrest, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpow, hrb, htb, hre, hC, hZ⟩
  · rw [f2, hmain, f3]
  · rw [hK] at f6
    exact List.length_eq_zero_iff.1 f6
  · rw [hat 0 (by decide)]
    omega
  · rw [hat 1 (by decide)]
    omega
  · rw [f7, hP]
  · rw [htl 0 (by decide), Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
  · rw [htl 1 (by decide), Nat.zero_mul, Nat.mul_one, Nat.add_zero]
  · intro j b hb
    rw [f9, getD_map_range] at hb
    split_ifs at hb with c1 c2
    exact ⟨hb, eq_of_powerOfTwo W.zk.ell c2⟩
  · intro j hj hb
    rw [f10, getD_map_range, hm, if_pos hj, hb]
    rfl
  · intro i hi
    rw [f4]
    exact hflat i hi

/-! ## The rest is side by side, for a target whose rest fills the mask table -/

/-- If an oracle message has mask rows, each index of its pad is at least the index of the place
number ell - answers in the last mask row. -/
theorem pad_index_ge (codes : Codes) (s : OracleShape) (hm : 0 < s.maskRows) (q : PadPlace)
    (hq : q ∈ padPlaces codes s) :
    s.maskRows - 1 + ((codes.mask.getD s.maskCode default).ell - s.answers)
      * 2 ^ ceilLog2 s.maskRows ≤ q.index := by
  unfold padPlaces Send.pad at hq
  simp only [Send.cube, hm, decide_true, if_true, Bool.true_or] at hq
  split_ifs at hq with c
  · cases hq
  · obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hq
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hi
    show _ ≤ s.maskRows - 1 + ((codes.mask.getD s.maskCode default).ell - 1 * s.answers + 1 * i + t)
      * 2 ^ ceilLog2 s.maskRows
    refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _
    omega

/-- If the rest's block is the whole mask table, entry i of the rest is at the index i, for
every i below the bound of `pad_index_ge`, before which there is no pad. -/
theorem make_flat (codes : Codes) (T : SwitchTarget) (hpart : T.rest.part = .mask)
    (h0 : T.rest.firstRow = 0) (hb : T.rest.bits = ceilLog2 T.shape.maskRows)
    (hm : 0 < T.shape.maskRows) (i : ℕ)
    (hi : i < T.shape.maskRows - 1 + ((codes.mask.getD T.shape.maskCode default).ell
      - T.shape.answers) * 2 ^ ceilLog2 T.shape.maskRows) :
    (SwitchPlaces.make codes T).get i = i := by
  have hrb : switchRowBits T T.rest.part = ceilLog2 T.shape.maskRows := by
    rw [hpart]
    rfl
  refine get_flat _ h0 (hb.trans hrb.symm) i fun p hp => ?_
  unfold SwitchPlaces.make at hp
  simp only [List.mem_mergeSort, List.mem_filterMap] at hp
  obtain ⟨q, hq, hp⟩ := hp
  split_ifs at hp with c
  have hge := pad_index_ge codes T.shape hm q hq
  have hp' : q.index % 2 ^ switchRowBits T T.rest.part - T.rest.firstRow
      + q.index / 2 ^ switchRowBits T T.rest.part * 2 ^ T.rest.bits = p := Option.some.inj hp
  rw [h0, Nat.sub_zero, hb, hrb, Nat.mod_add_div'] at hp'
  omega

end OnBytes.Slice

#print axioms OnBytes.Slice.switchPieces_eq
#print axioms OnBytes.Slice.pieces_loop
#print axioms OnBytes.Slice.switchPieces_flat
#print axioms OnBytes.Slice.switchPieces_zero
#print axioms OnBytes.Slice.runAt_unit
#print axioms OnBytes.Slice.readV_extract
#print axioms OnBytes.Slice.runAt_own
#print axioms OnBytes.Slice.runAt_stretch
#print axioms OnBytes.Slice.coefAt_restE
#print axioms OnBytes.Slice.coefAt_restF
#print axioms OnBytes.Slice.foldl_pad
#print axioms OnBytes.Slice.get_flat
#print axioms OnBytes.Slice.pick_none
#print axioms OnBytes.Slice.pick_block
#print axioms OnBytes.Slice.formAt_switchLift
#print axioms OnBytes.Slice.switchBox_some
#print axioms OnBytes.Slice.readE_switchOnBox
#print axioms OnBytes.Slice.cut_generatorTail
#print axioms OnBytes.Slice.cut_generatorMessage
#print axioms OnBytes.Slice.logEll_le_logDim
#print axioms OnBytes.Slice.vars_messageTensor
#print axioms OnBytes.Slice.cut_messageTensor
#print axioms OnBytes.Slice.switchGenerators_eq
#print axioms OnBytes.Slice.FrameOK.side
#print axioms OnBytes.Slice.genMain_main
#print axioms OnBytes.Slice.genMain_mask
#print axioms OnBytes.Slice.onMask_mask
#print axioms OnBytes.Slice.onMask_main
#print axioms OnBytes.Slice.genMask_mask
#print axioms OnBytes.Slice.genMask_main
#print axioms OnBytes.Slice.kind_restE
#print axioms OnBytes.Slice.kind_carriedRow
#print axioms OnBytes.Slice.kind_genMain
#print axioms OnBytes.Slice.kind_genMask
#print axioms OnBytes.Slice.target_carriedRow
#print axioms OnBytes.Slice.switchCarried_eq
#print axioms OnBytes.Slice.carried_main
#print axioms OnBytes.Slice.carried_mask
#print axioms OnBytes.Slice.gen_main
#print axioms OnBytes.Slice.gen_mask
#print axioms OnBytes.Slice.gen_target
#print axioms OnBytes.Slice.mapM_index
#print axioms OnBytes.Slice.switchOldSamples_nil
#print axioms OnBytes.Slice.switchRows_eq
#print axioms OnBytes.Slice.getD_map_range
#print axioms OnBytes.Slice.eq_of_powerOfTwo
#print axioms OnBytes.Slice.switchParts_eq
#print axioms OnBytes.Slice.switchFrame_fields
#print axioms OnBytes.Slice.frame_ok
#print axioms OnBytes.Slice.pad_index_ge
#print axioms OnBytes.Slice.make_flat
