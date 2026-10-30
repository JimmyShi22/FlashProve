-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/H2K/GenRowsAt.lean: the generator rows of one draw of the program's code switch
(`switchGenerators`, OnBytes/Iop/Cs.lean), read in the field entry by entry, at any frame: with kept
members, with a main block that is not the whole table, and with a rest whose places are not side by
side.

OnBytes/Slice/BlkCsRows.lean reads these rows for the switch into a stage of a proximity test alone:
no kept member, the main block the whole table, the rest side by side. Here each row is read on
every entry of every table, from Johnson/Top/H0/H2K/SwitchLiftAt.lean (the main row's message),
Johnson/Top/H0/H2K/BoxAt.lean (a mask row's message on a box), OnBytes/Slice/BlkCsStretch.lean
(coefficients on a stretch of the rest at any increasing places) and OnBytes/Slice/BlkCsKept.lean (a
form on a kept member's table), with the library's cut_generatorTail, cut_generatorMessage and
cut_messageTensor. Definitions, statements and proofs, on the program's pure functions alone.
Main names:
  `stretchAt_congr`, `stretch_tail`, `stretch_message`, `stretch_tensor`: the generator's row on a
    stretch has the format's weights wT and wM.
  `genMain_at`: the main row (`genMain`): on g's main table the lifted message, on the table that
    takes the rest the tail's weights on its stretch.
  `lift_message_cutIndex`, `lift_message_off`: the lifted message has the weight wM j at the index
    cutIndex of j, and 0 at every other index of the table.
  `MaskAt`, `genMask_at`: a mask row (`genMask`): in both arms (a box, or pieces) the message's
    weights wM on its stretch and the tail's weights wT on its stretch, on the table that takes the
    rest; 0 on every other table.
  `formAt_rowPick`, `keptForm`, `formAt_keptForm`: the generator's row on row number b of a kept
    member: the weight wM (J / 2 ^ rowBits) at the indices J whose low row bits are b, else 0.
  `genKept`, `genKept_at`, `genKept_new`, `genKept_g`, `genKept_other`: a kept row: on the new
    message's main table that form, but 0 at the pad's places; on the table of g that takes the rest
    the form's entries at the pad's places, where the old pad lies, and the tail's weights; 0 on
    every other table.
  `keptFrom`, `loop_rows`, `loop_kept`, `switchGenerators_all`: the rows of one draw in their order:
    the main row, the kept rows member by member and row by row (row number n has the target symbols
    (1 + n) and the tail number n), the mask rows. No premise.
Limits: No soundness is claimed, and nothing is said on hiding.
Premises, each on one stretch: the frame's pieces are switchPieces of the frame's places from a
given place on, and the places increase along that stretch (in the form in which
OnBytes/Slice/BlkCsStretch.lean asks it). That the places of a switch increase, and where each
stretch begins, is not shown here. For a box: its numbers lie in the table (shift + logEll ≤
restBits, start < 2 ^ restBits). For a kept row: the new message is not g, and no two places of the
pad have one index. Both old codes have logN ≤ 32; a position is below 2 ^ logN; the main code's
message length is a power of two.
genMask_at is stated at indices below 2 ^ restBits, formAt_keptForm below 2 ^ (rowBits + logEll): a
tensor does not look at the bits of an index above its variables.
A mask row is read at shortPosition zk.logN x.
Nothing is said on the carried claim, the old sample rows, or the order of all rows of a switch.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Top.H0.H2K.SwitchLiftAt
import Johnson.Top.H0.H2K.BoxAt
import OnBytes.Slice.BlkCsKept

set_option autoImplicit false
namespace H2K.Lift
open OnBytes OnBytes.Slice

/-! ## Coefficients on a stretch, at the format's points -/

/-- A stretch reads its coefficients below its length alone. -/
theorem stretchAt_congr (places : SwitchPlaces) (first count : ℕ) (c c' : ℕ → GE)
    (h : ∀ i, i < count → c i = c' i) (J : ℕ) :
    stretchAt places first count c J = stretchAt places first count c' J := by
  unfold stretchAt
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

/-- The generator's row on a tail, on a stretch. -/
theorem stretch_tail (places : SwitchPlaces) (first : ℕ) (c : OnBytes.Code) (x : ℕ)
    (ha : c.logN ≤ 32) (hx : x < 2 ^ c.logN) (J : ℕ) :
    stretchAt places first c.r
        (fun i => algebraMap GF GE (toF ((generatorTail c x).getD i 0))) J =
      stretchAt places first c.r (wT (codeOf c) x) J := by
  rw [← cut_generatorTail c x ha hx]
  refine stretchAt_congr _ _ _ _ _ (fun i hi => ?_) J
  rw [cut_of_lt hi]

/-- The generator's row on a message, written out, on a stretch. -/
theorem stretch_message (places : SwitchPlaces) (first : ℕ) (c : OnBytes.Code) (x : ℕ)
    (ha : c.logN ≤ 32) (hx : x < 2 ^ c.logN) (J : ℕ) :
    stretchAt places first c.ell
        (fun i => algebraMap GF GE (toF ((generatorMessage c x).getD i 0))) J =
      stretchAt places first c.ell (wM (codeOf c) x) J := by
  rw [← cut_generatorMessage c x ha hx]
  refine stretchAt_congr _ _ _ _ _ (fun i hi => ?_) J
  rw [cut_of_lt hi]

/-- The generator's row on a message, as a tensor, on a stretch. -/
theorem stretch_tensor (places : SwitchPlaces) (first : ℕ) (c : OnBytes.Code) (x : ℕ)
    (ha : c.logN ≤ 32) (hx : x < 2 ^ c.logN) (hpow : c.ell = 2 ^ c.logEll) (J : ℕ) :
    stretchAt places first (2 ^ c.logEll) (fun i => readE ((messageTensor c x).entry i)) J =
      stretchAt places first (2 ^ c.logEll) (wM (codeOf c) x) J := by
  rw [← cut_messageTensor c x ha hx hpow]
  refine stretchAt_congr _ _ _ _ _ (fun i hi => ?_) J
  rw [cut_of_lt hi]

/-! ## The main row -/

/-- The row of the generator of the old main code, on every entry of every table. a: where the main
row's tail begins in the rest. -/
theorem genMain_at (W : SwitchFrame) (a : ℕ)
    (hT : W.mainTail = switchPieces W.places a W.code.r)
    (hm : ∀ i j, i < j → j < W.code.r → W.places.get (a + i) < W.places.get (a + j))
    (hlog : W.code.logN ≤ 32) (x : ℕ) (hx : x < 2 ^ W.code.logN) (t : E) (o : ℕ) (part : Part)
    (J : ℕ) :
    coefAt (genMain W x t) o part J =
      (if W.g == o && part == .main then
        formAt (switchLift (Form.ofTensor (messageTensor W.code x)) W.code.logEll W.mainCut
          W.rowBits W.tableBits) J else 0) +
      if W.g == o && W.restPart == part then
        stretchAt W.places a W.code.r (wT (codeOf W.code) x) J else 0 := by
  show coefAt (switchAddRestF (({} : Row).addForm W.g (switchLift
    (Form.ofTensor (messageTensor W.code x)) W.code.logEll W.mainCut W.rowBits W.tableBits))
    W.g W.restPart W.mainTail (generatorTail W.code x)) o part J = _
  rw [hT, coefAt_restF_at _ _ _ _ _ _ hm, coefAt_addForm, coefAt_empty, zero_add,
    stretch_tail _ _ _ _ hlog hx]

/-- The main row's message in the new main table: entry j stands at the index cutIndex of j. -/
theorem lift_message_cutIndex (W : SwitchFrame) (hpow : W.code.ell = 2 ^ W.code.logEll)
    (hlog : W.code.logN ≤ 32) (hb : W.mainCut.bits ≤ W.code.logEll)
    (hR : W.mainCut.bits ≤ W.rowBits)
    (hv : W.code.logEll + (W.rowBits - W.mainCut.bits) ≤ W.tableBits)
    (hal : 2 ^ W.mainCut.bits ∣ W.mainCut.firstRow)
    (hf : W.mainCut.firstRow / 2 ^ W.mainCut.bits < 2 ^ (W.rowBits - W.mainCut.bits)) (x : ℕ)
    (hx : x < 2 ^ W.code.logN) (j : ℕ) (hj : j < 2 ^ W.code.logEll) :
    formAt (switchLift (Form.ofTensor (messageTensor W.code x)) W.code.logEll W.mainCut W.rowBits
      W.tableBits) (cutIndex W.mainCut W.rowBits j) = wM (codeOf W.code) x j := by
  rw [formAt_switchLift_cutIndex _ _ _ _ _ (fun v hv' => by
      rw [List.mem_singleton.1 hv']
      exact vars_messageTensor W.code x hpow) hb hR hv hal hf j hj, formAt_ofTensor,
    ← cut_messageTensor W.code x hlog hx hpow, cut_of_lt hj]

/-- Elsewhere in the new main table the main row's message has no weight. -/
theorem lift_message_off (W : SwitchFrame) (hpow : W.code.ell = 2 ^ W.code.logEll)
    (hb : W.mainCut.bits ≤ W.code.logEll) (hR : W.mainCut.bits ≤ W.rowBits)
    (hv : W.code.logEll + (W.rowBits - W.mainCut.bits) ≤ W.tableBits)
    (hal : 2 ^ W.mainCut.bits ∣ W.mainCut.firstRow)
    (hf : W.mainCut.firstRow / 2 ^ W.mainCut.bits < 2 ^ (W.rowBits - W.mainCut.bits)) (x J : ℕ)
    (hJ : J < 2 ^ W.tableBits)
    (h : ∀ j, j < 2 ^ W.code.logEll → cutIndex W.mainCut W.rowBits j ≠ J) :
    formAt (switchLift (Form.ofTensor (messageTensor W.code x)) W.code.logEll W.mainCut W.rowBits
      W.tableBits) J = 0 :=
  formAt_switchLift_off _ _ _ _ _ (fun v hv' => by
    rw [List.mem_singleton.1 hv']
    exact vars_messageTensor W.code x hpow) hb hR hv hal hf J hJ h

/-! ## The mask rows -/

/-- What is asked of the frame at mask row number j. aM, aT: where its message and its tail begin
in the rest. -/
structure MaskAt (W : SwitchFrame) (j aM aT : ℕ) : Prop where
  msg : W.box.getD j none = none →
    W.maskMessage.getD j [] = switchPieces W.places aM W.zk.ell
  box : ∀ b, W.box.getD j none = some b →
    switchBox W.places aM W.zk.logEll = some b ∧ W.zk.ell = 2 ^ W.zk.logEll ∧
      b.shift + W.zk.logEll ≤ W.restBits ∧ b.start < 2 ^ W.restBits
  tail : W.maskTail.getD j [] = switchPieces W.places aT W.zk.r
  incM : ∀ i k, i < k → k < W.zk.ell → W.places.get (aM + i) < W.places.get (aM + k)
  incT : ∀ i k, i < k → k < W.zk.r → W.places.get (aT + i) < W.places.get (aT + k)
  logZ : W.zk.logN ≤ 32

/-- The row of the generator of the old mask code for mask row number j, on every entry of every
table: in both arms (a box, or pieces) the message's weights on its stretch, and the tail's. -/
theorem genMask_at (W : SwitchFrame) (j aM aT : ℕ) (h : MaskAt W j aM aT) (x : ℕ) (t : E) (o : ℕ)
    (part : Part) (J : ℕ) (hJ : J < 2 ^ W.restBits) :
    coefAt (genMask W x j t) o part J =
      if W.g == o && W.restPart == part then
        stretchAt W.places aM W.zk.ell (wM (codeOf W.zk) (shortPosition W.zk.logN x)) J +
          stretchAt W.places aT W.zk.r (wT (codeOf W.zk) (shortPosition W.zk.logN x)) J
      else 0 := by
  have hx' : shortPosition W.zk.logN x < 2 ^ W.zk.logN := Nat.mod_lt _ (Nat.two_pow_pos _)
  have key : ∀ r : Row, coefAt ({ switchAddRestF r W.g W.restPart (W.maskTail.getD j [])
        (generatorTail W.zk (shortPosition W.zk.logN x)) with
        kind := .generator, target := t } : Row) o part J =
      coefAt r o part J + if W.g == o && W.restPart == part then
        stretchAt W.places aT W.zk.r (wT (codeOf W.zk) (shortPosition W.zk.logN x)) J else 0 := by
    intro r
    show coefAt (switchAddRestF r W.g W.restPart (W.maskTail.getD j [])
      (generatorTail W.zk (shortPosition W.zk.logN x))) o part J = _
    rw [h.tail, coefAt_restF_at _ _ _ _ _ _ h.incT, stretch_tail _ _ _ _ h.logZ hx']
  unfold genMask
  rw [key]
  have fin : ∀ a b : GE, ((if W.g == o && W.restPart == part then a else 0) +
      if W.g == o && W.restPart == part then b else 0) =
      if W.g == o && W.restPart == part then a + b else 0 := by
    intro a b
    by_cases c : (W.g == o && W.restPart == part) = true
    · rw [if_pos c, if_pos c, if_pos c]
    · rw [if_neg c, if_neg c, if_neg c, add_zero]
  split
  · rename_i b hb
    obtain ⟨hbox, hpow, hle, hs⟩ := h.box b hb
    rw [coefAt_add, coefAt_empty, zero_add,
      onBox_stretch _ _ _ b hbox _ _ J (vars_messageTensor W.zk _ hpow) hle hs hJ,
      stretch_tensor _ _ _ _ h.logZ hx' hpow, ← hpow, fin]
  · rename_i hb
    rw [h.msg hb, coefAt_restF_at _ _ _ _ _ _ h.incM, coefAt_empty, zero_add,
      stretch_message _ _ _ _ h.logZ hx', fin]

/-! ## The kept rows -/

/-- A form with cnt variables inserted below all others that pick the number b: on the indices
whose low cnt bits are b's it has the form's entries, elsewhere 0. -/
theorem formAt_rowPick (c : Form) (cnt b J : ℕ) :
    formAt (c.insertChoice 0 cnt b) J =
      (if J % 2 ^ cnt = b % 2 ^ cnt then 1 else 0) * formAt c (J / 2 ^ cnt) := by
  have h := Form.entry_insertChoice rdE c 0 cnt b J (fun _ _ => Nat.zero_le _)
  have hu : unshift 0 cnt J = J / 2 ^ cnt := by
    unfold unshift
    rw [pow_zero, Nat.mod_one, Nat.zero_add, Nat.one_mul, Nat.zero_add]
  rw [pow_zero, Nat.div_one, hu] at h
  exact h

/-- The form of the generator's row of the old main code on row number b of a kept member. -/
def keptForm (W : SwitchFrame) (k : KeptPlace) (b x : ℕ) : Form :=
  (Form.ofTensor (messageTensor W.code x)).insertChoice 0 k.rowBits b

/-- That form, at the format's points: on the entries of row b the generator's weights. -/
theorem formAt_keptForm (W : SwitchFrame) (k : KeptPlace) (b x J : ℕ)
    (hpow : W.code.ell = 2 ^ W.code.logEll) (hlog : W.code.logN ≤ 32) (hx : x < 2 ^ W.code.logN)
    (hb : b < 2 ^ k.rowBits) (hJ : J < 2 ^ (k.rowBits + W.code.logEll)) :
    formAt (keptForm W k b x) J =
      if J % 2 ^ k.rowBits = b then wM (codeOf W.code) x (J / 2 ^ k.rowBits) else 0 := by
  have hq : J / 2 ^ k.rowBits < 2 ^ W.code.logEll :=
    Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hJ)
  unfold keptForm
  rw [formAt_rowPick, Nat.mod_eq_of_lt hb, formAt_ofTensor,
    ← cut_messageTensor W.code x hlog hx hpow, cut_of_lt hq]
  by_cases c : J % 2 ^ k.rowBits = b
  · rw [if_pos c, if_pos c, one_mul]
  · rw [if_neg c, if_neg c, zero_mul]

/-- The row of the generator of the old main code for row number b of the kept member k, with the
target t. n: the row's number among all kept rows. -/
def genKept (W : SwitchFrame) (k : KeptPlace) (b n x : ℕ) (t : E) : Row :=
  { switchAddRestF (W.addKept {} k (keptForm W k b x)) W.g W.restPart (W.keptTail.getD n [])
      (generatorTail W.code x) with
    kind := .generator, target := t }

/-- A kept row, on every entry of every table. a: where its tail begins in the rest. -/
theorem genKept_at (W : SwitchFrame) (k : KeptPlace) (b n a : ℕ)
    (hT : W.keptTail.getD n [] = switchPieces W.places a W.code.r)
    (hm : ∀ i j, i < j → j < W.code.r → W.places.get (a + i) < W.places.get (a + j))
    (hlog : W.code.logN ≤ 32) (x : ℕ) (hx : x < 2 ^ W.code.logN) (t : E) (o : ℕ) (part : Part)
    (J : ℕ) :
    coefAt (genKept W k b n x t) o part J =
      coefAt (W.addKept {} k (keptForm W k b x)) o part J +
      if W.g == o && W.restPart == part then
        stretchAt W.places a W.code.r (wT (codeOf W.code) x) J else 0 := by
  show coefAt (switchAddRestF (W.addKept {} k (keptForm W k b x)) W.g W.restPart
    (W.keptTail.getD n []) (generatorTail W.code x)) o part J = _
  rw [hT, coefAt_restF_at _ _ _ _ _ _ hm, stretch_tail _ _ _ _ hlog hx]

/-- A kept row on the main table of the message that takes the member's rows: the form's entries,
but 0 at the pad's places. -/
theorem genKept_new (W : SwitchFrame) (k : KeptPlace) (b n a : ℕ)
    (hT : W.keptTail.getD n [] = switchPieces W.places a W.code.r)
    (hm : ∀ i j, i < j → j < W.code.r → W.places.get (a + i) < W.places.get (a + j))
    (hlog : W.code.logN ≤ 32) (x : ℕ) (hx : x < 2 ^ W.code.logN) (t : E) (hg : k.anew ≠ W.g)
    (hn : (k.pad.map (·.index)).Nodup) (J : ℕ) :
    coefAt (genKept W k b n x t) k.anew .main J =
      if J ∈ k.pad.map (·.index) then 0 else formAt (keptForm W k b x) J := by
  have hg' : (W.g == k.anew) = false := beq_false_of_ne fun e => hg e.symm
  rw [genKept_at W k b n a hT hm hlog x hx]
  unfold SwitchFrame.addKept
  rw [addKept_new _ _ _ _ _ _ _ _ hg hn, coefAt_empty, zero_add, hg', Bool.false_and]
  exact add_zero _

/-- A kept row on the table of g that takes the rest: the form's entries at the pad's places, where
the old pad lies, and the tail's weights. -/
theorem genKept_g (W : SwitchFrame) (k : KeptPlace) (b n a : ℕ)
    (hT : W.keptTail.getD n [] = switchPieces W.places a W.code.r)
    (hm : ∀ i j, i < j → j < W.code.r → W.places.get (a + i) < W.places.get (a + j))
    (hlog : W.code.logN ≤ 32) (x : ℕ) (hx : x < 2 ^ W.code.logN) (t : E) (hg : k.anew ≠ W.g)
    (J : ℕ) :
    coefAt (genKept W k b n x t) W.g W.restPart J =
      stretchAt W.places k.oldPadAt k.pad.length
          (fun q => formAt (keptForm W k b x) (k.pad.getD q default).index) J +
        stretchAt W.places a W.code.r (wT (codeOf W.code) x) J := by
  rw [genKept_at W k b n a hT hm hlog x hx]
  unfold SwitchFrame.addKept
  rw [addKept_g _ _ _ _ _ _ _ _ hg, coefAt_empty, zero_add, beq_self_eq_true, beq_self_eq_true,
    Bool.and_self, if_pos rfl]

/-- A kept row reads no other table. -/
theorem genKept_other (W : SwitchFrame) (k : KeptPlace) (b n a : ℕ)
    (hT : W.keptTail.getD n [] = switchPieces W.places a W.code.r)
    (hm : ∀ i j, i < j → j < W.code.r → W.places.get (a + i) < W.places.get (a + j))
    (hlog : W.code.logN ≤ 32) (x : ℕ) (hx : x < 2 ^ W.code.logN) (t : E) (o : ℕ) (part : Part)
    (h1 : ¬ (o = k.anew ∧ part = .main)) (h2 : ¬ (o = W.g ∧ part = W.restPart)) (J : ℕ) :
    coefAt (genKept W k b n x t) o part J = 0 := by
  have c : ¬ (W.g == o && W.restPart == part) = true := by
    intro e
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at e
    exact h2 ⟨e.1.symm, e.2.symm⟩
  rw [genKept_at W k b n a hT hm hlog x hx]
  unfold SwitchFrame.addKept
  rw [addKept_other _ _ _ _ _ _ _ _ o part h1 h2, coefAt_empty, zero_add, if_neg c]

/-! ## All rows of one draw, in their order -/

/-- The kept rows from the kept members ks on, the first of them being number n. -/
def keptFrom (W : SwitchFrame) (x : ℕ) (sy : ℕ → E) : List KeptPlace → ℕ → List Row
  | [], _ => []
  | k :: ks, n =>
    ((List.range k.rows).map fun b => genKept W k b (n + b) x (sy (1 + (n + b)))) ++
      keptFrom W x sy ks (n + k.rows)

/-- A loop that lays one item for each number below m in front of a list and counts. -/
theorem loop_rows {α : Type} (f : ℕ → ℕ → α) : ∀ (m : ℕ) (acc : List α) (n : ℕ),
    (List.range m).foldl (fun (s : List α × ℕ) b => (f b s.2 :: s.1, s.2 + 1)) (acc, n) =
      (((List.range m).map fun b => f b (n + b)).reverse ++ acc, n + m)
  | 0, acc, n => rfl
  | m + 1, acc, n => by
    rw [List.range_succ, List.foldl_append, loop_rows f m acc n, List.map_append,
      List.reverse_append]
    rfl

/-- The loop over the kept members. -/
theorem loop_kept (W : SwitchFrame) (x : ℕ) (sy : ℕ → E) : ∀ (ks : List KeptPlace)
    (acc : List Row) (n : ℕ),
    (ks.foldl (fun (s : List Row × ℕ) (k : KeptPlace) =>
      (List.range k.rows).foldl (fun (s : List Row × ℕ) b =>
        (genKept W k b s.2 x (sy (1 + s.2)) :: s.1, s.2 + 1)) s) (acc, n)).1.reverse =
      acc.reverse ++ keptFrom W x sy ks n
  | [], acc, n => by simp [keptFrom]
  | k :: ks, acc, n => by
    rw [List.foldl_cons, loop_rows (fun b m => genKept W k b m x (sy (1 + m))) k.rows acc n,
      loop_kept W x sy ks, List.reverse_append, List.reverse_reverse, List.append_assoc]
    rfl

/-- The rows of one draw: the main row, the kept rows member by member and row by row, the mask
rows. -/
theorem switchGenerators_all (W : SwitchFrame) (old : SingleRows) (x : ℕ) (sy : ℕ → E) :
    switchGenerators W old x sy =
      genMain W x (sy 0) :: keptFrom W x sy W.kept 0 ++
        (List.range old.masks).map fun j => genMask W x j (sy (old.maskRow j)) := by
  have h := loop_kept W x sy W.kept [] 0
  rw [List.reverse_nil, List.nil_append] at h
  rw [← h]
  rfl

end H2K.Lift

#print axioms H2K.Lift.genMain_at
#print axioms H2K.Lift.lift_message_cutIndex
#print axioms H2K.Lift.genMask_at
#print axioms H2K.Lift.formAt_keptForm
#print axioms H2K.Lift.genKept_new
#print axioms H2K.Lift.genKept_g
#print axioms H2K.Lift.genKept_other
#print axioms H2K.Lift.switchGenerators_all
