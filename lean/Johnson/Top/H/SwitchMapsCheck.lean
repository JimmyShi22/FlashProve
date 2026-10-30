-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchMapsCheck.lean: a frame that the program makes, behind the program's own
test on the public sizes, meets the comparisons under which the names of a code switch's two maps
lie in the tables of the sending.

Johnson/Top/H/SwitchMapsFit.lean brings the premise of the two maps iJ and iQ
(Johnson/Top/H/SwitchMaps.lean) down to comparisons of public numbers (`Fit`). Here these are shown
for the frame W that `switchFrame S old T g anew` returns, where `switchTargetCheck S old T` says
yes (both: OnBytes/Iop/Cs.lean). Statements and proofs.
Main names:
  `padsRun`, `padsRun_laws`: the loop of `switchParts` over the kept members' old pads.
  `sum_take_lt`: the running number of a kept row is below the number of all kept rows.
  `check_facts`: the clauses of `switchTargetCheck` that are used, one by one.
  `frame_fields`: the fields of a frame, for any new messages of the kept members.
  `parts_laws`: the old pads lie behind all other parts of the rest and end inside the rest.
  `fit_of_check`: `Fit`. So, by `Fit.nameJ` and `Fit.nameQ`, the two maps iJ and iQ are there at
    such a frame.
Limits: five premises of `fit_of_check` are not shown of any run of the programs here: that the
stage s has the frame's two codes; that the list
l begins with g's shape and the shapes of the messages that take the kept members; that the slots'
letters mem, row, pl name rows of the frame's kept members; that the old rows' count of kept rows is
the sum of the frame's members' rows; that a kept member's rows are at least as long as the main
row. No value is written here: whether all premises can be met together at the programs' sizes has
not been evaluated. Nothing on soundness.

-/
import Johnson.Top.H.SwitchMapsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

/-- The loop of `switchParts` over the kept members: where each old pad begins; where the last one
ends. len: a member's pad's length. -/
def padsRun (len : ℕ → ℕ) (ks : List ℕ) (acc : Array ℕ × ℕ) : Array ℕ × ℕ :=
  ks.foldl (fun (s : Array ℕ × ℕ) o => (s.1.push s.2, s.2 + len o)) acc

theorem padsRun_laws (len : ℕ → ℕ) : ∀ (ks : List ℕ) (acc : Array ℕ × ℕ),
    acc.2 ≤ (padsRun len ks acc).2 ∧
      (∀ i, i < acc.1.size → (padsRun len ks acc).1[i]? = acc.1[i]?) ∧
      ∀ i (h : i < ks.length), ∃ v, (padsRun len ks acc).1[acc.1.size + i]? = some v ∧
        v + len ks[i] ≤ (padsRun len ks acc).2
  | [], acc => ⟨Nat.le_refl _, fun _ _ => rfl, fun i h => absurd h (by simp)⟩
  | o :: ks, acc => by
    obtain ⟨h1, h2, h3⟩ := padsRun_laws len ks (acc.1.push acc.2, acc.2 + len o)
    have e : padsRun len (o :: ks) acc = padsRun len ks (acc.1.push acc.2, acc.2 + len o) := rfl
    rw [e]
    have h1' : acc.2 + len o ≤ (padsRun len ks (acc.1.push acc.2, acc.2 + len o)).2 := h1
    have hs : (acc.1.push acc.2).size = acc.1.size + 1 := Array.size_push _
    refine ⟨by omega, ?_, ?_⟩
    · intro i hi
      rw [h2 i (by show i < (acc.1.push acc.2).size; omega)]
      show (acc.1.push acc.2)[i]? = _
      rw [Array.getElem?_push, if_neg (by omega)]
    · intro i hi
      cases i with
      | zero =>
        refine ⟨acc.2, ?_, h1'⟩
        rw [Nat.add_zero, h2 _ (by show acc.1.size < (acc.1.push acc.2).size; omega)]
        show (acc.1.push acc.2)[acc.1.size]? = _
        rw [Array.getElem?_push, if_pos rfl]
      | succ i =>
        obtain ⟨v, ev, hv⟩ := h3 i (by simpa using hi)
        refine ⟨v, ?_, hv⟩
        rw [← ev]
        show _ = (padsRun len ks (acc.1.push acc.2, acc.2 + len o)).1[(acc.1.push acc.2).size + i]?
        rw [hs]
        congr 1
        omega

/-- The rows of the first i members and b more are fewer than all rows, if b is a row of member
number i. -/
theorem sum_take_lt : ∀ (rows : List ℕ) (i b r : ℕ), rows[i]? = some r → b < r →
    (rows.take i).sum + b < rows.sum
  | [], i, b, r, h, _ => by simp at h
  | a :: rows, 0, b, r, h, hb => by
    have : a = r := by simpa using h
    subst this
    simp
    omega
  | a :: rows, i + 1, b, r, h, hb => by
    have h' : rows[i]? = some r := by simpa using h
    have := sum_take_lt rows i b r h' hb
    simp
    omega

/-- The clauses of the program's test on the public sizes that are used below. -/
theorem check_facts {S : Statement} {old : SingleRows} {T : SwitchTarget}
    (h : switchTargetCheck S old T = true) :
    old.masks = 2 ∧ T.main.part = Part.main ∧
      T.main.firstRow + 2 ^ T.main.bits ≤ T.shape.mainRows ∧
      T.rest.firstRow + 2 ^ T.rest.bits ≤ T.shape.rows T.rest.part ∧
      (S.codes.base.getD old.code default).ell ≤
        (S.codes.base.getD T.shape.code default).ell * 2 ^ T.main.bits ∧
      (switchParts S old).length ≤ (SwitchPlaces.make S.codes T).size ∧
      T.kept.size = (switchKept old).size ∧
      ∀ i (h1 : i < (switchKept old).size) (h2 : i < T.kept.size),
        T.kept[i].shape.mainRows = (S.oracles.getD (switchKept old)[i] default).shape.mainRows ∧
          (S.codes.base.getD T.kept[i].shape.code default).ell =
            (S.codes.base.getD (S.oracles.getD (switchKept old)[i] default).shape.code default).ell
    := by
  unfold switchTargetCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hmp⟩, _⟩, _⟩, _⟩, hb⟩, _⟩, hl⟩, hroom⟩,
    hks⟩, hall⟩ := h
  have rows : T.main.firstRow + 2 ^ T.main.bits ≤ T.shape.mainRows ∧
      T.rest.firstRow + 2 ^ T.rest.bits ≤ T.shape.rows T.rest.part := by
    cases hp : T.rest.part with
    | mask =>
      rw [hp] at hb
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      simp only [OracleShape.rows]
      omega
    | main =>
      rw [hp] at hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      simp only [OracleShape.rows]
      omega
  refine ⟨hm, hmp, rows.1, rows.2, hl, hroom, hks, fun i h1 h2 => ?_⟩
  rw [Array.all_eq_true] at hall
  have hz : i < ((switchKept old).zip T.kept).size := by
    rw [Array.size_zip]
    omega
  have hi := hall i hz
  rw [Array.getElem_zip] at hi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
  exact ⟨hi.1.1.1.2, hi.2⟩

/-- The fields of a frame, for any new messages of the kept members. -/
theorem frame_fields (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (anew : Array ℕ) (W : SwitchFrame) (h : switchFrame S old T g anew = some W) :
    S.codes.base[old.code]? = some W.code ∧ S.codes.mask[old.maskCode]? = some W.zk ∧
    W.restPart = T.rest.part ∧ W.mainCut = T.main ∧
    W.rowBits = switchRowBits T .main ∧ W.places = SwitchPlaces.make S.codes T ∧
    W.parts = switchParts S old ∧
    W.kept = (List.range (switchKept old).size).map fun i =>
      { old := (switchKept old).getD i noId, anew := anew.getD i noId
        rows := (S.oracles.getD ((switchKept old).getD i noId) default).shape.mainRows
        rowBits := S.rowBits ((switchKept old).getD i noId) .main
        pad := padOf S ((switchKept old).getD i noId)
        oldPadAt := (switchParts S old).oldPadAt.getD i 0 } := by
  unfold switchFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨code, hc, zk, hz, nc, -, -, -, rfl⟩ := h
  exact ⟨hc, hz, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Where the old pads begin in the rest: behind the masks' messages and all tails. -/
def restHead (S : Statement) (old : SingleRows) : ℕ :=
  old.masks * (S.codes.mask.getD old.maskCode default).ell +
    (S.codes.base.getD old.code default).r +
    old.keptRows * (S.codes.base.getD old.code default).r +
    old.masks * (S.codes.mask.getD old.maskCode default).r

/-- The old pads lie behind that number and end inside the rest. -/
theorem parts_laws (S : Statement) (old : SingleRows) :
    restHead S old ≤ (switchParts S old).length ∧
      ∀ i (h : i < (switchKept old).size),
        (switchParts S old).oldPadAt.getD i 0 + (padOf S (switchKept old)[i]).length ≤
          (switchParts S old).length := by
  have e : (switchParts S old).oldPadAt =
        (padsRun (fun o => (padOf S o).length) (switchKept old).toList (#[], restHead S old)).1 ∧
      (switchParts S old).length =
        (padsRun (fun o => (padOf S o).length) (switchKept old).toList
          (#[], restHead S old)).2 := by
    unfold padsRun
    rw [Array.foldl_toList]
    exact ⟨rfl, rfl⟩
  obtain ⟨L1, -, L3⟩ := padsRun_laws (fun o => (padOf S o).length) (switchKept old).toList
    (#[], restHead S old)
  rw [e.1, e.2]
  refine ⟨L1, fun i h => ?_⟩
  obtain ⟨v, ev, hv⟩ := L3 i (by simpa using h)
  have ev' : (padsRun (fun o => (padOf S o).length) (switchKept old).toList
      (#[], restHead S old)).1[i]? = some v := by simpa using ev
  rw [Array.getD_eq_getD_getElem?, ev']
  simpa using hv

/-- The row bits of a message's main table, off its shape. -/
theorem rowBits_main (S : Statement) (o : ℕ) :
    S.rowBits o .main = ceilLog2 (S.oracles.getD o default).shape.mainRows := by
  unfold Statement.rowBits
  rw [Array.getD_eq_getD_getElem?]
  cases S.oracles[o]? with
  | none => rfl
  | some x => rfl

/-- An entry of a list that is made from the numbers below n. -/
theorem range_map_at {α : Type} (n : ℕ) (F : ℕ → α) (i : ℕ) (p : α)
    (h : ((List.range n).map F)[i]? = some p) : i < n ∧ p = F i := by
  by_cases hi : i < n
  · rw [List.getElem?_map, List.getElem?_range hi] at h
    exact ⟨hi, (Option.some.inj h).symm⟩
  · rw [List.getElem?_eq_none (by simpa using hi)] at h
    exact absurd h (by simp)

theorem ellOf_eq (cs : Codes) (T : SwitchTarget) (p : Part) :
    ellOf cs T.shape p = switchRowLength cs T p := by
  cases p <;> rfl

/-- The number of the places that the program makes, by the sorted pad's length. -/
theorem make_size (cs : Codes) (T : SwitchTarget) :
    (SwitchPlaces.make cs T).size =
      ellOf cs T.shape T.rest.part * 2 ^ T.rest.bits - (SwitchPlaces.make cs T).pad.length := by
  rw [ellOf_eq]
  unfold SwitchPlaces.make
  simp only [List.length_mergeSort]

/-- **A frame that the program makes, behind its own test on the public sizes, meets `Fit`.**
l: the sending's sampled messages: g's shape first, then the shapes of the messages that take the
kept members. s: the old rows' stage, with the frame's two codes. mem, row, pl: the slot k holds the
row number row k of the kept member number mem k, whose record in the frame is pl k. hkr: the old
rows' count of kept rows is that of the frame's members. hcode: a kept member's rows are at least as
long as the main row. -/
theorem fit_of_check (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (anew : Array ℕ) (W : SwitchFrame) (hW : switchFrame S old T g anew = some W)
    (hc : switchTargetCheck S old T = true)
    (l : List (OracleShape × ℕ)) (g0 : 0 < l.length) (hg : (l.get ⟨0, g0⟩).1 = T.shape)
    (hk : ∀ i (hi : i < T.kept.size), ∃ h : 1 + i < l.length,
      (l.get ⟨1 + i, h⟩).1 = T.kept[i].shape)
    (s : Sg) (hC : s.C = codeOf W.code) (hZ : s.Z = codeOf W.zk)
    {K : Type} (mem row : K → ℕ) (pl : K → KeptPlace)
    (hpl : ∀ k, W.kept[mem k]? = some (pl k)) (hrow : ∀ k, row k < (pl k).rows)
    (hkr : old.keptRows = (W.kept.map (·.rows)).sum)
    (hcode : ∀ k, W.code.ell ≤
      (S.codes.base.getD (S.oracles.getD (pl k).old default).shape.code default).ell) :
    Fit S.codes l s W mem row pl := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := frame_fields S old T g anew W hW
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := check_facts hc
  obtain ⟨-, o2, o3⟩ := SwitchPlaces.of_check hc
  obtain ⟨p1, p2⟩ := parts_laws S old
  have g1 : S.codes.base.getD old.code default = W.code := by
    rw [Array.getD_eq_getD_getElem?, f1]
    rfl
  have g2 : S.codes.mask.getD old.maskCode default = W.zk := by
    rw [Array.getD_eq_getD_getElem?, f2]
    rfl
  have hCl : s.C.l = W.code.ell := by rw [hC]; rfl
  have hCr : s.C.r = W.code.r := by rw [hC]; rfl
  have hZl : s.Z.l = W.zk.ell := by rw [hZ]; rfl
  have hZr : s.Z.r = W.zk.r := by rw [hZ]; rfl
  have hd : 2 * W.zk.ell + W.code.r + old.keptRows * W.code.r + 2 * W.zk.r ≤ W.parts.length := by
    have h := p1
    unfold restHead at h
    rw [g1, g2, c1] at h
    rw [f7]
    exact h
  have sMask : ∀ j, j < 2 → W.parts.maskAt.getD j 0 = W.zk.ell * j := fun j hj => by
    rw [f7]
    show (startsFrom 0 (S.codes.mask.getD old.maskCode default).ell old.masks).getD j 0 = _
    unfold startsFrom
    rw [getD_map_range, c1, if_pos hj, g2, Nat.zero_add]
  have sMain : W.parts.mainTailAt = 2 * W.zk.ell := by
    rw [f7]
    show old.masks * (S.codes.mask.getD old.maskCode default).ell = _
    rw [c1, g2]
  have sKept : ∀ n, n < old.keptRows →
      W.parts.keptTailAt.getD n 0 = 2 * W.zk.ell + W.code.r + W.code.r * n := fun n hn => by
    rw [f7]
    show (startsFrom (old.masks * (S.codes.mask.getD old.maskCode default).ell +
      (S.codes.base.getD old.code default).r) (S.codes.base.getD old.code default).r
      old.keptRows).getD n 0 = _
    unfold startsFrom
    rw [getD_map_range, if_pos hn, c1, g1, g2]
  have sTail : ∀ j, j < 2 → W.parts.maskTailAt.getD j 0 =
      2 * W.zk.ell + W.code.r + old.keptRows * W.code.r + W.zk.r * j := fun j hj => by
    rw [f7]
    show (startsFrom (old.masks * (S.codes.mask.getD old.maskCode default).ell +
      (S.codes.base.getD old.code default).r +
      old.keptRows * (S.codes.base.getD old.code default).r)
      (S.codes.mask.getD old.maskCode default).r old.masks).getD j 0 = _
    unfold startsFrom
    rw [getD_map_range, c1, if_pos hj, g1, g2]
  have recK := fun k => range_map_at _ _ _ _ (f8 ▸ hpl k)
  have ko : ∀ i (hi : i < (switchKept old).size),
      (switchKept old).getD i noId = (switchKept old)[i] := fun i hi => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rfl
  refine ⟨g0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg, f5]
    rfl
  · rw [f4, f5]
    have h := o3
    rw [c2] at h
    exact h
  · rw [f4, hg]
    exact c3
  · rw [hCl, hg, f4, ← g1]
    exact c5
  · rw [f6, hg, f3]
    rfl
  · rw [f6]
    exact o2
  · rw [f6, hg, f3]
    exact c4
  · rw [f7, f6, hg, f3]
    have h := make_size S.codes T
    exact h ▸ c6
  · intro j hj
    rw [sMask j hj, hZl]
    interval_cases j <;> omega
  · rw [sMain, hCr]
    omega
  · intro k
    have hn : keptNo W (mem k) (row k) < old.keptRows := by
      rw [hkr]
      unfold keptNo
      rw [List.map_take]
      exact sum_take_lt _ _ _ (pl k).rows (by rw [List.getElem?_map, hpl k]; rfl) (hrow k)
    have h5 : W.code.r * keptNo W (mem k) (row k) + W.code.r ≤ old.keptRows * W.code.r := by
      have h := Nat.mul_le_mul_left W.code.r (Nat.succ_le_of_lt hn)
      rw [Nat.mul_succ, Nat.mul_comm W.code.r old.keptRows] at h
      exact h
    rw [sKept _ hn, hCr]
    omega
  · intro j hj
    rw [sTail j hj, hZr]
    interval_cases j <;> omega
  · intro k
    obtain ⟨hi, e⟩ := recK k
    have e1 : (pl k).oldPadAt = (switchParts S old).oldPadAt.getD (mem k) 0 :=
      congrArg KeptPlace.oldPadAt e
    have e2 : (pl k).pad = padOf S ((switchKept old).getD (mem k) noId) :=
      congrArg KeptPlace.pad e
    rw [e1, e2, ko _ hi, f7]
    exact p2 _ hi
  · intro k
    obtain ⟨hi, e⟩ := recK k
    have hi' : mem k < T.kept.size := by rw [c7]; exact hi
    obtain ⟨h, hs⟩ := hk _ hi'
    obtain ⟨m1, m2⟩ := c8 _ hi hi'
    have e1 : (pl k).rowBits = S.rowBits ((switchKept old).getD (mem k) noId) .main :=
      congrArg KeptPlace.rowBits e
    have e2 : (pl k).rows =
        (S.oracles.getD ((switchKept old).getD (mem k) noId) default).shape.mainRows :=
      congrArg KeptPlace.rows e
    have e3 : (pl k).old = (switchKept old).getD (mem k) noId := congrArg KeptPlace.old e
    refine ⟨h, ?_, ?_, ?_⟩
    · rw [hs, e1, rowBits_main, ko _ hi, m1]
    · rw [hs, m1, ← ko _ hi, ← e2]
      exact hrow k
    · rw [hs, hCl]
      show _ ≤ (S.codes.base.getD T.kept[mem k].shape.code default).ell
      rw [m2, ← ko _ hi, ← e3]
      exact hcode k

end Johnson.Top.H

#print axioms Johnson.Top.H.padsRun_laws
#print axioms Johnson.Top.H.sum_take_lt
#print axioms Johnson.Top.H.check_facts
#print axioms Johnson.Top.H.frame_fields
#print axioms Johnson.Top.H.parts_laws
#print axioms Johnson.Top.H.fit_of_check
