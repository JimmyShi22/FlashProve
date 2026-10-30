-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/Returns.lean: conditional: the verifier's hearing of a lookup
returns on any rounds that fit (`hearV`, Johnson/Desc/First/Look/Via/Rounds.lean): general in the
face (one part of keys or several; with a shift or without). No honest prover is in it: the rounds
are any rounds. Theorems; one abbreviation.

Terms. Honest/K3/GLOSSARY.md: see there hearing, round, entry, window (of the ledger's slots),
stretch, ledger, slot, sumcheck, tie, key tree and face.

What is shown.
  `hearV_returns`: from the three hypotheses below: there are g and G with hearV f F rs = some (g,
    G).
  `messagesV_returns`: the same of the rounds heard in order, with any rounds left behind them.
  the walk: `sum_step` (one masked sumcheck with end values), `tieV_returns`, `partsV_returns`,
    `run_returns`, `keysV_returns`: each from the window, at start forms on filled slots of the
    window, where there is room, on a stretch that fits the piece's own entries: it returns, the
    window stands behind its slots, and the counts that the hearing's own tests read are as these
    tests ask.

Hypotheses that remain, in `hearV_returns`.
  `hok`: f.ok = true.
  `W`: `Win F.next F.next (F.next + f.slots) F` (Honest/K3/Shape/Window.lean): the ledger's arrays
    have their size, and the lookup's slots are there and free. A test with code on the ledger's
    shape gives it (`win_of_freeB`, there).
  `hR`: `Str (entriesV f) rs` (Honest/K3/Shape/Stretch.lean): the rounds fit the hearing's own
    entries. A sub-protocol's own test on its rounds gives it (`str_of_fit`,
    Honest/K3/Shape/ReturnsFit.lean).
In the walk: `hlo`, `hC`, `hr`: lo lies at or below the count; the start form names slots of the
window alone; there is room up to hi. `hs`: (in `sum_step`) the call passes `shapeOk`. `h`, `e`,
`hz`: a stretch, a length, a return (in the helpers). `partsV_returns`, `run_returns` and
`keysV_returns` have theirs without a name; among them: each level's order has as many entries as
the level has variables, and as many start forms as parts.

How the proof goes. What can reject in the hearing: each routine's own reading of its rounds (met by
`Str`, through Honest/K3/Shape/ReturnsAtoms.lean); each setting of values under slots (met by `Win`,
through the library's `LedgerReady`); a challenge of 0 at the round "PSC Y" (met by the third clause
of `Str`); three tests on counts of its own (met by the counts that the pieces pass on, and by the
sum of the pieces' slots in Honest/K3/Shape/Closed.lean); "nothing is left over" (the stretch has as
many rounds as there are entries). What stands behind each return is taken from
Honest/K3/Shape/Walk.lean and from Honest/K3/Parts/NamesOwn.lean; the pieces are put together by
Honest/K3/Parts/Forward.lean.

Users. ReturnsFit.lean imports this file.

Limits. Every statement here is conditional on its window and its stretch. No instance of these
hypotheses is exhibited in this file. An instance at every face that passes its own test:
`hearV_returns_blank` (ReturnsFit.lean, by proof). The lookup's hearing has no test on a value but
that one on three raw words. It says that the hearing returns, and nothing of what it returns: that
is said in Walk.lean and Honest/K3/Shape/HeardWalk.lean. The seat's decision around the hearing is
not spoken of.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.ReturnsAtoms
import Johnson.Desc.ProofFile.Honest.K3.Shape.Window
import Johnson.Desc.ProofFile.Honest.K3.Parts.Forward

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (E zeroE mulE subE)
open OnBytes.Model (Fork Aff orderDefault)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends entries entry shapeOk ownSlots)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV noVar leafVars bitsCall drawEntry entriesV)
open VerifiableInference.Desc.First.ProdV (level levelVars levelEnds levelEntries runEntries
  Carried stepDown LevelOut)
open ProofFile.Honest.K3.Forward
open ProofFile.Honest.K3.Parts (In in_mono in_slot in_ofConst sumV_names level_names partsV_succ_ret
  partsV_zero_ret keysV_nil_ret keysV_cons_ret messagesV_introP)

local notation "KFace" => VerifiableInference.Desc.K3.Face
local notation "kRounds" => VerifiableInference.Desc.K3.roundsOf
local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

/-! ## Tools -/

/-- A stretch at a list that is made of two, as two lists of rounds. Conditional on the stretch. -/
theorem Str.cut {a b : List Fmt.Entry} {x : List Fmt.RoundView} (h : Str (a ++ b) x) :
    ∃ x1 x2, x = x1 ++ x2 ∧ Str a x1 ∧ Str b x2 :=
  ⟨x.take a.length, x.drop a.length, (List.take_append_drop _ _).symm, h.split.1, h.split.2⟩

theorem take_left' {x rest : List Fmt.RoundView} {n : Nat} (h : x.length = n) :
    (x ++ rest).take n = x := by
  rw [← h, List.take_left]

theorem drop_left' {x rest : List Fmt.RoundView} {n : Nat} (h : x.length = n) :
    (x ++ rest).drop n = rest := by
  rw [← h, List.drop_left]

/-- So many copies of one list of entries, one more in front. No hypothesis. -/
theorem flat_succ (es : List Fmt.Entry) (n : Nat) :
    (List.range (n + 1)).flatMap (fun _ => es) = es ++ (List.range n).flatMap fun _ => es := by
  simp [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem entries_len (lead : Nat) (vs : List Var) (e : Ends) :
    (entries ⟨lead, vs, some e⟩).length = kRounds ⟨lead, vs, some e⟩ := by
  simp [entries, VerifiableInference.Desc.K3.roundsOf]

/-! ## One masked sumcheck with end values -/

/-- **The step at one masked sumcheck with end values.** Conditional on what follows. No instance of
these hypotheses is exhibited in this file. From the window, at a start form on filled slots of the
window, where there is room: it returns on a stretch that fits its entries; the window stands behind
its slots; its row names slots of the window alone. -/
theorem sum_step {lo a hi lead : Nat} {vs : List Var} {e : Ends} {C : Aff} {F : Fork}
    {x : List Fmt.RoundView} (endTerm : List E → List E → E) (W : Win lo a hi F) (hlo : lo ≤ a)
    (hC : In lo a C) (hs : shapeOk ⟨lead, vs, some e⟩ = true)
    (hr : a + (sumOp ⟨lead, vs, some e⟩).len ≤ hi) (hR : Str (entries ⟨lead, vs, some e⟩) x)
    (rest : List Fmt.RoundView) :
    ∃ y G, sumV C ⟨lead, vs, some e⟩ endTerm F (x ++ rest) = some (y, G, rest) ∧
      Win lo (a + (sumOp ⟨lead, vs, some e⟩).len) hi G ∧
      In lo (a + (sumOp ⟨lead, vs, some e⟩).len) y.2 ∧ a ≤ y.1.sEnd ∧
      a + (sumOp ⟨lead, vs, some e⟩).len = y.1.sEnd + e.n := by
  have hl : x.length = kRounds ⟨lead, vs, some e⟩ := hR.length.trans (entries_len _ _ _)
  have hr' : a + ownSlots (Call.all ⟨lead, vs, some e⟩) + (Call.endsN ⟨lead, vs, some e⟩) ≤ hi := by
    have : (sumOp ⟨lead, vs, some e⟩).len =
        ownSlots (Call.all ⟨lead, vs, some e⟩) + (Call.endsN ⟨lead, vs, some e⟩) := rfl
    omega
  obtain ⟨y, G, ey⟩ := sumV_returns (rs := x ++ rest) endTerm (ready_of_win W hC hr') hs
    (by rw [take_left' hl]; exact hR)
  rw [drop_left' hl] at ey
  have hW := win_sum W (sumV_went W.sized ey) hr'
  obtain ⟨n1, n2, n3⟩ := sumV_names (lo := lo) ey (by rw [W.next]; exact hC)
    (by rw [W.next]; exact hlo)
  rw [hW.next] at n1 n3
  rw [W.next] at n2
  have ea : a + ownSlots (Call.all ⟨lead, vs, some e⟩) + (Call.endsN ⟨lead, vs, some e⟩) =
      a + (sumOp ⟨lead, vs, some e⟩).len := Nat.add_assoc _ _ _
  rw [ea] at hW n1 n3
  exact ⟨y, G, ey, hW, n1, n2, n3⟩

/-! ## The tie of the two sides' roots -/

theorem tieStep_ret {s : Array Aff × Nat × Array Nat} {F G : Fork} {rs rest : List Fmt.RoundView}
    {y : MaskedSum.Heard × Aff}
    (e : sumV (Aff.slot s.2.1) (noVar 3 2) (fun _ v =>
      mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)) F rs = some (y, G, rest)) :
    tieStep s F rs = some ((s.1.push y.2, y.1.sEnd, s.2.2.push (y.1.sEnd + 1)), G, rest) := by
  unfold tieStep
  rw [bind_ret e]
  rfl

theorem str_nil {x : List Fmt.RoundView} (h : Str [] x) : x = [] := List.eq_nil_of_length_eq_zero h.length

/-- **The tie returns.** Conditional on the window, room for its slots and a stretch that fits its
entries. No instance of these hypotheses is exhibited in this file. -/
theorem tieV_returns {lo a hi w : Nat} (c : E) {F : Fork} {x : List Fmt.RoundView} (W : Win lo a hi F)
    (hlo : lo ≤ a) (hr : a + (7 + 6 * (w - 2)) ≤ hi)
    (hR : Str (entries (noVar 3 3) ++ (List.range (w - 2)).flatMap fun _ => entries (noVar 3 2)) x)
    (rest : List Fmt.RoundView) :
    ∃ rows sZ sG G, tieV w c F (x ++ rest) = some ((rows, sZ, sG), G, rest) ∧
      Win lo (a + (7 + 6 * (w - 2))) hi G ∧ rows.size = w - 2 + 1 := by
  obtain ⟨x1, x2, rfl, h1, h2⟩ := hR.cut
  obtain ⟨y, F1, e1, W1, _, y1, y2⟩ := sum_step (lead := 0) (vs := []) (e := ⟨3, 3⟩)
    (fun _ v => subE (v.getD 0 zeroE) (mulE c (mulE (mulE (v.getD 1 zeroE) (v.getD 1 zeroE))
      (v.getD 2 zeroE)))) W hlo (in_ofConst lo a zeroE) rfl
    (by show a + 7 ≤ hi; omega) h1 (x2 ++ rest)
  have y2' : a + 7 = y.1.sEnd + 3 := y2
  have W1' : Win lo (a + 7) hi F1 := W1
  obtain ⟨s, G, r', e2, x', er, hx', W2, _, _, hsz⟩ := foldlM_ret
    (f := fun (s : Array Aff × Nat × Array Nat) (_ : Nat) => tieStep s)
    (fun j s F rs => ∃ x', rs = x' ++ rest ∧
      Str ((List.range (w - 2 - j)).flatMap fun _ => entries (noVar 3 2)) x' ∧
      Win lo (a + 7 + 6 * j) hi F ∧ lo ≤ s.2.1 ∧ s.2.1 < a + 7 + 6 * j ∧ s.1.size = 1 + j)
    (List.range (w - 2)) 0 (#[y.2], y.1.sEnd + 1, #[y.1.sEnd + 2]) F1 (x2 ++ rest)
    (fun j hj s F rs hP => by
      rw [List.length_range] at hj
      rw [Nat.zero_add] at hP ⊢
      obtain ⟨x', rfl, hx', Wj, s1, s2, s3⟩ := hP
      rw [show w - 2 - j = (w - 2 - (j + 1)) + 1 by omega, flat_succ] at hx'
      obtain ⟨u1, u2, rfl, g1, g2⟩ := hx'.cut
      obtain ⟨z, G, ez, Wz, _, z1, z2⟩ := sum_step (lead := 0) (vs := []) (e := ⟨3, 2⟩)
        (fun _ v => mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)) Wj
        (by omega) (in_slot s1 s2) rfl (by show a + 7 + 6 * j + 6 ≤ hi; omega) g1 (u2 ++ rest)
      have z2' : a + 7 + 6 * j + 6 = z.1.sEnd + 2 := z2
      have Wz' : Win lo (a + 7 + 6 * j + 6) hi G := Wz
      refine ⟨_, G, u2 ++ rest, by rw [List.append_assoc]; exact tieStep_ret ez, u2, rfl, g2, ?_,
        ?_, ?_, ?_⟩
      · rw [show a + 7 + 6 * (j + 1) = a + 7 + 6 * j + 6 by omega]
        exact Wz'
      · show lo ≤ z.1.sEnd
        omega
      · show z.1.sEnd < _
        omega
      · show (s.1.push z.2).size = _
        rw [Array.size_push, s3]
        omega)
    ⟨x2, rfl, by rw [Nat.sub_zero]; exact h2, by rw [Nat.mul_zero, Nat.add_zero]; exact W1',
      by show lo ≤ y.1.sEnd + 1; omega, by show y.1.sEnd + 1 < _; omega, rfl⟩
  rw [Nat.zero_add, List.length_range] at hx' W2 hsz
  rw [Nat.sub_self] at hx'
  obtain rfl := str_nil hx'
  rw [List.nil_append] at er
  subst er
  refine ⟨s.1, y.1.sEnd, s.2.2.push s.2.1, G, ?_, ?_, by omega⟩
  · rw [List.append_assoc]
    exact tieV_ret e1 e2
  · rw [show a + (7 + 6 * (w - 2)) = a + 7 + 6 * (w - 2) by omega]
    exact W2

/-! ## From the product of the parts' roots to each root -/

/-- **The parts' roots return.** Conditional on the window, a start form on its filled slots, room
and a stretch that fits. No instance of these hypotheses is exhibited in this file. -/
theorem partsV_returns {lo hi : Nat} (rest : List Fmt.RoundView) : ∀ (n a : Nat) (rows : Array Aff)
    (C : Aff) (F : Fork) (x : List Fmt.RoundView), Win lo a hi F → lo ≤ a → In lo a C → a + 5 * n ≤ hi →
    Str ((List.range n).flatMap fun _ => entries (noVar 2 2)) x →
    ∃ rows' roots G, partsV n rows C F (x ++ rest) = some ((rows', roots), G, rest) ∧
      Win lo (a + 5 * n) hi G ∧ rows'.size = rows.size + n ∧ roots.length = n + 1 ∧
      ∀ y ∈ roots, In lo (a + 5 * n) y
  | 0, a, rows, C, F, x, W, _, hC, _, hR => by
    obtain rfl := str_nil hR
    refine ⟨rows, [C], F, partsV_zero_ret rows C F _, W, rfl, rfl, fun y hy => ?_⟩
    obtain rfl : y = C := by simpa using hy
    exact hC
  | n + 1, a, rows, C, F, x, W, hlo, hC, hr, hR => by
    rw [flat_succ] at hR
    obtain ⟨x1, x2, rfl, h1, h2⟩ := hR.cut
    obtain ⟨w, F1, e1, W1, _, w1, w2⟩ := sum_step (lead := 0) (vs := []) (e := ⟨2, 2⟩)
      (fun _ v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) W hlo hC rfl
      (by show a + 5 ≤ hi; omega) h1 (x2 ++ rest)
    have w2' : a + 5 = w.1.sEnd + 2 := w2
    have W1' : Win lo (a + 5) hi F1 := W1
    obtain ⟨rows', roots, G, e2, W2, r1, r2, r3⟩ := partsV_returns rest n (a + 5) (rows.push w.2)
      (Aff.slot (w.1.sEnd + 1)) F1 x2 W1' (by omega) (in_slot (by omega) (by omega)) (by omega) h2
    have ea : a + 5 + 5 * n = a + 5 * (n + 1) := by omega
    rw [ea] at W2 r3
    refine ⟨rows', Aff.slot w.1.sEnd :: roots, G, ?_, W2, ?_, by simp [r2], fun y hy => ?_⟩
    · rw [List.append_assoc]
      exact partsV_succ_ret e1 e2
    · rw [r1, Array.size_push]
      omega
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact in_slot (by omega) (by omega)
      · exact r3 y hy

/-! ## A run of levels; the parts' key trees -/

theorem runEntries_succ (m0 n : Nat) :
    runEntries m0 (n + 1) = runEntries m0 n ++ levelEntries (m0 + n) := by
  unfold runEntries
  rw [List.range_succ, List.flatMap_append]
  simp

theorem levelOps_succ (m0 : Nat) (orders : Nat → List Nat) (n : Nat) :
    levelOps m0 orders (List.range (n + 1)) =
      levelOps m0 orders (List.range n) ++ [levelOp (orders (m0 + n))] := by
  unfold levelOps
  rw [List.range_succ, List.map_append]
  rfl

theorem levelEntries_len (m : Nat) : (levelEntries m).length = m + 4 := by
  simp [levelEntries, entries]

/-- How many slots a list of steps takes. -/
abbrev lenOf (l : List Op) : Nat := (l.map Op.len).sum

/-- **A run of levels returns.** Conditional on the window, a start form on its filled slots, orders
of the levels' lengths, room and a stretch that fits. No instance of these hypotheses is exhibited
in this file. -/
theorem run_returns {lo hi m0 : Nat} (orders : Nat → List Nat) : ∀ (n a : Nat) (s : Carried)
    (F : Fork) (x rest : List Fmt.RoundView), Win lo a hi F → lo ≤ a → In lo a s.form →
    (∀ i, i < n → (orders (m0 + i)).length = m0 + i) →
    a + lenOf (levelOps m0 orders (List.range n)) ≤ hi → Str (runEntries m0 n) x →
    ∃ s' G, vRun m0 n orders s F (x ++ rest) = some (s', G, rest) ∧
      Win lo (a + lenOf (levelOps m0 orders (List.range n))) hi G ∧
      In lo (a + lenOf (levelOps m0 orders (List.range n))) s'.form ∧
      s'.rows.size = s.rows.size + n ∧ (s.point.size = m0 → s'.point.size = m0 + n)
  | 0, a, s, F, x, rest, W, _, hC, _, _, hR => by
    obtain rfl := str_nil hR
    exact ⟨s, F, rfl, W, hC, rfl, fun h => h⟩
  | n + 1, a, s, F, x, rest, W, hlo, hC, hord, hr, hR => by
    rw [runEntries_succ] at hR
    obtain ⟨x1, x2, rfl, h1, h2⟩ := hR.cut
    have hsum : lenOf (levelOps m0 orders (List.range (n + 1))) =
        lenOf (levelOps m0 orders (List.range n)) + (levelOp (orders (m0 + n))).len := by
      unfold lenOf
      rw [levelOps_succ, List.map_append, List.sum_append]
      simp
    rw [hsum] at hr ⊢
    obtain ⟨s1, F1, e1, W1, C1, r1, p1⟩ := run_returns orders n a s F x1 (x2 ++ rest) W hlo hC
      (fun i hi => hord i (by omega)) (by omega) h1
    have hl2 : x2.length = m0 + n + 4 := h2.length.trans (levelEntries_len _)
    have hk : (sumOp ⟨0, levelVars (m0 + n) s1.point (orders (m0 + n)), some levelEnds⟩).len =
        (levelOp (orders (m0 + n))).len := by rw [levelOp_eq]
    obtain ⟨o, G, e2, ho⟩ := level_returns (rs := x2 ++ rest) (z := s1.point) (C := s1.form)
      (ready_of_win W1 C1 (by
        have : (sumOp ⟨0, levelVars (m0 + n) s1.point (orders (m0 + n)), some levelEnds⟩).len =
          ownSlots (Call.all ⟨0, levelVars (m0 + n) s1.point (orders (m0 + n)), some levelEnds⟩) +
            Call.endsN ⟨0, levelVars (m0 + n) s1.point (orders (m0 + n)), some levelEnds⟩ := rfl
        omega))
      (hord n (by omega)) (by rw [take_left' hl2]; exact h2)
    rw [drop_left' hl2] at e2
    have W2 := win_sum W1 (level_went W1.sized e2) (by
      have : (levelOp (orders (m0 + n))).len =
        ownSlots (Call.all ⟨0, levelVars 0 #[] (orders (m0 + n)), some levelEnds⟩) +
          Call.endsN ⟨0, levelVars 0 #[] (orders (m0 + n)), some levelEnds⟩ := rfl
      omega)
    rw [Nat.add_assoc] at W2
    have W2' : Win lo (a + lenOf (levelOps m0 orders (List.range n)) +
        (levelOp (orders (m0 + n))).len) hi G := W2
    obtain ⟨_, n2, _⟩ := level_names (lo := lo) e2 (by rw [W1.next]; exact C1)
      (by rw [W1.next]; omega)
    rw [W2'.next] at n2
    rw [← Nat.add_assoc]
    refine ⟨⟨s1.rows.push o.row, (stepDown o).1, (stepDown o).2⟩, G, ?_, W2', n2, ?_,
      fun hp => ?_⟩
    · rw [List.append_assoc]
      exact run_succ_ret e1 e2
    · show (s1.rows.push o.row).size = _
      rw [Array.size_push, r1]
      omega
    · show (#[o.xi] ++ o.r).size = _
      rw [Array.size_append, ho]
      simp
      omega

/-- **The parts' key trees return.** Conditional on the window, as many start forms as trees, each
on filled slots, orders of the levels' lengths, room and a stretch that fits. No instance of these
hypotheses is exhibited in this file. -/
theorem keysV_returns (f : KFace) {lo hi : Nat} : ∀ (xs : List (Nat × Nat)) (Cs : List Aff)
    (a : Nat) (rows : Array Aff) (F : Fork) (x rest : List Fmt.RoundView), Cs.length = xs.length →
    Win lo a hi F → lo ≤ a → (∀ C ∈ Cs, In lo a C) →
    (∀ y ∈ xs, ∀ i, i < y.1 → (f.orders y.2 (0 + i)).length = 0 + i) →
    a + lenOf (keysOps f xs) ≤ hi → Str (xs.flatMap fun y => runEntries 0 y.1) x →
    ∃ rows' keys G, keysV f xs Cs rows F (x ++ rest) = some ((rows', keys), G, rest) ∧
      Win lo (a + lenOf (keysOps f xs)) hi G ∧ rows'.size = rows.size + (xs.map (·.1)).sum ∧
      keys.length = xs.length
  | [], Cs, a, rows, F, x, rest, _, W, _, _, _, _, hR => by
    obtain rfl := str_nil hR
    exact ⟨rows, [], F, keysV_nil_ret f Cs rows F _, W, rfl, rfl⟩
  | _ :: _, [], _, _, _, _, _, hl, _, _, _, _, _, _ => by cases hl
  | y :: xs, C :: Cs, a, rows, F, x, rest, hl, W, hlo, hC, hord, hr, hR => by
    rw [List.flatMap_cons] at hR
    obtain ⟨x1, x2, rfl, h1, h2⟩ := hR.cut
    have hsum : lenOf (keysOps f (y :: xs)) =
        lenOf (levelOps 0 (f.orders y.2) (List.range y.1)) + lenOf (keysOps f xs) := by
      unfold lenOf
      show ((levelOps 0 (f.orders y.2) (List.range y.1) ++ keysOps f xs).map Op.len).sum = _
      rw [List.map_append, List.sum_append]
    rw [hsum] at hr ⊢
    obtain ⟨k, F1, e1, W1, _, r1, _⟩ := run_returns (m0 := 0) (f.orders y.2) y.1 a
      ⟨rows, #[], C⟩ F x1 (x2 ++ rest) W hlo (hC C (List.mem_cons_self ..))
      (hord y (List.mem_cons_self ..)) (by omega) h1
    obtain ⟨rows', keys, G, e2, W2, r2, k2⟩ := keysV_returns f xs Cs _ k.rows F1 x2 rest
      (Nat.succ.inj hl) W1 (by omega)
      (fun D hD => in_mono (hC D (List.mem_cons_of_mem _ hD)) (by omega))
      (fun z hz => hord z (List.mem_cons_of_mem _ hz)) (by omega) h2
    rw [← Nat.add_assoc]
    refine ⟨rows', (k.point, k.form) :: keys, G, ?_, W2, ?_, by simp [k2]⟩
    · rw [List.append_assoc]
      exact keysV_cons_ret e1 e2
    · rw [r2, r1, List.map_cons, List.sum_cons]
      show rows.size + y.1 + _ = _
      omega

/-! ## The whole row -/

theorem draws_step {name : String} {n : Nat} (F : Fork) {x : List Fmt.RoundView}
    (hR : Str [drawEntry name n] x) (rest : List Fmt.RoundView) :
    ∃ a, drawsV n F (x ++ rest) = some (a, F, rest) ∧ a.size = n := by
  have hl : x.length = 1 := hR.length
  obtain ⟨a, e, hs⟩ := drawsV_returns (F := F) (rs := x ++ rest) (name := name) (n := n)
    (by rw [take_left' hl]; exact hR)
  rw [drop_left' hl] at e
  exact ⟨a, e, hs⟩

theorem draw_step {name : String} (F : Fork) {x : List Fmt.RoundView} (hR : Str [drawEntry name 1] x)
    (rest : List Fmt.RoundView) : ∃ a, drawV F (x ++ rest) = some (a, F, rest) := by
  have hl : x.length = 1 := hR.length
  obtain ⟨a, e⟩ := drawV_returns (F := F) (rs := x ++ rest) (name := name)
    (by rw [take_left' hl]; exact hR)
  rw [drop_left' hl] at e
  exact ⟨a, e⟩

theorem win_owed3 {lo a hi : Nat} {F : Fork} (W : Win lo a hi F) : Win lo a hi (owed3 F) := by
  have W1 := win_owe W (owe_went W.sized (owe_ret "look-up-mask-claims" F []))
  have W2 := win_owe W1 (owe_went W1.sized (owe_ret "look-up-plane-claims" _ []))
  exact win_owe W2 (owe_went W2.sized (owe_ret "look-up-join" _ []))

theorem flat_zipIdx (g : Nat → List Fmt.Entry) : ∀ (l : List Nat) (n : Nat),
    (l.zipIdx n).flatMap (fun y => g y.1) = l.flatMap g
  | [], _ => rfl
  | v :: l, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons, flat_zipIdx g l]

theorem entries_leaf (f : KFace) (z : Array E) :
    entries ⟨0, leafVars f z, none⟩ = entries ⟨0, leafVars f #[], none⟩ := by
  simp [entries, leafVars, Function.comp_def, Var.d]

theorem entries_bits (z : List E) (m : Nat) (hz : z.length = m) :
    entries (bitsCall z) = entries (bitsCall (List.replicate m zeroE)) := by
  subst hz
  simp [entries, bitsCall, Function.comp_def, Var.d, List.map_const']

/-- The entries of a lookup's rounds, piece by piece. No hypothesis. -/
theorem entriesV_eq (f : KFace) : entriesV f =
    (if f.shifted then [drawEntry "LKP shift" 1] else []) ++ ([drawEntry "LKP" 1] ++
      ((entries (noVar 3 3) ++ (List.range (f.planes - 2)).flatMap fun _ => entries (noVar 3 2)) ++
      ((List.range (f.parts.length - 1)).flatMap (fun _ => entries (noVar 2 2)) ++
      ([drawEntry "JOIN" f.mu] ++ (f.parts.flatMap (fun v => runEntries 0 v) ++
      (runEntries f.mu f.d ++ (entries ⟨0, leafVars f #[], none⟩ ++
      ([drawEntry "ZERO" (f.mu + f.d)] ++
        entries (bitsCall (List.replicate (f.mu + f.d) zeroE)))))))))) := by
  unfold entriesV
  simp only [List.append_assoc]

/-- **The lookup's rounds, heard in order, return**, whatever rounds stand behind the stretch.
Conditional on the face's own test, on the window and on the stretch fitting the hearing's own
entries. No instance of these hypotheses is exhibited in this file. -/
theorem messagesV_returns (f : KFace) (hok : f.ok = true) {F : Fork} {x : List Fmt.RoundView}
    (W : Win F.next F.next (F.next + f.slots) F) (hR : Str (entriesV f) x)
    (rest : List Fmt.RoundView) : ∃ g G, messagesV f F (x ++ rest) = some (g, G, rest) := by
  have hS := lookOps_len hok
  unfold lookOps at hS
  have l0 : Op.owe.len = 0 := rfl
  have l1 : ∀ o, (Op.left o).len = o := fun _ => rfl
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, l0, l1, len_tie, len_parts] at hS
  have hp := parts_pos hok
  have hmu : 1 ≤ f.mu ∧ 2 ≤ f.planes := by
    have h := hok
    unfold VerifiableInference.Desc.K3.Face.ok at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2⟩
  rw [entriesV_eq] at hR
  obtain ⟨x5, y5, rfl, h5, hR⟩ := hR.cut
  obtain ⟨x6, y6, rfl, h6, hR⟩ := hR.cut
  obtain ⟨x7, y7, rfl, h7, hR⟩ := hR.cut
  obtain ⟨x8, y8, rfl, h8, hR⟩ := hR.cut
  obtain ⟨x9, y9, rfl, h9, hR⟩ := hR.cut
  obtain ⟨x10, y10, rfl, h10, hR⟩ := hR.cut
  obtain ⟨x12, y12, rfl, h12, hR⟩ := hR.cut
  obtain ⟨x14, y14, rfl, h14, hR⟩ := hR.cut
  obtain ⟨x15, x16, rfl, h15, h16⟩ := hR.cut
  simp only [List.append_assoc]
  have W0 := win_owed3 W
  -- the shift, where there is one; the point at which the sides are compared
  obtain ⟨theta, e5⟩ : ∃ theta, (if f.shifted then drawV else pure zeroE : Hr E) (owed3 F)
      (x5 ++ (x6 ++ (x7 ++ (x8 ++ (x9 ++ (x10 ++ (x12 ++ (x14 ++ (x15 ++ (x16 ++ rest)))))))))) =
      some (theta, owed3 F,
        x6 ++ (x7 ++ (x8 ++ (x9 ++ (x10 ++ (x12 ++ (x14 ++ (x15 ++ (x16 ++ rest))))))))) := by
    cases hsh : f.shifted with
    | true =>
      rw [hsh] at h5
      exact draw_step _ h5 _
    | false =>
      rw [hsh] at h5
      obtain rfl := str_nil h5
      exact ⟨zeroE, rfl⟩
  obtain ⟨alpha, e6⟩ := draw_step (owed3 F) h6
    (x7 ++ (x8 ++ (x9 ++ (x10 ++ (x12 ++ (x14 ++ (x15 ++ (x16 ++ rest))))))))
  -- the tie
  obtain ⟨rows, sZ, sG, F7, e7, W7, z7⟩ := tieV_returns (w := f.planes) (f.factor theta alpha) W0
    (Nat.le_refl _) (by omega) h7 (x8 ++ (x9 ++ (x10 ++ (x12 ++ (x14 ++ (x15 ++ (x16 ++ rest)))))))
  obtain ⟨_, nZ, nG, sGs, _⟩ := ProofFile.Honest.K3.Parts.tieV_names (lo := F.next) e7
    (by rw [W0.next])
  rw [W7.next] at nZ nG
  -- the parts' roots
  obtain ⟨rows2, roots, F8, e8, W8, z8, l8, n8⟩ := partsV_returns
    (x9 ++ (x10 ++ (x12 ++ (x14 ++ (x15 ++ (x16 ++ rest)))))) (f.parts.length - 1) _ rows
    (Aff.slot sZ) F7 x8 W7 (by omega) (in_slot nZ.1 nZ.2) (by omega) h8
  obtain ⟨jo, e9, s9⟩ := draws_step F8 h9 (x10 ++ (x12 ++ (x14 ++ (x15 ++ (x16 ++ rest)))))
  -- the key side
  rw [← flat_zipIdx (fun v => runEntries 0 v) f.parts 0] at h10
  obtain ⟨rows3, keys, F10, e10, W10, z10, l10⟩ := keysV_returns f f.parts.zipIdx roots _ rows2 F8
    x10 (x12 ++ (x14 ++ (x15 ++ (x16 ++ rest)))) (by rw [l8, List.length_zipIdx]; omega) W8
    (by omega) n8 (fun y hy i hi => orders_len hok y hy i (List.mem_range.2 hi))
    (by unfold lenOf; omega) h10
  -- the table side
  obtain ⟨table, F12, e12, W12, n12, z12, p12⟩ := run_returns (m0 := f.mu) orderDefault f.d _
    ⟨rows3, jo.reverse, joinForm f sG jo.reverse⟩ F10 x12 (x14 ++ (x15 ++ (x16 ++ rest))) W10
    (by omega)
    (ProofFile.Honest.K3.Parts.in_joinForm f sG jo.reverse fun j hj => by
      have hm : sG.getD j 0 ∈ sG.toList := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
        exact Array.getElem_mem_toList _
      have := nG _ hm
      exact ⟨this.1, by unfold lenOf; omega⟩)
    (fun i _ => by simp [orderDefault]) (by unfold lenOf; omega) h12
  have hsz : table.point.size = f.mu + f.d := p12 (by simp [s9])
  -- the leaves' sumcheck, left open
  have hl14 : x14.length = (leafVars f table.point).length + 1 := by
    rw [h14.length]
    simp [entries, leafVars]
  obtain ⟨leaves, F14, e14⟩ := openV_returns (rs := x14 ++ (x15 ++ (x16 ++ rest)))
    (C := table.form) (vs := leafVars f table.point)
    (ready_of_win W12 n12 (by
      show _ + ownSlots (leafVars f table.point) + 0 ≤ _
      rw [leaf_own]
      unfold lenOf
      omega))
    (by
      have : 0 < f.mu + f.d := by omega
      simp [shapeOk, leafVars, Var.d]
      refine ⟨fun j _ => by split <;> simp, by omega⟩)
    (by rw [take_left' hl14, entries_leaf]; exact h14)
  rw [drop_left' hl14] at e14
  have W14 := win_left W12 (openV_went W12.sized e14)
  rw [leaf_own] at W14
  obtain ⟨ze, e15, s15⟩ := draws_step F14 h15 (x16 ++ rest)
  -- the bits
  have hz : ze.reverse.toList.length = f.mu + f.d := by simp [s15]
  rw [← entries_bits _ _ hz] at h16
  obtain ⟨bits, F16, e16, W16, _, _, _⟩ := sum_step (lead := 0)
    (vs := ze.reverse.toList.map fun x => Var.point x 3) (e := ⟨2, 1⟩)
    (fun _ x => subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)) W14
    (Nat.le_refl _) (in_ofConst _ _ zeroE) (by simp [shapeOk, Var.d])
    (by
      have : sumOp ⟨0, ze.reverse.toList.map fun x => Var.point x 3, some ⟨2, 1⟩⟩ =
        sumOp (bitsCall (List.replicate (f.mu + f.d) zeroE)) := bits_op _ _ hz
      rw [this]
      unfold lenOf
      omega) h16 rest
  have hb : sumOp ⟨0, ze.reverse.toList.map fun x => Var.point x 3, some ⟨2, 1⟩⟩ =
      sumOp (bitsCall (List.replicate (f.mu + f.d) zeroE)) := bits_op _ _ hz
  rw [hb] at W16
  exact ⟨_, F16, messagesV_introP f e5 e6 e7 e8 e9 e10 (by rw [l10, List.length_zipIdx]) e12 hsz
    e14 e15 e16 (by rw [W16.next]; unfold lenOf; omega) (by
      rw [Array.size_push, z12]
      show rows3.size + f.d + 1 = _
      rw [z10, z8, z7, map_zipIdx_fst (fun v => v)]
      unfold VerifiableInference.Desc.K3.Face.lins
      simp
      omega)⟩

/-- **The lookup's hearing returns.** Conditional on the face's own test, on the window (the
lookup's slots are there and free) and on the rounds fitting the hearing's own entries. No instance
of these hypotheses is exhibited in this file. -/
theorem hearV_returns (f : KFace) (hok : f.ok = true) {F : Fork} {rs : List Fmt.RoundView}
    (W : Win F.next F.next (F.next + f.slots) F) (hR : Str (entriesV f) rs) :
    ∃ g G, hearV f F rs = some (g, G) := by
  obtain ⟨g, G, e⟩ := messagesV_returns f hok W hR []
  rw [List.append_nil] at e
  exact ⟨g, G, hearV_intro f hok e⟩

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.Str.cut
#print axioms ProofFile.Honest.K3.Shape.take_left'
#print axioms ProofFile.Honest.K3.Shape.drop_left'
#print axioms ProofFile.Honest.K3.Shape.flat_succ
#print axioms ProofFile.Honest.K3.Shape.entries_len
#print axioms ProofFile.Honest.K3.Shape.sum_step
#print axioms ProofFile.Honest.K3.Shape.tieStep_ret
#print axioms ProofFile.Honest.K3.Shape.str_nil
#print axioms ProofFile.Honest.K3.Shape.tieV_returns
#print axioms ProofFile.Honest.K3.Shape.partsV_returns
#print axioms ProofFile.Honest.K3.Shape.runEntries_succ
#print axioms ProofFile.Honest.K3.Shape.levelOps_succ
#print axioms ProofFile.Honest.K3.Shape.levelEntries_len
#print axioms ProofFile.Honest.K3.Shape.run_returns
#print axioms ProofFile.Honest.K3.Shape.keysV_returns
#print axioms ProofFile.Honest.K3.Shape.draws_step
#print axioms ProofFile.Honest.K3.Shape.draw_step
#print axioms ProofFile.Honest.K3.Shape.win_owed3
#print axioms ProofFile.Honest.K3.Shape.flat_zipIdx
#print axioms ProofFile.Honest.K3.Shape.entries_leaf
#print axioms ProofFile.Honest.K3.Shape.entries_bits
#print axioms ProofFile.Honest.K3.Shape.entriesV_eq
#print axioms ProofFile.Honest.K3.Shape.messagesV_returns
#print axioms ProofFile.Honest.K3.Shape.hearV_returns
