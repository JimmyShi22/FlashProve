--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ProdV/LevelSound.lean: the grand product: one level's soundness law, over the
part's own text on a view's rounds (Johnson/Desc/First/ProdV/Level.lean) and over the masked
sumcheck's law (Johnson/Desc/Part/MaskedSumSound.lean, sound_hear). Definitions, statements and
proofs.

`LevelFacts`: what a level's return says, on the outputs of the masked sumcheck's hear and row and
on the round LINE. `level_facts`: the level, where it returns, has them (an unfolding).
`facts_ledger`: what a level hands on: a later ledger of the right sizes, its next free slot, the
rounds left, the next point's size, the next form on filled slots.

`level_sound` (from the outputs: `sound_of_facts`): the law. Fixed first, in this order: the number
of variables m, the point z, the order of the bits; the two maps A (above) and B (below) of a
product tree (Step m A B); the mask row; the next free slot nx (a public number); the start form's
value T on what was shown and its value Cv at the hidden values. The entries of the virtual rows
stand behind the sets, under the "for all" with the run: no set reads them. Then there are sets of
bad elements of K: for each mu at most one bad eps; for each mu, eps, rounds in front and round's
polynomial at most two bad challenges (the m variables' and beta); and, by a formula (badLine), at
most one bad xi, which reads B at (0, r) and (1, r) and the two hidden end values at the ledger
behind the sumcheck: all in front of LINE's draw. Such that: where a level returns, its row is
worth 0 and the next form is worth B at the next point, both at a ledger H later than the level's,
and no bad element was drawn: Cv = A at z: the start form's value is the map above at the point.

The error: at most 1, 2 (m times), 2, 0, 1 bad elements of K in the level's m + 4 rounds: 2 m + 4
(Johnson/Desc/First/ProdV/RunCount.lean).

Nothing that a bad set reads stands under a "there are" behind the run: mu, eps and every round's
sent list and challenge are the fields of R, which the premise readAll (levelCall m z order)
(rs.take (m + 3)) = some R ties to the rounds (readAll is a function); T' is tied by F.publicPart C
= some T'; xi is o.xi, which the level's return ties to the round LINE. The only "there are" are
the bad sets, in front of the run, with their bounds.

Who pays which premise. orderOk, z.size = m: the caller's test on the plan (runOk). Step m A B:
OnBytes/Desc/First/P2/ProdTree.lean, for the maps of any table. F.next = nx: the kind's test that
the ledger's count stands at the place's public number. Sized F: whoever opens the ledger
(slots_sized). OnFilled F C: the caller for its first form; the chain for the others
(onFilled_stepDown). The row's 0 and the next form's truth at H: the link's one equation, and the
next level or the caller's closing. okRounds: the fold's test on the view's words
(OnBytes/Maker/OkView.lean). In the proof it bears no load: a reading judges residues.
For the count it does: the bad sets are sets of K, and what is drawn is three machine words
(Johnson/Desc/First/ProdV/Drawn.lean).

Limits. That the letters which stand first are fixed in time before the rounds (that the mask row
and the leaves are committed in front) is owed where the block is laid in a link. Sets are counted:
no probability. The text on a tape (Johnson/Desc/First/Prod/Level.lean) is not spoken of here.
Not claimed: anything on an honest prover or on hiding; the soundness of a kind or of the protocol.

-/
import Johnson.Desc.First.ProdV.LevelKit
import OnBytes.Desc.First.P2.ProdSum
import OnBytes.Maker.OkView

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.ProdV
open OnBytes OnBytes.Model OnBytes.PscRun Polynomial
open VerifiableInference.Desc.Part
open OnBytes.Desc.First.P1 OnBytes.Desc.First.P2

/-- Every word of an element in these rounds, sent or drawn, is below the prime. -/
def okRounds (rs : List Fmt.RoundView) : Bool :=
  rs.all fun r => r.vals.all OnBytes.Maker.okGot && r.drawn.elems.all fun x => okE (E.ofTriple x)

/-- **What a level's return says**, on the outputs of the masked sumcheck's two texts and on LINE.
-/
def LevelFacts (m : Nat) (z : Array E) (order : List Nat) (C : Aff) (F : Fork) (rs : List Fmt.RoundView)
    (o : LevelOut) (G : Fork) (rest : List Fmt.RoundView) : Prop :=
  ∃ (hd : MaskedSum.Heard) (G1 : Fork) (a b : E) (line : Fmt.RoundView) (s : List E),
    MaskedSum.hear C (levelCall m z order) F (rs.take (m + 3)) = some (hd, G1) ∧
    G1.shown hd.sEnd = some a ∧ G1.shown (hd.sEnd + 1) = some b ∧
    MaskedSum.row hd (mulE a b) {} G1 = some (o.row, G) ∧
    rs.drop (m + 3) = line :: rest ∧ MaskedSum.roundOf 0 1 line = some (s, [o.xi]) ∧
    o.r = layBack m order (hd.r.take m) ∧ o.sL = hd.sEnd ∧ o.sR = hd.sEnd + 1

/-- Form 5's level, where it returns, has them. -/
theorem level_facts {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    LevelFacts m z order C F rs o G rest := by
  obtain ⟨hd, line, s, hw, hdrop, hline, hr, hsL, hsR⟩ := level_spec h
  obtain ⟨G1, sh, hh, hsh, hrow⟩ := whole_spec (e := levelEnds) rfl hw
  obtain ⟨a, b, ha, hb, rfl⟩ := shownEnds_two hsh
  exact ⟨hd, G1, a, b, line, s, hh, ha, hb, hrow, hdrop, hline, hr, hsL, hsR⟩

/-- The reading of the level's rounds returns where the level does. -/
theorem facts_read {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : LevelFacts m z order C F rs o G rest) :
    ∃ R, MaskedSum.readAll (levelCall m z order) (rs.take (m + 3)) = some R := by
  obtain ⟨hd, G1, _, _, _, _, hh, _⟩ := h
  obtain ⟨_, _, R, _, hR, _⟩ := MaskedSum.hear_spec hh
  exact ⟨R, hR⟩

/-- **What a level hands on.** -/
theorem facts_ledger {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (hF : Sized F)
    (h : LevelFacts m z order C F rs o G rest) :
    Later F G ∧ Sized G ∧ G.next = F.next + MaskedSum.ownSlots (levelCall m z order).all + 2 ∧
      rest = rs.drop (m + 4) ∧ (stepDown o).1.size = m + 1 ∧ OnFilled G (stepDown o).2 := by
  obtain ⟨R, hR⟩ := facts_read h
  obtain ⟨hd, G1, a, b, line, s, hh, _, _, hrow, hdrop, _, hr, hsL, hsR⟩ := h
  obtain ⟨_, e2, _, _, _, lFG, sG, nG, _, hen⟩ := ledger_of hF hh hrow hR
  obtain ⟨_, _, _, _, _, _, _, _, hsv⟩ := MaskedSum.readAll_spec (lead := 0)
    (vs := levelVars m z order) (e := levelEnds) hR
  have hvals : R.values.length = 2 := hsv.2.1
  rw [hvals] at nG hen
  have f0 := (hen 0 (by omega)).1
  have f1 := (hen 1 (by omega)).1
  rw [Nat.add_zero] at f0
  refine ⟨lFG, sG, by rw [nG, e2], (drop_succ_of_cons _ _ _ _ hdrop).symm, ?_, ?_⟩
  · show (#[o.xi] ++ o.r).size = m + 1
    rw [Array.size_append, hr, layBack_size]
    show 1 + m = m + 1
    omega
  · exact onFilled_stepDown ⟨by rw [hsL]; exact f0, by rw [hsL, nG]; omega⟩
      ⟨by rw [hsR]; exact f1, by rw [hsR, nG]; omega⟩

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- **THE GRAND PRODUCT: ONE LEVEL's SOUNDNESS LAW**, from LevelFacts. -/
theorem sound_of_facts (m : ℕ) (z : Array E) (order : List ℕ) (ho : orderOk m order = true)
    (hz : z.size = m) (A B : (ℕ → K) → K) (hAB : Step m A B) (mask : ℕ → K)
    (nx : ℕ) (T Cv : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧ (∀ mu eps pre g, (bad mu eps pre g).card ≤ 2) ∧
      ∀ (entry : ℕ → ℕ → ℕ → K) (C : Aff) (F G H : Fork) (rs rest : List Fmt.RoundView) (o : LevelOut)
        (R : MaskedSum.Read) (T' : E),
        okRounds rs = true → LevelFacts m z order C F rs o G rest →
        F.next = nx → Sized F → OnFilled F C →
        F.publicPart C = some T' → ρ.val T' = T → C.value ρ (F.worldOf ρ mask entry) = Cv →
        MaskedSum.readAll (levelCall m z order) (rs.take (m + 3)) = some R →
        Later G H →
        o.row.value ρ (H.worldOf ρ mask entry) = 0 →
        (stepDown o).2.value ρ (H.worldOf ρ mask entry) = B (pt ρ (stepDown o).1) →
        ρ.val R.eps ∉ badE (ρ.val R.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
          (MaskedSum.movesOf ρ (levelCall m z order).all R.rounds
            (addE R.mu (mulE R.eps T')))) →
        ρ.val o.xi ∉ badLine (B (pcons 0 (pt ρ o.r))) (B (pcons 1 (pt ρ o.r)))
          ((G.worldOf ρ mask entry).slot o.sL) ((G.worldOf ρ mask entry).slot o.sR) →
        Cv = A (pt ρ z) := by
  obtain ⟨hn, hlt, hall, hLlen⟩ := coords_facts ho
  obtain ⟨hlen, hblt, _⟩ := orderOk_facts ho
  have hS : IsSum ((⟨0, levelVars m z order, some levelEnds⟩ : MaskedSum.Call).all.map
      (MaskedSum.Var.wt ρ))
      (summand (lvY B (mask (nx + MaskedSum.ownSlots (levelCall m z order).all))
        (mask (nx + MaskedSum.ownSlots (levelCall m z order).all + 1)))
        (order.map fun b => m - 1 - b) (fun _ => 0)) (A (pt ρ z)) := by
    rw [all_wt]
    exact isSum_level hAB _ _ (pt ρ z) (fun _ => 0) (fun i => ptWt (pt ρ z i) 3) (ptWt 0 3)
      (fun i => sumsAt_ptWt _) (sumsAt_ptWt 0) _ hn hlt hall
      fun k hk => (pt_beyond ρ z k (by omega)).symm
  obtain ⟨badE, bad, hE, hB, hrun⟩ := MaskedSum.sound_hear ρ 0 (levelVars m z order) levelEnds
    (level_shapeOk m z order) (fun i => mask (nx + i)) _ _ hS T Cv
  have hd3 : ∀ w ∈ (⟨0, levelVars m z order, some levelEnds⟩ : MaskedSum.Call).all.map
      (MaskedSum.Var.wt ρ), w.d ≤ 3 := by
    rw [all_wt]
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
      exact Nat.le_refl 3
    · rw [List.mem_singleton] at h
      subst h
      exact Nat.le_refl 3
  refine ⟨badE, bad, hE, fun mu eps pre g => ?_, ?_⟩
  · have h1 := hB mu eps pre g
    have h2 := dAt_le _ 3 (by omega) hd3 pre.length
    omega
  intro entry C F G H rs rest o R T' _ hfacts hnx hF hC hpub hT hCv hR hGH hzero hnext hne hnb hxi
  obtain ⟨hd, G1, a, b, line, s, hh, ha, hb, hrow, _, _, hr, hsL, hsR⟩ := hfacts
  obtain ⟨e1, e2, e3, e4, e5, lFG, _, _, hco, hen⟩ := ledger_of hF hh hrow hR
  have hT' : hd.target = T' := Option.some.inj (e5.symm.trans hpub)
  -- the rounds: m variables' and Y's
  obtain ⟨_, _, _, _, _, _, _, hvr, hsv⟩ := MaskedSum.readAll_spec (lead := 0)
    (vs := levelVars m z order) (e := levelEnds) hR
  have hvals : R.values.length = 2 := hsv.2.1
  obtain ⟨_, _, l1, l2, _, hl, hv1, hv2⟩ := hvr.split
  obtain ⟨_, sY, β, _, hl2, _⟩ := hv2.one
  have hl1 : l1.length = m := by
    rw [hv1.length.2, levelVars, List.length_map]
    exact hlen
  have hrr : hd.r = l1.map (·.2) ++ [β] := by
    rw [e4, hl, hl2]
    simp
  have htake : hd.r.take m = l1.map (·.2) := by
    rw [hrr]
    exact take_app _ _ _ (by rw [List.length_map]; exact hl1)
  have hlast : hd.r.getLastD zeroE = β := by
    rw [hrr]
    exact getLastD_snoc _ _ _
  have hpt : pt ρ o.r = place (order.map fun b => m - 1 - b) ((l1.map (·.2)).map ρ.val)
      (fun _ => 0) := by
    rw [hr, htake]
    exact pt_layBack ρ m order _ hblt
  -- the two end slots
  rw [hvals] at hen
  obtain ⟨fL, vpL, mfL⟩ := hen 0 (by omega)
  obtain ⟨fR, vpR, mfR⟩ := hen 1 (by omega)
  rw [Nat.add_zero] at fL vpL mfL
  have haa : a = G1.vp.getD hd.sEnd zeroE := ((shown_iff G1 _ a).1 ha).2.2
  have hbb : b = G1.vp.getD (hd.sEnd + 1) zeroE := ((shown_iff G1 _ b).1 hb).2.2
  have hsE : hd.sEnd = nx + MaskedSum.ownSlots (levelCall m z order).all := by rw [e2, hnx]
  have wL : (G.worldOf ρ mask entry).slot o.sL = ρ.val a - ρ.val β *
      mask (nx + MaskedSum.ownSlots (levelCall m z order).all) := by
    rw [hsL]
    show ρ.val (G.vp.getD hd.sEnd zeroE) - ρ.val (G.mf.getD hd.sEnd zeroE) * mask hd.sEnd = _
    rw [vpL, mfL, hlast, ← haa, hsE]
  have wR : (G.worldOf ρ mask entry).slot o.sR = ρ.val b - ρ.val β *
      mask (nx + MaskedSum.ownSlots (levelCall m z order).all + 1) := by
    rw [hsR]
    show ρ.val (G.vp.getD (hd.sEnd + 1) zeroE) - ρ.val (G.mf.getD (hd.sEnd + 1) zeroE) *
      mask (hd.sEnd + 1) = _
    rw [vpR, mfR, hlast, ← hbb, hsE]
  -- the step down: both hidden end values are B's
  have v1 : (stepDown o).2.value ρ (H.worldOf ρ mask entry) =
      (1 - ρ.val o.xi) * (G.worldOf ρ mask entry).slot o.sL +
        ρ.val o.xi * (G.worldOf ρ mask entry).slot o.sR := by
    show (Aff.scale (Aff.slot o.sL) (subE oneE o.xi) + Aff.scale (Aff.slot o.sR) o.xi).value ρ
      (H.worldOf ρ mask entry) = _
    rw [Aff.value_add, Aff.value_scale, Aff.value_scale, Aff.value_slot, Aff.value_slot, ρ.sub,
      ρ.one, slot_later ρ hGH (j := o.sL) (by rw [hsL]; exact fL),
      slot_later ρ hGH (j := o.sR) (by rw [hsR]; exact fR)]
  have v2 : pt ρ (stepDown o).1 = pcons (ρ.val o.xi) (pt ρ o.r) := pt_cons ρ o.xi o.r
  obtain ⟨tL, tR⟩ := line_sound hAB.affB (pt ρ o.r) _ _ _ hxi (by rw [← v2, ← hnext, v1])
  -- the second world: as H's below the hiding coefficients' end, the mask row behind
  obtain ⟨n, hn'⟩ : ∃ n, n = (MaskedSum.hidingAt (hd.vars.zip hd.r)).1.length := ⟨_, rfl⟩
  rw [← hn'] at hco
  have hCW : C.value ρ (cutWorld (H.worldOf ρ mask entry) mask (hd.first + n)) =
      C.value ρ (H.worldOf ρ mask entry) :=
    value_congr ρ C _ _ rfl fun x hx => cutWorld_lt _ _ (by
      have := (hC x hx).2
      omega)
  have hbAll : ∀ i, (cutWorld (H.worldOf ρ mask entry) mask (hd.first + n)).slot (hd.first + i) =
      mask (nx + i) := by
    intro i
    by_cases hi : i < n
    · rw [cutWorld_lt (H.worldOf ρ mask entry) mask (c := hd.first + n) (j := hd.first + i)
        (by omega)]
      obtain ⟨f0, p0, q0⟩ := hco i hi
      obtain ⟨_, p1, q1⟩ := hGH.keep _ f0
      show ρ.val (H.vp.getD (hd.first + i) zeroE) - ρ.val (H.mf.getD (hd.first + i) zeroE) *
        mask (hd.first + i) = _
      rw [p1, q1, p0, q0, ρ.zero, ρ.sub, ρ.zero, ρ.one, e1, hnx]
      ring
    · rw [cutWorld_ge (H.worldOf ρ mask entry) mask (c := hd.first + n) (j := hd.first + i)
        (by omega), e1, hnx]
  have hdot : MaskedSum.dotFrom ρ
      (fun i => (cutWorld (H.worldOf ρ mask entry) mask (hd.first + n)).slot (hd.first + i))
      (MaskedSum.hidingAt (hd.vars.zip hd.r)).1 =
      MaskedSum.dotFrom ρ (fun i => (H.worldOf ρ mask entry).slot (hd.first + i))
        (MaskedSum.hidingAt (hd.vars.zip hd.r)).1 :=
    dotFrom_congr ρ _ _ _ fun i hi => cutWorld_lt _ _ (by omega)
  refine hrun (cutWorld (H.worldOf ρ mask entry) mask (hd.first + n)) C F G1 (rs.take (m + 3)) hd R
    (mulE a b) {} G1 G o.row hh hR (by rw [hT']; exact hT)
    (by rw [hCW, value_later ρ (lFG.trans hGH) C hC mask entry]; exact hCv)
    (by first | exact hbAll | exact fun i _ => hbAll i) hrow ?_ ?_ hne (by rw [hT']; exact hnb)
  · have r1 := MaskedSum.row_value ρ (cutWorld (H.worldOf ρ mask entry) mask (hd.first + n)) hrow
    have r2 := MaskedSum.row_value ρ (H.worldOf ρ mask entry) hrow
    rw [Aff.value_empty] at r1 r2
    rw [e3, hCW, hdot] at r1
    rw [e3] at r2
    rw [r1, ← r2]
    exact hzero
  · rw [Aff.value_empty, add_zero, ρ.mul, hrr, List.map_append]
    show summand _ _ _ ((l1.map (·.2)).map ρ.val ++ [ρ.val β]) = _
    rw [summand_place _ (ρ.val β) (order.map fun b => m - 1 - b) ((l1.map (·.2)).map ρ.val)
      (fun _ => 0) (by rw [List.length_map, List.length_map, hl1, hLlen]), ← hpt]
    unfold lvY
    rw [← tL, ← tR, wL, wR]
    ring

/-- **THE LAW, OF FORM 5's OWN TEXT.** -/
theorem level_sound (m : ℕ) (z : Array E) (order : List ℕ) (ho : orderOk m order = true)
    (hz : z.size = m) (A B : (ℕ → K) → K) (hAB : Step m A B) (mask : ℕ → K)
    (nx : ℕ) (T Cv : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧ (∀ mu eps pre g, (bad mu eps pre g).card ≤ 2) ∧
      ∀ (entry : ℕ → ℕ → ℕ → K) (C : Aff) (F G H : Fork) (rs rest : List Fmt.RoundView) (o : LevelOut)
        (R : MaskedSum.Read) (T' : E),
        okRounds rs = true → level m z order C F rs = some (o, G, rest) →
        F.next = nx → Sized F → OnFilled F C →
        F.publicPart C = some T' → ρ.val T' = T → C.value ρ (F.worldOf ρ mask entry) = Cv →
        MaskedSum.readAll (levelCall m z order) (rs.take (m + 3)) = some R →
        Later G H →
        o.row.value ρ (H.worldOf ρ mask entry) = 0 →
        (stepDown o).2.value ρ (H.worldOf ρ mask entry) = B (pt ρ (stepDown o).1) →
        ρ.val R.eps ∉ badE (ρ.val R.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
          (MaskedSum.movesOf ρ (levelCall m z order).all R.rounds
            (addE R.mu (mulE R.eps T')))) →
        ρ.val o.xi ∉ badLine (B (pcons 0 (pt ρ o.r))) (B (pcons 1 (pt ρ o.r)))
          ((G.worldOf ρ mask entry).slot o.sL) ((G.worldOf ρ mask entry).slot o.sR) →
        Cv = A (pt ρ z) := by
  obtain ⟨badE, bad, h1, h2, h3⟩ := sound_of_facts ρ m z order ho hz A B hAB mask nx T Cv
  exact ⟨badE, bad, h1, h2, fun entry C F G H rs rest o R T' hw hl =>
    h3 entry C F G H rs rest o R T' hw (level_facts hl)⟩

end

end VerifiableInference.Desc.First.ProdV

#print axioms VerifiableInference.Desc.First.ProdV.level_sound
#print axioms VerifiableInference.Desc.First.ProdV.facts_ledger
