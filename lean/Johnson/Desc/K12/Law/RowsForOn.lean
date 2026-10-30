-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.Ground.Calls
import Johnson.Desc.K1.Law.RowsOn
import Johnson.Desc.K1.Law.FormEq
import Johnson.Desc.Means.Order
/-
Johnson/Desc/K12/Law/RowsForOn.lean: THE SAMPLE ROWS THAT A SENDING MAKES (rowsFor, Johnson/Desc/Ground/Calls.lean) LIE ON THEIR MESSAGE (Means.RowOn), UNDER FIVE NAMED CONDITIONS. It stands over the plain ground, Means and the sending's own laws (K1/Law) alone: it reads no block. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  SampleFit S x seeds   THE FIVE: the codes' lengths are in order (Codes.lengthsOk) · the message's shape fits the codes (Blk.shapeOk) · its pad fits (Msg.padFits) · it has a table (K ≠ 0 or Kzk ≠ 0) · every seed's point has at least v coordinates
  rowsFor_on            the message x stands under o · SampleFit S x seeds · rowsFor S.codes x.shape o seeds is ys acc = some (rows, ys') · every row of acc lies on o ⇒ every row of rows lies on o
HOW: each row that rowsFor adds is Send.form's row with the answer as its target; by formLaw (Johnson/Desc/K1/Law/FormEq.lean) that is sampleRow; by rowIn_sample (Johnson/Desc/K1/Law/SaysTie.lean) sampleRow has what the laying of a row asks at the group whose one member is the message.
  padFits_of_pad · sampleFit_of   the codes' lengths are in order · the shape fits the codes (Blk.shapeOk) · every seed's point has at least the cube's coordinates · the pad's places exist ⇒ the five: what a step that admits carries (Johnson/Desc/K12/Law/CallsDef.lean), with admitP's own yes, gives all but the first
WHAT IT DOES NOT SAY: that the codes' lengths are in order: a test on the codes, which no call turns.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K1
open _root_.Desc.Plain (rowsFor)

/-- The five conditions. -/
structure SampleFit (S : Statement) (x : OnBytes.Oracle) (seeds : List SampleSeed) : Prop where
  lengths : S.codes.lengthsOk = true
  shape : Blk.shapeOk S.codes x.shape = true
  pad : (Msg.of S.codes x.shape).padFits = true
  table : ((Msg.of S.codes x.shape).K != 0 || (Msg.of S.codes x.shape).Kzk != 0) = true
  long : ∀ sd ∈ seeds, (Msg.of S.codes x.shape).v ≤ sd.z.length


theorem rowsFor_on (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (seeds : List SampleSeed) (H : SampleFit S x seeds) :
    ∀ (is : List Nat) (ys ys' : List E) (acc rows : Array Row),
      (∀ r ∈ acc.toList, RowOn S o r) →
      rowsFor S.codes x.shape o seeds is ys acc = some (rows, ys') →
      ∀ r ∈ rows.toList, RowOn S o r
  | [], ys, ys', acc, rows, ha, h => by
    rw [rowsFor] at h
    cases h
    exact ha
  | i :: is, [], ys', acc, rows, ha, h => by
    rw [rowsFor] at h
    cases h
  | i :: is, y :: ys, ys', acc, rows, ha, h => by
    rw [rowsFor] at h
    split at h
    · cases h
    · rename_i seed hseed
      split at h
      · cases h
      · rename_i row hform
        refine rowsFor_on S o x hx seeds H is ys ys' _ rows ?_ h
        intro r hr
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact ha r hr
        · have e : (Send.form S.codes x.shape o seed i).map (fun r => { r with target := y }) =
              some (sampleRow (Msg.of S.codes x.shape) o seed.z seed.beta i y) :=
            formLaw S.codes x.shape o seed.z seed.beta i y H.lengths H.shape H.pad
          have hform' : Send.form S.codes x.shape o seed i = some row := hform
          rw [hform'] at e
          have e' : ({ row with target := y } : OnBytes.Row) =
              sampleRow (Msg.of S.codes x.shape) o seed.z seed.beta i y := Option.some.inj e
          rw [e']
          exact rowIn_sample S _ o x hx (by simp) seed.z seed.beta i y H.table H.pad
            (H.long seed (List.mem_of_getElem? hseed))

/-- Where the pad's places exist, the pad fits. -/
theorem padFits_of_pad (codes : Codes) (s : OracleShape) (pl : List PadPlace)
    (hl : codes.lengthsOk = true) (hs : Blk.shapeOk codes s = true)
    (h : Send.pad codes s = some pl) : (Msg.of codes s).padFits = true := by
  simp only [Codes.lengthsOk, Bool.and_eq_true] at hl
  simp only [Blk.shapeOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  simp only [Msg.padFits, Msg.of, Msg.e, decide_eq_true_eq]
  by_cases hz : s.maskRows = 0
  · have hm : s.code < codes.base.size := by
      rcases hs.1.1.2 with h' | h'
      · omega
      · exact h'
    have e := pow_logEll codes.base s.code hm hl.1
    have hnot : ¬ (codes.base.getD s.code default).ell <
        (if (s.mainDeg == 3) = true then 1 else 3) * s.answers := by
      intro hlt
      have hn : Send.pad codes s = none := by
        unfold Send.pad Send.cube
        simp only [hz, Nat.lt_irrefl, decide_false, Bool.false_or, Bool.false_eq_true, hlt,
          ↓reduceIte]
      rw [hn] at h
      cases h
    simp only [hz, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, if_false, e]
    exact Nat.not_lt.1 hnot
  · have hm : s.maskCode < codes.mask.size := by
      rcases hs.1.2 with h' | h'
      · exact absurd h' hz
      · exact h'
    have hz' : 0 < s.maskRows := Nat.pos_of_ne_zero hz
    have hb : (s.maskRows != 0) = true := by simpa using hz
    have e := pow_logEll codes.mask s.maskCode hm hl.2
    have hnot : ¬ (codes.mask.getD s.maskCode default).ell < 1 * s.answers := by
      intro hlt
      have hn : Send.pad codes s = none := by
        unfold Send.pad Send.cube
        simp only [hz', decide_true, Bool.true_or, hlt, ↓reduceIte]
      rw [hn] at h
      cases h
    simp only [hb, Bool.true_or, if_true, e]
    exact Nat.not_lt.1 hnot

/-- What a step that admits carries gives the five. -/
theorem sampleFit_of (S : Statement) (x : OnBytes.Oracle) (seeds : List SampleSeed)
    (pl : List PadPlace) (hl : S.codes.lengthsOk = true)
    (hfit : Blk.shapeOk S.codes x.shape = true)
    (hlong : ∀ sd ∈ seeds, (Send.cube S.codes x.shape).bits ≤ sd.z.length)
    (hpad : Send.pad S.codes x.shape = some pl) : SampleFit S x seeds where
  lengths := hl
  shape := hfit
  pad := padFits_of_pad S.codes x.shape pl hl hfit hpad
  table := by
    have hs : Blk.shapeOk S.codes x.shape = true := hfit
    simp only [Blk.shapeOk, Bool.and_eq_true, decide_eq_true_eq] at hs
    have h0 := hs.1.1.1
    show (x.shape.mainRows != 0 || x.shape.maskRows != 0) = true
    by_cases hm : x.shape.mainRows = 0
    · have : x.shape.maskRows ≠ 0 := by omega
      simp [this]
    · simp [hm]
  long := fun sd hsd => by
    rw [← cube_bits]
    exact hlong sd hsd

end H2K.Out

#print axioms H2K.Out.rowsFor_on
#print axioms H2K.Out.padFits_of_pad
#print axioms H2K.Out.sampleFit_of
