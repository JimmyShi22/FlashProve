-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/PadShape.lean: THE FOURTH TEST ON VALUES OF THE SUB-PROTOCOL "THE ONE EQUATION" (`padB`: the row that is made has no
coefficient on an entry that masks an answer to a sample; the field `pad` of `OneRest`, Johnson/Desc/First/Batch/Shape/DoorChain.lean) FROM ONE Bool ON
THE SHAPE OF THE FIRST CHAIN's STATE (`chainSh`, Johnson/Desc/First/Shape/Chain.lean). The test itself reads values: scalars and weights that are made of
challenges stand in the row. By Honest/K9/PadForms.lean its yes hangs on places alone; and all these places are in the shape: the link's layout
and frame, the ledger's number of slots, and of each message of the statement its shape and ITS PAD's PLACES.

  `padS`, `offS`, `behindS`   the pad of a message; the two facts on places, with code, on shapes
  **`padsS`**                the Bool on the chain's shape:
       for each link born and each array a of the layout at born, where the present segment reads a message o for (born, a.message):
       each place (main, j) of o's pad is an index of o's main table, and no block of a covers it; and each place (mask, j) of the pad of
       the segment's message with the mask row lies at the ledger's number of slots or above
  `padS_sh`, `off_of`, `behind_of`   a yes on the shapes gives the two facts at the state
  **`padB_of_shape`**        where a link L and a ledger F are open at s and the link's group is there: `padsS (chainSh s) = true` gives the field
                          `pad` of `OneRest` to the letter

The Bool can say no: at a layout in which a block lies over a pad's place, and at a ledger with more slots than the mask row has entries in
front of its pad.

Limits. One way: a yes on the shape gives the test. That `padsS` accepts at any shape is not proved here. Where no link or no ledger is open
it says no. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.PadForms
import Johnson.Desc.First.Batch.Shape.DoorChain
import Johnson.Desc.First.Batch.Shape.DoorMkAtS
import Johnson.Desc.First.Batch.Law.RowInsideOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Params (ReqLayout ReqArray)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh LinkSh linkSh LedSh ledSh frameSh rowBitsS rowBits_sh)
open VerifiableInference.Desc.Ground.Sh (StSh stSh tableBitsS tableBitsS_eq orc_get)
open VerifiableInference.Desc.K9 (messageNow equation asRow St Equation)
open VerifiableInference.Desc.K9.Shape (padB)

/-! ## 1 The tests on shapes -/

/-- The pad of message o, in the statement's shape. -/
def padS (st : StSh) (o : ℕ) : List (Part × ℕ) := ((st.oracles[o]?).map (·.pad)).getD []

/-- No block of an array covers a place of the pad of the message that the segment reads for it. -/
def offS (layout : ReqLayout) (f : ReqFrame) (st : StSh) : Bool :=
  (List.range layout.link.length).all fun born =>
    ((layout.link[born]?).getD []).all fun a =>
      match messageNow f born a.message with
      | none => true
      | some o =>
        (padS st o).all fun p =>
          p.1 != .main ||
            (decide (p.2 < 2 ^ tableBitsS st o .main) &&
              a.blocks.all fun b => !laidCovers b (rowBitsS st o .main) p.2)

/-- The pad of the message with the mask row lies behind the first n mask entries. -/
def behindS (f : ReqFrame) (st : StSh) (n : ℕ) : Bool :=
  match ((f.shape.link[f.link]?.map (·.messages)).getD []).findIdx? (fun x => x.shape.maskRows != 0) with
  | none => true
  | some m =>
    match messageNow f f.link m with
    | none => true
    | some o => (padS st o).all fun p => p.1 != .mask || decide (n ≤ p.2)

/-- **The two facts on places, on the chain's shape.** -/
def padsS (a : ChainSh) : Bool :=
  match a.link, a.led with
  | some L, some F =>
    offS L.check.rows.layout L.check.frame.blank a.core.st && behindS L.check.frame.blank a.core.st F.ns
  | _, _ => false

/-! ## 2 A yes on the shapes gives the facts -/

theorem padS_sh (S₀ : Statement) (o : ℕ) : padS (stSh S₀) o = padAt S₀ o := by
  unfold padS padAt
  rw [orc_get]
  cases S₀.oracles[o]? <;> rfl

theorem off_of (layout : ReqLayout) (f : ReqFrame) (S₀ : Statement) (ts : List ReqTerm)
    (h : offS layout (frameSh f).blank (stSh S₀) = true) : PadsOffBlocks layout f S₀ ts := by
  intro t _ a o ha hmsg j hj
  obtain ⟨as, hl, hfind⟩ := Option.bind_eq_some_iff.1 ha
  have hA : a ∈ as := List.mem_of_find?_eq_some hfind
  have hlt : t.born < layout.link.length := (List.getElem?_eq_some_iff.1 hl).1
  unfold offS at h
  have h1 := List.all_eq_true.1 h t.born (List.mem_range.2 hlt)
  beta_reduce at h1
  rw [hl] at h1
  have h2 := List.all_eq_true.1 h1 a hA
  beta_reduce at h2
  have e : messageNow (frameSh f).blank t.born a.message = messageNow f t.born a.message := rfl
  rw [e, hmsg] at h2
  have h3 := List.all_eq_true.1 h2 (Part.main, j) (by rw [padS_sh]; exact hj)
  beta_reduce at h3
  have h4 : (decide (j < 2 ^ tableBitsS (stSh S₀) o .main) &&
      a.blocks.all fun b => !laidCovers b (rowBitsS (stSh S₀) o .main) j) = true := by
    simpa using h3
  rw [Bool.and_eq_true, tableBitsS_eq, ← rowBits_sh] at h4
  refine ⟨of_decide_eq_true h4.1, fun b hb => ?_⟩
  have h5 := List.all_eq_true.1 h4.2 b hb
  simpa using h5

theorem behind_of (f : ReqFrame) (S₀ : Statement) (n : ℕ) (h : behindS (frameSh f).blank (stSh S₀) n = true) :
    PadsBehindMasks f S₀ n := by
  intro m o hm hmsg j hj
  unfold behindS at h
  have e1 : (((frameSh f).blank.shape.link[(frameSh f).blank.link]?.map (·.messages)).getD []).findIdx?
      (fun x => x.shape.maskRows != 0) =
      ((f.shape.link[f.link]?.map (·.messages)).getD []).findIdx? (fun x => x.shape.maskRows != 0) := rfl
  have e2 : messageNow (frameSh f).blank (frameSh f).blank.link m = messageNow f f.link m := rfl
  rw [e1, hm] at h
  simp only at h
  rw [e2, hmsg] at h
  have h3 := List.all_eq_true.1 h (Part.mask, j) (by rw [padS_sh]; exact hj)
  simpa using h3

/-- **The field `pad` of `OneRest`, from the Bool on the shape.** -/
theorem padB_of_shape {s : S} {L : LinkCtx} {F : Fork} (hL : s.link? = some L) (hF : s.fork? = some F)
    (hg : (s.st.groups[L.check.group]?).isSome = true) (h : padsS (chainSh s) = true) :
    ∀ (q : Equation) (F' : Fork) (y : OnBytes.Row × St Unit), equation L F = .ok (q, F') →
      asRow L.check.rows L.check.frame q
        ({ st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } : St Unit) = .ok y →
      padB y.2.st L.check.group y.1 = true := by
  intro q F' y hq hy
  have l1 : (chainSh s).link = some (linkSh L) := by
    show s.link?.map linkSh = _
    rw [hL]
    rfl
  have l2 : (chainSh s).led = some (ledSh F) := by
    show s.fork?.map ledSh = _
    rw [hF]
    rfl
  unfold padsS at h
  rw [l1, l2] at h
  have h' : (offS L.check.rows.layout (frameSh L.check.frame).blank (stSh s.st) &&
      behindS (frameSh L.check.frame).blank (stSh s.st) F.ns) = true := h
  rw [Bool.and_eq_true] at h'
  refine padB_of_places L.check.rows L.check.frame q _ y hy L.check.group hg
    (off_of _ _ _ _ h'.1) ?_
  rw [VerifiableInference.Desc.K9L.equation_masks L F F' q hq]
  exact behind_of _ _ _ h'.2

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.padS_sh
#print axioms ProofFile.Honest.K9.off_of
#print axioms ProofFile.Honest.K9.behind_of
#print axioms ProofFile.Honest.K9.padB_of_shape
