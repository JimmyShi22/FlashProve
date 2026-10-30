-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03AsksAt.lean: AN ATTACK ON OUR OWN END: IS THE KIND "LOOKUP"'s SHARE AT THE CLOSED
CONSTANT, `h.Kind 𝔏 .K3` (Johnson/P5J/RowsAtAll.lean), HOLLOW? IT IS NOT HOLLOW FOR WANT OF A
PLACE, A PIECE OR A BLOCK: IT ASKS `TiedAtR` AT FIFTY BORDERS, AT EACH OF WHICH THE SEATED ROW HAS
A PIECE AND THE KIND's CONSTANT A BLOCK. WHETHER IT IS HOLLOW FOR WANT OF A STATE IS NOT SETTLED
HERE: see "What stays unshown". Two definitions with code and ten theorems: five by the kernel
(two of them negative tests), the others joinings.
Why. The share is `∀ i q a, row[i]? = some q → At.ps[i]? = some a → a.kind = .K3 → TiedAtR … i
(q.withMap …)` (`KindTiedR`, Johnson/Desc/Sound/TiedR.lean): it would be true for nothing if the
row were too short, or if the written list had no place of the kind. And every row of our law
begins `∀ q, row[k]? = some q → ∀ b', k3Const … = some b' →`: true for nothing where there is no
piece or no block.
  `k3Borders`, `k3BordersB`, `k3Borders_full`: the numbers below 358 at which the written list of
    places has a place of the kind K3 are `k3K l false`, `k3K l true`, l below 25, in their order,
    AND NO OTHER. `k3Borders_fifty`: fifty. `k3Borders_control`, `k3Borders_control2`: border 0 is
    not among them; the list with one border dropped is refused. `k03_border_of_kind`: so a place
    of the kind stands at one of the fifty. `k3K_lt`: each lies below 358.
  `k03_piece_some`: at each of the fifty the seated row has a piece (another author's `row_358`,
    Johnson/P5J/K09Len.lean). `k03_const_some`: the kind's constant has a block (another author's
    `k03_states_of`, Johnson/Desc/First/Look/K03States.lean; `IM.Open.W`).
  `k03_kind_asks`: FROM THE SHARE: at each of the fifty: a piece q of the row, and `TiedAtR` at
    it. `k03_kind_iff`: THE SHARE IS JUST THAT: nothing more is asked, nothing less.
WHAT STAYS UNSHOWN, SAID PLAINLY. (1) EVERY TIE OF `TiedAtR` BUT TWO STANDS UNDER THREE HANDS: the
table's promise at the border, "reached", no mark. THAT ANY STATE MEETS THE THREE AT ANY OF THE
FIFTY BORDERS, AND IS ACCEPTED THERE, IS PROVED NOWHERE: an honest proof's walk has been
evaluated: no theorem. Were there none, the letters o, o', R, R' could be chosen empty and the
share would be true for nothing. THAT IS NO FIND OF AN EMPTY CONDITION: no reason is known to think
the set empty: IT IS THE PLACE WHERE A PROOF LACKS. WHAT LACKS IS THE EXISTENCE OF
ACCEPTS, NOTHING ELSE: over an accept the ties themselves hand the promise and "reached" on. IT
BEARS ON THE CLAIM THAT THE LAW ASKS SOMETHING, NOT ON SOUNDNESS: a law that is idle at states
that no run reaches is still a sound law. (2) THE HEAD h IS MET AT THE COPIES (`headMember_zFull`,
`headMember_zGap`); THAT IT CAN BE MET AT THE RELEASE's OWN FILES AS BYTES is evaluated, not proved.
(3) What the promise and the sentences of the composed meaning SAY is not weighed here.
WHY (1) IS NO HOLE FOR WHAT IS BUILT ON THE SHARE, BY THE TEXTS (read at the sealed bytes of "v6 +
laws.8"; a reading, no theorem of this file). The letters o, o', R, R' do not reach the chain's
rule: `goodIn_of_tiedR` (Johnson/Desc/Sound/ChainOfPromisesR.lean :94-117) makes of `TiedAtR k q`
and `HandsOn Rch k q` the piece's law at FIXED conditions: `q.GoodIn (onR k) (onR (k + 1)) (relQ
k) (relQ (k + 1))`, onR k := the table's promise at border k and Rch k. `Piece.GoodIn p on on' R
R'` (Johnson/Desc/Sound/GoodIn.lean :69-72) says: at EVERY a with `on a`, outside a set of
transcripts of weight p.err, wherever the piece accepts, `on' b` holds behind and every witness
behind gives one in front. So it is the pieces' own laws that keep ANY prover's accepted run
inside "the promise and reached" from border to border: tie 2 for the promise, `HandsOn` for Rch,
the two last clauses of `TiedAtR` for a marked state (:108-113). `chainOfPromisesR` (:119-127)
strings them; `firstChainMeans_of_tiedR` (Johnson/P5J/LeadsFirstTiedR.lean :76-89) calls it from
border 0. Were no state inside the three hands at some border, no prover's run would pass that
border accepted, unmarked and inside the promise, but for the error: the verifier would then
accept next to nothing: a failure of completeness, which a run on a real proof shows or refutes;
not a false accept.
WHO PAYS THE REST OF THE RULE's PREMISES AT THE CONSTANT (another pen's reading of the same sealed
bytes, not this pen's): Rch at border 0 at the state at the start, at every typed instance:
Johnson/P5J/RowsAtMg.lean :307 (`rchAt_zero`, and "typed" by ⟨z, rfl⟩); `HandsOn` at h.rch at
every piece of the row, whatever its kind: `good_of_kinds`, the same file :228-248. READ BY
NEITHER: the facts on the start (`AtMg.tieStart`, Johnson/P5J/MgAtConst.lean :55-64), among which
the promise at border 0 is to be sought; what stands above `EachGoodIn` on the way to the file's
theorem.
Limits: at OnBytes.secondHashFunction. The full size alone. No soundness is claimed.

-/
import Johnson.P5J.RowsAtAll
import Johnson.P5J.K09Len
import Johnson.P5J.K03PiecesAt
import Johnson.Desc.First.Look.K03States
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound

/-! ## 1 The fifty borders, and no other -/

/-- The fifty borders, in their order. -/
def k3Borders : List ℕ := (List.range 25).flatMap fun l => [k3K l false, k3K l true]

/-- The numbers below 358 at which the written list has a place of the kind K3 are that list. -/
def k3BordersB (bs : List ℕ) : Bool :=
  ((List.range 358).filter fun i => (At.ps[i]?).any fun a => a.kind == KindName.K3) == bs

set_option maxRecDepth 1000000 in
theorem k3Borders_full : k3BordersB k3Borders = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem k3Borders_fifty : k3Borders.length = 50 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: border 0 is not among them. -/
theorem k3Borders_control : k3Borders.contains 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: with one border dropped the list is refused. -/
theorem k3Borders_control2 : k3BordersB (k3Borders.drop 1) = false := by decide +kernel

/-- A place of the kind K3 on the written list stands at one of the fifty. -/
theorem k03_border_of_kind {i : ℕ} {a : VerifiableInference.Desc.Place} (ha : At.ps[i]? = some a)
    (hk : a.kind = KindName.K3) : ∃ l, l < 25 ∧ ∃ d, i = k3K l d := by
  have hi : i < 358 := by
    have h0 := (List.getElem?_eq_some_iff.1 ha).1
    rw [ps_358] at h0
    exact h0
  have hm : i ∈ (List.range 358).filter fun i =>
      (At.ps[i]?).any fun a => a.kind == KindName.K3 := by
    refine List.mem_filter.2 ⟨List.mem_range.2 hi, ?_⟩
    rw [ha]
    show (a.kind == KindName.K3) = true
    rw [hk]
    rfl
  have e := k3Borders_full
  unfold k3BordersB at e
  rw [beq_iff_eq.1 e] at hm
  obtain ⟨l, hl, hm⟩ := List.mem_flatMap.1 hm
  refine ⟨l, List.mem_range.1 hl, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-! ## 2 A block and a piece at each -/

/-- **The kind's constant has a block at each of the fifty.** -/
theorem k03_const_some (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    (d : Bool) : ∃ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l d = some b' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨Lk, b', -, e, -⟩ := k03_states_of h.scope h.reads O l hl d
  rw [hW] at e
  exact ⟨b', e⟩

set_option maxRecDepth 1000000 in
theorem k3K_lt : ∀ l, l < 25 → ∀ d, k3K l d < 358 := by decide +kernel

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **The seated row has a piece at each of the fifty.** -/
theorem k03_piece_some {l : ℕ} (hl : l < 25) (d : Bool) :
    ∃ q, (h.toAtMg.row 𝔏)[k3K l d]? = some q := by
  have hlt : k3K l d < (h.toAtMg.row 𝔏).length := by
    rw [row_358 h.toAtMg 𝔏 q₁ q₂ q₃]
    exact k3K_lt l hl d
  exact ⟨_, List.getElem?_eq_getElem hlt⟩

/-- **THE SHARE ASKS SOMETHING AT EACH OF THE FIFTY.** -/
theorem k03_kind_asks (K : h.Kind 𝔏 KindName.K3) {l : ℕ} (hl : l < 25) (d : Bool) :
    ∃ q, (h.toAtMg.row 𝔏)[k3K l d]? = some q ∧
      TiedAtR (Fr := FrD) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch
        (k3K l d) (q.withMap (h.toAtMg.ex 𝔏 (k3K l d))) := by
  obtain ⟨q, hq⟩ := k03_piece_some h 𝔏 q₁ q₂ q₃ hl d
  exact ⟨q, hq, K (k3K l d) q (IM.k3Place l d) hq (K3Lot.k03_at_full l hl d) rfl⟩

/-- **AND IT IS JUST THAT.** -/
theorem k03_kind_iff : h.Kind 𝔏 KindName.K3 ↔
    ∀ l, l < 25 → ∀ d, ∃ q, (h.toAtMg.row 𝔏)[k3K l d]? = some q ∧
      TiedAtR (Fr := FrD) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch
        (k3K l d) (q.withMap (h.toAtMg.ex 𝔏 (k3K l d))) := by
  refine ⟨fun K l hl d => k03_kind_asks h 𝔏 q₁ q₂ q₃ K hl d, fun H i q a hq ha hk => ?_⟩
  obtain ⟨l, hl, d, rfl⟩ := k03_border_of_kind ha hk
  obtain ⟨q', hq', T⟩ := H l hl d
  obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
  exact T

end

end P5J

#print axioms P5J.k3Borders_full
#print axioms P5J.k3Borders_fifty
#print axioms P5J.k3Borders_control
#print axioms P5J.k3Borders_control2
#print axioms P5J.k03_border_of_kind
#print axioms P5J.k03_const_some
#print axioms P5J.k3K_lt
#print axioms P5J.k03_piece_some
#print axioms P5J.k03_kind_asks
#print axioms P5J.k03_kind_iff
