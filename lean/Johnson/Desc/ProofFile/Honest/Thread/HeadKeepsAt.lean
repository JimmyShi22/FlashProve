-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadKeepsAt.lean: at the first chain's invariant at the full
size with `keeps` given kind by kind (`lettersHead … (kpBy f)`, FirstHead.lean, KeepsBy.lean), what
`keeps` is at the sub-protocols of a segment that stand before its batching, by their numbers. The
library has the written place of each such sub-protocol as a proved fact (`IM.hear_placeW`,
Johnson/IMR/SendsK1.lean). So `keeps` at number `14 * l + i + 2` is the clause `f k` of the kind `k`
that the list `kindsBeforeBatching` has at index `i`, at the place with segment `l` and piece `i + 1`. From
this come two hypotheses of `csHead_stays` (GatherStays.lean). No definition.

  1  `head_keeps_hear`   the equivalence
  2  `att_sub`, `lay_sub`   segment `2 * g + 1` is an attention segment and `2 * g` a feed-forward
     one, for `g < 12`
  3  `head_hatt`   the hypothesis `hatt`: from "the clause at each of five places of an attention
     segment leaves the field `g`"
  4  `head_hlay`   the hypothesis `hlay`: from the like for the field `own` at four places of a
     feed-forward segment, and from `keeps` at the segment's batching

Limits.
  * `f` is an argument. Nothing shows that a clause leaves a field.
  * The batching is not in the list `kindsBeforeBatching`. Its hypothesis in `head_hlay` speaks of `keeps` at
    its number.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.Thread.HeadLetters
import Johnson.IMR.SendsK1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- Segment `2 * g + 1` is an attention segment. -/
theorem att_sub : ∀ g, g < 12 → IM.subAt (2 * g + 1) = ModelPart.attention := by decide

/-- Segment `2 * g` is a feed-forward segment. -/
theorem lay_sub : ∀ g, g < 12 → IM.subAt (2 * g) = ModelPart.layers := by decide

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`keeps` at a sub-protocol before a segment's batching is its kind's clause at its place.** -/
theorem head_keeps_hear {l i : Nat} {k : KindName} (hl : l < 25)
    (hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some k) (s s' : TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).keeps
        (14 * l + i + 2) s s' ↔
      f k { chain := 1, link := some l, piece := i + 1, kind := k } s s' := by
  have e : IM.placesW = P5J.At.ps :=
    head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
  have hp : P5J.At.ps[14 * l + i + 2]? =
      some { chain := 1, link := some l, piece := i + 1, kind := k } := by
    rw [← e]
    exact IM.hear_placeW hl hk
  exact (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hp s s').trans
    (kpBy_at f (κ := k) rfl s s')

/-- The hypothesis `hatt` of `csHead_stays`. -/
theorem head_hatt
    (hG : ∀ g, g < 12 → ∀ i k, 2 ≤ i → i ≤ 6 → (kindsBeforeBatching ModelPart.attention false)[i]? = some k →
      ∀ s s', f k { chain := 1, link := some (2 * g + 1), piece := i + 1, kind := k } s s' →
      ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g) :
    ∀ g, g < 12 → ∀ b, 14 * (2 * g + 1) + 4 ≤ b → b + 1 ≤ 14 * (2 * g + 1) + 9 →
      ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  intro g hg b h1 h2 s s' hK
  obtain ⟨i, hi2, hi6, rfl⟩ : ∃ i, 2 ≤ i ∧ i ≤ 6 ∧ b = 14 * (2 * g + 1) + i + 2 :=
    ⟨b - (14 * (2 * g + 1) + 2), by omega, by omega, by omega⟩
  have hlen : i < (kindsBeforeBatching ModelPart.attention false).length := by
    show i < 7
    omega
  have hk : (kindsBeforeBatching ModelPart.attention false)[i]? = some (kindsBeforeBatching ModelPart.attention false)[i] :=
    List.getElem?_eq_getElem hlen
  have hz : ((2 * g + 1) == 0) = false := beq_eq_false_iff_ne.2 (by omega)
  have hk' : (kindsBeforeBatching (IM.subAt (2 * g + 1)) ((2 * g + 1) == 0))[i]? =
      some (kindsBeforeBatching ModelPart.attention false)[i] := by
    rw [att_sub g hg, hz]
    exact hk
  exact hG g hg i _ hi2 hi6 hk s s'
    ((head_keeps_hear h H Q test carryX item n₁ n₂ b₀ Vd Rd f w (by omega) hk' s s').1 hK)

/-- The hypothesis `hlay` of `csHead_stays`. `hB`: the same at the segment's batching, asked of
`keeps` at its number. -/
theorem head_hlay
    (hO : ∀ g, g < 12 → ∀ i k, 3 ≤ i → i ≤ 6 →
      (kindsBeforeBatching ModelPart.layers ((2 * g) == 0))[i]? = some k →
      ∀ s s', f k { chain := 1, link := some (2 * g), piece := i + 1, kind := k } s s' →
      ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own)
    (hB : ∀ g, g < 12 → ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps (28 * g + 9) s
        s' →
      ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own) :
    ∀ g, g < 12 → ∀ b, 28 * g + 5 ≤ b → b + 1 ≤ 28 * g + 10 →
      ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  intro g hg b h1 h2 s s' hK
  by_cases h9 : b = 28 * g + 9
  · subst h9
    exact hB g hg s s' hK
  · obtain ⟨i, hi3, hi6, rfl⟩ : ∃ i, 3 ≤ i ∧ i ≤ 6 ∧ b = 14 * (2 * g) + i + 2 :=
      ⟨b - (14 * (2 * g) + 2), by omega, by omega, by omega⟩
    have hlen : i < (kindsBeforeBatching ModelPart.layers ((2 * g) == 0)).length := by
      show i < 7
      omega
    have hk : (kindsBeforeBatching ModelPart.layers ((2 * g) == 0))[i]? =
        some (kindsBeforeBatching ModelPart.layers ((2 * g) == 0))[i] := List.getElem?_eq_getElem hlen
    have hk' : (kindsBeforeBatching (IM.subAt (2 * g)) ((2 * g) == 0))[i]? =
        some (kindsBeforeBatching ModelPart.layers ((2 * g) == 0))[i] := by
      rw [lay_sub g hg]
      exact hk
    exact hO g hg i _ hi3 hi6 hk s s'
      ((head_keeps_hear h H Q test carryX item n₁ n₂ b₀ Vd Rd f w (by omega) hk' s s').1 hK)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.att_sub
#print axioms ProofFile.Honest.FirstThread.lay_sub
#print axioms ProofFile.Honest.FirstThread.head_keeps_hear
#print axioms ProofFile.Honest.FirstThread.head_hatt
#print axioms ProofFile.Honest.FirstThread.head_hlay
