-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CutIndex.lean: the library's object with an OOD sample on each committed table (`Iop.HolographicProtocol`,
Hiop/RecInterface.lean) on another index type, and the rules that carry the interface's properties
along. No protocol occurs here: everything is stated for every object L.

Why. The interface's properties are stated "for every index" of the object's index type. An object
whose index type is wider than the set of indices that it is meant for (every matrix of a shape,
say, where the decoder returns matrices in range alone) fails such a clause for a reason that has
nothing to do with its protocols. Here the index type is cut, and nothing else is touched.

Definitions.
  `reW H g`, `reWB H g`: an honest prover (of one protocol; of a batch) whose private input w' is
    read as g w'. Coins, strategies and abort sets are H's. The protocol is the same term.
  `reIndex L f g`: L on the index type I': an index i' is read as f i'; what the index decoder
    returns is brought back by g. The three protocols, the number of requests in a batch, the OOD
    seeds and answers' types, the test for a collision, `early` and `late` are L's own terms
    (`v_reIndex`).
  `cut L p`: the case I' = the indices with p. The decoder's answer is kept if it has p, and is
    "none" if not.
  `ExtR L`: the three clauses of `WiredR` that speak of the honest provers: the table that each
    holds is the encoder's.
  `simsRe f g Sm`: three simulators of L's protocols, read as simulators of `reIndex L f g`: the
    same three functions.
  `FormatsR L`: the seven clauses of `PropsH` on formats (three verifiers read their oracles at the
    declared positions alone; the batch's marks are coherent; every round's oracle is a string).

Rules (each says what it needs in its statement).
  by unfolding: `recOf_reIndex`, `validT_reIndex`, `validL_reIndex`, `validB_reIndex`,
    `ext_reW`, `reW_eq_comap`, `withheld_reW`, `output_reW`, `ext_reWB`, `one_reWB`, `output_reWB`,
    `v_reIndex`, `v_cut`, `dec_cut`.
  one prover: `acc_reW`, `hvzk_reW`, `acc_reWB`, `hvzk_reWB`.
  the object: `ext_reIndex`, `wired_reIndex`, `reads_reIndex`, `good_reIndex`, `hiding_reIndex`,
    `complete_reIndex`, `formats_reIndex_iff`, `propsH_reIndex`.
  the cut:
    `dec_cut_eq_some`: the cut decoder returns i if and only if L's returns i.
    `dec_cut_eq_none`: if L's decoder returns indices with p alone, the cut loses nothing.
    `wired_cut_iff`: `WiredR` at `cut L p` is L's decoder's clause at the indices with p, and
      `ExtR`.
    `reads_cut`, `formats_cut_iff`.
    `hiding_cut_of`, `complete_cut_of`: the clauses at `cut L p` from clauses on L's OWN provers,
      asked at the private inputs whose index has p. One direction; no converse is stated.

Limits.
- Nothing here says that any object has any property.
- If no index has p, `cut L p` has an empty index type: `WiredR`, `HidingR`, `CompleteR` and the
  clause `hidE` hold of it for nothing. If one index has p, `hidE` holds for nothing. Who uses the
  cut has to show two different members.
- `reIndex` asks nothing of f and g. With g constantly "none" the decoder never answers: `WiredR`
  then fails at every index, and a statement on soundness would be empty. With f constant every
  clause "does not depend on the index" holds for nothing. The rules that need a law of f and g name
  it.
- The cut makes the decoder say "none" where L's decoder returns an index without p. Whether L's
  decoder ever does so is not said here (`dec_cut_eq_none` takes it as a premise). No rule on
  soundness is in this file.
- `hiding_reIndex`, `complete_reIndex`, `good_reIndex`, `propsH_reIndex` ask the clause of L at
  every index of L. For a cut the forms to use are `wired_cut_iff`, `hiding_cut_of`,
  `complete_cut_of`.
- The numbers (z, p, b and the counts) are carried as they are. At z = 1 or p = 1 the clauses that
  bear them hold of every prover.

The definitions `ExtR` and `FormatsR` name premises of later statements; they add nothing to the
library's clauses, of which they are parts, written out.

`ExtR` and `FormatsR` gather clauses of the interface that are to be proved of an object: they may
be read as part of a goal. They are not among this library's goals.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import Hiop.RecWhole
import Hiop.RecKitHonest
import Hiop.RecSide

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Cut
open Iop Prob Hiop
open scoped ENNReal

variable {I I' X : Type} {E : ExtSpec}

/-! ## 1. One honest prover, its private input read through a function -/

section One
variable {Q : InteractiveOracleProof X E} {Wt Wt' : Type}

/-- The same honest prover of the same protocol; the private input w' is read as g w'. -/
def reW (H : Honest Q Wt) (g : Wt' → Wt) : Honest Q Wt' where
  Coin := H.Coin
  ext := fun w => H.ext (g w)
  strat := fun w x c => H.strat (g w) x c
  Bad := H.Bad
  Hid := fun w x => H.Hid (g w) x

/-- The table that it holds at w is H's at g w. -/
theorem ext_reW (H : Honest Q Wt) (g : Wt' → Wt) (w : Wt') : (reW H g).ext w = H.ext (g w) := rfl

/-- It is the library's `Honest.comap` (Hiop/RecKit.lean) at the identity on instances. -/
theorem reW_eq_comap (H : Honest Q Wt) (g : Wt' → Wt) : reW H g = H.comap id g := rfl

/-- Its abort set at w is H's at g w. -/
theorem withheld_reW (H : Honest Q Wt) (g : Wt' → Wt) (w : Wt') (x : X) :
    (reW H g).withheld w x = H.withheld (g w) x := rfl

/-- Its output at w is H's at g w. -/
theorem output_reW (H : Honest Q Wt) (g : Wt' → Wt) (w : Wt') (x : X) (ρ : Rho Q.shape) :
    (reW H g).output w x ρ = H.output (g w) x ρ := rfl

/-- Acceptance outside the abort set is kept, if the new condition on (w, x) implies the old one on
(g w, x). -/
theorem acc_reW {H : Honest Q Wt} {valid : Wt → X → Prop} (h : H.Acc valid) (g : Wt' → Wt)
    (valid' : Wt' → X → Prop) (hv : ∀ w x, valid' w x → valid (g w) x) : (reW H g).Acc valid' :=
  fun w x c ρ hw hρ => h (g w) x c ρ (hv w x hw) hρ

/-- `Honest.HVZK` is kept, with the same simulator and the same number, under the same condition. -/
theorem hvzk_reW {H : Honest Q Wt} {valid : Wt → X → Prop} {z : ℝ≥0∞} (h : H.HVZK valid z)
    (g : Wt' → Wt) (valid' : Wt' → X → Prop) (hv : ∀ w x, valid' w x → valid (g w) x) :
    (reW H g).HVZK valid' z := by
  obtain ⟨Sim, hS⟩ := h
  exact ⟨Sim, fun w x hw => hS (g w) x (hv w x hw)⟩

end One

section Batch
variable {Q : BatchInteractiveOracleProof X E} {Wt Wt' : Type}

/-- The same for the honest prover of a batch. -/
def reWB (H : BatchHonestProver Q Wt) (g : Wt' → Wt) : BatchHonestProver Q Wt' where
  Coin0 := H.Coin0
  Coin := H.Coin
  ext := fun w => H.ext (g w)
  strat0 := fun w c0 => H.strat0 (g w) c0
  strat := fun w c0 x c => H.strat (g w) c0 x c
  Bad := H.Bad
  Hid := fun w x => H.Hid (g w) x
  stop0 := H.stop0

theorem ext_reWB (H : BatchHonestProver Q Wt) (g : Wt' → Wt) (w : Wt') : (reWB H g).ext w = H.ext (g w) :=
  rfl

/-- One request's honest prover of `reWB H g` is `reW` of H's. -/
theorem one_reWB (H : BatchHonestProver Q Wt) (g : Wt' → Wt) : (reWB H g).one = reW H.one g := rfl

/-- Its output for a set J of requests at w is H's at g w. -/
theorem output_reWB (H : BatchHonestProver Q Wt) (g : Wt' → Wt) {N : ℕ} (w : Wt') (x : Fin N → Option X)
    (ρ : BRho N Q.loc.shape Q.ann) (J : Finset (Fin N)) :
    (reWB H g).output w x ρ J = H.output (g w) x ρ J := rfl

theorem acc_reWB {H : BatchHonestProver Q Wt} {valid : Wt → X → Prop} (h : H.Acc valid) (g : Wt' → Wt)
    (valid' : Wt' → X → Prop) (hv : ∀ w x, valid' w x → valid (g w) x) : (reWB H g).Acc valid' :=
  fun w x c ρ hw hρ => h (g w) x c ρ (hv w x hw) hρ

theorem hvzk_reWB {H : BatchHonestProver Q Wt} {N : ℕ} {valid : Wt → X → Prop} {z : ℝ≥0∞}
    (h : H.HVZK N valid z) (g : Wt' → Wt) (valid' : Wt' → X → Prop)
    (hv : ∀ w x, valid' w x → valid (g w) x) : (reWB H g).HVZK N valid' z := by
  obtain ⟨Sim, hS⟩ := h
  exact ⟨Sim, fun w x hw J xs hxs =>
    hS (g w) x (fun j xj hj => hv w xj (hw j xj hj)) J xs hxs⟩

end Batch

/-! ## 2. The object on another index type -/

/-- A private input (index, rest): the index is read through f. -/
abbrev onFst {β : Type} (f : I' → I) : I' × β → I × β := fun w => (f w.1, w.2)

/-- **The same object on other indices**: i' is read as f i'; what the index decoder returns is
brought back by g. -/
def reIndex (L : HolographicProtocol I X) (f : I' → I) (g : I → Option I') : HolographicProtocol I' X where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := fun i r => L.encodeIndex (f i) r
  OutOfDomainSeed := L.OutOfDomainSeed
  OutOfDomainAnswer := L.OutOfDomainAnswer
  honestOutOfDomainAnswer := fun i r s => L.honestOutOfDomainAnswer (f i) r s
  hasCollisionAt := L.hasCollisionAt
  decodeIndex := fun y rec => (L.decodeIndex y rec).bind g
  offline := L.offline
  link := L.link
  maxBatchSize := L.maxBatchSize
  onlineBatch := L.onlineBatch
  honestOfflineProver := reW L.honestOfflineProver (onFst f)
  honestLinkProver := reW L.honestLinkProver (onFst f)
  honestOnlineBatchProver := reWB L.honestOnlineBatchProver (onFst f)
  early := L.early
  late := L.late

open Classical in
/-- An index as a member of the indices with p, if it is one. -/
def back (p : I → Prop) : I → Option {i // p i} := fun i => if h : p i then some ⟨i, h⟩ else none

theorem back_val (p : I → Prop) (i : {i // p i}) : back p i.1 = some i := by
  unfold back
  exact dif_pos i.2

theorem back_eq_some (p : I → Prop) (j : I) (i : {i // p i}) : back p j = some i ↔ j = i.1 := by
  constructor
  · intro h
    unfold back at h
    by_cases hj : p j
    · rw [dif_pos hj] at h
      exact congrArg Subtype.val (Option.some.inj h)
    · rw [dif_neg hj] at h
      cases h
  · intro h
    subst h
    exact back_val p i

/-- **The object cut to the indices with p.** -/
def cut (L : HolographicProtocol I X) (p : I → Prop) : HolographicProtocol {i // p i} X := reIndex L Subtype.val (back p)

section Rules
variable (L : HolographicProtocol I X) (f : I' → I) (g : I → Option I')

/-! ## 3. What holds by unfolding -/

/-- **The verifier's side of the re-indexed object is L's**: word length, symbols, OOD seeds and
answers, the three protocols, the number of requests in a batch, `early`, `late` (the library's
`HolographicProtocol.v`, Hiop/RecSide.lean). -/
theorem v_reIndex : (reIndex L f g).v = L.v := rfl

theorem v_cut (p : I → Prop) : (cut L p).v = L.v := rfl

/-- The honest OOD sample at i' is L's at f i'. -/
theorem recOf_reIndex (i : I') (r : L.EncodingRandomness) (s : L.OutOfDomainSeed) :
    (reIndex L f g).recOf i r s = L.recOf (f i) r s := rfl

theorem validT_reIndex (w : I' × L.EncodingRandomness × L.OutOfDomainSeed) (rec : L.Rec) :
    (reIndex L f g).validT w rec ↔ L.validT (onFst f w) rec := Iff.rfl

theorem validL_reIndex (w : I' × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)) (rr : L.Rec × L.Rec) :
    (reIndex L f g).validL w rr ↔ L.validL (onFst f w) rr := Iff.rfl

theorem validB_reIndex (Ryes : I → X → Prop) (w : I' × L.EncodingRandomness × L.OutOfDomainSeed) (a : X × L.Rec) :
    (reIndex L f g).validB (fun i => Ryes (f i)) w a ↔ L.validB Ryes (onFst f w) a := Iff.rfl

/-- The cut decoder, written out. -/
theorem dec_cut (p : I → Prop) (y : Fin L.wordLength → L.Symbol) (rec : L.Rec) :
    (cut L p).decodeIndex y rec = (L.decodeIndex y rec).bind (back p) := rfl

/-- **The cut decoder returns i if and only if L's decoder returns i.** -/
theorem dec_cut_eq_some (p : I → Prop) (y : Fin L.wordLength → L.Symbol) (rec : L.Rec) (i : {i // p i}) :
    (cut L p).decodeIndex y rec = some i ↔ L.decodeIndex y rec = some i.1 := by
  rw [dec_cut, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨j, hj, hb⟩
    rw [hj, (back_eq_some p j i).1 hb]
  · intro h
    exact ⟨i.1, h, back_val p i⟩

/-- **If L's decoder returns indices with p alone, the cut decoder says "none" only where L's
does.**
-/
theorem dec_cut_eq_none (p : I → Prop) (hp : ∀ y rec i, L.decodeIndex y rec = some i → p i)
    (y : Fin L.wordLength → L.Symbol) (rec : L.Rec) : (cut L p).decodeIndex y rec = none ↔ L.decodeIndex y rec = none := by
  rw [dec_cut]
  cases h : L.decodeIndex y rec with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some i =>
    constructor
    · intro h'
      have e : back p i = some ⟨i, hp y rec i h⟩ := back_val p ⟨i, hp y rec i h⟩
      have h'' : back p i = none := h'
      rw [e] at h''
      cases h''
    · intro h'
      cases h'

end Rules

/-! ## 4. The clauses of `WiredR` -/

/-- The three clauses of `WiredR` that speak of the honest provers: the committed table (for the
link proof: the two tables) that belongs to a prover's private input is the encoder's. A member:
every object whose provers are laid so; E2E/ObjectAtFiles.lean has one (`ext_silent`). -/
structure ExtR (L : HolographicProtocol I X) : Prop where
  extT : ∀ i r s, L.honestOfflineProver.ext (i, r, s) = L.encodeIndex i r
  extL : ∀ i r s r' s', L.honestLinkProver.ext (i, (r, s), (r', s')) = (L.encodeIndex i r, L.encodeIndex i r')
  extB : ∀ i r s, L.honestOnlineBatchProver.ext (i, r, s) = L.encodeIndex i r

/-- `WiredR` is the decoder's clause and these three. -/
theorem wired_iff (L : HolographicProtocol I X) :
    L.WiredR ↔ (∀ i r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i) ∧ ExtR L :=
  ⟨fun h => ⟨h.dec_enc, h.extT, h.extL, h.extB⟩,
    fun h => ⟨h.1, h.2.extT, h.2.extL, h.2.extB⟩⟩

theorem ext_reIndex {L : HolographicProtocol I X} (f : I' → I) (g : I → Option I') (h : ExtR L) :
    ExtR (reIndex L f g) :=
  ⟨fun i r s => h.extT (f i) r s, fun i r s r' s' => h.extL (f i) r s r' s',
    fun i r s => h.extB (f i) r s⟩

/-- `WiredR` of the re-indexed object: L's decoder returns f i' on the honest table and OOD sample
of f i'; g brings f i' back to i'; the three clauses on the provers, at the new object. -/
theorem wired_reIndex (L : HolographicProtocol I X) (f : I' → I) (g : I → Option I')
    (hdec : ∀ i r s, L.decodeIndex (L.encodeIndex (f i) r) (L.recOf (f i) r s) = some (f i))
    (hg : ∀ i, g (f i) = some i) (hE : ExtR (reIndex L f g)) : (reIndex L f g).WiredR :=
  ⟨fun i r s => by
      show (L.decodeIndex (L.encodeIndex (f i) r) (L.recOf (f i) r s)).bind g = some i
      rw [hdec i r s]
      exact hg i,
    hE.extT, hE.extL, hE.extB⟩

/-- **`WiredR` of the cut object is: L's decoder's clause at the indices with p, and the three
clauses on the provers at these indices.** -/
theorem wired_cut_iff (L : HolographicProtocol I X) (p : I → Prop) :
    (cut L p).WiredR ↔
      (∀ i, p i → ∀ r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i) ∧ ExtR (cut L p) :=
  ⟨fun h => ⟨fun i hi r s =>
        (dec_cut_eq_some L p (L.encodeIndex i r) (L.recOf i r s) ⟨i, hi⟩).1 (h.dec_enc ⟨i, hi⟩ r s),
      h.extT, h.extL, h.extB⟩,
    fun h => ⟨fun i r s =>
        (dec_cut_eq_some L p (L.encodeIndex i.1 r) (L.recOf i.1 r s) i).2 (h.1 i.1 i.2 r s),
      h.2.extT, h.2.extL, h.2.extB⟩⟩

/-! ## 5. `ReadsR` -/

/-- The four counts are about the same three protocols; the clause `hidE` is asked at f i, f i'. -/
theorem reads_reIndex {L : HolographicProtocol I X} (f : I' → I) (g : I → Option I') {b qT qpar qch qon : ℕ}
    (h : L.ReadsR b qT qpar qch qon) : (reIndex L f g).ReadsR b qT qpar qch qon :=
  ⟨h.cntT, h.cntLp, h.cntLc, h.cntB, fun S hS s i i' => h.hidE S hS s (f i) (f i')⟩

theorem reads_cut {L : HolographicProtocol I X} (p : I → Prop) {b qT qpar qch qon : ℕ}
    (h : L.ReadsR b qT qpar qch qon) : (cut L p).ReadsR b qT qpar qch qon :=
  reads_reIndex Subtype.val (back p) h

/-! ## 6. Simulators of the three protocols -/

/-- Three simulators of L's protocols as simulators of the re-indexed object's: the same functions
(the protocols are the same terms). -/
def simsRe {L : HolographicProtocol I X} (f : I' → I) (g : I → Option I') (Sm : SimsR L) :
    SimsR (reIndex L f g) := ⟨Sm.T, Sm.Lk, Sm.B⟩

/-- Good simulators stay good, with the same numbers, for every relation Ryes' on the new indices
that lies inside Ryes. -/
theorem good_reIndex {L : HolographicProtocol I X} (f : I' → I) (g : I → Option I') {Sm : SimsR L}
    {Ryes : I → X → Prop} {Ryes' : I' → X → Prop} (hy : ∀ i x, Ryes' i x → Ryes (f i) x)
    {zT zL zO : ℝ≥0∞} (h : Sm.Good Ryes zT zL zO) : (simsRe f g Sm).Good Ryes' zT zL zO :=
  ⟨fun w x hv => h.goodT (onFst f w) x hv, fun w x hv => h.goodL (onFst f w) x hv,
    fun w x hv J xs hxs =>
      h.goodB (onFst f w) x (fun j xj hj => ⟨(hv j xj hj).1, hy _ _ (hv j xj hj).2⟩) J xs hxs⟩

/-! ## 7. `HidingR` and `CompleteR` -/

theorem hiding_reIndex {L : HolographicProtocol I X} (f : I' → I) (g : I → Option I') {Ryes : I → X → Prop}
    {Ryes' : I' → X → Prop} (hy : ∀ i x, Ryes' i x → Ryes (f i) x) {zT zL zO : ℝ≥0∞}
    (h : L.HidingR Ryes zT zL zO) : (reIndex L f g).HidingR Ryes' zT zL zO :=
  ⟨hvzk_reW h.hidT (onFst f) (reIndex L f g).validT fun _ _ hv => hv,
    hvzk_reW h.hidL (onFst f) (reIndex L f g).validL fun _ _ hv => hv,
    hvzk_reWB h.hidB (onFst f) ((reIndex L f g).validB Ryes') fun _ _ hv => ⟨hv.1, hy _ _ hv.2⟩⟩

theorem complete_reIndex {L : HolographicProtocol I X} (f : I' → I) (g : I → Option I') {Ryes : I → X → Prop}
    {Ryes' : I' → X → Prop} (hy : ∀ i x, Ryes' i x → Ryes (f i) x) {pT pL pO : ℝ≥0∞}
    (h : L.CompleteR Ryes pT pL pO) : (reIndex L f g).CompleteR Ryes' pT pL pO :=
  ⟨acc_reW h.accT (onFst f) (reIndex L f g).validT fun _ _ hv => hv,
    acc_reW h.accL (onFst f) (reIndex L f g).validL fun _ _ hv => hv,
    acc_reWB h.accB (onFst f) ((reIndex L f g).validB Ryes') fun _ _ hv => ⟨hv.1, hy _ _ hv.2⟩,
    fun w x hv => h.prT (onFst f w) x hv, fun w x hv => h.prL (onFst f w) x hv,
    fun w x hv => h.prB (onFst f w) x ⟨hv.1, hy _ _ hv.2⟩⟩

/-- **`HidingR` of the cut object, from L's own provers**: the library's three clauses with "the
index has p" added to the condition on the private input. (`Honest.HVZK` and `BatchHonestProver.HVZK` take
that condition as an argument, so the premises are in the library's own words.) -/
theorem hiding_cut_of (L : HolographicProtocol I X) (p : I → Prop) (Ryes : I → X → Prop) {zT zL zO : ℝ≥0∞}
    (hT : L.honestOfflineProver.HVZK (fun w x => p w.1 ∧ L.validT w x) zT)
    (hL : L.honestLinkProver.HVZK (fun w x => p w.1 ∧ L.validL w x) zL)
    (hB : L.honestOnlineBatchProver.HVZK L.maxBatchSize (fun w x => p w.1 ∧ L.validB Ryes w x) zO) :
    (cut L p).HidingR (fun i => Ryes i.1) zT zL zO :=
  ⟨hvzk_reW hT (onFst (Subtype.val : {i // p i} → I)) (cut L p).validT
      fun w _ hv => ⟨w.1.2, hv⟩,
    hvzk_reW hL (onFst (Subtype.val : {i // p i} → I)) (cut L p).validL
      fun w _ hv => ⟨w.1.2, hv⟩,
    hvzk_reWB hB (onFst (Subtype.val : {i // p i} → I)) ((cut L p).validB fun i => Ryes i.1)
      fun w _ hv => ⟨w.1.2, hv⟩⟩

/-- **`CompleteR` of the cut object, from L's own provers**, in the same way: acceptance outside the
abort set, and the measure of the abort set, at the private inputs whose index has p. -/
theorem complete_cut_of (L : HolographicProtocol I X) (p : I → Prop) (Ryes : I → X → Prop) {pT pL pO : ℝ≥0∞}
    (aT : L.honestOfflineProver.Acc (fun w x => p w.1 ∧ L.validT w x))
    (aL : L.honestLinkProver.Acc (fun w x => p w.1 ∧ L.validL w x))
    (aB : L.honestOnlineBatchProver.Acc (fun w x => p w.1 ∧ L.validB Ryes w x))
    (mT : ∀ w x, p w.1 → L.validT w x → prRho (L.honestOfflineProver.withheld w x) ≤ pT)
    (mL : ∀ w x, p w.1 → L.validL w x → prRho (L.honestLinkProver.withheld w x) ≤ pL)
    (mB : ∀ w x, p w.1 → L.validB Ryes w x → prRho (L.honestOnlineBatchProver.one.withheld w x) ≤ pO) :
    (cut L p).CompleteR (fun i => Ryes i.1) pT pL pO :=
  ⟨acc_reW aT (onFst (Subtype.val : {i // p i} → I)) (cut L p).validT
      fun w _ hv => ⟨w.1.2, hv⟩,
    acc_reW aL (onFst (Subtype.val : {i // p i} → I)) (cut L p).validL
      fun w _ hv => ⟨w.1.2, hv⟩,
    acc_reWB aB (onFst (Subtype.val : {i // p i} → I)) ((cut L p).validB fun i => Ryes i.1)
      fun w _ hv => ⟨w.1.2, hv⟩,
    fun w x hv => mT (onFst Subtype.val w) x w.1.2 hv,
    fun w x hv => mL (onFst Subtype.val w) x w.1.2 hv,
    fun w x hv => mB (onFst Subtype.val w) x w.1.2 hv⟩

/-! ## 8. The formats -/

/-- The seven clauses of `PropsH` on formats. They speak of the three verifiers alone. A member:
E2E/ObjectAtFiles.lean (`formats_fullD`). -/
structure FormatsR (L : HolographicProtocol I X) : Prop where
  localT   : L.offline.IsLocal
  localL   : L.link.IsLocal
  localB   : L.onlineBatch.loc.IsLocal
  cohB     : L.onlineBatch.ann.Coherent
  pointT   : Nonempty L.offline.shape.IsPoint
  pointL   : Nonempty L.link.shape.IsPoint
  pointB   : Nonempty L.onlineBatch.loc.shape.IsPoint

/-- The protocols are the same terms, so the formats are the same statements. -/
theorem formats_reIndex_iff (L : HolographicProtocol I X) (f : I' → I) (g : I → Option I') :
    FormatsR (reIndex L f g) ↔ FormatsR L :=
  ⟨fun h => ⟨h.localT, h.localL, h.localB, h.cohB, h.pointT, h.pointL, h.pointB⟩,
    fun h => ⟨h.localT, h.localL, h.localB, h.cohB, h.pointT, h.pointL, h.pointB⟩⟩

theorem formats_cut_iff (L : HolographicProtocol I X) (p : I → Prop) : FormatsR (cut L p) ↔ FormatsR L :=
  formats_reIndex_iff L Subtype.val (back p)

/-- All of `PropsH` along a re-indexing, if g brings f i' back to i'. The premise asks `PropsH` of L
at EVERY index of L. So this rule does not serve the cut for which this file is written (there L
fails the decoder's clause at an index without p); it serves a second re-indexing of an object that
has the properties already, say from matrices in range to the indices that they hold. -/
theorem propsH_reIndex {L : HolographicProtocol I X} (f : I' → I) (g : I → Option I')
    (hg : ∀ i, g (f i) = some i) {Ryes : I → X → Prop} {Ryes' : I' → X → Prop}
    (hy : ∀ i x, Ryes' i x → Ryes (f i) x) {M : LH.Nums} (h : L.PropsH Ryes M) :
    (reIndex L f g).PropsH Ryes' M where
  wired := wired_reIndex L f g (fun i r s => h.wired.dec_enc (f i) r s) hg
    (ext_reIndex f g ⟨h.wired.extT, h.wired.extL, h.wired.extB⟩)
  reads := reads_reIndex f g h.reads
  hidden := hiding_reIndex f g hy h.hidden
  complete := complete_reIndex f g hy h.complete
  localT := h.localT
  localL := h.localL
  localB := h.localB
  cohB := h.cohB
  pointT := h.pointT
  pointL := h.pointL
  pointB := h.pointB

end AtPublicFiles.Cut

#print axioms AtPublicFiles.Cut.output_reW
#print axioms AtPublicFiles.Cut.acc_reW
#print axioms AtPublicFiles.Cut.hvzk_reW
#print axioms AtPublicFiles.Cut.one_reWB
#print axioms AtPublicFiles.Cut.output_reWB
#print axioms AtPublicFiles.Cut.acc_reWB
#print axioms AtPublicFiles.Cut.hvzk_reWB
#print axioms AtPublicFiles.Cut.back_eq_some
#print axioms AtPublicFiles.Cut.reW_eq_comap
#print axioms AtPublicFiles.Cut.v_reIndex
#print axioms AtPublicFiles.Cut.dec_cut_eq_some
#print axioms AtPublicFiles.Cut.dec_cut_eq_none
#print axioms AtPublicFiles.Cut.wired_iff
#print axioms AtPublicFiles.Cut.ext_reIndex
#print axioms AtPublicFiles.Cut.wired_reIndex
#print axioms AtPublicFiles.Cut.wired_cut_iff
#print axioms AtPublicFiles.Cut.reads_reIndex
#print axioms AtPublicFiles.Cut.reads_cut
#print axioms AtPublicFiles.Cut.good_reIndex
#print axioms AtPublicFiles.Cut.hiding_reIndex
#print axioms AtPublicFiles.Cut.complete_reIndex
#print axioms AtPublicFiles.Cut.hiding_cut_of
#print axioms AtPublicFiles.Cut.complete_cut_of
#print axioms AtPublicFiles.Cut.formats_reIndex_iff
#print axioms AtPublicFiles.Cut.formats_cut_iff
#print axioms AtPublicFiles.Cut.propsH_reIndex
