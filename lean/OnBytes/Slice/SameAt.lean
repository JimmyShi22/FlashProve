-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SameAt.lean: two implementations that agree on bit strings give, place by place, one
string under one root, for any reading by leaves; and the case of two descriptions of chains that
open stored tables.

OnBytes/Slice/SameStored.lean proves it for the library's own reading `Compile.Batch.extEnc`
(`extEnc_same`). OnBytes/Slice/Reading.lean has other ways of reading a string off what a log
determines at the leaves under a root. This file proves the same for every reading that goes leaf by
leaf: what it makes of the leaf queries is matched on bit strings (`SameRead`,
OnBytes/Slice/SameRead.lean), and the two ways of building a string from symbols agree where their
inputs do. The strings of two interfaces have two types, so the statements are place by place, with
a match u of the symbols.

Main definitions.
 `keepAll`                 the reading of a leaf query that keeps the stored table's symbol,
                           whatever the salt.
 `Reading.ByLeaves R keep g`   R's string is g of what `keep` makes of the leaves.
Main theorems.
 `Reading.byLeaf_all_at`   the reading by leaves at `keepAll` is the library's `extEnc`.
 `Reading.byLeaf_byLeaves` `Reading.byLeaf` goes by leaves, with the wiring's `build` as g.
 `Reading.wide_byLeaves`   so does the library's own reading `Reading.wide`, at `keepAll`.
 `Reading.at_same_of`      two readings that go by leaves, through two implementations that meet
                           `SameRead` at their two `keep`, read one symbol at each place, off a log
                           in which no two strings have one answer.
 `at_same`                 the same for two `Reading.byLeaf`, with `extEnc_same`'s hypothesis on the
                           two `build`.
 `build_same_any`, `ext_ok_any`   at the wirings `WkAny` of two descriptions that hypothesis holds,
                           with the identity as u, and the external part's three laws hold.
 `extEnc_same_any`, `at_same_any`   `extEnc_same` and `at_same` at the wirings and encodings of two
                           descriptions. Left in the first, beside what the encodings themselves ask
                           (a configuration digest of 32 bytes; a reader for the statement,
                           `StmInv`): one configuration digest, one salt length, one depth of stored
                           trees.

What is not claimed. No probability: the log is fixed, and that no two of its strings have one
answer is a hypothesis (a bound: OnBytes/Slice/OneLog.lean). That any two implementations meet
`SameRead` at a `keep` other than `keepAll`: in `at_same_any` it is a hypothesis. For a reading that
does not go by leaves nothing is said. A reading is worth what its test is worth
(OnBytes/Slice/Reading.lean). The encodings in the last two theorems are `Tie.pageX`'s, made for the
protocol under the tag `link`: of an encoding for a key's or a proof's interface nothing is said.
Nothing on any protocol, language, checker or hash function.

-/
import OnBytes.Slice.Reading
import OnBytes.Slice.SameStored
import OnBytes.Slice.SameStoredAt
import OnBytes.Slice.TopAny

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch

section
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The reading of a leaf query that keeps the stored table's symbol, at every place and whatever
the salt. -/
def keepAll : ℕ → LeafIn L → Option L.Symbol := fun _ q => storedSym q

/-- The reading by leaves that keeps every stored symbol gives the library's `extEnc`. -/
theorem Reading.byLeaf_all_at {W : QueryLayout lam L} (h : W.B.ext.OK) (tr : Tc W) (cm : Dig lam) :
    (Reading.byLeaf h keepAll).at W tr cm = extEnc W tr cm := by
  rw [Reading.byLeaf_at, extEnc_eq_storedSym]
  rfl

/-- **The reading R goes by leaves**: its string is g of what `keep j` makes of the leaf query at
each place j, and of nothing else. -/
structure Reading.ByLeaves (R : Reading L) (keep : ℕ → LeafIn L → Option L.Symbol)
    (g : (ℕ → Option L.Symbol) → Fin L.wordLength → L.Symbol) : Prop where
  /-- the string that R makes of the leaves is g of what `keep` makes of them -/
  of_eq : ∀ f, R.of f = g fun j => (f j).bind (keep j)

/-- `Reading.byLeaf` goes by leaves, with the wiring's way of building a string from symbols. -/
theorem Reading.byLeaf_byLeaves {W : QueryLayout lam L} (h : W.B.ext.OK)
    (keep : ℕ → LeafIn L → Option L.Symbol) :
    (Reading.byLeaf h keep).ByLeaves keep fun φ => W.B.ext.build fun q => φ q.val :=
  ⟨fun _ => rfl⟩

/-- The library's own reading goes by leaves, at `keepAll`. -/
theorem Reading.wide_byLeaves {W : QueryLayout lam L} (h : W.B.ext.OK) :
    (Reading.wide h).ByLeaves keepAll fun φ => W.B.ext.build fun q => φ q.val := by
  refine ⟨fun f => ?_⟩
  show W.B.ext.build _ = W.B.ext.build _
  refine congrArg _ (funext fun q => ?_)
  show _ = (f q.val).bind (keepAll q.val)
  rcases f q.val with _ | ⟨_ | (s | y), salt⟩ <;> rfl

end

variable {I₁ X₁ I₂ X₂ : Type} {lam : ℕ} {L₁ : BatchProtocol I₁ X₁} {L₂ : BatchProtocol I₂ X₂}

/-- **Two readings that go by leaves read one symbol at each place, through two implementations that
agree on bit strings.** Off a log in which no two strings have one answer, under one digest cm.
Asked: `OneBlock` of both implementations; `SameRead` at what the two `keep` make of leaf queries
(the first matched by u); one depth of the two wirings; and `hg`: the two ways of building a string
agree at equal places where their inputs agree at all places. No probability. -/
theorem Reading.at_same_of (W₁ : QueryLayout lam L₁) (W₂ : QueryLayout lam L₂)
    {m₁ : OracleCoding (spec lam W₁.K L₁) lam} {m₂ : OracleCoding (spec lam W₂.K L₂) lam} {u : L₁.Symbol ≃ L₂.Symbol}
    (h₁ : OneBlock m₁) (h₂ : OneBlock m₂) (R₁ : Reading L₁) (R₂ : Reading L₂)
    {keep₁ : ℕ → LeafIn L₁ → Option L₁.Symbol} {keep₂ : ℕ → LeafIn L₂ → Option L₂.Symbol}
    {g₁ : (ℕ → Option L₁.Symbol) → Fin L₁.wordLength → L₁.Symbol} {g₂ : (ℕ → Option L₂.Symbol) → Fin L₂.wordLength → L₂.Symbol}
    (B₁ : R₁.ByLeaves keep₁ g₁) (B₂ : R₂.ByLeaves keep₂ g₂)
    (h : SameRead (fun j q => (keep₁ j q).map u) keep₂ m₁ m₂) (σ : Trace (rom lam))
    (hσ : NoClash σ) (cm : Dig lam) (hd : W₁.depth = W₂.depth)
    (hg : ∀ (φ₁ : ℕ → Option L₁.Symbol) (φ₂ : ℕ → Option L₂.Symbol), (∀ j, (φ₁ j).map u = φ₂ j) →
      ∀ q₁ q₂, q₁.val = q₂.val → u (g₁ φ₁ q₁) = g₂ φ₂ q₂) :
    ∀ (q₁ : Fin L₁.wordLength) (q₂ : Fin L₂.wordLength), q₁.val = q₂.val →
      u (R₁.at W₁ (singleTr m₁ σ) cm q₁) = R₂.at W₂ (singleTr m₂ σ) cm q₂ := by
  intro q₁ q₂ hq
  show u (R₁.of _ q₁) = R₂.of _ q₂
  rw [B₁.of_eq, B₂.of_eq]
  refine hg _ _ (fun j => ?_) q₁ q₂ hq
  have e := extLeaf_sameRead h₁ h₂ h σ hσ W₁.depth j cm
  rw [← hd, ← e]
  cases Batch.extLeaf (singleTr m₁ σ) W₁.depth cm j <;> rfl

/-- **The strings that two readings leaf by leaf read under one root, through both implementations,
agree place by place.** `extEnc_same` for any two `keep`. Asked beside `OneBlock`, `SameRead` and
`NoClash`: the two wirings have one depth; and their fillings (`build`) agree where their inputs do.
No probability. -/
theorem at_same (W₁ : QueryLayout lam L₁) (W₂ : QueryLayout lam L₂) {m₁ : OracleCoding (spec lam W₁.K L₁) lam}
    {m₂ : OracleCoding (spec lam W₂.K L₂) lam} {u : L₁.Symbol ≃ L₂.Symbol} (h₁ : OneBlock m₁) (h₂ : OneBlock m₂)
    (b₁ : W₁.B.ext.OK) (b₂ : W₂.B.ext.OK) (keep₁ : ℕ → LeafIn L₁ → Option L₁.Symbol)
    (keep₂ : ℕ → LeafIn L₂ → Option L₂.Symbol)
    (h : SameRead (fun j q => (keep₁ j q).map u) keep₂ m₁ m₂) (σ : Trace (rom lam))
    (hσ : NoClash σ) (cm : Dig lam) (hd : W₁.depth = W₂.depth)
    (hb : ∀ (f₁ : Fin L₁.wordLength → Option L₁.Symbol) (f₂ : Fin L₂.wordLength → Option L₂.Symbol),
      (∀ q₁ q₂, q₁.val = q₂.val → (f₁ q₁).map u = f₂ q₂) →
      ∀ q₁ q₂, q₁.val = q₂.val → u (W₁.B.ext.build f₁ q₁) = W₂.B.ext.build f₂ q₂) :
    ∀ (q₁ : Fin L₁.wordLength) (q₂ : Fin L₂.wordLength), q₁.val = q₂.val →
      u ((Reading.byLeaf b₁ keep₁).at W₁ (singleTr m₁ σ) cm q₁) =
        (Reading.byLeaf b₂ keep₂).at W₂ (singleTr m₂ σ) cm q₂ :=
  Reading.at_same_of W₁ W₂ h₁ h₂ _ _ (Reading.byLeaf_byLeaves b₁ keep₁)
    (Reading.byLeaf_byLeaves b₂ keep₂) h σ hσ cm hd fun φ₁ φ₂ hφ =>
      hb _ _ fun p₁ p₂ hp => by rw [hφ p₁.val, hp]

/-! ## At two descriptions of chains that open stored tables -/

section
open _root_.Run _root_.Run.PQ
open OnBytes.Tie (StmInv theImplX pageX)

variable (D₁ D₂ : XD) (dec₁ dec₂ : View → Bool)

/-- The external part of Batch's wiring in `WkAny` obeys the library's three laws. -/
theorem ext_ok_any (D : XD) (dec : View → Bool) : (WkAny D dec).B.ext.OK :=
  WireE.one_ok _ _ _

/-- **At the wirings of two descriptions the two ways of building a string from symbols agree where
their inputs do**, with the identity as the match of symbols: both put the symbol (0, []) where
there is none. No condition on the descriptions. -/
theorem build_same_any (f₁ : Fin (D₁.L dec₁).wordLength → Option SgX) (f₂ : Fin (D₂.L dec₂).wordLength → Option SgX)
    (h : ∀ q₁ q₂, q₁.val = q₂.val → (f₁ q₁).map (Equiv.refl SgX) = f₂ q₂)
    (q₁ : Fin (D₁.L dec₁).wordLength) (q₂ : Fin (D₂.L dec₂).wordLength) (hq : q₁.val = q₂.val) :
    Equiv.refl SgX ((WkAny D₁ dec₁).B.ext.build f₁ q₁) = (WkAny D₂ dec₂).B.ext.build f₂ q₂ := by
  show (f₁ q₁).getD (0, []) = (f₂ q₂).getD (0, [])
  rw [← h q₁ q₂ hq]
  cases f₁ q₁ <;> rfl

variable (hcfg₁ : D₁.base.cfg.size = 32) (hcfg₂ : D₂.base.cfg.size = 32) (V₁ : StmInv D₁)
  (V₂ : StmInv D₂)

/-- **The strings under one root, through the encodings of two descriptions, agree place by place.**
`extEnc_same` at two descriptions. Left beside what the encodings themselves ask (a configuration
digest of 32 bytes; a reader for the statement, `StmInv`): three hypotheses on the descriptions, one
configuration digest, one salt length, one depth of stored trees; and that no two strings of the log
have one answer. Decisions, rounds, statements and numbers of blocks may differ. No probability. -/
theorem extEnc_same_any (hc : D₁.base.cfg = D₂.base.cfg)
    (hs : D₁.base.plan.salt = D₂.base.plan.salt) (ha : D₁.a = D₂.a) (σ : Trace (rom 256))
    (hσ : NoClash σ) (cm : Dig 256) (q₁ : Fin (D₁.L dec₁).wordLength) (q₂ : Fin (D₂.L dec₂).wordLength)
    (hq : q₁.val = q₂.val) :
    extEnc (WkAny D₁ dec₁) (singleTr (theImplX (pageX dec₁ (D₁.K + 1) hcfg₁ V₁)) σ) cm q₁ =
      extEnc (WkAny D₂ dec₂) (singleTr (theImplX (pageX dec₂ (D₂.K + 1) hcfg₂ V₂)) σ) cm q₂ :=
  extEnc_same (WkAny D₁ dec₁) (WkAny D₂ dec₂) (u := Equiv.refl SgX) (oneBlock_implX _)
    (oneBlock_implX _) (sameStored_pageX D₁ D₂ dec₁ dec₂ _ _ hcfg₁ hcfg₂ V₁ V₂ hc hs ha) σ hσ cm ha
    (build_same_any D₁ D₂ dec₁ dec₂) q₁ q₂ hq

/-- **The same for two readings leaf by leaf.** `at_same` at the wirings and encodings of two
descriptions with one depth of stored trees. `SameRead` at the two `keep` stays a hypothesis:
nothing here says that it holds at a `keep` other than `keepAll`. No probability. -/
theorem at_same_any (ha : D₁.a = D₂.a) (keep₁ : ℕ → LeafIn (D₁.L dec₁) → Option SgX)
    (keep₂ : ℕ → LeafIn (D₂.L dec₂) → Option SgX)
    (h : SameRead (fun j q => (keep₁ j q).map (Equiv.refl SgX)) keep₂
      (theImplX (pageX dec₁ (D₁.K + 1) hcfg₁ V₁)) (theImplX (pageX dec₂ (D₂.K + 1) hcfg₂ V₂)))
    (σ : Trace (rom 256)) (hσ : NoClash σ) (cm : Dig 256) (q₁ : Fin (D₁.L dec₁).wordLength)
    (q₂ : Fin (D₂.L dec₂).wordLength) (hq : q₁.val = q₂.val) :
    (Reading.byLeaf (ext_ok_any D₁ dec₁) keep₁).at (WkAny D₁ dec₁)
        (singleTr (theImplX (pageX dec₁ (D₁.K + 1) hcfg₁ V₁)) σ) cm q₁ =
      (Reading.byLeaf (ext_ok_any D₂ dec₂) keep₂).at (WkAny D₂ dec₂)
        (singleTr (theImplX (pageX dec₂ (D₂.K + 1) hcfg₂ V₂)) σ) cm q₂ :=
  at_same (WkAny D₁ dec₁) (WkAny D₂ dec₂) (u := Equiv.refl SgX) (oneBlock_implX _)
    (oneBlock_implX _) (ext_ok_any D₁ dec₁) (ext_ok_any D₂ dec₂) keep₁ keep₂ h σ hσ cm ha
    (build_same_any D₁ D₂ dec₁ dec₂) q₁ q₂ hq

end

end OnBytes.Slice
