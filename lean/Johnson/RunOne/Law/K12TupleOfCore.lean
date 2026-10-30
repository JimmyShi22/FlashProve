-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12TupleOfCore.lean: The key file's tables, the rows that
a proximity test closes on the shared chain (2.9 · 2.10): FROM THE TEST's TUPLE OF TYPED MESSAGES TO
THE TUPLE OF TABLES THAT THE ROW's «law» LAYS, at Johnson/RunOne/KeyFillSeed.lean's filling (baseK
at the six). Definitions, statements and proofs; each proof is a few calls.
The seam's core behind the game's relations (`core_behind_QW` | `core_behind_QWO`,
Johnson/Desc/K12/Coin/CoreBehindQ.lean) hands μ : a typed message a member, with «all rows taken in
hold of μ's words» and «μ x is a candidate at every member x that sits». The tables' side
(`law_29`, K12Law29.lean; its like at 2.10) takes tbl : a table a message number, with «tbl k is a
member of its committed word's list and meets its out-of-domain (OOD) sample» and «the words are
tbl's».
  `tblOf μ`: message number k ↦ ofU … (μ ⟨sixS, k⟩).
  `member_of_core₂`: the candidate is a member (`cand_laid_of_candAt₂`, CandBridge.lean), in the
  form
    that the engine's `pin_laid` | `ride_is` take.
  `words_of_core`: μ's words at a statement's message number whose member is ⟨sixS, i⟩ are tblOf μ
  i's
    table, read in the field.
What it is not. hB3 («the laid table ofU … u IS the typed message's own table tabP … u») is A NAMED
PREMISE: it is left to other files to type. hlog · told · the sample's tie hsm
· «every leaf is shown» are premises, as in the bridge. It pays no field of the tables. No soundness
is claimed. Nothing on hiding.

-/
import Johnson.Top.Fire.Code.CandBridge
import Johnson.Desc.K14.Law.LedgerSay
import Johnson.Desc.K12.Law.TupleWords
import Johnson.Desc.Key.KeyNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12TupleOfCore
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open LPFD.CandLaid
open H2K.Pin (tabP)

/-- The tuple of tables: message number k ↦ the table of the typed message at the six's member k. -/
def tblOf (μ : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg) (k : ℕ) : Fill.Tab :=
  if h : k < six.length then
    ofU csKey (six.get ⟨k, h⟩).1 (six.get ⟨k, h⟩).2 (μ ⟨sixS, ⟨k, h⟩⟩)
  else fun _ _ => 0

theorem tblOf_at (μ : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg) (i : Fin six.length) :
    tblOf μ i.val = ofU csKey (six.get i).1 (six.get i).2 (μ ⟨sixS, i⟩) := by
  unfold tblOf
  rw [dif_pos i.isLt]
  rfl

section
variable {XI Cells Rec : Type} (F : FileDescription XI)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F)

include tab in
/-- **The candidate is a member**, in the form that the engine takes. -/
theorem member_of_core₂
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (μ : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg) (i : Fin six.length)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      o.logLength = aOf csKey (six.get i).1)
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true) (a : P₂ × St₂) (y : Strs)
    (hs : hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂
      (atSix i.val).1 (atSix i.val).2 a = true)
    (hsm : ∀ σ : (OmAt csKey six i).Smp, smp a sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D, (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i a ρ σ.2)
    (hsh : Sound.ShownAt F csKey six (seatAt six numSix atSix) y i)
    (hc : Sound.CandAt csKey F smp ⟨sixS, i⟩ a y (μ ⟨sixS, i⟩)) :
    ∃ o z, F.oracleAt (atSix i.val).1 = some o ∧
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp a (atSix i.val).1
        (atSix i.val).2 = some z ∧
      Member F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ o
        (atSix i.val).1 (atSix i.val).2 y z (tblOf μ i.val) := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 told
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hs
  rw [tblOf_at]
  exact ⟨o, z, ho, hz, (cand_laid_of_candAt₂ F (fun y : Strs => y) decT recOf orc₁ tab smp i hlog
    told a y o z (μ ⟨sixS, i⟩) ho hz hsm hsh hc).1⟩

/-- **μ's words are the tuple of tables', read in the field.** -/
theorem words_of_core (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (hB3 : ∀ (i : Fin six.length) (u : (OmAt csKey six i).Msg),
      ofU csKey (six.get i).1 (six.get i).2 u = tabP csKey (six.get i).1 u)
    (μ : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg) (o : ℕ) (i : Fin six.length)
    (hmem : mem o = some ⟨sixS, i⟩) :
    _root_.Desc.K14.Law.wordsT csKey mem rd μ o =
      entOf OnBytes.Model.Reading.gl (kreadFam (Cells := Cells) csKey six numSix atSix tab)
        (tblOf μ i.val) := by
  funext part k
  show (match mem o with
    | some x => rd x (μ x) part k
    | none => 0) = KeyRows23.readE ((kreadFam (Cells := Cells) csKey six numSix atSix tab).val
      (tblOf μ i.val) part k)
  rw [hmem, read_val, tblOf_at, hB3 i]
  exact hrd _ _ _ _

end

end Johnson.RunOne.Law.K12TupleOfCore

#print axioms Johnson.RunOne.Law.K12TupleOfCore.tblOf_at
#print axioms Johnson.RunOne.Law.K12TupleOfCore.member_of_core₂
#print axioms Johnson.RunOne.Law.K12TupleOfCore.words_of_core
