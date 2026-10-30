-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/CarryK2.lean: the code switch: «carry», THE ITEM OF THE TABLE OF
JOINTS THAT THE SWITCH CLOSES, AS ONE SENTENCE ON A RECORD AND THE ORACLES, WITH ITS READERS MADE.

K2Hands/CarryOf.lean has the sentence over two letters: a reading fa of (record, oracles) into the
typed statement and strings in front of the switch, and a reading rest of the witness. Here both are
terms, at the typed record r of a place and the plain letters (Member.lean's Letters.plain).
  plainD       the typed data of the fold in front, at the plain letters
  plainR       the group's data in front, with its kept slots (LawAt.lean's selR there)
  memK, rowK, plK  a typed kept slot's member BY ITS PLACE IN r.kept, its row, and that member's
               record in the frame
  plain_none   at the plain letters no old message stays open beside the held ones
  faAt         THE READING, at a front fx and its frame W₀: the claim's target: the carried rows'
               target, read · its vector: ClaimJoin.lean's vecOf · the held samples: smp (A LETTER)
               · the open word's string: StrMade.lean's wordOf of what the front reads off the
               oracles (LongOne.lean's longFront), at the frame's own numbering coordOf
  carryRow     THE SENTENCE AT A TYPED RECORD: the text makes a front of the record, the front has a
               frame, and carryOf holds there
  carryK2      THE ITEM: at segment m: through the way in of the place's seated block (door m), at
               the typed record rowAt m, where that record passes its test; FALSE where the segment
               has no record or the record fails the test
WHAT IS STILL A LETTER: FOUR, EACH A FUNCTION OF THE PLAN: rowAt (the typed record at a segment) ·
pAt (the place's numbers) · door (the way in) · orc (the oracles read by key and position) ; AND ONE
THAT READS THE RECORD: smp (the held samples: a typed sample holds the SEED, which is no field of
the record: it is to be read back off the stored sample rows). IT READS NOTHING OF THE WITNESS: at
the plain letters the stage's witness is the open word's pair alone, and that stands under the
«there is». BY READING, NOT SHOWN: it speaks of the witness through the item pinKept beside it: each
held slot of the open word decodes to its part of the pair's message.
LIMITS. A definition and its unfolding: no law. Whether the sentence can be met is not shown. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.Member
import Johnson.Top.H0.K2Hands.CarryOf
import Johnson.Top.H0.K2Hands.StrMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands

section
variable (r : SwRow) (H : r.OK)

/-- The typed data of the fold in front, at the plain letters. -/
noncomputable abbrev plainD : LdFoldD GE (Letters.plain r H).Kc :=
  (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ
    (Letters.plain r H).kq).foldD (Letters.plain r H).Sb (Letters.plain r H).sl
      (Letters.plain r H).Z (Letters.plain r H).A₀

/-- The group's data in front, with its kept slots. -/
noncomputable abbrev plainR : RowsK (sigOf r.cs r.lo) :=
  (rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep r.kp

variable {r H}

/-- A typed kept slot's member, by its place in r.kept. -/
def memK (κ : (plainR r H).Kp) : ℕ := r.kept.idxOf κ.1.1.1.val
/-- Its row. -/
def rowK (κ : (plainR r H).Kp) : ℕ := κ.2.val
/-- That member's record in the frame. -/
def plK (W₀ : SwitchFrame) (κ : (plainR r H).Kp) : KeptPlace :=
  W₀.kept.getD (memK κ) ⟨0, 0, 0, 0, [], 0⟩

variable (r H)

/-- At the plain letters no old message stays open beside the held ones. -/
theorem plain_none : IsEmpty (vecD (plainD r H)).S₂.O :=
  ⟨fun i => i.2 ⟨by
    have h := H.kept i.1.1.val i.1.2
    rw [List.getElem?_eq_getElem i.1.1.isLt] at h
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1, i.1.2⟩⟩

variable {Y : Type} (p : K2.P2) (orc : Y → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)

/-- **The reading of a record and the oracles**, at a front and its frame. -/
noncomputable def faAt (a : VerifiableInference.Desc.First.S × _root_.Tw.K2.Front × SwitchFrame)
    (y : Y) : (vecD (plainD r H)).tgt.X × (vecD (plainD r H)).tgt.Ex.Str :=
  (((((readE a.2.1.f.rows.target,
        vecOf (plainR r H).s (plainR r H).Kp a.2.1.f.rows rowK (plK a.2.2)), smp a.2.1 a.2.2), ()),
      fun i => ((plain_none r H).false i).elim),
    ((wordOf (plainR r H).s (plainR r H).Kp fun q α =>
        readE (((K2.longFront p a.1 a.2.1 (orc y) q.val).getD #[]).getD
          (coordOf (plainR r H).s (plainR r H).Kp a.2.2 a.2.1.f.rows memK rowK α) OnBytes.zeroE),
      ()), fun i => ((plain_none r H).false i).elim))

/-- **The sentence at a typed record.** -/
def carryRow (t : VerifiableInference.Desc.First.S) (y : Y) : Prop :=
  ∃ fx W₀, K2.frontAt p t = some fx ∧ K2.frameAt fx = some W₀ ∧
    carryOf (W := Unit) (vecD (plainD r H)) (faAt r H p orc smp)
      (fun _ _ _ => (fun i => ((plain_none r H).false i).elim, ())) (t, fx, W₀) y ()

end

/-- **«carry».** -/
def carryK2 {P Y W : Type} (rowAt : ℕ → Option SwRow) (pAt : ℕ → K2.P2)
    (door : ℕ → VerifiableInference.Desc.First.S → Option VerifiableInference.Desc.First.S)
    (orc : Y → ℕ → ℕ → List UInt64)
    (smp : ∀ (r : SwRow) (H : r.OK), _root_.Tw.K2.Front → SwitchFrame →
      (vecD (plainD r H)).held.Smp) :
    ℕ → P × VerifiableInference.Desc.First.S → Y → W → Prop := fun m a y _ =>
  match rowAt m, door m a.2 with
  | some r, some t =>
    ∃ h : r.ok = true, carryRow r (r.ok_says h) (pAt m) orc (smp r (r.ok_says h)) t y
  | _, _ => False

end VerifiableInference.Desc.First.K2Caller
