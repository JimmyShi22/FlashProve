-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSay.lean: WHAT THE TWO PROXIMITY TESTS' CLAUSES ASK OF THE ROWS' MEANING,
AT THE LEDGER's FILLING. The rule of a proximity test at the ledger (clause_of_test,
Johnson/Desc/Sound/SharedJointCountTests.lean) speaks of a letter Say: what a class
of rows says of a TUPLE of typed messages, one for each member; it asks hrow (Say at the witness's
own messages gives the item) and hcong (Say reads the laid and the kept messages alone). HERE Say IS
FILLED at mgI's rows (Johnson/Desc/K14/Law/LedgerOne.lean), hrow is by make, and hcong is proved AT
A RECORD WHOSE STATEMENT IS IN ORDER and whose group has the laid and the kept messages for its
members.

  wordsT, rgOf_wordsT   the words built of a tuple by the plan's mem and the reader rd; the table's
                  fixed reader rgOf is that at the witness's own messages, by rfl.
  rowW, SayK      mgI's rows as a function of the words; **the filling of Say**.
  say_row         **hrow**: by make, where the samples' rows are filled by SmpSay.
  allSay_agree, smpSay_agree   rows of a group's list | a message's sample rows, said at a statement
                  that has grown out of one in order, read the group's members' | that message's
                  words alone: by says_agree (Johnson/Desc/Means/ItemsRead.lean), RowIn.extends and
                  extends_of_grows.
  cong_nine, cong_ten   **hcong** at the classes that the test on G_u | on G_omega closes.
WHY NOT AT EVERY RECORD. mgI's rows are "the rows as they lie in the record say their claims", and a
row's claim is a sum over all messages of the statement: at an arbitrary record a row of G_u's list
may name any number. So hcong asked bare, at every record, is FALSE at this filling. It holds inside
a promise that says: the statement is in order (Means.InOrder; as a test with code: inOrderB) and
the group's members are the laid and the kept messages' numbers (membX 9 | 10).
The rule's premises are to be asked so: otherwise
nine_paid | ten_paid cannot be called at mgI.
WHAT STAYS. hI (the statement is in order) and hG, hM (the group's members): had from two tests
beside shapeK in cong_nine_at | cong_ten_at (Johnson/Desc/K14/Law/LedgerTidy.lean) · the plan's mem
at the members' numbers, in ms, at the tenants' seats · num.
What is not claimed. No member. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerOne
import Johnson.Desc.Means.ItemsRead
import Johnson.Desc.Means.GrowsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open OnBytes.Means (Words InOrder RowIn RowOn says_agree extends_of_grows)
open VerifiableInference.Desc (Wit Grows)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

variable {P₁ Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem)
  (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)

/-- The words built of a tuple of typed messages. -/
def wordsT (m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) : Words GE := fun o part i =>
  match mem o with
  | some x => rd x (m x) part i
  | none => 0

/-- The table's fixed reader is that at the witness's own messages. -/
theorem rgOf_wordsT (w : Wit Cells Tok MsgT) : rgOf cs arr mem rd w =
    wordsT cs mem rd fun x => msgsOf cs x.1.l x.1.seat arr w x.2 := rfl

/-- Two tuples that are one at the member at a number give the same words there. -/
theorem wordsT_same (m m' : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) (o : ℕ) (x : Mem)
    (hm : mem o = some x) (h : m' x = m x) (part : Part) (i : ℕ) :
    wordsT cs mem rd m o part i = wordsT cs mem rd m' o part i := by
  unfold wordsT
  rw [hm]
  show rd x (m x) part i = rd x (m' x) part i
  rw [h]

/-- mgI's rows, as a function of the words. -/
def rowW (P : Par) (n : ℕ) (num : Msg2 → ℕ) : RowS → St → Words GE → Prop
  | .recG, s, W => RowsUL OnBytes.Model.Reading.gl 0 P.S.fold.index.answers s W
  | .loc, s, W => RowsUL OnBytes.Model.Reading.gl P.S.fold.index.answers n s W
  | .fold, s, W => FoldAt OnBytes.Model.Reading.gl P.S s W
  | .foldU, s, W => RowsU OnBytes.Model.Reading.gl (P.S.fold.index.answers + n) 1 s W
  | .foldOmega, s, W => RowsO OnBytes.Model.Reading.gl 0 1 s W
  | .sample μ, s, W => SmpSay (num μ) s W

/-- **The filling of Say.** -/
def SayK (P : Par) (n : ℕ) (num : Msg2 → ℕ) (s : St) (q : RowS)
    (m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) : Prop :=
  rowW P n num q s (wordsT cs mem rd m)

/-- **hrow**: by make. -/
theorem say_row (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (P : Par) (uR : St → St)
    (omW : Wit Cells Tok MsgT → ℕ → GE) (e' n : ℕ) (num : Msg2 → ℕ)
    (hsmp : ∀ μ s w, SmpSay (num μ) s (rgOf cs arr mem rd w) → Mg₀.row (.sample μ) s w)
    (q : RowS) (s : St) (w : Wit Cells Tok MsgT)
    (h : SayK cs mem rd P n num s q fun x => msgsOf cs x.1.l x.1.seat arr w x.2) :
    (mgI cs arr Mg₀ mem rd P uR omW e' n).row q s w := by
  cases q with
  | sample μ => exact hsmp μ s w h
  | recG => exact h
  | loc => exact h
  | fold => exact h
  | foldU => exact h
  | foldOmega => exact h

/-- Rows of a group's list, said at a statement that has grown out of one in order, read the
group's members' words alone. -/
theorem allSay_agree (S T : Statement) (hI : InOrder S) (gr : Grows S T) (g : ℕ) (G : Group)
    (hG : S.groups[g]? = some G) (l : List Row) (hl : ∀ r ∈ l, r ∈ G.rows.toList)
    (m m' : Words GE) (h : ∀ o ∈ G.members.toList, ∀ part i, m o part i = m' o part i)
    (hs : Means.AllSay OnBytes.Model.Reading.gl T l m) :
    Means.AllSay OnBytes.Model.Reading.gl T l m' := fun r hr =>
  (says_agree OnBytes.Model.Reading.gl
    (RowIn.extends (extends_of_grows gr) (fun _ c => c) (hI.rows g G hG r (hl r hr))) h).1 (hs r hr)

/-- A message's sample rows read that message's words alone. -/
theorem smpSay_agree (o : ℕ) (s : St) (hI : InOrder s.st) (m m' : Words GE)
    (h : ∀ part i, m o part i = m' o part i) (hs : SmpSay o s m) : SmpSay o s m' := by
  obtain ⟨x, T, hx, gr, ha⟩ := hs
  refine ⟨x, T, hx, gr, fun r hr => (says_agree OnBytes.Model.Reading.gl
    (RowIn.extends (extends_of_grows gr) (fun _ c => c) (hI.samples o x hx r hr))
    fun o' ho' part i => ?_).1 (ha r hr)⟩
  have e : o' = o := by simpa using ho'
  rw [e]
  exact h part i

/-- A slice of the list of a group that is there lies in the group's rows. -/
theorem slice_in (s : St) (g : ℕ) (G : Group) (hG : s.st.groups[g]? = some G) (i n : ℕ) :
    ∀ r ∈ ((rowsOn s g).drop i).take n, r ∈ G.rows.toList := fun r hr => by
  have h := List.mem_of_mem_drop (List.mem_of_mem_take hr)
  unfold rowsOn at h
  rw [hG] at h
  exact h

variable (ms : List Mem) (N : NumbersS) (P : Par) (n : ℕ) (num : Msg2 → ℕ)

/-- **hcong at the classes that the test on G_u closes**: at a record whose statement is in order
and whose G_u has o_u and o_sp for its members. -/
theorem cong_nine (s : St) (hI : InOrder s.st) (G : Group) (nU nS : ℕ)
    (hG : s.st.groups[s.loc.gU]? = some G) (hM : G.members = #[nU, nS]) (hnum : num .oU = nU)
    (xU xS : Mem) (hU : mem nU = some xU) (hSp : mem nS = some xS) (mU : xU ∈ ms) (mS : xS ∈ ms)
    (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
    (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
    (m m' : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg)
    (hsame : ∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oSp] →
      ∀ x ∈ ms, SitsAt x (N.tenant μ).1 (N.tenant μ).2 → m' x = m x)
    (q : RowS) (hq : q ∈ [RowS.sample .oU, .recG, .loc, .foldU])
    (h : SayK cs mem rd P n num s q m) : SayK cs mem rd P n num s q m' := by
  have aU := wordsT_same cs mem rd m m' nU xU hU (hsame .oU (Or.inl rfl) xU mU sU)
  have aS := wordsT_same cs mem rd m m' nS xS hSp (hsame .oSp (Or.inr (by simp)) xS mS sS)
  have hA : ∀ o ∈ G.members.toList, ∀ part i,
      wordsT cs mem rd m o part i = wordsT cs mem rd m' o part i := by
    intro o ho
    rw [hM] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact aU
    · exact aS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact smpSay_agree _ s hI _ _ (by rw [hnum]; exact aU) h
  · obtain ⟨T, gr, ha⟩ := h
    exact ⟨T, gr, allSay_agree s.st T hI gr _ G hG _ (slice_in s _ G hG _ _) _ _ hA ha⟩
  · obtain ⟨T, gr, ha⟩ := h
    exact ⟨T, gr, allSay_agree s.st T hI gr _ G hG _ (slice_in s _ G hG _ _) _ _ hA ha⟩
  · exact allSay_agree s.st s.st hI (Grows.refl _) _ G hG _ (slice_in s _ G hG _ _) _ _ hA h

/-- **hcong at the classes that the test on G_omega closes.** -/
theorem cong_ten (s : St) (hI : InOrder s.st) (G : Group) (nO nS : ℕ)
    (hG : s.st.groups[s.loc.gOmega]? = some G) (hM : G.members = #[nO, nS])
    (hnO : num .oOmega = nO) (hnS : num .oSp = nS)
    (xO xS : Mem) (hO : mem nO = some xO) (hSp : mem nS = some xS) (mO : xO ∈ ms) (mS : xS ∈ ms)
    (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
    (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
    (m m' : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg)
    (hsame : ∀ μ, μ = Msg2.oSp ∨ μ ∈ [Msg2.oOmega] →
      ∀ x ∈ ms, SitsAt x (N.tenant μ).1 (N.tenant μ).2 → m' x = m x)
    (q : RowS) (hq : q ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega])
    (h : SayK cs mem rd P n num s q m) : SayK cs mem rd P n num s q m' := by
  have aO := wordsT_same cs mem rd m m' nO xO hO (hsame .oOmega (Or.inr (by simp)) xO mO sO)
  have aS := wordsT_same cs mem rd m m' nS xS hSp (hsame .oSp (Or.inl rfl) xS mS sS)
  have hA : ∀ o ∈ G.members.toList, ∀ part i,
      wordsT cs mem rd m o part i = wordsT cs mem rd m' o part i := by
    intro o ho
    rw [hM] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact aO
    · exact aS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact smpSay_agree _ s hI _ _ (by rw [hnO]; exact aO) h
  · exact smpSay_agree _ s hI _ _ (by rw [hnS]; exact aS) h
  · exact allSay_agree s.st s.st hI (Grows.refl _) _ G hG _ (slice_in s _ G hG _ _) _ _ hA h

end Desc.K14.Law
