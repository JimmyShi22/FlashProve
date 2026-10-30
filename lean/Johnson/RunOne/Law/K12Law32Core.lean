-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Law32Core.lean: The key
file's tables, row 3.2 (the proximity test on the last chain's own group; border 2 of that chain):
THE «law» OF ITS WAY BACK (the premise of that name of `relAt_back_to`, KeyQuietSub.lean), FROM THE
TEST's OWN LAW: at the tables' files' filling (baseK at the six; at_ := atSix; the reader kreadFam).
The like of `law_29_coreF` (K12Law29Core.lean). Statements; each proof is calls.
The row (Johnson/Desc/Key/KeyBorders23.lean): ins := [claim 1 "Eval", claim 3 "Dot", srow 0, srow 2,
srow 4, pin 0, pin 2, pin 4] · outs := [] · ctx := [] · lays := [0, 2, 4] (0: I · 2: V · 4: Omega).
WHAT PARTS IT FROM ROWS 2.9 | 2.10: ALL THREE MEMBERS OF THE GROUP ARE LAID, NONE RIDES: so the law
holds at EVERY witness behind; nothing is asked of what stays across the test. The plan's numbers are
plan₃ K₁ (nOwn …): K₁ is a free letter: its values at I and V are premises.
  `shape32_facts` · `msgIs_facts` · `grpIs_facts`: what the book-keeping's Bool at border 2 says.
  `seats_024`: the three seats' trees are 0 · 5 · 7.
  `member_of_core₃`: the candidate is a member (`cand_laid_of_candAt₃`, CandBridge.lean), in the form
    that the engine's `pin_laid` takes.
  `srow₃_none` · `items_32`: what the row's eight closed items say, unfolded: the own group's two open
    rows and the rows of the three messages' out-of-domain (OOD) samples («sample rows») hold at the
    witness, and the three are PINned.
  `law_32_coreF`: the game's relation `QW` AT ANY NUMBERING BY LABELS nl (meant: nlKW t₁,
    Johnson/Desc/K12/Coin/LabelsAtKeyW.lean) · johOk · planOk · the border's promise on₃ … 2 x ·
    `CoreLeft` at no := nuOf π nl t, ASKED ONLY WHERE THE TEST's OWN DECISION ACCEPTS (so that its
    payer can spend that accept) · the bridge's four at the three members · LayIdem · five facts
    on K₁ and idx · which member sits at which message number · OpenKinds · I's message is sampled
    and has sample rows ⊢ THERE IS A TUPLE OF TABLES tbl SUCH THAT FOR EVERY ROW WITH THESE ins AND
    EVERY WITNESS w: the eight items hold in front, at the witness with 0, 2 and 4 laid.
BESIDE THEM: `law_32_of_core` (from the seam's core's conclusion to the «law») ·
`law_32_coreM` («left» member by member: `MemberLeft`, by `core_behind_QWm`).
ALSO: `law_32_coreM₂`: over the parted remainder `MemberLeft₂`, by `core_behind_QWm₂`.
What it is not. NO EXAMPLE: that the premises of `law_32_coreF` can hold together, at the release's own
values or at any, is shown nowhere: until then the statement may be empty. PREMISES, EACH NAMED, NONE
PAID HERE. THE HARD ONE IS `CoreLeft`: its last clause
(the members' words at no := nuOf π nl t) says: «nl of the label that the book's tree at the member's
place bears is the seat's tree over the file»: that nothing is asked of the book HERE does not mean
that this debt is gone: it has moved there. It pays no field of the tables. No soundness is claimed.
Nothing on hiding.

-/
import Johnson.RunOne.Law.K12LawLay
import Johnson.RunOne.Law.K12TupleOfCore
import Johnson.RunOne.Law.KeyRide23
import Johnson.Desc.K12.Coin.CoreBehindQ
import Johnson.Desc.K12.Coin.MemberAtYes
import Johnson.RunOne.Law.GrowsOfAllSay
import Johnson.RunOne.Law.K12Hval

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Law32Core
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf)
open Cb Johnson.Pack OnBytes.Maker
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.KeyRide23 (ins32)
open LPFD.CandLaid
open H2K.Pin (tabP)
open H2K.Pub (johOk)
open Johnson.RunOne.Law.K12TupleOfCore

/-! ## 1 The book-keeping at border 2 -/

/-- What the last chain's book-keeping at border 2 says of the verifier's state in front of the own
test. -/
theorem shape32_facts (S : LinShape) (a : Nat) (idx : List Nat)
    (s : VerifiableInference.Desc.Third.S₃)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a (s.loc.w + 2) (s.loc.own + 1)
      (s.loc.firstTree - 1) idx 2 s) = true) :
    s.loc.border = none ∧ s.loc.omega = s.loc.w + 2 ∧ s.loc.mask = some (s.loc.w + 1) ∧
      LKFU.Shape23.msgIs s.st s.loc.w (some a) false = true ∧
      LKFU.Shape23.msgIs s.st (s.loc.w + 2) (some a) false = true ∧
      LKFU.Shape23.grpIs s.st s.loc.own (idx ++ [s.loc.w, s.loc.w + 2]) 2 0 false = true := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₃, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨_, _, _, _, _, c6, _, c8, c9, c10, c11, c12, _⟩ := h
  simp at c6 c8 c9 c10 c11 c12
  exact ⟨c8, c9, c6, c10.1, c11, c12⟩

/-- A message that the book-keeping calls sampled with n sample rows. -/
theorem msgIs_facts (st : Statement) (o n : Nat)
    (h : LKFU.Shape23.msgIs st o (some n) false = true) :
    ∃ x, st.oracles[o]? = some x ∧ x.sampled = true ∧ x.sampleRows.size = n := by
  unfold LKFU.Shape23.msgIs at h
  cases hx : st.oracles[o]? with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨x, rfl, h.1.1, h.1.2⟩

/-- A group as the book-keeping describes it. -/
theorem grpIs_facts (st : Statement) (g : Nat) (ms : List Nat) (p q : Nat) (r : Bool)
    (h : LKFU.Shape23.grpIs st g ms p q r = true) :
    ∃ G0, st.groups[g]? = some G0 ∧ G0.members.toList = ms ∧ G0.rows.size = p + q := by
  unfold LKFU.Shape23.grpIs at h
  cases hG : st.groups[g]? with
  | none => rw [hG] at h; cases h
  | some G0 =>
    rw [hG] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨G0, rfl, h.1.1.1.1, h.1.2⟩

/-- The three seats' trees, over the file. -/
theorem seats_024 : (atSix 0).1 = 0 ∧ (atSix 2).1 = 5 ∧ (atSix 4).1 = 7 := ⟨rfl, rfl, rfl⟩

/-- The six's members at the messages 0 (I), 2 (V) and 4 (Omega). -/
def i0 : Fin six.length := ⟨0, by decide⟩
def i2 : Fin six.length := ⟨2, by decide⟩
def i4 : Fin six.length := ⟨4, by decide⟩

theorem apart_024 : SeatsApart atSix [0, 2, 4] [0, 2, 4] := by
  intro k hk k' hk' e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk hk'
  rcases hk with rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl <;>
    first | rfl | exact absurd e (by decide)

/-! ## 2 The candidate is a member -/

section
variable {XI Cells Rec : Type} (F : FileDescription XI)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F)

include tab in
/-- **The candidate is a member**, at the last chain's reading. -/
theorem member_of_core₃
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (μ : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg) (i : Fin six.length)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      o.logLength = aOf csKey (six.get i).1)
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true) (a : P₃ × St₃) (y : Strs)
    (hs : hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃
      (atSix i.val).1 (atSix i.val).2 a = true)
    (hsm : ∀ σ : (OmAt csKey six i).Smp, smp a sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D, (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i a ρ σ.2)
    (hsh : Sound.ShownAt F csKey six (seatAt six numSix atSix) y i)
    (hc : Sound.CandAt csKey F smp ⟨sixS, i⟩ a y (μ ⟨sixS, i⟩)) :
    ∃ o z, F.oracleAt (atSix i.val).1 = some o ∧
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃.smp a (atSix i.val).1
        (atSix i.val).2 = some z ∧
      Member F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ o
        (atSix i.val).1 (atSix i.val).2 y z (tblOf μ i.val) := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 told
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hs
  rw [tblOf_at]
  exact ⟨o, z, ho, hz, (cand_laid_of_candAt₃ F (fun y : Strs => y) decT recOf orc₁ tab smp i hlog
    told a y o z (μ ⟨sixS, i⟩) ho hz hsm hsh hc).1⟩

end

/-! ## 3 What the row's items say -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI)
  (G₃ : VerifiableInference.Desc.Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where) (S : LinShape)
  (K₁ : KPlan) (R : KRead Cells M)

/-- Behind the chain's first sub-protocol (the border is taken) the rows of a message's OOD sample are
read in the chain's own statement. -/
theorem srow₃_none (k : Nat) (a : P₃ × St₃) (y : Strs) (w : Wit Cells Unit M)
    (hb : a.2.loc.border = none) :
    (meaning₃ S K₁ R).srow k a y w = srowAt R (plan₃ K₁ (nOwn a.2)) a.2.st k w := by
  simp only [meaning₃, hb]

/-- **What the row's eight closed items say.** -/
theorem items_32 (a : P₃ × St₃) (y : Strs) (w' : Wit Cells Unit M) (G0 : OnBytes.Group) (oI : ℕ)
    (xI xV xO : OnBytes.Oracle) (hb : a.2.loc.border = none)
    (hG : a.2.st.groups[a.2.loc.own]? = some G0) (hc : 2 ≤ G0.rows.size)
    (hoI : K₁.orc 0 = some oI) (hoV : K₁.orc 2 = some a.2.loc.w)
    (hxI : a.2.st.oracles[oI]? = some xI) (hxV : a.2.st.oracles[a.2.loc.w]? = some xV)
    (hxO : a.2.st.oracles[nOwn a.2]? = some xO)
    (hs : ∀ x ∈ [xI, xV, xO], x.sampled = true ∧ x.sampleRows.size ≠ 0)
    (hrows : ∀ r ∈ G0.rows.toList,
      RowHolds R.same a.2.st (valOf (plan₃ K₁ (nOwn a.2)) R w') r)
    (hsr : ∀ x ∈ [xI, xV, xO], ∀ r ∈ x.sampleRows.toList,
      RowHolds R.same a.2.st (valOf (plan₃ K₁ (nOwn a.2)) R w') r)
    (hpin : ∀ k ∈ [0, 2, 4], PIN F G₃ (at_ k).1 (at_ k).2 a y w') :
    ∀ i ∈ ins32, i.holds F G₃ at_ (meaning₃ S K₁ R) a y w' := by
  have run : ∀ lo n, lo + n ≤ G0.rows.size → n ≠ 0 →
      rowsHold R.same a.2.st (valOf (plan₃ K₁ (nOwn a.2)) R w') a.2.loc.own lo n := fun lo n hl hn =>
    ⟨G0, hG, hl, hn, fun r hr => hrows r (List.mem_of_mem_drop (List.mem_of_mem_take hr))⟩
  have o0 : (plan₃ K₁ (nOwn a.2)).orc 0 = some oI := by simpa [plan₃] using hoI
  have o2 : (plan₃ K₁ (nOwn a.2)).orc 2 = some a.2.loc.w := by simpa [plan₃] using hoV
  have o4 : (plan₃ K₁ (nOwn a.2)).orc 4 = some (nOwn a.2) := by simp [plan₃]
  intro i hi
  simp only [ins32, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show claim₃ (plan₃ K₁ (nOwn a.2)) R (readers₃ S) 1 "Eval" a y w'
    have e : claim₃ (plan₃ K₁ (nOwn a.2)) R (readers₃ S) 1 "Eval" a y w' =
        rowsHold R.same a.2.st (valOf (plan₃ K₁ (nOwn a.2)) R w') a.2.loc.own 0 1 := by
      unfold claim₃
      simp
      rfl
    rw [e]
    exact run _ _ (by omega) (by decide)
  · show claim₃ (plan₃ K₁ (nOwn a.2)) R (readers₃ S) 3 "Dot" a y w'
    have e : claim₃ (plan₃ K₁ (nOwn a.2)) R (readers₃ S) 3 "Dot" a y w' =
        rowsHold R.same a.2.st (valOf (plan₃ K₁ (nOwn a.2)) R w') a.2.loc.own 1 1 := by
      unfold claim₃
      simp
      rfl
    rw [e]
    exact run _ _ (by omega) (by decide)
  · show (meaning₃ S K₁ R).srow 0 a y w'
    rw [srow₃_none S K₁ R 0 a y w' hb]
    exact ⟨oI, xI, o0, hxI, (hs xI (by simp)).1, (hs xI (by simp)).2, hsr xI (by simp)⟩
  · show (meaning₃ S K₁ R).srow 2 a y w'
    rw [srow₃_none S K₁ R 2 a y w' hb]
    exact ⟨a.2.loc.w, xV, o2, hxV, (hs xV (by simp)).1, (hs xV (by simp)).2, hsr xV (by simp)⟩
  · show (meaning₃ S K₁ R).srow 4 a y w'
    rw [srow₃_none S K₁ R 4 a y w' hb]
    exact ⟨nOwn a.2, xO, o4, hxO, (hs xO (by simp)).1, (hs xO (by simp)).2, hsr xO (by simp)⟩
  · exact hpin 0 (by simp)
  · exact hpin 2 (by simp)
  · exact hpin 4 (by simp)

end

/-! ## 4 The law -/

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₃ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan) (a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **Row 3.2's «law», from the proximity test's own law.** -/
theorem law_32_coreF (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₃ × St₃) × Fr₃.E.Str)
    (hQ : QW Fr₃ π nl r rdN Seat.enterOwn Seat.leaveOwn x y)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t tE rs gs, Seat.enterOwn x.1.2 = .ok t →
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE →
      CoreLeft csKey F Fr₃ π (nuOf π nl t) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩) t x.2 x.1 (strsOf Fr₃ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) y.1
          (strsOf Fr₃ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) x.1
          (strsOf Fr₃ x.2) (layAt atSix [0, 2, 4] tbl w) := by
  obtain ⟨hshape, hhas, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  have hsB : LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a (x.1.2.loc.w + 2) (x.1.2.loc.own + 1)
      (x.1.2.loc.firstTree - 1) idx 2 x.1.2) = true ∧ K₁.orc 2 = some x.1.2.loc.w := by
    have h' := hshape
    simp only [shapeB₃, Bool.and_eq_true, beq_iff_eq] at h'
    exact ⟨h'.1.1.1.1.1, h'.1.1.1.1.2⟩
  obtain ⟨hbd, _, _, hV, hO, hgr⟩ := shape32_facts S a idx x.1.2 hsB.1
  obtain ⟨xV, hxV, hsV, hzV⟩ := msgIs_facts _ _ _ hV
  obtain ⟨xO, hxO, hsO, hzO⟩ := msgIs_facts _ _ _ hO
  obtain ⟨G1, hG1, hmem1, hsz1⟩ := grpIs_facts _ _ _ _ _ _ hgr
  obtain ⟨tq, tE, hq1, _, _, rsq, gsq, hyq⟩ := id hQ
  obtain ⟨t, G0, ht, hG, μ, hall, hc⟩ := core_behind_QWn csKey F Fr₃ π nl r rdN smp mem _ rd hrd _ _
    x y x.1 (strsOf Fr₃ x.2) hQ hj (H2K.JointK.early_of_planOk π hp) hp
    (fun t ht => by
      obtain rfl : tq = t := Except.ok.inj (hq1.symm.trans ht)
      exact left tq tE rsq gsq hq1 hyq)
    (fun t ht => by cases ht; exact hfree.order)
  cases ht
  obtain rfl : G1 = G0 := Option.some.inj (hG1.symm.trans hG)
  have has : ∀ k ∈ [0, 2, 4],
      hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ (atSix k).1
        (atSix k).2 x.1 = true := fun k hk =>
    List.all_eq_true.1 hhas k (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> decide)
  have hm0 := member_of_core₃ F decT recOf orc₁ tab smp μ i0 (hlog i0 (.inl rfl))
    (told i0 (.inl rfl)) x.1 _ (has 0 (by simp)) (hsm i0 (.inl rfl)) (hsh i0 (.inl rfl))
    (hc _ (.inl rfl))
  have hm2 := member_of_core₃ F decT recOf orc₁ tab smp μ i2 (hlog i2 (.inr (.inl rfl)))
    (told i2 (.inr (.inl rfl))) x.1 _ (has 2 (by simp)) (hsm i2 (.inr (.inl rfl)))
    (hsh i2 (.inr (.inl rfl))) (hc _ (.inr (.inl rfl)))
  have hm4 := member_of_core₃ F decT recOf orc₁ tab smp μ i4 (hlog i4 (.inr (.inr rfl)))
    (told i4 (.inr (.inr rfl))) x.1 _ (has 4 (by simp)) (hsm i4 (.inr (.inr rfl)))
    (hsh i4 (.inr (.inr rfl))) (hc _ (.inr (.inr rfl)))
  refine ⟨tblOf μ, fun rw w hins _ => ?_⟩
  rw [hins]
  have hread := reads_layAt (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
    (kreadFam (Cells := Cells) csKey six numSix atSix tab) [0, 2, 4] (tblOf μ) w hfree.arr hfree.reads hi
    apart_024
  have n0 : (plan₃ K₁ (nOwn x.1.2)).num oI = some 0 := by
    unfold plan₃
    simp [hIn, hnI]
  have n2 : (plan₃ K₁ (nOwn x.1.2)).num x.1.2.loc.w = some 2 := by
    unfold plan₃ nOwn
    simp [hnV]
  have n4 : (plan₃ K₁ (nOwn x.1.2)).num (nOwn x.1.2) = some 4 := by
    unfold plan₃
    simp
  have hval : ∀ o ∈ G1.members.toList, ∀ pt, ∀ i < Means.tableSize x.1.2.st o pt,
      _root_.Desc.K14.Law.wordsT csKey mem rd μ o pt i =
        OnBytes.Slice.readE (valOf (plan₃ K₁ (nOwn x.1.2))
          (kreadFam (Cells := Cells) csKey six numSix atSix tab)
          (layAt atSix [0, 2, 4] (tblOf μ) w) o pt i) := by
    intro o ho pt i _
    rw [hmem1, hidx] at ho
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact K12Hval.hval_of_links csKey (plan₃ K₁ (nOwn x.1.2)) _ mem rd hrd μ _ _ 0 ⟨sixS, i0⟩ hmI
        n0 ((hread 0 (by simp)).trans (tblOf_at μ i0)) (fun part j => read_val _ _ _ _ _ _ _ _) pt i
    · exact K12Hval.hval_of_links csKey (plan₃ K₁ (nOwn x.1.2)) _ mem rd hrd μ _ _ 2 ⟨sixS, i2⟩ hmV
        n2 ((hread 2 (by simp)).trans (tblOf_at μ i2)) (fun part j => read_val _ _ _ _ _ _ _ _) pt i
    · exact K12Hval.hval_of_links csKey (plan₃ K₁ (nOwn x.1.2)) _ mem rd hrd μ _ _ 4 ⟨sixS, i4⟩ hmO
        n4 ((hread 4 (by simp)).trans (tblOf_at μ i4)) (fun part j => read_val _ _ _ _ _ _ _ _) pt i
  obtain ⟨hrows, hsr⟩ := GrowsOfAllSay.holds_of_allSay hfree.order hK hG _ hall _ hval
  have mI : oI ∈ G1.members.toList := by rw [hmem1, hidx]; simp
  have mV : x.1.2.loc.w ∈ G1.members.toList := by rw [hmem1]; simp
  have mO : x.1.2.loc.w + 2 ∈ G1.members.toList := by rw [hmem1]; simp
  exact items_32 F _ atSix S K₁ _ x.1 (strsOf Fr₃ x.2) _ G1 oI xI xV xO hbd hG (by omega) hoI hsB.2
    hxI hxV hxO
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨hsI, hzI⟩
      · exact ⟨hsV, by omega⟩
      · exact ⟨hsO, by omega⟩)
    hrows
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact hsr oI mI _ hxI
      · exact hsr _ mV _ hxV
      · exact hsr _ mO _ hxO)
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact K12LawLay.pin_laid F _ atSix [0, 2, 4] (tblOf μ) w hfree.arr hi apart_024 x.1
          (strsOf Fr₃ x.2) 0 (by simp) hm0
      · exact K12LawLay.pin_laid F _ atSix [0, 2, 4] (tblOf μ) w hfree.arr hi apart_024 x.1
          (strsOf Fr₃ x.2) 2 (by simp) hm2
      · exact K12LawLay.pin_laid F _ atSix [0, 2, 4] (tblOf μ) w hfree.arr hi apart_024 x.1
          (strsOf Fr₃ x.2) 4 (by simp) hm4)

/-- **From the seam's core's CONCLUSION to the row's «law»**: `law_32_coreF`'s proof
behind its first call, as a statement of its own: whoever has «one tuple of typed messages of which all
rows taken in hold, a candidate at the group's three members», by whichever form of the core, has the
«law». No term of the game, none of the place. -/
theorem law_32_of_core
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₃ × St₃) × Fr₃.E.Str)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (hcore : ∃ t G0, Seat.enterOwn x.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (z : Sound.Mem) → ((sigOf csKey z.1.l).om z.2).Msg,
        Means.AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT csKey mem rd m) ∧
        ∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ →
          Sound.CandAt csKey F smp z x.1 (strsOf Fr₃ x.2) (m z))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) y.1
          (strsOf Fr₃ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) x.1
          (strsOf Fr₃ x.2) (layAt atSix [0, 2, 4] tbl w) := by
  obtain ⟨hshape, hhas, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  have hsB : LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a (x.1.2.loc.w + 2) (x.1.2.loc.own + 1)
      (x.1.2.loc.firstTree - 1) idx 2 x.1.2) = true ∧ K₁.orc 2 = some x.1.2.loc.w := by
    have h' := hshape
    simp only [shapeB₃, Bool.and_eq_true, beq_iff_eq] at h'
    exact ⟨h'.1.1.1.1.1, h'.1.1.1.1.2⟩
  obtain ⟨hbd, _, _, hV, hO, hgr⟩ := shape32_facts S a idx x.1.2 hsB.1
  obtain ⟨xV, hxV, hsV, hzV⟩ := msgIs_facts _ _ _ hV
  obtain ⟨xO, hxO, hsO, hzO⟩ := msgIs_facts _ _ _ hO
  obtain ⟨G1, hG1, hmem1, hsz1⟩ := grpIs_facts _ _ _ _ _ _ hgr
  obtain ⟨t, G0, ht, hG, μ, hall, hc⟩ := hcore
  cases ht
  obtain rfl : G1 = G0 := Option.some.inj (hG1.symm.trans hG)
  have has : ∀ k ∈ [0, 2, 4],
      hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ (atSix k).1
        (atSix k).2 x.1 = true := fun k hk =>
    List.all_eq_true.1 hhas k (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> decide)
  have hm0 := member_of_core₃ F decT recOf orc₁ tab smp μ i0 (hlog i0 (.inl rfl))
    (told i0 (.inl rfl)) x.1 _ (has 0 (by simp)) (hsm i0 (.inl rfl)) (hsh i0 (.inl rfl))
    (hc _ (.inl rfl))
  have hm2 := member_of_core₃ F decT recOf orc₁ tab smp μ i2 (hlog i2 (.inr (.inl rfl)))
    (told i2 (.inr (.inl rfl))) x.1 _ (has 2 (by simp)) (hsm i2 (.inr (.inl rfl)))
    (hsh i2 (.inr (.inl rfl))) (hc _ (.inr (.inl rfl)))
  have hm4 := member_of_core₃ F decT recOf orc₁ tab smp μ i4 (hlog i4 (.inr (.inr rfl)))
    (told i4 (.inr (.inr rfl))) x.1 _ (has 4 (by simp)) (hsm i4 (.inr (.inr rfl)))
    (hsh i4 (.inr (.inr rfl))) (hc _ (.inr (.inr rfl)))
  refine ⟨tblOf μ, fun rw w hins _ => ?_⟩
  rw [hins]
  have hread := reads_layAt (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
    (kreadFam (Cells := Cells) csKey six numSix atSix tab) [0, 2, 4] (tblOf μ) w hfree.arr hfree.reads hi
    apart_024
  have n0 : (plan₃ K₁ (nOwn x.1.2)).num oI = some 0 := by
    unfold plan₃
    simp [hIn, hnI]
  have n2 : (plan₃ K₁ (nOwn x.1.2)).num x.1.2.loc.w = some 2 := by
    unfold plan₃ nOwn
    simp [hnV]
  have n4 : (plan₃ K₁ (nOwn x.1.2)).num (nOwn x.1.2) = some 4 := by
    unfold plan₃
    simp
  have hval : ∀ o ∈ G1.members.toList, ∀ pt, ∀ i < Means.tableSize x.1.2.st o pt,
      _root_.Desc.K14.Law.wordsT csKey mem rd μ o pt i =
        OnBytes.Slice.readE (valOf (plan₃ K₁ (nOwn x.1.2))
          (kreadFam (Cells := Cells) csKey six numSix atSix tab)
          (layAt atSix [0, 2, 4] (tblOf μ) w) o pt i) := by
    intro o ho pt i _
    rw [hmem1, hidx] at ho
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact K12Hval.hval_of_links csKey (plan₃ K₁ (nOwn x.1.2)) _ mem rd hrd μ _ _ 0 ⟨sixS, i0⟩ hmI
        n0 ((hread 0 (by simp)).trans (tblOf_at μ i0)) (fun part j => read_val _ _ _ _ _ _ _ _) pt i
    · exact K12Hval.hval_of_links csKey (plan₃ K₁ (nOwn x.1.2)) _ mem rd hrd μ _ _ 2 ⟨sixS, i2⟩ hmV
        n2 ((hread 2 (by simp)).trans (tblOf_at μ i2)) (fun part j => read_val _ _ _ _ _ _ _ _) pt i
    · exact K12Hval.hval_of_links csKey (plan₃ K₁ (nOwn x.1.2)) _ mem rd hrd μ _ _ 4 ⟨sixS, i4⟩ hmO
        n4 ((hread 4 (by simp)).trans (tblOf_at μ i4)) (fun part j => read_val _ _ _ _ _ _ _ _) pt i
  obtain ⟨hrows, hsr⟩ := GrowsOfAllSay.holds_of_allSay hfree.order hK hG _ hall _ hval
  have mI : oI ∈ G1.members.toList := by rw [hmem1, hidx]; simp
  have mV : x.1.2.loc.w ∈ G1.members.toList := by rw [hmem1]; simp
  have mO : x.1.2.loc.w + 2 ∈ G1.members.toList := by rw [hmem1]; simp
  exact items_32 F _ atSix S K₁ _ x.1 (strsOf Fr₃ x.2) _ G1 oI xI xV xO hbd hG (by omega) hoI hsB.2
    hxI hxV hxO
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨hsI, hzI⟩
      · exact ⟨hsV, by omega⟩
      · exact ⟨hsO, by omega⟩)
    hrows
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact hsr oI mI _ hxI
      · exact hsr _ mV _ hxV
      · exact hsr _ mO _ hxO)
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact K12LawLay.pin_laid F _ atSix [0, 2, 4] (tblOf μ) w hfree.arr hi apart_024 x.1
          (strsOf Fr₃ x.2) 0 (by simp) hm0
      · exact K12LawLay.pin_laid F _ atSix [0, 2, 4] (tblOf μ) w hfree.arr hi apart_024 x.1
          (strsOf Fr₃ x.2) 2 (by simp) hm2
      · exact K12LawLay.pin_laid F _ atSix [0, 2, 4] (tblOf μ) w hfree.arr hi apart_024 x.1
          (strsOf Fr₃ x.2) 4 (by simp) hm4)

/-- **Row 3.2's «law», with «left» MEMBER BY MEMBER**: by `core_behind_QWm`
(Johnson/Desc/K12/Coin/MemberAtYes.lean): of the seam's bundle the payer owes, at
whatever the state behind the door in fixes: the codes' equation and `MemberLeft` at each member. FIRST
LIMIT: the book's price stands in MemberLeft's clause (7), at no := nuOf π nl t. -/
theorem law_32_coreM (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₃ × St₃) × Fr₃.E.Str)
    (hQ : QW Fr₃ π nl r rdN Seat.enterOwn Seat.leaveOwn x y)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1 (strsOf Fr₃ x.2) s D
            j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) y.1
          (strsOf Fr₃ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) x.1
          (strsOf Fr₃ x.2) (layAt atSix [0, 2, 4] tbl w) := by
  have hfree := (id (hon.resolve_left (fun h => h trivial))).2.2.1
  exact law_32_of_core F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ smp mem rd hrd x y hon
    (core_behind_QWm csKey F Fr₃ π nl r rdN smp mem _ rd hrd _ _ x y x.1 (strsOf Fr₃ x.2) hQ hj hp left
      (fun t ht => by cases ht; exact hfree.order))
    hi hlog told hsm hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI

/-- **The same over the PARTED remainder `MemberLeft₂`**: by `core_behind_QWm₂`: where a member's
shape has rows of both kinds (V) «every coordinate of the OOD seed's point is canonical» stands under a
«there is» of its own, beside clause (6): so that two separate files' lemmas can pay the two. A WEAKER premise
than `law_32_coreM`'s (`MemberLeft.parted`). -/
theorem law_32_coreM₂ (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₃ × St₃) × Fr₃.E.Str)
    (hQ : QW Fr₃ π nl r rdN Seat.enterOwn Seat.leaveOwn x y)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (left : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft₂ csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1 (strsOf Fr₃ x.2) s D
            j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab), rw.ins = ins32 →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) y.1
          (strsOf Fr₃ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix
          (meaning₃ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab)) x.1
          (strsOf Fr₃ x.2) (layAt atSix [0, 2, 4] tbl w) := by
  have hfree := (id (hon.resolve_left (fun h => h trivial))).2.2.1
  exact law_32_of_core F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ smp mem rd hrd x y hon
    (core_behind_QWm₂ csKey F Fr₃ π nl r rdN smp mem _ rd hrd _ _ x y x.1 (strsOf Fr₃ x.2) hQ hj hp left
      (fun t ht => by cases ht; exact hfree.order))
    hi hlog told hsm hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI

end Johnson.RunOne.Law.K12Law32Core

#print axioms Johnson.RunOne.Law.K12Law32Core.shape32_facts
#print axioms Johnson.RunOne.Law.K12Law32Core.seats_024
#print axioms Johnson.RunOne.Law.K12Law32Core.member_of_core₃
#print axioms Johnson.RunOne.Law.K12Law32Core.items_32
#print axioms Johnson.RunOne.Law.K12Law32Core.law_32_coreF
#print axioms Johnson.RunOne.Law.K12Law32Core.law_32_of_core
#print axioms Johnson.RunOne.Law.K12Law32Core.law_32_coreM
#print axioms Johnson.RunOne.Law.K12Law32Core.law_32_coreM₂
