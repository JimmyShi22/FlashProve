-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttCalls.lean

Every lookup call of a shape that the verifier's function shape returns has the library's table: the
tables of Johnson/Road/Lane5AttTabs.lean at the calls that the verifier itself lays.

* "calls_of_shape": what shape has run for its calls: the list of calls is what layCall returns on
  the expanded call list; the tests on the shifts have passed; there are 2^ll shifts.
* "isLut_calls": each call k of S.calls has the table lutK (tbOf S) S.u0 k.kind k.sh, in the sense
  Hd.IsLut. Conditions: ldh = 7, kFD = 16; the table of exponentials has an entry, fewer than 2^16
  entries, each at most 2^12.
* "isLut_calls12": at S = 12, rx = 8 the last three hold (Johnson/Road/Lane5AttExp.lean and the
  library's bound on its table).
* "call_sh": the shift of a call whose table depends on the shift is one of the configuration's.
* "lutK_lut": with one shift in the group (AttFit.one) the table lutK of a call is the library's
  AttSeg.lut at the letters of AttOrd (sclOf S, dimOf S, tbOf S), at the number of the call's kind:
  KR 0, KFD 1, R16 2, WH 3.
* "isLut_ord": all together.

shapeHid sets the number iota of each call and leaves the table (Hd.IsLut.iota).

Not claimed: what the lookup shows; which keys a call holds.
-/
import Johnson.Road.Lane5AttTabs
import Johnson.Road.Lane5AttExp

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open Attention (ACall Cfg Shape Listed Table shape layCall expandLine shTests)

/-! ## Tools -/

/-- Each value of a list that mapM returns is the value on a member. -/
theorem mapM_mem {α β : Type} (f : α → Except String β) :
    ∀ (l : List α) (r : List β), l.mapM f = Except.ok r → ∀ b ∈ r, ∃ a ∈ l, f a = Except.ok b
  | [], r, h, b, hb => by
    rw [List.mapM_nil] at h
    have e : [] = r := Except.ok.inj h
    subst e
    cases hb
  | x :: l, r, h, b, hb => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨ys, hys, h⟩ := bind_ok h
    have e : y :: ys = r := Except.ok.inj h
    subst e
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact ⟨x, List.mem_cons.2 (Or.inl rfl), hy⟩
    · obtain ⟨a, ha, hf⟩ := mapM_mem f l ys hys b hb'
      exact ⟨a, List.mem_cons.2 (Or.inr ha), hf⟩

/-- If forM ends well, the function has ended well on every member. -/
theorem forM_mem {α : Type} (f : α → Except String PUnit.{1}) :
    ∀ (l : List α), l.forM f = Except.ok PUnit.unit → ∀ a ∈ l, f a = Except.ok PUnit.unit
  | [], _, a, ha => by cases ha
  | x :: l, h, a, ha => by
    have h : (f x >>= fun _ => l.forM f) = Except.ok PUnit.unit := h
    obtain ⟨u, hu, h⟩ := bind_ok h
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact hu
    · exact forM_mem f l h a ha'

/-! ## What shape has run for its calls -/

/-- The values of the shift in the group, in increasing order, each once. -/
def shsOf (cf : Cfg) : List ℕ := (cf.sh.toList.mergeSort fun a b => decide (a ≤ b)).eraseDups

/-- The verifier's bound on a score. -/
def smOf (cf : Cfg) : ℕ := 2 ^ cf.ldh * Model.clamp * Model.clamp

theorem calls_of_shape {cf : Cfg} {S : Shape} (h : shape cf = Except.ok S) :
    ∃ calls : List ACall,
      (cf.lines.flatMap (expandLine (shsOf cf))).mapM
          (layCall cf (cf.H / 2 ^ cf.lgk) (smOf cf) S.Tt) = Except.ok calls ∧
        S.calls = calls.toArray ∧
        (shsOf cf).forM (shTests cf S.Tt.size (smOf cf)) = Except.ok PUnit.unit ∧
        cf.sh.size = 2 ^ cf.ll := by
  unfold Attention.shape at h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨e3, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨Tt, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨u, hF, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨calls, hM, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨calls, hM, rfl, hF, bne_eq_false_iff_eq.1 e3⟩

/-- A shift that has passed shTests is at most 12. -/
theorem sh_le_of_tests {cf : Cfg} {u0 Sm sh : ℕ}
    (h : shTests cf u0 Sm sh = Except.ok PUnit.unit) : sh ≤ 12 := by
  unfold Attention.shTests at h
  obtain ⟨e, -⟩ := refuse_ok h
  simp only [Bool.or_eq_false_iff] at e
  exact Nat.not_lt.mp (of_decide_eq_false e.2)

/-- The shift of a member of the expanded call list: one of the group's, or 0 at a kind whose table
does not depend on the shift. -/
theorem listed_sh {shs : List ℕ} {lines : List Attention.Line} {x : Listed}
    (hx : x ∈ lines.flatMap (expandLine shs)) :
    (x.2.1.bySh = true ∧ x.2.2.1 ∈ shs) ∨ (x.2.1.bySh = false ∧ x.2.2.1 = 0) := by
  obtain ⟨l, -, hl⟩ := List.mem_flatMap.1 hx
  unfold Attention.expandLine at hl
  by_cases hb : l.kind.bySh = true
  · rw [if_pos hb] at hl
    obtain ⟨sh, hs, rfl⟩ := List.mem_map.1 hl
    exact Or.inl ⟨hb, hs⟩
  · rw [if_neg hb] at hl
    obtain rfl := List.mem_singleton.1 hl
    exact Or.inr ⟨eq_false_of_ne_true hb, rfl⟩

/-! ## The tables of the calls -/

theorem smOf_ref {cf : Cfg} (hl : cf.ldh = 7) : ((smOf cf : ℕ) : ℤ) = Smax := by
  unfold smOf
  rw [hl]
  show ((2 ^ 7 * 2047 * 2047 : ℕ) : ℤ) = 128 * 2047 ^ 2
  norm_num

/-- **Every call of the shape has the library's table of its kind and shift.** -/
theorem isLut_calls {cf : Cfg} {S : Shape} (h : shape cf = Except.ok S) (hl : cf.ldh = 7)
    (hkF : cf.kFD = 16) (h0 : 0 < S.u0) (hu : S.u0 < 65536)
    (hT : ∀ ι : ℕ, ι < S.u0 → S.Tt.getD ι 0 ≤ 4096) :
    ∀ k ∈ S.calls.toList, Hd.IsLut k.call (lutK (tbOf S) S.u0 k.kind k.sh) := by
  have P := shaped_of_shape h
  obtain ⟨calls, hM, hc, hF, -⟩ := calls_of_shape h
  intro k hk
  rw [hc] at hk
  obtain ⟨x, hx, hx2⟩ := mapM_mem _ _ _ hM k hk
  rw [P.u0] at h0 hu hT ⊢
  have hsh : x.2.2.1 ≤ 12 := by
    rcases listed_sh hx with ⟨-, hs⟩ | ⟨-, hs⟩
    · exact sh_le_of_tests (forM_mem _ _ hF _ hs)
    · rw [hs]
      norm_num
  exact (isLut_layCall hx2 (tb := tbOf S) hkF hsh (smOf_ref hl) h0 hu hT (fun _ _ => rfl)).2.2

/-- The same at S = 12, rx = 8. -/
theorem isLut_calls12 {cf : Cfg} {S : Shape} (h : shape cf = Except.ok S) (hl : cf.ldh = 7)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) :
    ∀ k ∈ S.calls.toList, Hd.IsLut k.call (lutK (tbOf S) S.u0 k.kind k.sh) := by
  obtain ⟨hu, hE⟩ := exp_of_shaped (shaped_of_shape h) h12 h8
  refine isLut_calls h hl hkF (by omega) (by omega) fun ι hι => ?_
  have hι' : ι < 2307 := hu ▸ hι
  have b : tbRef.Exp (ι : ℕ) ≤ 2 ^ 12 := (tbRef_ok.2.2.2.1 ι hι').2
  rw [← hE ι hι] at b
  have b' : ((S.Tt.getD ι 0 : ℕ) : ℤ) ≤ ((4096 : ℕ) : ℤ) := by
    refine le_trans b ?_
    norm_num
  exact Int.ofNat_le.1 b'

/-! ## One shift -/

/-- The number of the library's call for a kind of table. -/
def noK : Table → Fin 4
  | .kr => 0
  | .kfd => 1
  | .r16 => 2
  | .wh => 3

/-- Kind and shift of the call that layCall returns. -/
theorem layCall_kind {cf : Cfg} {HA Sm : ℕ} {Tt : Array ℕ} {x : Listed} {k : ACall}
    (h : layCall cf HA Sm Tt x = Except.ok k) : k.kind = x.2.1 ∧ k.sh = x.2.2.1 := by
  obtain ⟨name, kind, sh, segs⟩ := x
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨rfl, rfl⟩

/-- The shift of a call whose table depends on the shift is an entry of the configuration's array of
shifts. -/
theorem call_sh {cf : Cfg} {S : Shape} (h : shape cf = Except.ok S) {k : ACall}
    (hk : k ∈ S.calls.toList) (hb : k.kind.bySh = true) : k.sh ∈ cf.sh.toList := by
  obtain ⟨calls, hM, hc, -, -⟩ := calls_of_shape h
  rw [hc] at hk
  obtain ⟨x, hx, hx2⟩ := mapM_mem _ _ _ hM k hk
  have e := layCall_kind hx2
  rw [e.1] at hb
  rw [e.2]
  rcases listed_sh hx with ⟨-, hs⟩ | ⟨hn, -⟩
  · unfold shsOf at hs
    simpa using hs
  · rw [hn] at hb
    cases hb

/-- With one shift in the group the table of a call is the library's, at the letters of AttOrd. -/
theorem lutK_lut {cf : Cfg} {S : Shape} (h : shape cf = Except.ok S) (h1 : OneShift S) {k : ACall}
    (hk : k ∈ S.calls.toList) :
    lutK (tbOf S) S.u0 k.kind k.sh =
      AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) (noK k.kind) := by
  have P := shaped_of_shape h
  obtain ⟨-, -, -, -, hsz⟩ := calls_of_shape h
  have key : k.kind.bySh = true → k.sh = S.cf.sh.getD 0 0 := by
    intro hb
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 (call_sh h hk hb)
    have hi' : i < cf.sh.size := by simpa using hi
    have e1 : cf.sh.getD i 0 = k.sh := by
      rw [← e]
      simp [Array.getD, hi']
    have e2 := h1 i (by rw [P.Lam, ← hsz]; exact hi')
    rw [P.cfg] at e2 ⊢
    rw [← e1, e2]
  cases hkind : k.kind with
  | kr =>
    have e := key (by rw [hkind]; rfl)
    show tau1 k.sh = tau1 (S.cf.sh.getD 0 0)
    rw [e]
  | kfd =>
    have e := key (by rw [hkind]; rfl)
    show tau2 k.sh S.u0 (tbOf S) = tau2 (S.cf.sh.getD 0 0) S.u0 (tbOf S)
    rw [e]
  | r16 => rfl
  | wh => rfl

/-- **Every call of the shape has the table that AttOrd's relation asks of its kind**: at ldh = 7
with one shift (AttFit), kFD = 16, S = 12, rx = 8. -/
theorem isLut_ord {cf : Cfg} {S : Shape} (h : shape cf = Except.ok S) (F : AttFit S)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) :
    ∀ k ∈ S.calls.toList,
      Hd.IsLut k.call (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) (noK k.kind)) := by
  intro k hk
  have hl : cf.ldh = 7 := by
    have e := F.ldh
    rw [(shaped_of_shape h).cfg] at e
    exact e
  rw [← lutK_lut h F.one hk]
  exact isLut_calls12 h hl hkF h12 h8 k hk

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.calls_of_shape
#print axioms OnBytes.Road.L5.isLut_calls
#print axioms OnBytes.Road.L5.isLut_calls12
#print axioms OnBytes.Road.L5.lutK_lut
#print axioms OnBytes.Road.L5.isLut_ord
