-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Say58.lean: kind K5: what the claims say, member by member: claims 5
to 8, and the whole.

Main names:
  `endsE`, `endsV`, `endsK`, `endsH`: the reader's form under end value number j of: denominator ×
    output; a value product; the key at the index; "the index's cells are bits". `bitsF`: the
    weighted bits of pair b's index.
  `Say5` … `Say8` with `say5` … `say8`; `Say` with `say_lists`; `Spec.SayIff`, `say_iff`: every form
    that "first" and "second" gather at a record of the kind's own is worth 0 if and only if Say
    holds at oldOf S gL i.
The numbers j: a sumcheck of products: 2 b and 2 b + 1; the key: lam, and Lam + b lt + k. The score
at the index has a claim on its end values 2 b alone: 2 b + 1 is the start of the key's sumcheck.
Used of OnBytes: as Johnson/Desc/First/Att/Claims/Say.lean.
Not claimed: that a claim holds; what an entry of a table means.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Say

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention

variable {Kf : Type} [CommRing Kf] (ρ : Reading Kf) (W : World Kf)

theorem val_neg (c : E) : ρ.val (mulE minusOne c) = - ρ.val c := by
  unfold minusOne
  rw [ρ.mul, ρ.sub, ρ.zero, ρ.one]
  ring

/-- A sum taken off a form, against the sum by itself. -/
theorem foldl_neg {α : Type} (fv : α → Aff) (c : α → E) : ∀ (l : List α) (s t : Aff),
    (l.foldl (fun s a => Aff.addMul s (fv a) (mulE minusOne (c a))) s).value ρ W =
      s.value ρ W - ((l.foldl (fun s a => Aff.addMul s (fv a) (c a)) t).value ρ W - t.value ρ W)
  | [], s, t => by simp
  | a :: l, s, t => by
    rw [List.foldl_cons, List.foldl_cons, foldl_neg fv c l _ (Aff.addMul t (fv a) (c a)),
      Aff.value_addMul, Aff.value_addMul, val_neg]
    ring

/-- A block of places behind a first stretch. -/
theorem forall_block (L n m : ℕ) (C : ℕ → Prop) :
    ((∀ a < L, C a) ∧ ∀ b < n, ∀ k < m, C (L + b * m + k)) ↔ ∀ j < L + n * m, C j := by
  constructor
  · rintro ⟨h1, h2⟩ j hj
    by_cases hl : j < L
    · exact h1 j hl
    · have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hj; omega
        · exact h
      have hj' : j - L < n * m := by omega
      have hb : (j - L) / m < n := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hj')
      have := h2 _ hb _ (Nat.mod_lt (j - L) hm)
      have e : L + (j - L) / m * m + (j - L) % m = j := by
        have := Nat.div_add_mod (j - L) m
        rw [Nat.mul_comm] at this
        omega
      rwa [e] at this
  · intro h
    refine ⟨fun a ha => h a (by omega), fun b hb k hk => h _ ?_⟩
    have : (b + 1) * m ≤ n * m := Nat.mul_le_mul_right m hb
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

variable (h : Attention.Heard) (K : ℕ)

/-! ### claim 5 -/

def endsE (j : ℕ) : Aff :=
  if j % 2 = 0 then
    Fo.readDenominatorF h K h.t.hE h.d.scE.r (h.d.pwW.getD (j / 2) default).lam
      (h.d.pwW.getD (j / 2) default).a
  else
    Fo.readHeadT h K h.t.qO h.S.atO h.d.scE.r h.d.zcW (h.d.pwW.getD (j / 2) default).lam
      (h.d.pwW.getD (j / 2) default).a

structure Say5 : Prop where
  zc : (Fo.lessF (Aff.slot h.d.sZC) h.d.pwW fun w =>
    Fo.readDenominatorF h K h.t.hW h.d.zgW w.lam w.a).value ρ W = 0
  rh : (Fo.lessF (Aff.slot h.d.sRH) h.d.pwW fun w =>
    Fo.readHeadT h K h.t.tO (atRh h.S) h.d.zgW h.d.zcW w.lam w.a).value ρ W = 0
  rhp : (Fo.lessF (Aff.slot h.d.sRHP) h.d.pwW fun w =>
    Fo.readHeadT h K h.t.tO (atRhp h.S) h.d.zgW h.d.zcW w.lam w.a).value ρ W = 0
  ib : ∀ k < h.S.cf.lt, (Fo.lessF (Aff.slot (h.d.sIB + k)) h.d.pwX fun w =>
    Fo.readIndexBitF h K h.t.hX h.d.zgX w.lam w.a k).value ρ W = 0
  r2 : (Fo.lessF (Aff.slot h.d.s5h) h.d.pwH fun w =>
    Fo.readHeadT h K h.t.tO (atRh h.S) h.d.zgH h.d.zcH w.lam w.a).value ρ W = 0
  r2p : (Fo.lessF (Aff.slot (h.d.s5h + 1)) h.d.pwH fun w =>
    Fo.readHeadT h K h.t.tO (atRhp h.S) h.d.zgH h.d.zcH w.lam w.a).value ρ W = 0
  row : h.d.scE.rowU.value ρ W = 0
  ends : ∀ j < 2 * h.S.NP, W.slot (h.d.scE.sEnd + j) = (endsE h K j).value ρ W

theorem say5 : AllZero ρ W (Fo.claim5T h K) ↔ Say5 ρ W h K := by
  unfold Fo.claim5T
  simp only [allZero_append, allZero_single, allZero_flatMap, allZero_nil, List.mem_range,
    Fo.endValuesET, and_true]
  have e : (∀ b < h.S.NP,
      (sc3A h.d.scE b - Fo.readDenominatorF h K h.t.hE h.d.scE.r (h.d.pwW.getD b default).lam
        (h.d.pwW.getD b default).a).value ρ W = 0 ∧
      (sc3B h.d.scE b - Fo.readHeadT h K h.t.qO h.S.atO h.d.scE.r h.d.zcW
        (h.d.pwW.getD b default).lam (h.d.pwW.getD b default).a).value ρ W = 0) ↔
      ∀ j < 2 * h.S.NP, W.slot (h.d.scE.sEnd + j) = (endsE h K j).value ρ W := by
    rw [← forall_pairs]
    refine forall₂_congr fun b _ => and_congr ?_ ?_
    · unfold sc3A endsE
      rw [slot_sub, if_pos (by omega), show 2 * b / 2 = b by omega]
    · unfold sc3B endsE
      rw [slot_sub, if_neg (by omega), show (2 * b + 1) / 2 = b by omega]
  rw [e]
  exact ⟨fun ⟨a, b, c, d, e, f, g, i⟩ => ⟨a, b, c, d, e, f, g, i⟩,
    fun ⟨a, b, c, d, e, f, g, i⟩ => ⟨a, b, c, d, e, f, g, i⟩⟩

/-! ### claim 6 -/

def endsV (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool) (tV : ℕ) (j : ℕ) : Aff :=
  if j % 2 = 0 then
    Fo.planeF h K tS 3 (h.d.pwW.getD (j / 2) default).lam (h.d.pwW.getD (j / 2) default).a pt isD +
      Aff.ofConst (ofNat 128) +
      Aff.scale (Fo.planeF h K tS 4 (h.d.pwW.getD (j / 2) default).lam
        (h.d.pwW.getD (j / 2) default).a pt isD) (ofNat 256)
  else
    Aff.ofConst h.d.gam + Fo.readGroupT h K tV h.S.atV sc.r h.d.zcW (h.d.pwW.getD (j / 2) default).lam

structure ProdSay (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool) (tV : ℕ) : Prop where
  row : sc.rowU.value ρ W = 0
  ends : ∀ j < 2 * h.S.NP, W.slot (sc.sEnd + j) = (endsV h K sc tS pt isD tV j).value ρ W

theorem prod_say (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool) (tV : ℕ) :
    AllZero ρ W (Fo.valueProductT h K sc tS pt isD tV) ↔ ProdSay ρ W h K sc tS pt isD tV := by
  unfold Fo.valueProductT
  simp only [allZero_append, allZero_single, allZero_flatMap, List.mem_range]
  constructor
  · rintro ⟨a, b⟩
    refine ⟨a, (forall_pairs _ _).1 fun c hc => ?_⟩
    obtain ⟨b1, b2⟩ := b c hc
    unfold sc3A at b1
    unfold sc3B at b2
    rw [slot_sub] at b1 b2
    unfold endsV
    rw [if_pos (by omega), if_neg (by omega), show 2 * c / 2 = c by omega,
      show (2 * c + 1) / 2 = c by omega]
    exact ⟨b1, b2⟩
  · rintro ⟨a, b⟩
    refine ⟨a, fun c hc => ?_⟩
    obtain ⟨b1, b2⟩ := (forall_pairs _ _).2 b c hc
    unfold endsV at b1 b2
    rw [if_pos (by omega), show 2 * c / 2 = c by omega] at b1
    rw [if_neg (by omega), show (2 * c + 1) / 2 = c by omega] at b2
    unfold sc3A sc3B
    rw [slot_sub, slot_sub]
    exact ⟨b1, b2⟩

structure Say6 : Prop where
  acc : W.slot h.d.sCl + W.slot (h.d.sCl + 1) - W.slot h.d.sACC - ρ.val h.d.gam * W.slot h.d.sZC = 0
  below : ProdSay ρ W h K h.d.vpm h.t.tVM h.t.ptM false h.t.qVM
  on : ProdSay ρ W h K h.d.vpd h.t.tVD h.t.ptD true h.t.qVD

theorem say6 : AllZero ρ W (Fo.claim6T h K) ↔ Say6 ρ W h K := by
  unfold Fo.claim6T
  simp only [allZero_append, allZero_single, prod_say, Aff.value_sub, Aff.value_add, Aff.value_slot,
    Aff.value_scale]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-! ### claim 7 -/

/-- The reader's form under end value number j of the key's sumcheck: lam ↦ the key's group · Lam + b lt + k ↦ bit k of pair b's index. -/
def endsK (j : ℕ) : Aff :=
  if j < h.S.Lam then Fo.readGroupT h K h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) j
  else Fo.readIndexBitF h K h.t.hPi (h.x.pg h.S) ((j - h.S.Lam) / h.S.cf.lt / h.S.HA)
    ((j - h.S.Lam) / h.S.cf.lt % h.S.HA) ((j - h.S.Lam) % h.S.cf.lt)

structure Say7 : Prop where
  maxima : ∀ b < h.S.NP, W.slot (h.x.sM6 + b) =
    (Fo.readMaximumF h K h.t.hT h.x.tg (b / h.S.HA) (b % h.S.HA)).value ρ W
  rowF : h.x.scF.rowU.value ρ W = 0
  endsF : ∀ b < h.S.NP, W.slot (h.x.scF.sEnd + 2 * b) =
    (Fo.readHeadT h K h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S) (b / h.S.HA) (b % h.S.HA)).value ρ W
  rowK : h.x.scd.rowU.value ρ W = 0
  endsK : ∀ j < h.S.Lam + h.S.NP * h.S.cf.lt, W.slot (h.x.scd.sEnd + j) = (endsK h K j).value ρ W

theorem endsK_lam {lam : ℕ} (hl : lam < h.S.Lam) :
    endsK h K lam = Fo.readGroupT h K h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) lam := by
  unfold endsK
  rw [if_pos hl]

theorem endsK_bit (b : ℕ) {k : ℕ} (hk : k < h.S.cf.lt) :
    endsK h K (h.S.Lam + b * h.S.cf.lt + k) =
      Fo.readIndexBitF h K h.t.hPi (h.x.pg h.S) (b / h.S.HA) (b % h.S.HA) k := by
  unfold endsK
  have e : h.S.Lam + b * h.S.cf.lt + k - h.S.Lam = k + b * h.S.cf.lt := by omega
  rw [if_neg (by omega), e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

theorem say7 : AllZero ρ W (Fo.claim7T h K) ↔ Say7 ρ W h K := by
  unfold Fo.claim7T
  simp only [allZero_append, allZero_single, allZero_flatMap, List.mem_range, slot_sub]
  have e : ((∀ lam < h.S.Lam, W.slot (h.x.sKC + lam) =
        (Fo.readGroupT h K h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) lam).value ρ W) ∧
      ∀ b < h.S.NP, ∀ k < h.S.cf.lt, W.slot (h.x.sIb h.S b k) =
        (Fo.readIndexBitF h K h.t.hPi (h.x.pg h.S) (b / h.S.HA) (b % h.S.HA) k).value ρ W) ↔
      ∀ j < h.S.Lam + h.S.NP * h.S.cf.lt, W.slot (h.x.scd.sEnd + j) = (endsK h K j).value ρ W := by
    rw [← forall_block]
    refine and_congr (forall₂_congr fun lam hl => ?_) (forall₂_congr fun b _ => forall₂_congr fun k hk => ?_)
    · rw [endsK_lam h K hl]
      rfl
    · rw [endsK_bit h K b hk]
      rfl
  constructor
  · rintro ⟨a, b, c, d, f, g⟩
    refine ⟨a, b, ?_, d, e.1 ⟨f, g⟩⟩
    intro x hx
    have := c x hx
    unfold sc3A at this
    rwa [slot_sub] at this
  · rintro ⟨a, b, c, d, f⟩
    refine ⟨a, b, ?_, d, (e.2 f).1, (e.2 f).2⟩
    intro x hx
    unfold sc3A
    rw [slot_sub]
    exact c x hx

/-! ### claim 8 -/

/-- The weighted bits of pair b's index. -/
def bitsF (b : ℕ) : Aff :=
  (List.range h.S.cf.lt).foldl (fun s k =>
    Aff.addMul s (Fo.readIndexBitF h K h.t.hR2 (h.x.rg2 h.S) (b / h.S.HA) (b % h.S.HA) k)
      ((eqTab (h.x.rk h.S)).getD k zeroE)) (Aff.ofConst zeroE)

/-- The reader's form under end value number j of "the index's cells are bits": 2 b ↦ the weighted bits · 2 b + 1 ↦ the same less 1. -/
def endsH (j : ℕ) : Aff :=
  if j % 2 = 0 then bitsF h K (j / 2) else bitsF h K (j / 2) - Aff.ofConst oneE

structure Say8 : Prop where
  row : h.x.scH.rowU.value ρ W = 0
  ends : ∀ j < 2 * h.S.NP, W.slot (h.x.scH.sEnd + j) = (endsH h K j).value ρ W

theorem bitsSum_value (b : ℕ) :
    (Fo.bitsSumF h K b).value ρ W = W.slot (h.x.scH.sEnd + 2 * b) - (bitsF h K b).value ρ W := by
  unfold Fo.bitsSumF bitsF
  rw [foldl_neg ρ W _ (fun k => (eqTab (h.x.rk h.S)).getD k zeroE) _ _ (Aff.ofConst zeroE),
    Aff.value_ofConst, ρ.zero, sub_zero]
  unfold sc3A
  rw [Aff.value_slot]

theorem say8 : AllZero ρ W (Fo.claim8T h K) ↔ Say8 ρ W h K := by
  unfold Fo.claim8T
  simp only [allZero_append, allZero_single, allZero_flatMap, List.mem_range, bitsSum_value]
  have e : (∀ b < h.S.NP, (sc3B h.x.scH b - sc3A h.x.scH b + Aff.ofConst oneE).value ρ W = 0 ∧
      W.slot (h.x.scH.sEnd + 2 * b) - (bitsF h K b).value ρ W = 0) ↔
      ∀ j < 2 * h.S.NP, W.slot (h.x.scH.sEnd + j) = (endsH h K j).value ρ W := by
    rw [← forall_pairs]
    refine forall₂_congr fun b _ => ?_
    unfold sc3A sc3B endsH
    rw [if_pos (by omega), if_neg (by omega), show 2 * b / 2 = b by omega,
      show (2 * b + 1) / 2 = b by omega, Aff.value_add, Aff.value_sub, Aff.value_sub, Aff.value_slot,
      Aff.value_slot, Aff.value_ofConst, ρ.one]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := sub_eq_zero.1 h2
      refine ⟨h3, ?_⟩
      rw [← h3]
      linear_combination h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, sub_eq_zero.2 h1⟩
      rw [h2, h1]
      ring
  rw [e]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-! ### the whole -/

/-- **What the claims say.** -/
structure Say : Prop where
  s3 : Say3 ρ W h K
  s4 : Say4 ρ W h K
  s5 : Say5 ρ W h K
  s6 : Say6 ρ W h K
  s7 : Say7 ρ W h K
  s8 : Say8 ρ W h K

theorem say_lists : AllZero ρ W ((Fo.claim3T h K ++ (Fo.claim4T h K ++ Fo.claim5T h K)) ++
    (Fo.claim6T h K ++ (Fo.claim7T h K ++ Fo.claim8T h K))) ↔ Say ρ W h K := by
  simp only [allZero_append, say3, say4, say5, say6, say7, say8]
  exact ⟨fun ⟨⟨a, b, c⟩, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨⟨a, b, c⟩, d, e, f⟩⟩

namespace Spec

/-- **Every form that "first" and "second" gather at a record of the kind's own is worth 0 ⇔ the written conjunction at the plain record of OnBytes/Model made of it.** -/
def SayIff : Prop :=
  ∀ (Kf : Type) [CommRing Kf] (ρ : Reading Kf) (W : World Kf) (A : Plan) (S : Shape)
    (gL : Forest.Heard) (i : VerifiableInference.Desc.First.Att.P.Runs.In) (K : ℕ) (l₁ l₂ : List Aff)
    (j : VerifiableInference.Desc.First.Att.P.Runs.JoinsP),
    i.g = VerifiableInference.Desc.First.Att.P.geoOf S → i.zk = gL.zk → A.NC = S.calls.size →
    VerifiableInference.Desc.First.Att.P.Runs.firstRun i K = some (l₁, j) →
    VerifiableInference.Desc.First.Att.P.Runs.secondRun i K = some l₂ →
      (AllZero ρ W (l₁ ++ l₂) ↔ Say ρ W (oldOf S gL i) K)

end Spec

theorem say_iff : Spec.SayIff := by
  intro Kf _ ρ W A S gL i K l₁ l₂ j hg hz hN h1 h2
  rw [(first_any A S gL i K l₁ j hg hz hN h1).1, second_any S gL i K l₂ hg hz h2]
  exact say_lists ρ W _ K

end K5Law
