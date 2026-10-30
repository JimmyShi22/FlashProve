-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean: the lookup of a sub-proof as one typed block: the
reduction, its knowledge soundness, its list of rounds, its errors; general in the forest's public
numbers h, the caller's layout L, the field, and the filling V, VC of the short sumcheck.

 1. forB E h L V VC: the draw of the shift if the forest has several calls (the verifier's own test
    1 < NC), then the whole chain of the lookup at the letters forA E h L.
 2. HoleC, a closed proposition: at every h with FoNums.ok h = true and 2^d (2^32 - 1) < p, KnowAt
    (all four fields) of forB's reduction between the block's own joints. forIn: R0 beside «for
    every call c < NC each of its 2^(n_c) keys is one of the 2^(k_c) rows of its own table». forOut:
    R0 beside the out-claim of a lookup (the masked claim on the keys and all rows hold) at the
    shifted joint vectors. The extractor is the identity on the further witness; the errors are
    forB's own; the game is played for each fixed tuple of messages m : M (KnowAt.know,
    Cb/G6/Cut.lean). holeC proves it.
 3. forB_shape: the block's rounds are forEnts wk h (the shift's entry if 1 < NC, then entN wk
    (h.v - 1) h.d 5 30) in the sense of ShapeIs (OnBytes/G4/RoundIs.lean): each round sends as many
    bytes, draws as many elements, and as many of them not 0, as its entry says. The entry's name
    and its other numbers, wk among them, are tied to the round by nothing.
 4. forB_eps: the block's numbers of bad challenges are forEps q h, q the number of E's elements:
    2^d if 1 < NC, then epsN (h.v - 1) h.d 5 30 q.
Premises left: FoNums.ok h = true, one Bool on public numbers; CharP E p; 2^d (2^32 - 1) < p (the
verifier's test no-wrap-pin-forest is 2^(d + 32) < its prime: ok_wrap). None reads the messages, a
witness or a transcript.
ok_parts, ok_portOK, ok_v, ok_adm, ok_padsOK, ok_NC, ok_wrap: what the general theorems ask, from
that Bool.

Main definitions: forB, forIn, forOut, HoleC, forEnts, forEps. Main theorems: holeC, forB_shape,
forB_eps.
Not claimed: that forB's reduction is the function Forest.pad (OnBytes/Model/Look.lean): no
statement compares the two; that L.K holds a sub-proof's keys; the end claims in the verifier's own
forms; the hashed form; what the verifier accepts (V and VC stay letters here;
OnBytes/Tie/Pv/Lookup/Forest/FoAt.lean fills them); that the errors are small (each is below the
size of its round's challenge set: OnBytes/Tie/Pv/Lookup/Forest/FoSmall.lean). That the success of
Forest.shape and Forest.pubAsk gives FoNums.ok h is shape_ok
(OnBytes/Tie/Pv/Lookup/Port/FoShape.lean).
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoA

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwRound TwPlan TwErr OnBytes.G4

/-! ### what the general theorems ask, from the one Bool -/

theorem ok_parts {h : Sh} (H : FoNums.ok h = true) :
    (10 ≤ h.dT ∧ 1 ≤ h.NC ∧ h.NC ≤ 2 ^ h.cK ∧ h.NT ≤ 2 ^ h.rK ∧ h.v < 32 ∧ h.pub.size = h.NT ∧
        h.calls.size = h.NC) ∧
    (∀ y < h.NT, FoNums.co h y < h.NC ∧ FoNums.fst h (FoNums.co h y) ≤ y ∧ y < FoNums.fst h
        (FoNums.co h y) + 2 ^ FoNums.io h (FoNums.co h y)) ∧
    (∀ c < h.NC, FoNums.t0Of h c < 2 ^ FoNums.kOf h c ∧ FoNums.kOf h c ≤ h.kT ∧ FoNums.nOf h c =
        FoNums.io h c + h.dT ∧
      ∀ b < 2 ^ FoNums.io h c, FoNums.fst h c + b < h.NT ∧ FoNums.co h (FoNums.fst h c + b) = c ∧
          (FoNums.fst h c + b) % 2 ^ FoNums.io h c = b) ∧
    (∀ e ∈ FoNums.pads h, e.1 < 2 ^ h.d) ∧ ((FoNums.pads h).map Prod.snd).sum ≤ 2 ^ h.v ∧
    h.kT ≤ 16 ∧ h.NC ≤ 16 ∧ 2 ^ (h.d + 32) < OnBytes.pW.toNat := by
  simp only [FoNums.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.mem_range] at H
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, b⟩, c⟩, d⟩, e⟩, f1⟩, f2⟩, f3⟩ := H
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, fun y hy => ⟨(b y hy).1.1, (b y hy).1.2, (b y hy).2⟩,
    fun k hk => ⟨(c k hk).1.1.1, (c k hk).1.1.2, (c k hk).1.2, fun x hx =>
        ⟨((c k hk).2 x hx).1.1, ((c k hk).2 x hx).1.2, ((c k hk).2 x hx).2⟩⟩, d, e, f1, f2, f3⟩

theorem ok_portOK {h : Sh} (H : FoNums.ok h = true) : Port.OK h := by
  obtain ⟨⟨_, a2, a3, a4, _, _, _⟩, b, c, _, _⟩ := ok_parts H
  exact ⟨a2, a3, a4, b, (c 0 a2).1, fun k hk => ⟨(c k hk).2.1, (c k hk).2.2.1, (c k hk).2.2.2⟩⟩

theorem ok_v {h : Sh} (H : FoNums.ok h = true) : h.v = FoNums.v' h + 1 := by
  obtain ⟨⟨a1, _⟩, _⟩ := ok_parts H
  have : h.v = h.dT + h.rK := rfl
  unfold FoNums.v'
  omega

/-- the verifier's test no-wrap-pin-forest gives the premise on the characteristic, at every p from
the verifier's prime on -/
theorem ok_wrap {h : Sh} (H : FoNums.ok h = true) {p : ℕ} (hp : OnBytes.pW.toNat ≤ p) :
    2 ^ h.d * (2 ^ 32 - 1) < p := by
  obtain ⟨_, _, _, _, _, _, _, f3⟩ := ok_parts H
  have h1 : 2 ^ h.d * (2 ^ 32 - 1) ≤ 2 ^ h.d * 2 ^ 32 := Nat.mul_le_mul_left _ (by norm_num)
  rw [← Nat.pow_add] at h1
  omega

theorem ok_NC {h : Sh} (H : FoNums.ok h = true) {p : ℕ} (hp : 2 ^ h.d * (2 ^ 32 - 1) < p) :
    h.NC ≤ p := by
  obtain ⟨⟨_, _, a3, _⟩, _⟩ := ok_parts H
  have h1 : 2 ^ h.cK ≤ 2 ^ h.d := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  have h2 : 2 ^ h.d * 1 ≤ 2 ^ h.d * (2 ^ 32 - 1) := Nat.mul_le_mul_left _ (by norm_num)
  omega

section
variable (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

theorem ok_adm {h : Sh} (H : FoNums.ok h = true) (L : Lay E St₀ J₀) {p : ℕ}
    (hp : 2 ^ h.d * (2 ^ 32 - 1) < p) :
    (forA E h L).H.lkb.Adm p := by
  obtain ⟨⟨_, _, _, _, a5, _⟩, _⟩ := ok_parts H
  refine ⟨(by decide : FoNums.n + 2 ≤ 2 ^ FoNums.w), ?_, hp⟩
  show 2 ^ (FoNums.v' h + 1) < 2 ^ 32
  rw [← ok_v H]
  exact Nat.pow_lt_pow_right (by norm_num) a5

theorem ok_padsOK {h : Sh} (H : FoNums.ok h = true) (L : Lay E St₀ J₀) :
    padsOK ((forA E h L).v' + 1) (forA E h L).d (forA E h L).pads = true := by
  obtain ⟨_, _, _, d, e, _⟩ := ok_parts H
  show padsOK (FoNums.v' h + 1) h.d (FoNums.pads h) = true
  rw [← ok_v H]
  unfold padsOK padNum
  rw [Bool.and_eq_true]
  exact ⟨List.all_eq_true.2 fun x hx => decide_eq_true (d x hx), decide_eq_true e⟩

theorem forA_full (h : Sh) (L : Lay E St₀ J₀) : (forA E h L).n + 1 + 1 = 2 ^ (forA E h L).w :=
  (by decide : FoNums.n + 1 + 1 = 2 ^ FoNums.w)
theorem forA_oE (h : Sh) (L : Lay E St₀ J₀) : (forA E h L).oE = Fin.revPerm := rfl

/-! ### (1) the typed reduction, with its errors -/

/-- The lookup of a sub-proof: the shift (if there are several calls), then the whole chain. -/
noncomputable def forB (h : Sh) (L : Lay E St₀ J₀) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) {Ex : ExtSpec} :
        BkK St₀ (TX (St₀ × E) E (Option J₀)) Ex :=
  (forP E h L).allK (forA E h L) (FoNums.several h) V VC

/-- the block's own in-joint: R0 beside «each call's keys lie in that call's table» -/
def forIn {Kc M Wp : Type} {Ex : ExtSpec} (h : Sh) (L : Lay E St₀ J₀) (R0 : Rels Kc St₀ Ex (M × Wp))
    (msg₀ : M → J₀ → E) :
    Rels Kc St₀ Ex (M × Wp) :=
  Port.jIn h (forT E h) (forK E L) (fun m => zext (msg₀ m)) R0

/-- the block's own out-joint: R0 beside the library's out-claim of a lookup, at the shifted joint
vectors -/
def forOut {Kc M Wp : Type} {Ex : ExtSpec} (h : Sh) (L : Lay E St₀ J₀)
    (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → E) :
    Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp) :=
  cj (ShiftQ.ride R0) (fun m => zext (msg₀ m)) Prod.fst ((forA E h L).lk.out id id)
      ((forA E h L).lk.out id id)

end

/-! ### (2) knowledge soundness -/

/-- Knowledge soundness of the lookup of a sub-proof, a closed proposition. -/
def HoleC : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St₀ J₀ : Type) [Fintype J₀]
      [DecidableEq J₀]
    (h : Sh) (L : Lay E St₀ J₀) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
        (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → E),
    FoNums.ok h = true → 2 ^ h.d * (2 ^ 32 - 1) < p →
    KnowAt (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
        (fun _ _ _ wp => wp)
      (forB E h L V VC (Ex := Ex)).e

theorem holeC : HoleC := by
  intro E _ _ p _ St₀ J₀ _ _ h L V VC Ex Kc M Wp R0 msg₀ H hp
  have g : (forB E h L V VC (Ex := Ex)).Know (((forP E h L).on fun m => zext (msg₀ m)).jIn R0)
      (forOut E h L R0 msg₀) :=
    allK_base E p St₀ (forA E h L) (forP E h L) (FoNums.several h) V VC Ex Kc M Wp R0
        (fun m => zext (msg₀ m))
      (port_ok E p St₀ (Option J₀) h (forT E h) (forK E L) (ok_portOK H) (ok_NC H hp)) (ok_v H) rfl
      (ok_adm E H L hp) (ok_padsOK E H L) (forA_full E h L)
  have e : ((forP E h L).on fun m => zext (msg₀ m)).jIn R0 = forIn E h L R0 msg₀ :=
    port_jIn E St₀ (Option J₀) M Kc Wp Ex h (forT E h) (forK E L) _ R0 (ok_portOK H)
  rw [e] at g
  exact g

/-! ### (3), (4) its list of rounds; its errors -/

/-- the list of rounds, as data: computable, general in h -/
def forEnts (wk : Nat) (h : Sh) : List Fmt.Entry :=
  shHead (FoNums.several h) (shiftN wk) ++ entN wk (FoNums.v' h) h.d FoNums.w FoNums.n
/-- the number of bad challenges, one a round; q: the size of the field -/
def forEps (q : Nat) (h : Sh) : List Nat :=
  shHead (FoNums.several h) (2 ^ h.d) ++ epsN (FoNums.v' h) h.d FoNums.w FoNums.n q

section
variable (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  (h : Sh) (L : Lay E St₀ J₀) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
      (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Ex : ExtSpec)

theorem forB_shape (wk : Nat) : ShapeIs E (forB E h L V VC (Ex := Ex)).R.shape (forEnts wk h) :=
  allK_shape V VC Ex (forA E h L) (forP E h L) (FoNums.several h) wk rfl

theorem forB_eps : errList (forB E h L V VC (Ex := Ex)).e = forEps (Fintype.card E) h :=
  allK_eps V VC Ex (forA E h L) (forP E h L) (FoNums.several h) rfl

end
end Cb.Fo
