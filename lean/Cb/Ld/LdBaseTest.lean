-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBaseTest.lean: the statement on the base case of a proximity test beyond unique decoding
(Cb/Ld/LdBase.lean, `Spec.ldBase_good`) is not empty there, and an extractor that sees only the
oracles cannot reach it (exactly: `Spec.blind_fails`, told next, and `Spec.instance2_blind`).

`Spec.blind_fails`: for every code C with `C.Laws` and at least one long position (N of them): let a
native word f have two candidates w₁, w₂ within the radius e, let x₁ be a claim that w₁ meets and x₂
one that w₂ meets, and let no (message, randomness) be a witness of both (x₁, f) and (x₂, f) in the
relaxation (`(C.rels sl e _).relR`, Cb/Ld/LdRel.lean). Then for every function ext' of the implicit
part and of the oracles sent alone (and of the output statement's witness, here of type `Unit`; this
is the type of the extractors of `IOR.Good`, Ior/Chain.lean), knowledge soundness (`Know`,
Ior/Know.lean: round by round) of the block (`ldBaseIOR C sl t cov`) with ext' fails for every error
list (ε₁, ε₂) with ε₁ below the number of values of μ (the verifier's first message, in E) and ε₂
below (N - e)^t. The block's own second error, (N - e - 1)^t, is below (N - e)^t as soon as t ≥ 1
and e < N; for the block's own errors to fall under `Spec.blind_fails`, its first error has to be
below the number of values of μ too.

Statements (in `Cb.LdBaseTest.Spec`) and their proofs, in one file.

Why: the prover sends the zero word and the scalar 0 in both runs, then μ w₁ in the one run and μ w₂
in the other. It is accepted for every μ on at least (N - e)^t lists Q (the verifier's second
message: t long positions); ext' sees the same oracles in both runs.

Main names:
  `rep2 E`: the smallest code with a radius not below half the distance: one symbol repeated at two
    positions, over any finite field, read as it stands. Distance 2, radius 1 (so 2 e = d: every
    word with two different symbols has two candidates).
  `Spec.rep2_laws` to `Spec.rep2_list`: it has the laws, the distance 2, transparency, at most 1
    exceptional value on every line at the radius 1, and with two interleaved rows at most 2
    candidates at the radius 1 (`Laws`, `Dist`, `Transparent`, `MCAat`, `ListAt`, Cb/Ld/LdRel.lean).
  `Spec.instance2`: so the bundle of `Spec.ldBase_good` (`IOR.GoodT`, Ior/KnowCollGood.lean) holds
    of it at e = 1, d = 2, with the errors (3, 0^t): they say something over every field with more
    than 3 elements, for t ≥ 1 (they are below the numbers of all values, |E| and 2^t).
  `Spec.instance2_blind`: and at this instance, with the form `Slf.idf`, no extractor of the type in
    `Spec.blind_fails` has any errors (ε₁, 0) with ε₁ below the size of the field; so not these,
    where they say something.
  `Spec.rel_both`.
  `Spec.instance5`: a second instance, at the toy of Cb/Ld/LdRelToy.lean (Reed-Solomon of length 5
    and dimension 2 over the field with 101 elements, any interleaved rows, radius 2 with distance
    4): the bundle holds with the errors (16 + 2, 2^t) = (18 of 101 values of μ, 2^t of 5^t lists
    Q), nothing assumed.

Limits: this file does not say that the errors of `Spec.ldBase_good` are attained. On zero knowledge
the file has one thing: the bundle `IOR.GoodT`, which `Spec.instance2` and `Spec.instance5`
conclude, has the field `exact` (`Honest.Exact`, Ior/Honest.lean), at the budget `ldBaseBud`; beyond
this field no statement of the file speaks of it.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBaseCode
import Cb.Ld.LdRelToy

set_option autoImplicit false

namespace Cb
namespace LdBaseTest
open Iop Prob Blocks Hiop

/-! ## A prover that escapes in two rounds -/

/-- If after the first message m1 more than e1 values μ allow a second message after which more than
e2 values Q are not bad for the prover, the prover has not lost (`Doomed`, Iop/Rbr.lean) at the
errors (e1, e2), towards `bad`. -/
theorem not_doomed2 {r1 r2 : Round} (e1 e2 : ℕ) (bad : Tr [r1, r2] → Prop) (m1 : r1.Msg)
    (A : r1.Chal → Prop) (hA : e1 < cnt A) (m2 : r1.Chal → r2.Msg)
    (h : ∀ μ, A μ → e2 < cnt fun Q => ¬ bad (m1, μ, m2 μ, Q, ())) :
    ¬ Doomed [r1, r2] (e1, (e2, ())) bad := by
  intro hd
  have h1 : cnt (fun μ : r1.Chal => ¬ Doomed [r2] (e2, ()) fun τ => bad (m1, μ, τ)) ≤ e1 := hd m1
  refine absurd (lt_of_lt_of_le hA (le_trans (cnt_mono fun μ hμ hd2 => ?_) h1)) (lt_irrefl _)
  have h2 : cnt (fun Q : r2.Chal => ¬ bad (m1, μ, m2 μ, Q, ())) ≤ e2 := hd2 (m2 μ)
  exact absurd (h μ hμ) (not_lt.mpr h2)

namespace Spec

/-- No extractor that sees only the implicit part and the oracles.
(not all hypotheses are named here: see the statement below) -/
def blind_fails : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (St : Type)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (e : ℕ)
      (ext' : C.ext.Str → Orcs (ldBaseShape C t) → Unit → C.N.Wit) (ε₁ ε₂ : ℕ) (f : C.Word)
      (x₁ x₂ : E × St) (w₁ w₂ : C.N.Wit),
    C.Laws → (C.rels sl e fun _ => ()).relR (x₁, f) w₁ → (C.rels sl e fun _ => ()).relR (x₂, f) w₂ →
    (∀ w, ¬ ((C.rels sl e fun _ => ()).relR (x₁, f) w ∧ (C.rels sl e fun _ => ()).relR (x₂, f) w)) →
    ε₁ < Fintype.card E → ε₂ < (Fintype.card P - e) ^ t →
    ¬ (ldBaseIOR C sl t cov).red.Know (fun _ => True) (C.rels sl e fun _ => ()).relR trivRels.relR
      (fun a τ w => ext' a.2 τ.read w) (ε₁, (ε₂, ()))

end Spec

section
variable {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] {C : LdCode E P} {St : Type}
  {sl : Slf E St C.J} {t : ℕ} {cov : C.NP → P} {e : ℕ}

/-- Under `C.Laws`, with at least one long position, if w meets x: the prover that sends zeros and
then μ w is accepted at every μ on the lists of positions at which the input is the transform of the
encoding of w. -/
theorem accept_zero (hC : C.Laws) {f : C.Word} {x : E × St} {w : C.MR} (hw : sl.Holds x w.1) (μ : E)
    {Q : Fin t → P} (hQ : ∀ i, ¬ C.T f (Q i) ≠ ldCw C w (Q i)) :
    (ldBaseIOR C sl t cov).out x f (((0 : C.Word), (0 : E)), μ, ((), μ • w), Q, ()) = some () := by
  refine if_pos ⟨?_, fun i => ?_⟩
  · have h := ldForm_form sl x 0 w μ
    rw [zero_add] at h
    have h0 : ldForm (C := C) sl x 0 = 0 := Finset.sum_eq_zero fun j _ => mul_zero _
    have hw' : ldForm (C := C) sl x w = x.1 := hw
    rw [h, h0, hw']
  · have h := ldCw_lin hC 0 w μ (Q i)
    rw [zero_add] at h
    have h0 : ldCw C 0 = 0 := by
      show C.T (C.enc 0 0) = 0
      have h1 : C.enc 0 0 = 0 := hC.encLin.map_zero
      rw [h1, hC.tLin.map_zero]
    have hT0 : C.T (0 : C.Word) = 0 := hC.tLin.map_zero
    rw [h, h0, hT0, not_not.1 (hQ i)]

/-- Under `hC`, `hw`, `h1`, `h2` below, with at least one long position: if the extractor's answer
at the zero oracle is no witness of (x, f), knowledge soundness (`Know`: round by round) fails. -/
theorem escapes (hC : C.Laws)
    (ext' : C.ext.Str → Orcs (ldBaseShape C t) → Unit → C.N.Wit) {ε₁ ε₂ : ℕ} {f : C.Word}
    {x : E × St} {w : C.N.Wit} (hw : (C.rels sl e fun _ => ()).relR (x, f) w)
    (h1 : ε₁ < Fintype.card E) (h2 : ε₂ < (Fintype.card P - e) ^ t)
    (hk : (ldBaseIOR C sl t cov).red.Know (fun _ => True) (C.rels sl e fun _ => ()).relR
      trivRels.relR (fun a τ w => ext' a.2 τ.read w) (ε₁, (ε₂, ()))) :
    (C.rels sl e fun _ => ()).relR (x, f)
      (ext' f (ldBaseTr (C := C) (t := t) (0, fun _ => Classical.arbitrary P, ()) 0 0 0).read
        ()) := by
  by_contra hno
  refine not_doomed2 ε₁ ε₂ _ (((0 : C.Word), (0 : E))) (fun _ => True) (by rw [cnt_true]; exact h1)
    (fun μ => ((), μ • (w : C.MR))) (fun μ _ => ?_) (hk (x, f) trivial)
  have hoff : cnt (fun y => C.T f y ≠ ldCw C w y) ≤ e := hw.1
  have hpow : (Fintype.card P - e) ^ t ≤
      cnt fun Q : Fin t → P => ∀ i, ¬ C.T f (Q i) ≠ ldCw C w (Q i) := by
    rw [cnt_forall_pow (fun y => ¬ C.T f y ≠ ldCw C w y) t]
    refine Nat.pow_le_pow_left ?_ t
    have := cnt_add_cnt_not (fun y => C.T f y ≠ ldCw C w y)
    omega
  refine lt_of_lt_of_le h2 (hpow.trans (cnt_mono fun Q hQ hbad => hno ?_))
  have hout : (ldBaseIOR C sl t cov).red.out
        (x, f) (((0 : C.Word), (0 : E)), μ, ((), μ • (w : C.MR)), Q, ()) =
      some ((), ()) := by
    show Option.map _ ((ldBaseIOR C sl t cov).out x f _) = _
    rw [accept_zero hC hw.2 μ hQ]
    rfl
  have h3 := hbad ((), ()) () hout trivial
  have hread : (show Tr (ldBaseShape C t)
        from (((0 : C.Word), (0 : E)), μ, ((), μ • (w : C.MR)), Q, ())).read =
      (ldBaseTr (C := C) (t := t) (0, fun _ => Classical.arbitrary P, ()) 0 0 0).read := by
    funext p
    rcases p with p | p | p
    · rfl
    · exact p.elim
    · exact p.elim
  rw [← hread]
  exact h3

end

theorem blind_fails : Spec.blind_fails := by
  intro E P _ _ _ _ C St sl t cov e ext' ε₁ ε₂ f x₁ x₂ w₁ w₂ hC hw₁ hw₂ hno h1 h2 hk
  exact hno _ ⟨escapes hC ext' hw₁ h1 h2 hk, escapes hC ext' hw₂ h1 h2 hk⟩

/-! ## The smallest code with a radius not below half the distance -/

/-- One symbol, repeated at two positions, read as it stands. -/
@[reducible] def rep2 (E : Type) : LdCode E Bool where
  NP := Bool
  NS := fun _ => Unit
  J := Unit
  Q := Empty
  enc := fun m _ _ _ => m ()
  Aa := Unit
  T := fun f x _ => f x ()
  src := fun x => {x}

/-- the word (0, 1), its two candidates, and the two claims "the message is 0", "the message is
1" -/
def word01 (E : Type) [Field E] : (rep2 E).Word := fun x _ => bif x then 1 else 0
def cand (E : Type) (c : E) : (rep2 E).MR := (fun _ => c, fun q => q.elim)
def claim (E : Type) [Field E] (c : E) : E × (Unit → E) := (c, fun _ => 1)

namespace Spec
open IOR

def rep2_laws : Prop := ∀ (E : Type) [Field E], (rep2 E).Laws
def rep2_dist : Prop := ∀ (E : Type) [Field E], (rep2 E).Dist 2
def rep2_transp : Prop := ∀ (E : Type) [Field E], (rep2 E).Transparent
def rep2_mca : Prop := ∀ (E : Type) [Field E] [Fintype E], (rep2 E).MCAat 1 1
def rep2_list : Prop := ∀ (E : Type) [Field E] [Fintype E], ((rep2 E).il Bool).ListAt 1 2

/-- An instance at 2 e = d. -/
def instance2 : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (St : Type) (sl : Slf E St Unit) (t : ℕ) (cov : Bool → Bool),
    GoodT (ldBaseIOR (rep2 E) sl t cov) (ldBaseHon (rep2 E) sl t cov)
      ((rep2 E).rels sl 1 fun _ => ()) trivRels
      (ldBaseExt (rep2 E) t 2) (ldBaseNums (rep2 E) sl t cov 1 1 2) ∧
    ldBaseErr (rep2 E) t 1 1 2 = (3, (0 ^ t, ()))

/-- At this instance no extractor that sees only the oracles will do. States: at `rep2 E`, `Slf.idf`
and the radius 1, knowledge soundness (`Know`: round by round) fails with every ext' of the type in
`Spec.blind_fails`, at all errors (ε₁, 0) with ε₁ < |E|. -/
def instance2_blind : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (t : ℕ) (cov : Bool → Bool)
      (ext' : (rep2 E).ext.Str → Orcs (ldBaseShape (rep2 E) t) → Unit → (rep2 E).N.Wit) (ε₁ : ℕ),
    ε₁ < Fintype.card E →
    ¬ (ldBaseIOR (rep2 E) Slf.idf t cov).red.Know (fun _ => True)
      ((rep2 E).rels Slf.idf 1 fun _ => ()).relR trivRels.relR
      (fun a τ w => ext' a.2 τ.read w) (ε₁, (0, ()))

/-- States, at `rep2 E` and the form `Slf.idf`: the honest relation is not empty; the relaxation at
the radius 1 is not everything. -/
def rel_both : Prop :=
  ∀ (E : Type) [Field E] [Fintype E],
    (∃ x y w, ((rep2 E).rels Slf.idf 1 fun _ => ()).rel x y w) ∧
    ∃ a, ∀ w, ¬ ((rep2 E).rels Slf.idf 1 fun _ => ()).relR a w

end Spec

theorem rep2_laws : Spec.rep2_laws := fun _ _ =>
  { encLin := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    tLin := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    inj := fun _ _ h => ⟨funext fun _ => congrFun (congrFun h false) (), funext fun q => q.elim⟩
    loc := fun _ _ x h => funext fun _ => congrFun (h x (Finset.mem_singleton_self x)) () }

theorem rep2_dist : Spec.rep2_dist := by
  intro E _ m r hne
  have hm : m () ≠ 0 := fun h0 => hne ⟨funext fun _ => h0, funext fun q => q.elim⟩
  have h : cnt (fun x : Bool => (rep2 E).T ((rep2 E).enc m r) x ≠ 0) = Fintype.card Bool :=
    (cnt_congr fun x => iff_true_intro fun h => hm (congrFun h ())).trans cnt_true
  rw [h, Fintype.card_bool]

theorem rep2_transp : Spec.rep2_transp := fun _ _ => ⟨fun _ s _ _ => s (), fun _ _ _ _ _ => rfl⟩

/-- On a set that misses a position every word is on the code. -/
theorem rep2_onCode_of_not_mem
    {E : Type} [Field E] (y : Bool → Unit → E) {S : Finset Bool} {x : Bool} (hx : x ∉ S) :
    (rep2 E).OnCode y S := by
  refine ⟨fun _ => y (!x) (), fun q => q.elim, fun z hz => ?_⟩
  have hzx : z = !x := by
    cases x <;> cases z <;> first | rfl | exact absurd hz hx
  rw [hzx]

/-- Of an exceptional value θ at the radius 1: the two differences a, b of the ends of the line are
not both 0, and a + θ b = 0. -/
theorem rep2_exc {E : Type} [Field E] {g f : (rep2 E).Word} {θ : E}
    (h : ∃ S : Finset Bool,
      Fintype.card Bool ≤ S.card + 1 ∧
      (rep2 E).OnCode ((rep2 E).T g + θ • (rep2 E).T f) S ∧
      ¬ ((rep2 E).OnCode ((rep2 E).T g) S ∧ (rep2 E).OnCode ((rep2 E).T f) S)) :
    (g false () - g true ()) + θ * (f false () - f true ()) = 0 ∧
    ¬ (g false () - g true () = 0 ∧ f false () - f true () = 0) := by
  obtain ⟨S, -, ⟨m, r, h1⟩, h2⟩ := h
  have hall : ∀ x, x ∈ S := fun x =>
    by_contra fun hx => h2 ⟨rep2_onCode_of_not_mem _ hx, rep2_onCode_of_not_mem _ hx⟩
  have e0 : g false () + θ * f false () = m () := congrFun (h1 false (hall false)) ()
  have e1 : g true () + θ * f true () = m () := congrFun (h1 true (hall true)) ()
  refine ⟨by linear_combination e0 - e1,
    fun hab =>
      h2 ⟨⟨fun _ => g false (), fun q => q.elim, fun z _ => ?_⟩,
          ⟨fun _ => f false (), fun q => q.elim, fun z _ => ?_⟩⟩⟩
  · funext u
    cases z
    · rfl
    · exact (sub_eq_zero.mp hab.1).symm
  · funext u
    cases z
    · rfl
    · exact (sub_eq_zero.mp hab.2).symm

theorem rep2_mca : Spec.rep2_mca := by
  intro E _ _ g f
  refine cnt_le_one fun θ θ' h h' => ?_
  obtain ⟨h1, hn⟩ := rep2_exc h
  obtain ⟨h2, -⟩ := rep2_exc h'
  by_contra hne
  have h3 : (θ - θ') * (f false () - f true ()) = 0 := by linear_combination h1 - h2
  have hb : f false () - f true () = 0 := (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne)
  rw [hb, mul_zero, add_zero] at h1
  exact hn ⟨h1, hb⟩

theorem rep2_list : Spec.rep2_list := by
  intro E _ _ F
  have key : ∀ w : ((rep2 E).il Bool).MR,
      ((rep2 E).il Bool).Near 1 F (((rep2 E).il Bool).enc w.1 w.2) →
      w = ((fun j => F false (j.1, ()), fun q => q.2.elim) : ((rep2 E).il Bool).MR) ∨
      w = ((fun j => F true (j.1, ()), fun q => q.2.elim) : ((rep2 E).il Bool).MR) := by
    intro w hw
    have hex : ∃ x : Bool,
        ((rep2 E).il Bool).T F x = ((rep2 E).il Bool).T (((rep2 E).il Bool).enc w.1 w.2) x := by
      by_contra hno
      have h2 : cnt (fun x : Bool =>
            ((rep2 E).il Bool).T F x ≠ ((rep2 E).il Bool).T (((rep2 E).il Bool).enc w.1 w.2) x) =
          Fintype.card Bool :=
        (cnt_congr fun x => iff_true_intro fun h => hno ⟨x, h⟩).trans cnt_true
      have h3 : cnt (fun x : Bool =>
            ((rep2 E).il Bool).T F x ≠ ((rep2 E).il Bool).T (((rep2 E).il Bool).enc w.1 w.2) x) ≤
          1 := hw
      rw [h2, Fintype.card_bool] at h3
      omega
    obtain ⟨x, hx⟩ := hex
    have hw1 : ∀ j : Bool × Unit, w.1 j = F x (j.1, ()) := fun j => (congrFun hx (j.1, ())).symm
    cases x
    · exact Or.inl (Prod.ext (funext hw1) (funext fun q => q.2.elim))
    · exact Or.inr (Prod.ext (funext hw1) (funext fun q => q.2.elim))
  refine (cnt_le_add key).trans ?_
  rw [cnt_eq_const, cnt_eq_const]

theorem instance2 : Spec.instance2 := by
  intro E _ _ St sl t cov
  refine ⟨ldBase_good E Bool (rep2 E) St sl t cov 2 1 1 2 (rep2_laws E) (rep2_transp E)
      (by norm_num) (rep2_mca E) (rep2_list E),
    ?_⟩
  unfold ldBaseErr
  rw [Fintype.card_bool]
  rfl

section
variable (E : Type) [Field E] [Fintype E]

/-- The word (0, 1) is within one position of both constant words 0 and 1, and each meets its own
claim. -/
theorem word01_cand (b : Bool) :
    ((rep2 E).rels Slf.idf 1 fun _ => ()).relR
      (claim E (bif b then 1 else 0), word01 E) (cand E (bif b then 1 else 0)) := by
  refine ⟨?_, ?_⟩
  · show cnt (fun x : Bool =>
        (rep2 E).T (word01 E) x ≠
          (rep2 E).T
            ((rep2 E).enc (cand E (bif b then 1 else 0)).1 (cand E (bif b then 1 else 0)).2) x) ≤ 1
    refine cnt_le_one fun x y hx hy => ?_
    have hxb : x = !b := by
      cases b <;> cases x <;> first | rfl | exact absurd rfl hx
    have hyb : y = !b := by
      cases b <;> cases y <;> first | rfl | exact absurd rfl hy
    rw [hxb, hyb]
  · show ∑ j : Unit, (1 : E) * (bif b then 1 else 0) = (bif b then 1 else 0)
    simp

end

theorem instance2_blind : Spec.instance2_blind := by
  intro E _ _ t cov ext' ε₁ h1
  refine blind_fails E Bool (rep2 E) (Unit → E) Slf.idf t cov 1 ext' ε₁ 0 (word01 E) (claim E 0)
    (claim E 1) (cand E 0) (cand E 1) (rep2_laws E) (word01_cand E false) (word01_cand E true)
    (fun w hw => ?_) h1 (by rw [Fintype.card_bool]; simp)
  have ha : ∑ j : Unit, (1 : E) * w.1 j = 0 := hw.1.2
  have hb : ∑ j : Unit, (1 : E) * w.1 j = 1 := hw.2.2
  exact zero_ne_one (ha.symm.trans hb)

theorem rel_both : Spec.rel_both := by
  intro E _ _
  refine ⟨⟨claim E 0, (rep2 E).enc (cand E 0).1 (cand E 0).2, cand E 0, rfl, ?_⟩,
    ⟨(claim E 1, 0), fun w hw => ?_⟩⟩
  · show ∑ j : Unit, (1 : E) * (0 : E) = 0
    simp
  · have hb : ∑ j : Unit, (1 : E) * w.1 j = 1 := hw.2
    have hw1 : w.1 () = 1 := by simpa using hb
    have h2 : cnt
          (fun x : Bool => (rep2 E).T (0 : (rep2 E).Word) x ≠ (rep2 E).T ((rep2 E).enc w.1 w.2) x) =
        Fintype.card Bool :=
      (cnt_congr fun x =>
        iff_true_intro fun h => zero_ne_one ((congrFun h ()).trans hw1)).trans cnt_true
    have h3 : cnt
          (fun x : Bool => (rep2 E).T (0 : (rep2 E).Word) x ≠ (rep2 E).T ((rep2 E).enc w.1 w.2) x) ≤
        1 := hw.1
    rw [h2, Fintype.card_bool] at h3
    omega

/-! ## The toy of Cb/Ld/LdRelToy.lean -/

open LdToy

instance : Nonempty (Reading.one C5).P := ⟨(⟨0, by decide⟩ : Fin 5)⟩

namespace Spec
open IOR

def instance5 : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R] (St : Type) (sl : Slf K St (toyLd R).J) (t : ℕ)
      (cov : (toyLd R).NP → (Reading.one C5).P),
    GoodT (ldBaseIOR (toyLd R) sl t cov) (ldBaseHon (toyLd R) sl t cov)
      ((toyLd R).rels sl 2 fun _ => ()) trivRels (ldBaseExt (toyLd R) t 4)
      (ldBaseNums (toyLd R) sl t cov 2 16 2) ∧
    ldBaseErr (toyLd R) t 2 16 2 = (18, (2 ^ t, ())) ∧
    18 < Fintype.card K ∧
    Fintype.card (Fin t → (Reading.one C5).P) = 5 ^ t

end Spec

theorem instance5 : Spec.instance5 := by
  intro R _ _ St sl t cov
  obtain ⟨hL, hD, -, -, hm, -, -, htr, -⟩ := ld_toy R
  have hc : Fintype.card (Reading.one C5).P = 5 := Fintype.card_fin 5
  have hJ : InJohnson (Fintype.card (Reading.one C5).P) 4 2 := by
    rw [hc]
    unfold InJohnson
    norm_num
  have hl : listMax (Fintype.card (Reading.one C5).P) 4 2 = 2 := by
    rw [hc]
    unfold listMax
    norm_num
  have h := ldBase_good_johnson K _ (toyLd R) St sl t cov 4 2 16 hL htr hD (by norm_num) hJ hm
  rw [hl] at h
  refine ⟨h, ?_, ?_, ?_⟩
  · unfold ldBaseErr
    rw [hc]
    rfl
  · rw [ZMod.card]
    norm_num
  · rw [Fintype.card_fun, hc, Fintype.card_fin]

end LdBaseTest
end Cb
