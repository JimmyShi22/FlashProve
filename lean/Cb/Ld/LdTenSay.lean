-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTenSay.lean: for toys: the prover says the masked values of tensor forms on the encoded
index: so tensor rows with mask forms and public targets come to stand.

In standard terms: a one-round interactive oracle reduction for small example instances: for each of
finitely many claims the prover sends the value of a linear form on the messages' entries
(`BattPar.lhs`, Cb/Ld/LdBatt.lean), and the new statement takes these values as the claims' targets.

Definitions, statements (in `Cb.Spec`) and proofs.
No block of a write-up of ours (lean/CREDITS.md): a stand-in, in a toy, for the end of a
sumcheck at a map of the index. There a tensor row with a mask form and a public target is what a
sumcheck leaves. The batching of tensor rows (Cb/Ld/LdBatt.lean, Cb/Req1/LdSegRefTen.lean) takes
such rows as given; a guard that runs it on a row which reads the index needs something that makes
one.

The protocol. For each name q of a claim: a public row vector and a public point (functions of the
state), and a mask form. One round: the prover says, in the clear, for each q the value
< row vector ⊗ eq(point, ·), matrix > + < mask form, entries >; the verifier sends nothing, reads
nothing, never rejects.
Nothing is claimed of these values before. So knowledge soundness is the identity with the error 0:
whatever is said, a witness of the new statement is one of the old.
Zero knowledge: the item "masked messages" (Ior/Masked.lean). Each claim has a mask entry of its
own, κ q, sent earlier: its own form reads it with the coefficient 1, no other claim's form reads
it, it is no entry of the matrix (`B.SayOK κ Rd`, which has two fields more, `rdM`, `rdS`, on what
is read: see the structure below). Then over uniform own entries, all else fixed, the values said
are uniform: the simulator draws them.

Main names:
  `B.say`, `B.sayH`, `B.sayN`, `B.sayD κ Rd`: at the base, in the parameters of Cb/Ld/LdBatt.lean
    (`B : BattPar`): from any joint A0 on (state, oracles, witness) to `B.baseIn A0`: the joint at
    which the batching starts.
  `Spec.ldTenSay_goodAt`: `GoodAt` (Cb/Ld/LdSigLift.lean) of that block, without hypothesis.
    `Spec.ldTenSay_mm`: see its statement.
    `H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the
    honest prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under
    `D.put`; and where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the
    distribution `D.sim xp ρ`. Here `H.MM D` is the conclusion of `Spec.ldTenSay_mm`, under
    `B.SayOK κ Rd`.
    `GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every
    (x, y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here `GoodM` is the conclusion
    of `Spec.ldTenSay_goodM`, under `X.SayOK κ` (there of a link: `Link.GoodM`,
    Ior/KnowCollRulesChain.lean, which unfolds to it).
  `X.p1`, `X.sayLink`, `X.sayMask κ`: over the oracle messages of a stage, the index decoded by the
    statement (`X : LdTenD`, Cb/Req1/LdSegRefTen.lean): from `X.p1` to `X.m0`, the stage at which
    the batching's block starts.
  `Spec.ldTenSay_goodM`: `X.sayLink` is a masked block, with the letters `X.sayMask κ`, from
    `X.SayOK κ`: conditions on places and on the functions mf: κ injective into the names, μAt
    injective on them, mf st q (κ q) = 1, mf st q (κ q') = 0 for q' other than q; the places are
    read. These two clauses on mf are asked at all states: they are met only if the coefficients at
    the names κ q do not depend on free data of the state (constant readers, as at the toy); with
    coefficients filed in the state they fail.
  `X.stepBack`, `X.sayT`, `Spec.ldTenSay_prog`: the two moves, from `X.p1` to `X.src`, the stage at
    which the last three moves of a request start (Cb/Obj/LdObjectReqEnd.lean): hypotheses, what
    honest-verifier zero knowledge asks (the own entries are fresh before the block), beside their
    hypotheses
    (`X.sayT.Hyp`), kinds, in this sense: under `X.SayOK κ`:
      `X.sayT.Hyp`;
      `X.sayT.Zk base` for every `base` with `base (X.sayMask κ).fact`;
      `X.sayT.All fun t => t = .sub ∨ t = .step`.

Limits: this file does not say that the own entries are fresh when the block begins.
It says nothing on where row vectors and points come from.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdSegRefTenProofs
import Cb.Ld.LdSplitProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

namespace BattPar
variable {E : Type} [Field E] [Fintype E] (B : BattPar E) (Ex : ExtSpec)

/-- The prover says the left sides. -/
def say : IOR B.St Ex ((B.Q → E) × B.St) Ex := ldSay (0 : B.Q → E) (fun st a => (a, st)) Ex
def sayH {Wt : Type} (msg : Wt → B.J → E) : (B.say Ex).Honest Wt Wt :=
  ldSayH (0 : B.Q → E) (fun st a => (a, st)) Ex fun w st q => B.lhs st q (msg w)
def sayN (Kc : Type) : Nums Kc (B.say Ex) := ldSayN (0 : B.Q → E) (fun st a => (a, st)) Ex Kc

/-- Each claim has a mask entry of its own. -/
structure SayOK (κ : B.Q → B.J) (Rd : B.J → Prop) : Prop where
  inj : Function.Injective κ
  own : ∀ st q, B.slM q st (κ q) = 1
  oth : ∀ st q q', q' ≠ q → B.slM q st (κ q') = 0
  mat : ∀ q a, κ q ≠ B.mAt a
  rdM : ∀ a, Rd (B.mAt a)
  rdS : ∀ q st j, ¬ Rd j → B.slM q st j = 0

open Classical in
/-- The letters of the item "masked messages". -/
def sayD {Wt : Type} (msg : Wt → B.J → E) (κ : B.Q → B.J) (Rd : B.J → Prop) :
    MaskData (B.say Ex) Wt where
  Kc  := B.J → E
  kc  := fun w j => if Rd j then msg w j else 0
  Xp  := B.St
  pub := fun st => st
  Mk  := B.Q → E
  put := fun M k => Function.extend κ M k
  Cl  := fun _ _ => True
  msg := fun k st _ => (((fun q => B.lhs st q k), ()) : (B.Q → E) × Unit)
  sim := fun _ _ => (unif (B.Q → E)).map fun u => ((u, ()) : (B.Q → E) × Unit)

end BattPar

namespace LdTenD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)

/-- the stage before the values are said: the rows that ride along, and what else is claimed -/
@[reducible] def p1 : LdStage E Kc :=
  ⟨X.S, X.Xr × X.St, X.C.E0, X.C.PIdx × X.Wp, idxAt X.C (fun x => X.rc x.2) X.A1⟩

/-- The block's link. -/
def sayLink : Link Kc X.p1.J X.m0.J :=
  X.p1.lift X.m0.A (X.bt.say X.C.E0)
    (idxH X.C (X.bt.sayH X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1))
    (idxExt X.C fun _ _ _ wp => wp) (X.bt.sayN X.C.E0 Kc)

/-- The conditions: on places and on the functions of the state. -/
structure SayOK (κ : X.Q → X.Nm) : Prop where
  inj  : Function.Injective κ
  injP : Function.Injective X.μAt
  own  : ∀ st q, X.mf st q (κ q) = 1
  oth  : ∀ st q q', q' ≠ q → X.mf st q (κ q') = 0
  rdM  : ∀ a, X.Rd (X.μAt a)

def sayMask (κ : X.Q → X.Nm) : MaskData X.sayLink.R X.p1.J.W :=
  idxMask X.C X.S
    (X.bt.sayD X.C.E0 (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)
      (fun q => Sum.inr (X.μAt (κ q))) X.RdJ)

/-- a step without rounds: the rows come out again: to the stage `X.src`, "rows on all entries,
beside the claims on the index" -/
def stepBack : LdMv X.m0 X.src :=
  .step X.m0 X.src (sideF X.S fun x => (x.2.1, (x.1, x.2.2))) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB X.S fun _ w => w.2)

/-- The values are said; the rows come out: from `X.p1` to `X.src`. -/
def sayT : LdProg X.p1 X.src :=
  ((LdProg.nil X.p1).snoc (.sub X.p1 X.m0 (.one X.sayLink))).snoc X.stepBack

end LdTenD

namespace Spec

def ldTenSay_goodAt : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (B : BattPar E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E),
    GoodAt (B.say Ex) (B.sayH Ex fun w : M × Wp => msg w.1) A0 (B.baseIn Ex A0 fun w => msg w.1)
      (fun _ _ _ wp => wp) (B.sayN Ex Kc)

def ldTenSay_mm : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (B : BattPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → B.J → E)
      (κ : B.Q → B.J) (Rd : B.J → Prop),
    B.SayOK κ Rd → (B.sayH Ex msg).MM (B.sayD Ex msg κ Rd)

/-- Under the hypotheses below, the block is a masked block. -/
def ldTenSay_goodM : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (κ : X.Q → X.Nm),
    X.SayOK κ → X.sayLink.GoodM (X.sayMask κ)

/-- The two moves: what is asked of them; what zero knowledge asks, beside their hypotheses; their
kinds. -/
def ldTenSay_prog : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (κ : X.Q → X.Nm), X.SayOK κ →
    X.sayT.Hyp ∧
    (∀ base : MaskFact X.p1.J.W → Prop, base (X.sayMask κ).fact → X.sayT.Zk base) ∧
    X.sayT.All fun t => t = .sub ∨ t = .step

end Spec

theorem ldTenSay_goodAt : Spec.ldTenSay_goodAt := by
  intro E _ _ B Ex M Wp Kc A0 msg
  refine ⟨⟨((Blocks.plainPoint (B.Q → E) Unit 0, ()) : (sayRound (B.Q → E) 0).IsPoint × Unit)⟩,
    ⟨fun x y y' τ τ' _ hpl _ _ => ?_,
      fun y y' τ τ' p _ _ hE _ => hE p (Finset.mem_singleton_self p)⟩,
    fun x y w c ρ hR _ => ⟨rfl, hR, fun _ => rfl⟩,
    ?_, fun _ _ _ _ => rfl,
    prRho_empty _ fun _ h => h,
    fun _ _ => le_refl _,
    fun _ => prRho_empty _ fun _ h => h,
    fun _ _ _ _ => rfl, ?_⟩
  · have e : said τ = said τ' :=
      congrArg (fun r : Plains [sayRound (B.Q → E) 0] => (show (B.Q → E) × Unit from r).1) hpl
    show some ((said τ, x) : (B.Q → E) × B.St) = some (said τ', x)
    rw [e]
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = ((said τ, a.1), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e]
    exact ha
  · intro m a ha mm
    refine Nat.le_of_eq (cnt_false fun c hc => hc fun b w hb hw => ?_)
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = ((mm.2, a.1), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e] at hw
    exact hw.1

/-- a form at entries overwritten at injective places -/
theorem sum_extend {E Q J : Type} [Field E] [Fintype Q] [Fintype J] (κ : Q → J)
    (hκ : Function.Injective κ) (f : J → E) (M : Q → E) (k : J → E) :
    ∑ j, f j * Function.extend κ M k j =
      ∑ j, f j * Function.extend κ (fun _ => 0) k j + ∑ q, f (κ q) * M q := by
  classical
  have h1 : ∑ q, f (κ q) * M q = ∑ j, f j * Function.extend κ M (fun _ => 0) j := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image κ)) (fun j _ hj => by
      rw [Function.extend_apply' _ _ _ (fun ⟨q', e⟩ => hj (Finset.mem_image.2 ⟨q', Finset.mem_univ _, e⟩)), mul_zero]), Finset.sum_image (fun a _ b _ h => hκ h)]
    exact Finset.sum_congr rfl fun q' _ => by rw [hκ.extend_apply]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add]
  congr 1
  by_cases hj : ∃ q, κ q = j
  · obtain ⟨q, rfl⟩ := hj
    rw [hκ.extend_apply, hκ.extend_apply, hκ.extend_apply, zero_add]
  · rw [Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj,
      Function.extend_apply' _ _ _ hj, add_zero]

theorem ldTenSay_mm : Spec.ldTenSay_mm := by
  classical
  intro E _ _ B Ex Wt msg κ Rd h
  refine ⟨⟨fun p => p.elim (fun q => q.elim) fun q => q.elim⟩,
    fun _ _ => Set.union_self _,
    fun w x c ρ => ?_,
    fun _ _ _ _ => trivial,
    fun k st ρ _ => ?_⟩
  · show (((fun q => B.lhs x q (msg w)), ()) : (B.Q → E) × Unit) =
      ((fun q => B.lhs x q fun j => if Rd j then msg w j else 0), ())
    refine congrArg (fun u : B.Q → E => ((u, ()) : (B.Q → E) × Unit)) (funext fun q => ?_)
    exact (B.lhs_congr (fun a => if_pos (h.rdM a)) fun j hj =>
      if_pos (by by_contra hr; exact hj (h.rdS q x j hr))).symm
  · have key : ∀ (M : B.Q → E) q, B.lhs st q (Function.extend κ M k) =
        B.lhs st q (Function.extend κ (fun _ => 0) k) + M q := by
      intro M q
      have hc : B.col (Function.extend κ M k) (B.g st q) =
          B.col (Function.extend κ (fun _ => 0) k)
            (B.g st q) := funext fun c => Finset.sum_congr rfl fun r _ => by
        rw [Function.extend_apply' _ _ _ (fun ⟨q', e⟩ => h.mat q' _ e),
          Function.extend_apply' _ _ _ (fun ⟨q', e⟩ => h.mat q' _ e)]
      have hs : ∑ q', B.slM q st (κ q') * M q' = M q := by
        rw [Finset.sum_eq_single q (fun q' _ hq => by rw [h.oth st q q' hq, zero_mul])
              (fun hq => absurd (Finset.mem_univ q) hq),
          h.own, one_mul]
      unfold BattPar.lhs BattPar.ten
      rw [hc, sum_extend κ h.inj (B.slM q st) M k, hs, add_assoc]
    have e : (fun M : B.Q → E =>
          (((fun q => B.lhs st q (Function.extend κ M k)), ()) : (B.Q → E) × Unit)) =
        (fun u : B.Q → E => ((u, ()) : (B.Q → E) × Unit)) ∘
          fun M : B.Q → E => (fun q => B.lhs st q (Function.extend κ (fun _ => 0) k)) + M := by
      funext M
      exact congrArg (fun u : B.Q → E => ((u, ()) : (B.Q → E) × Unit)) (funext fun q => key M q)
    show (unif (B.Q → E)).map (fun M : B.Q → E =>
        (((fun q => B.lhs st q (Function.extend κ M k)), ()) : (B.Q → E) × Unit)) =
      (unif (B.Q → E)).map fun u => ((u, ()) : (B.Q → E) × Unit)
    rw [e, ← PMF.map_comp, map_unif_of_bijective (AddGroup.addLeft_bijective _)]

/-- coefficients laid at injective places -/
theorem placed_inj {I J E : Type} [Fintype I] [DecidableEq J] [AddCommMonoid E] (at' : I → J)
    (h : Function.Injective at') (a : I → E) (x : I) :
    RngPk.placed at' a (at' x) = a x := by
  classical
  unfold RngPk.placed
  rw [Finset.sum_eq_single x (fun y _ hy => if_neg fun e => hy (h e))
        (fun hx => absurd (Finset.mem_univ x) hx), if_pos rfl]

theorem placed_off {I J E : Type} [Fintype I] [DecidableEq J] [AddCommMonoid E] (at' : I → J)
    (a : I → E) (n : J) (h : ∀ x, at' x ≠ n) : RngPk.placed at' a n = 0 :=
  Finset.sum_eq_zero fun x _ => if_neg (h x)

open Classical in
theorem LdTenD.sayOK_base {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)
    (κ : X.Q → X.Nm) (h : X.SayOK κ) :
    X.bt.SayOK (fun q => Sum.inr (X.μAt (κ q))) X.RdJ where
  inj := fun _ _ e => h.inj (h.injP (Sum.inr_injective e))
  own := fun st q => (placed_inj X.μAt h.injP _ _).trans (h.own st.2 q)
  oth := fun st q q' hq => (placed_inj X.μAt h.injP _ _).trans (h.oth st.2 q q' hq)
  mat := fun _ _ e => Sum.inr_ne_inl e
  rdM := fun _ => trivial
  rdS := fun q st j hj => by
    cases j with
    | inl a => exact absurd trivial hj
    | inr n => exact placed_off X.μAt _ n fun a e => hj (e ▸ h.rdM a)

theorem ldTenSay_goodM : Spec.ldTenSay_goodM := by
  intro E Kc _ _ X κ h
  have gM := idxLift_goodM E X.C X.S Kc _ _ X.Wp X.Wp (X.bt.say X.C.E0)
    (X.bt.sayH X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1) X.A1
    (X.bt.baseIn X.C.E0 X.A1 fun w => X.msg w.1)
    (fun x => X.rc x.2) (fun x => X.rc x.2.2) (fun _ _ _ wp => wp) (X.bt.sayN X.C.E0 Kc)
    (X.bt.sayD X.C.E0 (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)
      (fun q => Sum.inr (X.μAt (κ q))) X.RdJ)
    (fun x y τ z hz => by
      obtain rfl := Option.some.inj hz
      rfl) (fun _ _ => rfl) (ldTenSay_goodAt E X.bt X.C.E0 (X.C.Msg × X.S.Msg) X.Wp Kc X.A1 X.msg)
    (ldTenSay_mm E X.bt X.C.E0 _ _ _ X.RdJ (X.sayOK_base κ h)) (fun _ _ _ _ => trivial)
  exact ldSeg_sub_goodM E Kc X.p1 X.m0 X.sayLink (X.sayMask κ) gM

theorem LdTenD.stepBack_hyp {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc) :
    X.stepBack.Hyp :=
  ldSeg_step E Kc X.m0 X.src _ _ _ _
    (ldPeel_base E Kc _ _ _ _ X.S X.C.E0 X.C.E0 X.m0.A X.src.A (fun x => (x.2.1, (x.1, x.2.2)))
      (ExtMap.id X.C.E0) (fun _ w => w.2) (fun _ w => w.2) (extMap_isLocal.1 _)
    (fun _ _ _ hw => ⟨hw.2.1.1, hw.1, hw.2.1.2, hw.2.2⟩) (fun _ _ hh => hh) (fun _ _ => rfl)
    (fun _ _ _ _ hw => by
      obtain ⟨hr, U, hU, ha, ht⟩ := hw
      exact ⟨U, hU, ⟨hr, ha⟩, ht⟩))

theorem ldTenSay_prog : Spec.ldTenSay_prog := by
  intro E Kc _ _ X κ h
  have g := ldTenSay_goodM E Kc X κ h
  refine ⟨?_, fun base hb => ?_, ?_⟩
  · unfold LdTenD.sayT
    rw [LdProg.hyp_snoc, LdProg.hyp_snoc]
    exact ⟨⟨LdProg.hyp_nilK _, (Chain.allB_one X.sayLink).2 g.base⟩, X.stepBack_hyp⟩
  · unfold LdTenD.sayT
    rw [LdProg.zk_snoc, LdProg.zk_snoc, LdProg.after_nil]
    refine ⟨⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩, ?_⟩
    · rw [LdMv.Zk]
      exact (Chain.okGiven_one X.sayLink _).2 (Or.inr ⟨X.sayMask κ, g, hb⟩)
    · unfold LdTenD.stepBack
      rw [LdMv.Zk]
      trivial
  · unfold LdTenD.sayT
    rw [LdProg.all_snoc, LdProg.all_snoc]
    exact ⟨⟨LdProg.all_nilK _ _, Or.inl rfl⟩, Or.inr rfl⟩

end Cb
