-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpFormatAsm.lean: the formats of the assembled lookup.

Statements (in `Cb.Spec`) and proofs, block by block, by the rules of Cb/Ld/LdLkpFormat.lean.
Formats are among what a caller of a lookup asks of it beside completeness and knowledge soundness:
Cb/Ld/LdLkpFormat.lean, Why (what the formats are: the head of Cb/Ld/LdLkpFormat.lean).
The lookup of Cb/Ld/LdLkpAsm.lean (`A : LkAsm E`; `A.baseA` at the base; `A.sub S E₀ Kc Wp msg` over
a signature) is a chain of draws, sumchecks and steps without rounds. No hypothesis is made on A.
It claims that every key is an entry of a table; its parts, in order, are the head (the first
challenge, then the tie), the keys' side and the table's side.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names, at the base:
  `ldLkpFmt_plain`: `A.baseA` is `BkA.Plain` (Cb/Ld/LdLkpFormat.lean): it reads none of its input
    oracles, ties nothing, only copies; its honest prover ends with the witness with which it began;
    every budget is borne; nothing is withheld.
  `ldLkpFmt_pass`: whenever the verifier puts out x', the state in x' is the state with which the
    lookup began.
  The same for the parts: the theorems `plain_tie` to `pass_segT` below.
Over a signature, for `A.sub`:
  `ldLkpFmt_idx`: the further oracles E₀ (an encoded index) are not read, nothing is tied to them,
    they are copied, a symbol of the copy comes from that symbol alone, no other new symbol comes
    from them (`IdxStep`, Cb/Ld/LdWfPre.lean).
  `ldLkpFmt_passes`: state and samples are handed on (`Passes`, Cb/Ld/LdWfPre.lean).
  `ldLkpFmt_same`: the honest prover ends with the witness with which it began; `ldLkpFmt_hands`: so
    it hands on whatever is read off the witness (`Honest.Hands`, Cb/Ld/LdWfPre.lean).
  `ldLkpFmt_need`, `ldLkpFmt_bud`, `ldLkpFmt_bears`: what is needed of the old oracles is what is
    needed of the new ones; every budget is borne (Ior/Bears.lean).
  `ldLkpFmt_free`: nothing is withheld.

Limits: this file says nothing on relations (Cb/Ld/LdLkpAsm.lean). It says nothing on zero
knowledge, and nothing on blindness to the masks of later blocks.
-/
import Cb.Ld.LdLkpFormat
import Cb.Ld.LdLkpAsm

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section Tools
variable {K M : Type} {Ex : ExtSpec} {Wp Rc : Type}

theorem passes_chain (X : ℕ → Type) (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (r : ∀ l, X l → Rc)
    (h : ∀ l, (b l).R.Passes (r l) (r (l + 1))) :
    ∀ n, (BkA.chain X b n).R.Passes (r 0) (r (n + 1))
  | 0 => h 0
  | n + 1 => (passes_chain X b r h n).seq (h (n + 1))

theorem passes_map {X₁ X₂ Rc' : Type} {E₁ E₂ : ExtSpec} {R : IOR X₁ E₁ X₂ E₂} {r : X₁ → Rc}
    {r' : X₂ → Rc} (h : R.Passes r r') (f : Rc → Rc') :
    R.Passes (fun x => f (r x)) fun x => f (r' x) :=
  fun x y τ x' hx => congrArg f (h x y τ x' hx)

end Tools

section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec) (M Wp Kc : Type)

/-! ### The tie -/

theorem plain_tie (D : TieP E) (msg : M → D.J → E) (n : ℕ) : (D.tieA Ex Wp Kc msg n).Plain :=
  plain_chain _ _
    (fun l =>
      plain_postM (plain_psc (D.lv l).T.par Ex Kc M Wp fun w => D.msgAt M msg l w.1) (D.nxt l)) n

theorem pass_tie (D : TieP E) (msg : M → D.J → E) (n : ℕ) :
    (D.tieA Ex Wp Kc msg n).R.Passes (fun x => (D.lv 0).base x.2) fun x =>
      (D.lv (n + 1)).base x.2 :=
  passes_chain (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg) (fun l x => (D.lv l).base x.2) (fun l => (passes_map (psc_passes (D.lv l).T.par Ex) (D.lv l).base).post _ _ fun o x' e => by
    obtain rfl := Option.some.inj e
    rfl) n

/-! ### The tree -/

theorem plain_lev (D : TreeP E) (msg : M → D.J → E) (l : ℕ) : (D.levA Ex Wp Kc msg l).Plain :=
  plain_seq (plain_psc (D.lv l).T.par Ex Kc M Wp fun w => D.msgAt M msg l w.1) (plain_draw _ _ _)

theorem plain_tree (D : TreeP E) (msg : M → D.J → E) (n : ℕ) : (D.treeA Ex Wp Kc msg n).Plain :=
  plain_chain _ _ (plain_lev Ex M Wp Kc D msg) n

theorem pass_lev (D : TreeP E) (msg : M → D.J → E) (l : ℕ) :
    (D.levA Ex Wp Kc msg l).R.Passes (fun x => D.root l x.2) fun x => D.root (l + 1) x.2 :=
  (passes_map (psc_passes (D.lv l).T.par Ex) (D.root l)).seq (Passes.draw _ _ Ex _ _ fun _ _ => rfl)

theorem pass_tree (D : TreeP E) (msg : M → D.J → E) (n : ℕ) :
    (D.treeA Ex Wp Kc msg n).R.Passes (fun x => D.root 0 x.2) fun x => D.root (n + 1) x.2 :=
  passes_chain (fun l => E × (D.lv l).T.St)
    (D.levA Ex Wp Kc msg) (fun l x => D.root l x.2) (pass_lev Ex M Wp Kc D msg) n

/-! ### Head, keys' side, table's side -/

theorem plain_head (H : LkHead E) (msg : M → H.J → E) : (H.headA Ex M Wp Kc msg).Plain :=
  plain_seq (plain_draw _ _ _)
    (plain_preM (plain_tie Ex M Wp Kc H.tie msg H.n) fun x => ((0 : E), x))

theorem pass_head (H : LkHead E) (msg : M → H.J → E) :
    (H.headA Ex M Wp Kc msg).R.Passes id fun x => ((H.tie.lv (H.n + 1)).base x.2).1 :=
  (Passes.draw E Prod.mk Ex id Prod.fst fun _ _ => rfl).seq ((passes_map (pass_tie Ex M Wp Kc H.tie msg H.n) Prod.fst).pre _ _ fun x x' e => by
    obtain rfl := Option.some.inj e
    rfl)

theorem plain_segK (I : LkInst E) (v' : ℕ) (tK : I.X → E) (msg : M → I.J → E) :
    (segK I v' tK Ex M Wp Kc msg).Plain :=
  plain_preM (plain_tree Ex M Wp Kc (I.setV (v' + 1)).DK msg v') (enterK (I.setV (v' + 1)) tK)

theorem pass_segK (I : LkInst E) (v' : ℕ) (tK : I.X → E) (msg : M → I.J → E) :
    (segK I v' tK Ex M Wp Kc msg).R.Passes id (oldK I v') :=
  (passes_map (pass_tree Ex M Wp Kc (I.setV (v' + 1)).DK msg v') Prod.fst).pre _ _ fun x x' e => by
    obtain rfl := Option.some.inj e
    rfl

theorem plain_forest (Q : SegTab E) (msg : M → Q.I.J → E) : ∀ l, (Q.forest Ex Wp Kc msg l).Plain
  | 0 => plain_draw _ _ _
  | l + 1 => plain_seq (plain_forest Q msg l) (plain_lev Ex M Wp Kc Q.D msg l)

theorem pass_forest (Q : SegTab E) (msg : M → Q.I.J → E) :
    ∀ l, (Q.forest Ex Wp Kc msg l).R.Passes id fun x => (Q.D.root l x.2).1
  | 0 => Passes.draw _ _ Ex _ _ fun _ _ => rfl
  | l + 1 => (pass_forest Q msg l).seq (passes_map (pass_lev Ex M Wp Kc Q.D msg l) Prod.fst)

theorem plain_segT (Q : SegTab E) (msg : M → Q.I.J → E) : (Q.segT Ex Wp Kc msg).Plain :=
  plain_seq (plain_seq (plain_forest Ex M Wp Kc Q msg Q.I.d)
      (plain_psc Q.En.psc.par Ex Kc M Wp fun w => msg w.1))
    (plain_seq (plain_draw _ _ _) (plain_psc Q.Bt.zc.next.par Ex Kc M Wp fun w => msg w.1))

theorem pass_segT (Q : SegTab E) (msg : M → Q.I.J → E) : (Q.segT Ex Wp Kc msg).R.Passes id Q.oldT :=
  ((pass_forest Ex M Wp Kc Q msg Q.I.d).seq
      (passes_map (psc_passes Q.En.psc.par Ex) fun s => (Q.D.root Q.I.d s).1)).seq
    ((Passes.draw _ _ Ex (fun oE : Q.XE => (Q.D.root Q.I.d oE.st).1)
        (fun x : E × Q.Bt.zc.next.St => (Q.D.root Q.I.d x.2.1.st).1) fun _ _ => rfl).seq
      (passes_map (psc_passes Q.Bt.zc.next.par Ex) fun s : Q.Bt.zc.next.St =>
        (Q.D.root Q.I.d s.1.st).1))

end

/-! ## The statements on the assembled lookup -/

namespace Spec
variable (E : Type) [Field E] [Fintype E]

def ldLkpFmt_plain : Prop :=
  ∀ (A : LkAsm E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseA Ex M Wp Kc msg).Plain
def ldLkpFmt_pass : Prop :=
  ∀ (A : LkAsm E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseA Ex M Wp Kc msg).R.Passes id fun x' => x'.1

/-- The further oracles are not read, not tied, copied. -/
def ldLkpFmt_idx : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E),
    (A.sub S E₀ Kc Wp msg).R.IdxStep
/-- State and samples are handed on. -/
def ldLkpFmt_passes : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E),
    (A.sub S E₀ Kc Wp msg).R.Passes (fun x => x) fun x => (x.1.1, x.2)
/-- The honest prover ends with the witness with which it began. -/
def ldLkpFmt_same : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) w x c ρ,
    (((A.sub S E₀ Kc Wp msg).H.strat w x c).run ρ).2.2 = w
def ldLkpFmt_hands : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp Pw : Type) (msg : S.Msg → A.J → E)
      (Ri : A.St × S.Smp → (E₀.prod S.ext).Str → S.Wit × Wp → Prop) (px : S.Wit × Wp → Pw),
    (A.sub S E₀ Kc Wp msg).H.Hands Ri px px
/-- What is needed of the old oracles is what is needed of the new ones; `ldLkpFmt_bud`,
`ldLkpFmt_bears`: every budget is borne. -/
def ldLkpFmt_need : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) ρ U,
    (A.sub S E₀ Kc Wp msg).R.need ρ U = U
def ldLkpFmt_bud : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) ρ T,
    (A.sub S E₀ Kc Wp msg).P.bud ρ T
def ldLkpFmt_free : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) w x,
    (A.sub S E₀ Kc Wp msg).H.withheld w x = ∅
def ldLkpFmt_bears : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E)
      (q : Finset (E₀.prod S.ext).Pos → Prop),
    (A.sub S E₀ Kc Wp msg).R.Bears (A.sub S E₀ Kc Wp msg).P.bud q q

end Spec

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpFmt_plain : Spec.ldLkpFmt_plain E := fun A Ex M Wp Kc msg =>
  plain_postM (plain_seq
    (plain_seq (plain_head Ex M Wp Kc A.H msg) (plain_segK Ex M Wp Kc A.IK A.v' A.tK msg))
    (plain_segT Ex M Wp Kc A.Q msg)) A.rd

theorem ldLkpFmt_pass : Spec.ldLkpFmt_pass E := fun A Ex M Wp Kc msg =>
  (((pass_head Ex M Wp Kc A.H msg).seq
    (passes_map (pass_segK Ex M Wp Kc A.IK A.v' A.tK msg) fun x => (A.b2 x).1)).seq
    (passes_map (pass_segT Ex M Wp Kc A.Q msg) fun x => (A.b2 (A.o4 x)).1)).post _ _ fun o x' e => by
      obtain rfl := Option.some.inj e
      rfl

theorem ldLkpFmt_idx : Spec.ldLkpFmt_idx E := fun A S E₀ Kc Wp msg =>
  lift_idxStep S (ldLkpFmt_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt_passes : Spec.ldLkpFmt_passes E := fun A S E₀ Kc Wp msg =>
  lift_passes S (ldLkpFmt_pass E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt_same : Spec.ldLkpFmt_same E := fun A S E₀ Kc Wp msg =>
  lift_keepsW S (ldLkpFmt_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt_hands : Spec.ldLkpFmt_hands E := fun A S E₀ Kc Wp _ msg Ri px =>
  lift_hands S (ldLkpFmt_plain E A E₀ S.Msg Wp Kc msg) Ri px
theorem ldLkpFmt_need : Spec.ldLkpFmt_need E := fun A S E₀ Kc Wp msg =>
  lift_need S (ldLkpFmt_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt_bud : Spec.ldLkpFmt_bud E := fun A S E₀ Kc Wp msg =>
  lift_bud S (ldLkpFmt_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt_free : Spec.ldLkpFmt_free E := fun A S E₀ Kc Wp msg =>
  lift_free S (ldLkpFmt_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt_bears : Spec.ldLkpFmt_bears E := fun A S E₀ Kc Wp msg =>
  lift_bears S (ldLkpFmt_plain E A E₀ S.Msg Wp Kc msg)

end
end Cb
