-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PayAttention.lean: THE ASSEMBLY OF THE KINDS' LAWS AT AN ATTENTION LINK:
`LinkOwes`' four duties on the runs and its hφ (Johnson/Desc/First/Link/Law/LinkOwes.lean), PAID at
the one closed φ, as far as the kinds' laws on their runs reach today. One structure of what they
take, and theorems. The like of PayLayers.lean and PayHead.lean.

What is said.
  `tmA`, `lenA`: the table of terms by the entries of attention's order. `AttTake`: what the laws
    take: THE TIES, UP TO A GUARD (`Under`; `AttTies`: a list of their own): attention's three runs
    «first», «keys», «second»; the smallness test's three functions; the lookup's «guests» under the
    idle run · a reader of φ for what attention's runs see beside the ledger · THE NAMED PREMISES ON
    Ok AND Fu · the equations' first four claims · AND, AS THEY STAND, THE FOUR DUTIES OF THE
    LOOKUP's RUNS «objects» (blocks 1 and 6), «planes» and «join».
  `att_pair`: hψ and hrd can be met together. `pay_att`, `payd_att`, `quiet_att`, `quietd_att`,
    `phi_att`: **the five fields of `LinkOwes` at an attention link.**

Limits. AN IMPLICATION: `AttTake` is shown of no record. It closes φ alone, and one φ a link (u is
that link's record); Ok and Fu stay letters. Every premise on them here is an upper bound («Ok q →
…», «Fu t → …»): they cannot cross each other; whether they can be met is decided where `LinkOwes`
asks the lower bounds: `hready` and `hend`. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Att.Claims.K5Still

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail (UnitRow)
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows
open VerifiableInference.Desc.First.TailClaims (rkSelfTestP)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)
open K5Law

variable {β : Type}

/-- The terms by the entries of attention's order. t3: the lookup's runs' terms, by entry. -/
noncomputable def tmA (rd : Phi β → Option (Forest.Heard × Heard)) (c : ParC)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (o : ℕ × String) :
    ℕ → Q β → Bound GE8 → List (ℕ × GE8) :=
  if o.2 == "first" then plainTm (valsStill Reading.gl (fsFirst rd c) ent)
  else if o.2 == "keys" then plainTm (valsStill Reading.gl fsKeys ent)
  else if o.2 == "second" then plainTm (valsStill Reading.gl (fsSecond rd c) ent)
  else if o.2 == "K8.equations" then fun n q y => tm4 n q y ++ tmRest pi8 q y
  else if o.2 == "guests" then plainTm (valsStill Reading.gl fsNone ent)
  else t3 o

/-- The numbers of claims by the entries of attention's order. -/
noncomputable def lenA (rd : Phi β → Option (Forest.Heard × Heard)) (c : ParC)
    (l3 : ℕ × String → Q β → ℕ) (o : ℕ × String) : Q β → ℕ :=
  if o.2 == "first" then lenStill (fsFirst rd c)
  else if o.2 == "keys" then lenStill fsKeys
  else if o.2 == "second" then lenStill (fsSecond rd c)
  else if o.2 == "K8.equations" then len8 pi8
  else if o.2 == "guests" then lenStill fsNone
  else l3 o

/-- **THE TIES**: which run stands at an entry of the orders, up to a guard. -/
structure AttTies (L : Link S Claim) (c : ParC) (nU : Array ℕ) :
    Prop where
  /-- TIE: the run at (2, "first") stands under attention's -/
  tFirst : ∀ run, At L (2, "first") run → Under run (runFirst c)
  /-- TIE: the run at (2, "keys") -/
  tKeys : ∀ run, At L (2, "keys") run → Under run (runKeys c)
  /-- TIE: the run at (2, "second") -/
  tSecond : ∀ run, At L (2, "second") run → Under run (runSecond c)
  /-- TIE: the runs at (1, "guests") and (6, "guests") stand under the run that returns no claim and
  hands the record back -/
  tGuests : ∀ k ∈ [1, 6], ∀ run, At L (k, "guests") run → Under run idle0
  /-- TIE: the run at (4, "K8.equations") -/
  tEq : ∀ run, At L (4, "K8.equations") run → Under run k8Run.2
  /-- TIE: the run behind the batching at (4, "K8.lsTail") -/
  tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail
  /-- TIE: the run behind the batching at (4, "K8.tests") -/
  tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)

/-- **WHAT THE KINDS' LAWS TAKE AT AN ATTENTION LINK.** -/
structure AttTake (L : Link S Claim) (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (Fu : S → Prop)
    (rd : Phi β → Option (Forest.Heard × Heard)) (c : ParC) (nU : Array ℕ)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) :
    Prop where
  /-- TIES: which run stands at an entry, up to a guard -/
  ties : AttTies L c nU
  /-- the further kinds' letter rests under the writings behind the draw -/
  hψ : Rests u ψ
  /-- φ shows what attention's runs see beside the ledger -/
  hrd : ∀ e, rd (phiAll u ψ e) = psiAtt e
  /-- ON Ok, for "first" and "second" -/
  okK5 : ∀ q v g h, Ok q → q.2 = some v → rd q.1 = some (g, h) → K5OkAt c g.zk h v.F
  /-- ON Ok, for the equations -/
  okEq : ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb → OnBytes.Tie.Pv.Tail.Port.Fits tlb
  /-- ON Fu, for "first": the entries that its forms name -/
  fuFirst : ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    fsFirst rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx
  /-- ON Fu, for "second" -/
  fuSecond : ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    fsSecond rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx
  /-- ON Fu, for the equations: at a full state that goes on from q -/
  fuEq : ∀ q t b ts funs, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    t.tl? = some ts → t.funs? = some funs →
    rkSelfTestP ts b.F = .ok () ∧
      (b.F.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2 ∧
      ∀ x ∈ readsList ts funs, UnitRow b.F (uOf ts x.1) ∧
        ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU b.F (uOf ts x.1)
  /-- the equations' first four claims -/
  h4 : ∀ q front e a c' e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
    k8Run.2 front e = .ok (c', e₁) →
    ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok Fu) e₁ t → Fu t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c'.take 4) =
        termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  /-- AS IT STANDS: RunOk of the lookup's runs "objects" (both blocks), "planes" and "join" -/
  k3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run →
    RunOk Reading.gl atS (O9 (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o)
  /-- AS IT STANDS: these four keep the door -/
  k3d : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run →
    ∀ n e c' e₁, run n e = .ok (c', e₁) → KeepsDoor atS e e₁

/-- **hψ AND hrd CAN BE MET TOGETHER**: lay what attention's runs see into the free field of φ,
beside the other kinds' letter. -/
theorem att_pair {γ : Type} (u : HTailF2) {ψ' : S → γ} (hψ' : Rests u ψ') :
    Rests u (fun s => (psiAtt s, ψ' s)) ∧
      ∀ e, (phiAll u (fun s => (psiAtt s, ψ' s)) e).more.1 = psiAtt e :=
  ⟨rests_pair u (rests_att u) hψ', fun _ => rfl⟩

variable {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
  {rd : Phi β → Option (Forest.Heard × Heard)} {c : ParC} {nU : Array ℕ}
  {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- **hφ AT THE CLOSED φ.** -/
theorem phi_att (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) (s : S) (a : K9.Part) :
    phiAll u ψ (atS.set s a) = phiAll u ψ s := phi_set u ψ A.hψ s a

/-- **hpay AT AN ATTENTION LINK.** -/
theorem pay_att (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderOf .attention, ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run
        (tmA rd c ent tm4 t3 o) (lenA rd c l3 o) := by
  rw [order_attention]
  refine ⟨A.k3 _ (by simp),
    fun run hr => runOk_under _ _ _ _ (A.ties.tGuests 1 (by simp) run hr)
      (idle_runOk Reading.gl _ Ok Fu (fun _ _ => rfl) ent),
    fun run hr => ?_, fun run hr => ?_, A.k3 _ (by simp), fun run hr => ?_, A.k3 _ (by simp),
    A.k3 _ (by simp),
    fun run hr => runOk_under _ _ _ _ (A.ties.tGuests 6 (by simp) run hr)
      (idle_runOk Reading.gl _ Ok Fu (fun _ _ => rfl) ent),
    fun run hr => ?_⟩
  · exact runOk_under _ _ _ _ (A.ties.tFirst run hr)
      (first_runOk (phiAll u ψ) Ok rd c A.hrd A.okK5 Reading.gl Fu ent A.fuFirst)
  · exact runOk_under _ _ _ _ (A.ties.tKeys run hr) (keys_runOk (phiAll u ψ) Ok c Reading.gl Fu ent)
  · exact runOk_under _ _ _ _ (A.ties.tSecond run hr)
      (second_runOk (phiAll u ψ) Ok rd c A.hrd A.okK5 Reading.gl Fu ent A.fuSecond)
  · exact runOk_under _ _ _ _ (A.ties.tEq run hr)
      (k8_runOk (phiAll u ψ) Ok Fu u pi8 (fun s => phi_k8_pi u ψ s)
        (fun s tl tl' F1 h1 h2 => phi_k8_keep u ψ A.hψ s tl tl' F1 h1 h2) A.okEq A.fuEq tm4 A.h4)

/-- **hpayd AT AN ATTENTION LINK.** -/
theorem payd_att (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderOf .attention, ∀ run, At L o run →
      ∀ n e c' e₁, run n e = .ok (c', e₁) → KeepsDoor atS e e₁ := by
  rw [order_attention]
  refine ⟨A.k3d _ (by simp),
    fun run hr => door_under atS (A.ties.tGuests 1 (by simp) run hr) (idle_door fun _ _ => rfl),
    fun run hr => ?_, fun run hr => ?_, A.k3d _ (by simp), fun run hr => ?_, A.k3d _ (by simp),
    A.k3d _ (by simp),
    fun run hr => door_under atS (A.ties.tGuests 6 (by simp) run hr) (idle_door fun _ _ => rfl),
    fun run hr => ?_⟩
  · exact door_under atS (A.ties.tFirst run hr)
      (still_door (phiAll u ψ) Ok _ _ (still_first (phiAll u ψ) Ok rd c A.hrd A.okK5))
  · exact door_under atS (A.ties.tKeys run hr)
      (still_door (phiAll u ψ) Ok _ _ (still_keys (phiAll u ψ) Ok c))
  · exact door_under atS (A.ties.tSecond run hr)
      (still_door (phiAll u ψ) Ok _ _ (still_second (phiAll u ψ) Ok rd c A.hrd A.okK5))
  · exact door_under atS (A.ties.tEq run hr) fun n e c' e₁ hr => k8Run_door n e e₁ c' hr

/-- **hquiet AT AN ATTENTION LINK.** -/
theorem quiet_att (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderAfterOf .attention, ∀ run, AtAfter L o run →
      QuietOk atS (O9 (K := GE8) (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run := by
  rw [after_attention]
  refine ⟨fun run hr => ?_, fun run hr => ?_⟩
  · exact quietOk_under _ _ _ (A.ties.tLs run hr) (k8_lsTail_quietOk (phiAll u ψ) Ok Fu u
      fun s tl tl' h1 h2 => phi_k8_keepT u ψ A.hψ s tl tl' h1 h2)
  · exact quietOk_under _ _ _ (A.ties.tTests run hr) (k8_tests_quietOk (phiAll u ψ) Ok Fu u
      (fun s tl tl' F1 h1 h2 => phi_k8_keep u ψ A.hψ s tl tl' F1 h1 h2) nU)

/-- **hquietd AT AN ATTENTION LINK.** -/
theorem quietd_att (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderAfterOf .attention, ∀ run, AtAfter L o run →
      ∀ e e₁, run e = .ok e₁ → KeepsDoor atS e e₁ := by
  rw [after_attention]
  refine ⟨fun run hr => ?_, fun run hr => ?_⟩
  · exact doorAfter_under atS (A.ties.tLs run hr) k8LsTail_door
  · exact doorAfter_under atS (A.ties.tTests run hr) (k8Tests_door nU)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.att_pair
#print axioms VerifiableInference.Desc.LinkJoin.phi_att
#print axioms VerifiableInference.Desc.LinkJoin.pay_att
#print axioms VerifiableInference.Desc.LinkJoin.payd_att
#print axioms VerifiableInference.Desc.LinkJoin.quiet_att
#print axioms VerifiableInference.Desc.LinkJoin.quietd_att
