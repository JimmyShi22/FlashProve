-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RunsPaid.lean: THE LIST "runs" (`OwesRuns`, LinkOwes.lean: the kinds'
laws on their runs: hφ, hpay, hpayd, hquiet, hquietd) INSIDE THE FIELD A OF THE ONE LIST OF WHAT IS
LEFT OF A LINK's LAW (LinkList.lean), A SORT OF LINK AT A TIME, AT ANY Ok THAT HOLDS THE SORT's
NAMED Ok (OkOne.lean), AT Fu := FullAt nU AND ent := entUnit. Theorems: assemblies.

How. runs_layers, runs_attention, runs_head (LinkLawAt.lean) give OwesRuns from a
sort's "Take" (`LayersTake`, `AttTake`, `HeadTake`: 11, 11 and 14 fields). By a search over the
library's sources in a state that may differ from the one that ships, and over the folders of the
files on a link's law, EVERYBODY TAKES A Take AND NOBODY ENDS IN ONE. Here the three are built.

What is said. Ok: any condition on what is fixed with hL | hA | hH: "Ok q gives the sort's named Ok
at q" (at the list: Ok' := fun q => Ok q ∧ rowsFit p.rows π q, and the premise is the first
projection).
  `layersTake_of`, `attTake_of`, `headTake_of`: **the three Takes.** `runs_layers_ok`,
    `runs_att_ok`, `runs_head_ok`: **OwesRuns at the three sorts.**

WHICH FIELDS OF A Take ARE LAID IN HERE, AND HOW. THEY ARE NO PAYMENTS: the named Ok is a
definition by conjunction (its own head says so): okFront, okBack | okK5 | okK6, okJoin, okMerge
and okEq are its clauses read back; fuEq and the seven "fu" fields are theorems of OkOne.lean and of
SistersFull.lean UNDER clauses of the named Ok. ALL THEIR WEIGHT LIES ON ONE DEBT A LINK: the named
Ok at what is fixed at the states of the law's hready.

PREMISES THAT ARE LEFT, each in the Take's own text at these letters: ties (the sort's ties of runs
to the link) · hψ (Rests u ψ) · hrd | hkap (the readers of φ's free field) · h4 (the smallness
test's first four claims) · k3, k3d (RunOk and the door at the lookup's entries: 2, 4 and 3 of
them).

Limits. BOOK-KEEPING. NOTHING IS SHOWN OF ANY STATE OR RUN. WHETHER ANY STATE HAS A NAMED Ok WHOLE
IS NOT KNOWN BY A THEOREM. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OkOne
import Johnson.Desc.First.Link.Law.LinkLawAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Sized Filled)
open OnBytes.Tie.Pv.Tail (UnitRow)
open OnBytes.Tie.Pv.Tail.Port (readsList uOf posOf colsU Fits)
open VerifiableInference.Desc.K4Values (backForms frontForms frontWins winOf)
open VerifiableInference.Desc.First.TailClaims (rkSelfTestP)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open K5Law

variable {β : Type}

/-- **THE LAYERS' Take.** -/
theorem layersTake_of {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ} {tlD : HTailF2}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (hL : ∀ q, Ok q → OkLayers p nU tlD q)
    (ties : LayersTies L p nU)
    (hψ : Rests u ψ)
    (h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
      k8Run.2 front e = .ok (c, e₁) →
      ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok (FullAt nU)) e₁ t → (FullAt nU) t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
      termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta))
    (k3 : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok (FullAt nU)) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o))
    (k3d : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁) :
    LayersTake L u ψ Ok (FullAt nU) p nU entUnit tm4 t3 l3 where
  ties := ties
  hψ := hψ
  okFront := fun q o v h => (hL q h).front o v
  okBack := fun q o v h => (hL q h).back o v
  okEq := core_okEq fun q h => (hL q h).core
  fuFront := fuFront_full u ψ Ok nU p fun q o v h ho hv l hl =>
    core_ents (fun q h => (hL q h).core) h ((hL q h).entsFront o v ho hv l hl)
  fuBack := fuBack_full u ψ Ok nU fun q o h ho =>
    core_ents (fun q h => (hL q h).core) h ((hL q h).entsBack o ho)
  fuEq := core_fuEq (fun q h => (hL q h).core) u ψ
  h4 := h4
  k3 := k3
  k3d := k3d

/-- **THE ATTENTION's Take.** -/
theorem attTake_of {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC} {nU : Array ℕ}
    {tlD : HTailF2} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (hA : ∀ q, Ok q → OkAtt rd c nU tlD q)
    (ties : AttTies L c nU)
    (hψ : Rests u ψ)
    (hrd : ∀ e, rd (phiAll u ψ e) = psiAtt e)
    (h4 : ∀ q front e a c' e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
      k8Run.2 front e = .ok (c', e₁) →
      ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok (FullAt nU)) e₁ t → (FullAt nU) t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c'.take 4) =
      termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta))
    (k3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok (FullAt nU)) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o))
    (k3d : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c' e₁, run n e = .ok (c', e₁) → KeepsDoor atS e e₁) :
    AttTake L u ψ Ok (FullAt nU) rd c nU entUnit tm4 t3 l3 where
  ties := ties
  hψ := hψ
  hrd := hrd
  okK5 := fun q v g h H => (hA q H).k5 v g h
  okEq := core_okEq fun q h => (hA q h).core
  fuFirst := fuFirst_full u ψ Ok nU rd c fun q l h hl =>
    core_ents (fun q h => (hA q h).core) h ((hA q h).entsFirst l hl)
  fuSecond := fuSecond_full u ψ Ok nU rd c fun q l h hl =>
    core_ents (fun q h => (hA q h).core) h ((hA q h).entsSecond l hl)
  fuEq := core_fuEq (fun q h => (hA q h).core) u ψ
  h4 := h4
  k3 := k3
  k3d := k3d

/-- **THE HEAD's Take.** -/
theorem headTake_of {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {h : OnBytes.Model.Head.Shape} {iU3 l piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Seen} {nU : Array ℕ} {tlD : HTailF2}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (hH : ∀ q, Ok q → OkHead h iU3 p kap nU tlD q)
    (ties : HeadTies L h iU3 l piece p nU)
    (hψ : Rests u ψ)
    (hkap : ∀ e, kap (phiAll u ψ e) = seenOf e)
    (h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
      k8Run.2 front e = .ok (c, e₁) →
      ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok (FullAt nU)) e₁ t → (FullAt nU) t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
      termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta))
    (k3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok (FullAt nU)) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o))
    (k3d : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁) :
    HeadTake L u ψ Ok (FullAt nU) h iU3 l piece p kap nU entUnit tm4 t3 l3 where
  ties := ties
  hψ := hψ
  hkap := hkap
  okK6 := fun q z v H => (hH q H).k6 z v
  okJoin := fun q z v g H => (hH q H).join z v g
  okEq := core_okEq fun q H => (hH q H).core
  okMerge := fun q wo v H => (hH q H).merge wo v
  fuK6 := fuK6_full u ψ Ok nU h iU3 p kap fun name hn q l' H hl =>
    core_ents (fun q H => (hH q H).core) H ((hH q H).entsK6 name hn l' hl)
  fuJoin := fuJoin_full u ψ Ok nU h iU3 p kap fun q l' H hl =>
    core_ents (fun q H => (hH q H).core) H ((hH q H).entsJoin l' hl)
  fuEq := core_fuEq (fun q H => (hH q H).core) u ψ
  fuMerge := fuMerge_full u ψ Ok nU fun q wo H hw x hx =>
    core_ents (fun q H => (hH q H).core) H ((hH q H).entsMerge wo hw) _ List.mem_cons_self x hx
  h4 := h4
  k3 := k3
  k3d := k3d

/-- **OwesRuns AT A LAYERS' LINK, AT AN Ok THAT HOLDS THE NAMED ONE.** -/
theorem runs_layers_ok {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ} {tlD : HTailF2}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (hL : ∀ q, Ok q → OkLayers p nU tlD q)
    (ties : LayersTies L p nU)
    (hψ : Rests u ψ)
    (h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
      k8Run.2 front e = .ok (c, e₁) →
      ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok (FullAt nU)) e₁ t → (FullAt nU) t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
      termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta))
    (k3 : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok (FullAt nU)) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o))
    (k3d : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁) :
    OwesRuns .layers L (phiAll u ψ) Ok (FullAt nU) (tmL p entUnit tm4 t3) (lenL p l3) :=
  runs_layers (layersTake_of hL ties hψ h4 k3 k3d)

/-- **AT AN ATTENTION LINK.** -/
theorem runs_att_ok {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC} {nU : Array ℕ}
    {tlD : HTailF2} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (hA : ∀ q, Ok q → OkAtt rd c nU tlD q)
    (ties : AttTies L c nU)
    (hψ : Rests u ψ)
    (hrd : ∀ e, rd (phiAll u ψ e) = psiAtt e)
    (h4 : ∀ q front e a c' e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
      k8Run.2 front e = .ok (c', e₁) →
      ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok (FullAt nU)) e₁ t → (FullAt nU) t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c'.take 4) =
      termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta))
    (k3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok (FullAt nU)) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o))
    (k3d : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c' e₁, run n e = .ok (c', e₁) → KeepsDoor atS e e₁) :
    OwesRuns .attention L (phiAll u ψ) Ok (FullAt nU) (tmA rd c entUnit tm4 t3) (lenA rd c l3) :=
  runs_attention (attTake_of hA ties hψ hrd h4 k3 k3d)

/-- **AT THE HEAD's LINK.** -/
theorem runs_head_ok {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {h : OnBytes.Model.Head.Shape} {iU3 l piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Seen} {nU : Array ℕ} {tlD : HTailF2}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (hH : ∀ q, Ok q → OkHead h iU3 p kap nU tlD q)
    (ties : HeadTies L h iU3 l piece p nU)
    (hψ : Rests u ψ)
    (hkap : ∀ e, kap (phiAll u ψ e) = seenOf e)
    (h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
      k8Run.2 front e = .ok (c, e₁) →
      ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok (FullAt nU)) e₁ t → (FullAt nU) t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
      termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta))
    (k3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok (FullAt nU)) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o))
    (k3d : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁) :
    OwesRuns .head L (phiAll u ψ) Ok (FullAt nU) (tmH h iU3 p kap entUnit tm4 t3)
      (lenH h iU3 p kap l3) :=
  runs_head (headTake_of hH ties hψ hkap h4 k3 k3d)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layersTake_of
#print axioms VerifiableInference.Desc.LinkJoin.attTake_of
#print axioms VerifiableInference.Desc.LinkJoin.headTake_of
#print axioms VerifiableInference.Desc.LinkJoin.runs_layers_ok
#print axioms VerifiableInference.Desc.LinkJoin.runs_att_ok
#print axioms VerifiableInference.Desc.LinkJoin.runs_head_ok
