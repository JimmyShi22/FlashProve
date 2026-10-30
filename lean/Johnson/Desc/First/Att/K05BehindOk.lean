-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05BehindOk.lean: kind K5: WHO PAYS BehindOk (Att/K05ReadersHold.lean: what the reader's three lists ask of the record behind the kind's lay): from what holds for certain of what the kind's piece puts out
(LaidBehind, Att/K05Seam.lean: a real hearing from a record with "on"), the law's own premise on what the lookup's kind leaves (K3LeftOutIs, Att/K05LeftSeats.lean), two facts on the record IN FRONT, each at every statement
with "on", and one on the record BEHIND.

Main names:
  left_parts: of K3LeftOutIs what is spent here: Fo.PadLeft, the shape, "heard", "fork".
  behind_inj: two lays that make one record laid one ledger and one heard record, over segments' parts that agree in every other field.
  behindOk_core: the rule, its premises on the hearing and the lookup in plain form. behindOk_of_laid: **at LaidBehind and K3LeftOutIs.**
  hk3_of_left: the letter k3 := padOfO hs meets padOfO (gOf a).shape.
THE PREMISES THAT STAY: IN FRONT, at every a with "on": hlook : a.1.look? = some (gOf a) [the claims' seat reads a.g; the lookup's promise speaks of lookHeard alone] · hfront : the ledger in front has the array A.iU3, with one own
  row and Kc columns, and A.nW ≤ Kc [a public item has it] · BEHIND, where b.1 is what the lay makes of a.1: hjoin : the join's form's entries meet ownRow.
IS IT EMPTY HERE? An implication.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReadersHold
import Johnson.Desc.First.Att.K05Seam
import Johnson.Desc.First.Att.K05LeftSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)
open VerifiableInference.Desc.K9 (ownRow)

/-- Of the lookup's sharp promise what is spent here. -/
theorem left_parts {S St₀ J₀ : Type} [DecidableEq J₀] {fork : S → Option Fork} {heard : S → Option Forest.Heard}
    {hs : Forest.Shape} {lm first : ℕ} {ι : Fo.Pl → Option J₀} {Q : Fork → Prop}
    {x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)} {g : Forest.Heard} {s : S}
    (h : K3LeftOutIs fork heard hs lm first ι Q x0 g s) :
    ∃ F F', Fo.PadLeft hs F F' g ∧ g.shape = hs ∧ heard s = some g ∧ fork s = some F' := by
  obtain ⟨F, F', rs, _, _, L, e1, e2, _⟩ := h
  exact ⟨F, F', L.padLeft, L.shape, e1, e2⟩

/-- Two lays that make one record. -/
theorem behind_inj {s s' : First.S} {a a' : First.AttOwn} {h h' : Heard} {G G' : Fork}
    (e : behind s a h G = behind s' a' h' G') : G = G' ∧ h = h' ∧ a.g = a'.g ∧ a.lookHeard = a'.lookHeard := by
  have e1 : (First.Here.att { a with F := G, heard5 := some h }) = .att { a' with F := G', heard5 := some h' } :=
    congrArg (·.here) e
  have e2 := First.Here.att.inj e1
  exact ⟨congrArg (·.F) e2, Option.some.inj (congrArg (·.heard5) e2), congrArg (·.g) e2, congrArg (·.lookHeard) e2⟩

/-- **The rule, in plain form.** a: the statement of the law's tuple; a': the statement from which the hearing ran. -/
theorem behindOk_core (A : Attention.Plan) (Kc : ℕ) {hs : Forest.Shape} {s s' t : First.S} {gL gL' : Forest.Heard}
    {F F0 G G' : Fork} {h h' : Heard} {x : Params.AttentionRounds} {rs : List Fmt.RoundView}
    (l1 : seatSO.ledger s = some F) (l2 : seatSO.lay s h G = some t)
    (l1' : seatSO.ledger s' = some F0) (l2' : seatSO.lay s' h' G' = some t)
    (hh : hear x (F0, rs, 0) = some (h', G', [], 0))
    (hk : s.look? = some gL) (hd : s.lookHeard? = some gL) (hd' : s'.lookHeard? = some gL')
    {Fm : Fork} (pl : Fo.PadLeft hs Fm F0 gL')
    (hfront : ∃ T, F0.trees[A.iU3]? = some T ∧ T.K = Kc ∧ T.R = 1 ∧ A.nW ≤ T.K)
    (hjoin : ∀ kf xj, keysOfO A t = some kf → Look.joinF gL kf G [] = some xj → xj.1.ents.all (ownRow G) = true) :
    BehindOk A Kc gL t := by
  obtain ⟨a, ea, _, rfl⟩ := lay_is l1 l2
  obtain ⟨a', ea', _, eb⟩ := lay_is l1' l2'
  obtain ⟨rfl, rfl, _, elk⟩ := behind_inj eb
  have hg : a.g = some gL := by
    unfold First.S.look? at hk
    rw [ea] at hk
    exact hk
  have hl : a.lookHeard = some gL := by
    unfold First.S.lookHeard? at hd
    rw [ea] at hd
    exact hd
  have hl' : a'.lookHeard = some gL' := by
    unfold First.S.lookHeard? at hd'
    rw [ea'] at hd'
    exact hd'
  obtain rfl : gL = gL' := Option.some.inj (hl.symm.trans (elk.trans hl'))
  have z0 : Sized F0 := ⟨pl.fit.1, pl.fit.2.1, pl.fit.2.2⟩
  obtain ⟨_, bl⟩ := hear_below hh z0
  obtain ⟨T, hT, hK, hR, hW⟩ := hfront
  exact ⟨⟨_, T, rfl, hg, hl, by show G.trees[A.iU3]? = some T; rw [bl.trees]; exact hT, hK, hR, hW,
    by show K3.unpaid G gL.owedJoin = true; rw [unpaid_below bl]; exact unpaid_of_left pl, hjoin⟩⟩

section Laid
open VerifiableInference.Desc.Sound (Frame)
variable {Fr : Frame} {Cl St₀ J₀ : Type} [DecidableEq J₀] (A : Attention.Plan) (Kc : ℕ) (p : Par) (base : ℕ)
  (on : First.S × Fr.E.Str → Prop) (gOf : First.S × Fr.E.Str → Forest.Heard) (claim : Aff → Cl) (hs : Forest.Shape)
  (lm first : ℕ) (ι : Fo.Pl → Option J₀) (Q : Fork → Prop)
  (x0 : First.S × Fr.E.Str → TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀))
  (hleft : ∀ a, on a → K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard hs lm first ι Q (x0 a) (gOf a) a.1)

include hleft in
/-- **BehindOk, at LaidBehind and the lookup's sharp promise.** -/
theorem behindOk_of_laid (hlook : ∀ a, on a → a.1.look? = some (gOf a))
    (hfront : ∀ a, on a → ∀ F, seatSO.ledger a.1 = some F →
      ∃ T, F.trees[A.iU3]? = some T ∧ T.K = Kc ∧ T.R = 1 ∧ A.nW ≤ T.K)
    (hjoin : ∀ (a b : First.S × Fr.E.Str), on a → ∀ (F G : Fork) (h : Heard), seatSO.ledger a.1 = some F →
      seatSO.lay a.1 h G = some b.1 →
      ∀ kf xj, keysOfO A b.1 = some kf → Look.joinF (gOf a) kf G [] = some xj → xj.1.ents.all (ownRow G) = true) :
    ∀ a b, on a → LaidBehind Fr seatSO p base on b → ∀ (F G : Fork) (h : Heard), seatSO.ledger a.1 = some F →
      seatSO.lay a.1 h G = some b.1 → BehindOk A Kc (gOf a) b.1 := by
  intro a b ha hLB F G h l1 l2
  obtain ⟨a', F0, G', h', rs, ha', _, l1', _, _, hh, l2', _⟩ := hLB
  obtain ⟨_, _, _, _, hd, _⟩ := left_parts (hleft a ha)
  obtain ⟨Fm, F', pl, _, hd', hf'⟩ := left_parts (hleft a' ha')
  obtain rfl : F' = F0 := Option.some.inj (hf'.symm.trans (ledgerO_fork claim l1'))
  exact behindOk_core A Kc l1 l2 l1' l2' hh (hlook a ha) hd hd' pl (hfront a' ha' F' l1') (hjoin a b ha F G h l1 l2)

include hleft in
/-- The letter k3 := padOfO hs meets the seat's pad. -/
theorem hk3_of_left : ∀ a, on a → padOfO hs = padOfO (gOf a).shape := fun a ha => by
  obtain ⟨_, _, _, e, _, _⟩ := left_parts (hleft a ha)
  rw [e]

end Laid

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.behindOk_of_laid
#print axioms VerifiableInference.Desc.First.Att.P.hk3_of_left
#print axioms VerifiableInference.Desc.First.Att.P.left_parts
#print axioms VerifiableInference.Desc.First.Att.P.behind_inj
#print axioms VerifiableInference.Desc.First.Att.P.behindOk_core
