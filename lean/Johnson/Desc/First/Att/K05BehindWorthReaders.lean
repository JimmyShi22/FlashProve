-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05BehindWorthReaders.lean: kind K5: THE LAW's PREMISE K5Behind.worth (k5Behind_worth, Att/K05BehindWorth.lean) WITH ITS PREMISE hRd GONE: the reader's three lists hold the law's, out of LaidBehind, the law's own
premise on what the lookup's kind leaves (K3LeftOutIs), and what is asked in front anyway (FrontAll). FrontAll holds two small facts in front (one own row; the pad).

Why a second form beside Att/K05ReadersHold.lean's BehindOk. That one asks a₀.g = some gL whole; FrontAll gives "what the claims' seat reads of a₀.g is what it would read of gL" (SeatReadsSame). And its clause on the join's form has a payer
(ents_of_returns, Att/K05EntsOf.lean) that wants the law's structure of returns (Returns), which a premise on the verifier's state alone does not hold.


The premise hitems of k5Behind_worth_readers is THE SENTENCE ITSELF (formsTQ at every run that the table lists under the two items): no constant of the composed filling stands in a statement.

Main names:
  BehindOk₀ A Kc gL s: what is asked of the verifier's state s after the kind's block has laid what it heard: no clause on the join's form; of a₀.g only what is read of it.
  readers_hold₀: at one such state: the reader gives just l₁, just l₂, just [xj.1], no late slot.
  behindOk₀_of_laid: BehindOk₀ out of LaidBehind, K3LeftOutIs, FrontAll: under the lay's equation.
  hRds_of_link: the readers "of the link" (Johnson/Desc/First/Batch/ReadersOfLink.lean) meet hRds at every filling of their two holes.
  k5Behind_worth_readers: **k5Behind_worth's statement with hRd gone**, at tj := [] and k3 := padOfO hs.
IN hRd's PLACE: hRds (what "the run itself" gives at block 2, at a name other than the smallness test's, the link's readers give too: NOT an equation between the two structures of readers: readers with holes that speak elsewhere meet
  it) · hst (block 2 states the kind's four runs) · hleft (the law's own).
THE LETTERS UNDER "FOR ALL" IN THE PREMISES THAT ARE NEW HERE, ONE BY ONE: hst: an equation between letters of the statement · hRds: name, s: free ON PURPOSE (a law of the readers' make, paid by unfolding at readers "of the link"); R: pinned by the run's equation · hleft: a: fenced by "on a"; all else are letters of the statement. IN THE LEMMAS: behindOk₀_of_laid's conclusion: b: fenced by
  LaidBehind (its own hearing); F: pinned by the ledger's equation; G, h: the lay pins b.1 by them, and behind_inj ties them to LaidBehind's own G', h' · readers_hold₀: G, h: fenced by BehindOk₀ at "behind s₀ att h G", Said and Returns.
IS IT EMPTY HERE? An implication.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BehindWorth
import Johnson.Desc.First.Att.K05BehindOk
import Johnson.Desc.First.Batch.ReadersOfLink
import Johnson.Desc.First.Att.K05ReadersLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit Place)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Item)
open VerifiableInference.Desc.K9 (Readers segAt? atMoment1)
open VerifiableInference.Desc.Sound (Stated Mem msgsOf MsgT formsTQ seatTab Frame strsOf relAt meansQ outsQ
  second)
open VerifiableInference.Desc.First.Look (Sent JAtt attSg sigListCalls bornAt)
open K5Law (funsAt inAt_is firstAt_is secondAt_is readers_at runsN_is)
open VerifiableInference.Desc.K9 (Read lateOf ownRow readerOf RunOf runOfForms)

/-- **What is asked of the verifier's state after the kind's block**: of a₀.g only what is read of it. -/
def BehindOk₀ (A : Attention.Plan) (Kc : ℕ) (gL : Forest.Heard) (s : First.S) : Prop :=
  ∃ a₀ g₀ T, s.here = .att a₀ ∧ a₀.g = some g₀ ∧ SeatReadsSame g₀ gL ∧ a₀.lookHeard = some gL ∧ a₀.F.trees[A.iU3]? = some T ∧ T.K = Kc ∧ T.R = 1 ∧ A.nW ≤ T.K ∧
    K3.unpaid a₀.F gL.owedJoin = true

/-- **At one state: the reader's three lists are the law's.** -/
theorem readers_hold₀ (A A0 : Attention.Plan) (eu : A0.iU3 = A.iU3) {states : ℕ → List (RunOf First.S)}
    (hst : states 2 = runsN A) {Kc : ℕ} {gL : Forest.Heard} {s₀ : First.S} {att : First.AttOwn} {h : Heard} {G : Fork}
    {xr : Params.AttentionRounds} {Ls : Lists} (hs : Said xr h G Ls) (B : BehindOk₀ A Kc gL (behind s₀ att h G))
    (hc : gL.cEnd.ents = #[]) {l : Left} {i : Runs.In} {l₁ l₂ : List Aff} {jn : Runs.JoinsP} {kf : Array Aff}
    {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    (Rt : Returns A.S gL.zx gL.zk G h l A0 gL i Kc l₁ l₂ jn (padOfO gL.shape) kf G [] xj A.seam.tl A.nW
      (lookOfO (parCOf A).geo.lmb gL)) :
    readerOf states 2 "first" (behind s₀ att h G) = some { forms := l₁, late := [] } ∧
      readerOf states 2 "second" (behind s₀ att h G) = some { forms := l₂, late := [] } ∧
      readerOf states 2 "join" (behind s₀ att h G) = some { forms := [xj.1], late := [] } := by
  obtain ⟨a₀, g₀, T, he, hg, sm, hlk, hT, hK, hR1, hW, hun⟩ := B
  obtain rfl : a₀ = { att with F := G, heard5 := some h } := by
    have : (First.Here.att { att with F := G, heard5 := some h }) = .att a₀ := he
    cases this
    rfl
  have hT' : G.trees[A.iU3]? = some T := hT
  have u3 : i.iU3 = A.iU3 := Rt.u3.trans eu
  have left : LeftIs (geoOf A.S) g₀.zk h G l := by rw [sm.zk]; exact Rt.left
  have zkI : i.zk = g₀.zk := by rw [sm.zk]; exact Rt.zkI
  have points : pointsOf i.g g₀.zk h l = some i.p := by rw [sm.zk]; exact Rt.points
  have tables : tablesP i.g (K5Law.matsOf A.seam.tl.mats) A.nW (lookOfO (parCOf A).geo.lmb g₀) i.p = some i.t := by
    rw [lookOfO_same sm]; exact Rt.tables
  have en := ents_of_returns Rt eu hs ⟨T, hT', hK, hW, hR1⟩ hc
  have own : ∀ f ∈ l₁ ++ l₂ ++ [xj.1], f.ents.all (ownRow G) = true := fun f hf =>
    all_ownRow fun e he' => ⟨(en f hf e he').2, T, by rw [(en f hf e he').1]; exact hT', hR1⟩
  have hst' : states 2 = (runsO A).map runOfForms := hst.trans (runsN_is A)
  obtain ⟨r1, r2⟩ := readers_at A left Rt.geo zkI u3 points tables hT' hK hst' (s := behind s₀ att h G) rfl hg rfl rfl
    Rt.first Rt.second (fun f hf => own f (by simp [hf])) (fun f hf => own f (by simp [hf]))
  refine ⟨r1, r2, ?_⟩
  have hin := inAt_is A left Rt.geo zkI u3 points tables hT' hK
  have hk : keysOfO A (behind s₀ att h G) = some kf :=
    keysOfO_is A (s := behind s₀ att h G) rfl hg rfl rfl hin Rt.first (by rw [sm.shape]; exact Rt.keys)
  have hG2 : ((behind s₀ att h G).putFork xj.2.1).fork? = some (G.paid gL.owedJoin) := by
    rw [joinF_ledger Rt.join]
    rfl
  exact readerOf_runN' (by rw [hst]; exact find_join A) (joinRun_behind A hlk hun hk Rt.join) rfl hG2 (lateOf_paid G _)
    fun f hf => own f (by simp [List.mem_singleton.1 hf])

section Laid
variable {Fr : Frame} {Cl St₀ J₀ : Type} [DecidableEq J₀] (x : VerifiableInference.Desc.First.Look.Place)
  (A : Attention.Plan) (D : Sent) (p : Par) (base : ℕ) (on : First.S × Fr.E.Str → Prop)
  (gOf : First.S × Fr.E.Str → Forest.Heard) (claim : Aff → Cl) (hs : Forest.Shape) (lm first : ℕ)
  (ι : Fo.Pl → Option J₀) (Q : Fork → Prop) (x0 : First.S × Fr.E.Str → TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀))
  (hleft : ∀ a, on a → K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard hs lm first ι Q (x0 a) (gOf a) a.1)

include hleft in
/-- **BehindOk₀, out of LaidBehind, the lookup's sharp promise and what is asked in front.** -/
theorem behindOk₀_of_laid (own : List (ℕ × ℕ)) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) (hi : ℕ)
    (hfront : ∀ a : First.S × Fr.E.Str, on a → FrontAll x A D own ps qs hi (gOf a) a.1) :
    ∀ a b : First.S × Fr.E.Str, on a → LaidBehind Fr seatSO p base on b → ∀ (F G : Fork) (h : Heard),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → BehindOk₀ A (plannedK A) (gOf a) b.1 := by
  intro a b ha hLB F G h l1 l2
  obtain ⟨a', F0, G', h', rs, ha', _, l1', _, _, hh, l2', _⟩ := hLB
  obtain ⟨_, _, _, _, hd, _⟩ := left_parts (hleft a ha)
  obtain ⟨Fm, F', pl, _, hd', hf'⟩ := left_parts (hleft a' ha')
  obtain rfl : F' = F0 := Option.some.inj (hf'.symm.trans (ledgerO_fork claim l1'))
  obtain ⟨t, ea, _, eb⟩ := lay_is l1 l2
  obtain ⟨t', ea', _, eb'⟩ := lay_is l1' l2'
  obtain ⟨rfl, rfl, _, elk⟩ := behind_inj (eb.symm.trans eb')
  have hl : t.lookHeard = some (gOf a) := by
    have := hd
    show t.lookHeard = _
    unfold K3.seatCalls First.S.lookHeard? at this
    simp only [ea] at this
    exact this
  have hl' : t'.lookHeard = some (gOf a') := by
    have := hd'
    unfold K3.seatCalls First.S.lookHeard? at this
    simp only [ea'] at this
    exact this
  have eg : gOf a = gOf a' := Option.some.inj (hl.symm.trans (elk.trans hl'))
  obtain ⟨g₀, hg, sm⟩ := (hfront a ha).reads t ea
  obtain ⟨z0, _, T, hT, hK, hW, hR1⟩ := (hfront a' ha').ledger F' l1'
  obtain ⟨_, bl⟩ := hear_below hh z0
  rw [eb]
  exact ⟨_, g₀, T, rfl, hg, sm, hl, by show G.trees[A.iU3]? = some T; rw [bl.trees]; exact hT, hK, hR1, hW, by
      show K3.unpaid G (gOf a).owedJoin = true
      rw [unpaid_below bl, eg]
      exact unpaid_of_left pl⟩

end Laid

section Top
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

/-- **K5Behind's field worth, with hRd gone.** -/
theorem k5Behind_worth_readers {Fr : Frame} (p : Par) (ns base : ℕ)
    (gOf : First.S × Fr.E.Str → Forest.Heard)
    (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base (Wit Cells Tok MsgT) (attSg x D rad).Msg)
    (R' : First.S × Fr.E.Str → Wit Cells Tok MsgT → Prop) (Rds : ℕ → Readers)
    (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
    (Nn : Numbers)
    (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (hi : ℕ)
    (hpart : I.part = fun w => msgsOf D.codes (sigListCalls D rad x.link) seat arr w)
    (hitems : ∀ b w, LaidBehind Fr seatSO p base on b → R' b w →
      (∀ p ∈ runs x.link 3 "own", formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arr ms w)) ∧
      ∀ p ∈ runs x.link 2 "join", formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arr ms w))
    (hpub : TiePub D x A.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    {states : ℕ → List (VerifiableInference.Desc.K9.RunOf First.S)}
    (hRds : ∀ (name : String) (s : First.S) (R : VerifiableInference.Desc.K9.Read), (name == "K8.equations") = false →
      readerOf states 2 name s = some R → (Rds x.link).forms 2 name s = some R)
    (hst : states 2 = runsN A)
    {Cl St₀ J₀ : Type} [DecidableEq J₀] (claim : Aff → Cl) (hs : Forest.Shape) (lm first : ℕ) (ι : Fo.Pl → Option J₀)
    (Q : Fork → Prop) (x0 : First.S × Fr.E.Str → TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀))
    (hleft : ∀ a, on a →
      K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard hs lm first ι Q (x0 a) (gOf a) a.1)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    (hfront : ∀ a : First.S × Fr.E.Str, on a →
      FrontAll x A D (Nn.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) hi (gOf a) a.1) :
    BillsWorthJ x A.seam.tl D rad Ex Wp α A.S ns
      (numsPlan p.own (x.F.next + Forest.elems x.fs)) { A with NC := A.S.calls.size } (plannedK A) (padOfO hs)
      A.nW [] gOf (fun a => lookOfO (parCOf A).geo.lmb (gOf a)) seatSO p.own
      (fun a : First.S × Fr.E.Str => a.1) (fun a : First.S × Fr.E.Str => a.1) on I.part
      (fun b w => LaidBehind Fr seatSO p base on b ∧ R' b w) := by
  refine k5Behind_worth x A D rad Ex Wp α p ns base (padOfO hs) [] gOf on I R' Rds runs St Nn arr seat ms hi
    hpart hitems hpub r1 r2 r3 ?_ hm hSt hfront
  intro a b w ha hR F G h Ls h1 h2 sd _ _ l i l₁ l₂ jn kf xj Rt
  obtain ⟨att, _, _, eb⟩ := lay_is h1 h2
  have B := behindOk₀_of_laid x A D p base on gOf claim hs lm first ι Q x0 hleft _ _ _ hi hfront a b ha hR.1 F G h
    h1 h2
  rw [eb] at B
  rw [hk3_of_left on gOf claim hs lm first ι Q x0 hleft a ha] at Rt
  obtain ⟨q1, q2, q3⟩ := readers_hold₀ A { A with NC := A.S.calls.size } rfl hst sd B (hfront a ha).plain Rt
  rw [eb]
  exact ⟨_, _, _, hRds "first" _ _ (by decide) q1, rfl, fun f hf => hf, hRds "second" _ _ (by decide) q2, rfl, fun f hf => hf,
    hRds "join" _ _ (by decide) q3, rfl, List.mem_singleton.2 rfl⟩

end Top

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.readers_hold₀
#print axioms VerifiableInference.Desc.First.Att.P.behindOk₀_of_laid
#print axioms VerifiableInference.Desc.First.Att.P.k5Behind_worth_readers
