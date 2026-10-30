-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/K4Turn.lean: K4's HEARING MEMBER's STEP ON SHAPES IS ONE FUNCTION AT TWO
PUBLIC RECORDS THAT DIFFER IN THE TABLE OF SCALES AND THE LAYOUT's THREE eps.

  pansB_skel, claimsB_turn, joinB_turn, hearB_turn, k4PlanB_turn   the guards read neither.
  **own_returns**   under the test on the plan, the host's count of the padding keys, the ledger's
                    room and the guard on the lookup's record, the hearing at blanks returns.
  ownOf_turn        so the hearing on shapes has one value at the two records.
  **k4StepW_turn**  the step.

Limits. Equations of functions: no step is shown to return at any shape.
-/
import Johnson.AtFull.Shape.Scope.K4Two
import Johnson.AtFull.Shape.K4Fit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt.Two
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own Scales Env TableAt callsTS)
open OnBytes.Flat (All2 OptRel ClaimAlike)
open OnBytes.Desc.First.K4.RtPub
open OnBytes.Desc.First.K4.Total (EnvSkel)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K8.Honest (ledBlank)
open Johnson.AtFull.Shape (k4StepW k4StepS noneWaitsSh)

set_option maxHeartbeats 1000000

/-- The record with its table of scales and its three eps set. -/
abbrev pT (P : Pub) (e1 e2 eF : Nat) (s : Scales) : Pub :=
  { P with y := turnY P.y e1 e2 eF, sc := s }

/-! ## 1 The guards -/

theorem pansB_mono {P : Pub} {v v₀ : Env} (S : EnvSkel v v₀) {lamS n : Nat}
    (h : pansB P v lamS n = true) : pansB P v₀ lamS n = true := by
  unfold pansB at h
  split at h
  · cases h
  · rename_i TS hTS
    split at h
    · cases h
    · rename_i pans hp
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      exact pansB_of_one S hTS hp h1 h2 Array.size_replicate h3

theorem pansB_skel {P : Pub} {v v₀ : Env} (S : EnvSkel v v₀) (lamS n : Nat) :
    pansB P v lamS n = pansB P v₀ lamS n :=
  Bool.eq_iff_iff.2 ⟨pansB_mono S, pansB_mono ⟨S.y.symm, S.tab.symm, S.K3.symm⟩⟩

theorem any_rel {α : Type} {R : α → α → Prop} {x y : Option α} (h : OptRel R x y)
    {f f' : α → Bool} (hf : ∀ a b, R a b → f a = f' b) : x.any f = y.any f' := by
  cases x <;> cases y
  · rfl
  · exact h.elim
  · exact h.elim
  · exact hf _ _ h

theorem isSome_rel {α : Type} {R : α → α → Prop} {x y : Option α} (h : OptRel R x y) :
    x.isSome = y.isSome := by
  cases x <;> cases y
  · rfl
  · exact h.elim
  · exact h.elim
  · rfl

variable (P : Pub) (e1 e2 eF : Nat) (s : Scales) (hp : HPlan2) (g : Nat)

/-- The test on the claims: the table of scales is not read by any answer, and eps nowhere. -/
theorem claimsB_turn : claimsB (pT P e1 e2 eF s) hp g = claimsB P hp g := by
  have e : claimsB (pT P e1 e2 eF s) hp g = claimsB { P with sc := s } hp g := rfl
  rw [e]
  have CS : ClaimSkel (blankClaims { P with sc := s } hp g) (blankClaims P hp g) :=
    ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  unfold claimsB
  show Option.any _ (callsTS P) = Option.any _ (callsTS P)
  refine congrArg (fun f => Option.any f (callsTS P)) (funext fun TS => ?_)
  refine any_rel (weightClaims_rel CS TS) fun cP cP₀ hc => ?_
  by_cases hg : (g == 0) = true
  · simp only [if_pos hg]
    have r := claimE_rel CS (ZE := Array.replicate (P.y.ls + P.y.h.lt) zeroE)
      (ZE₀ := Array.replicate (P.y.ls + P.y.h.lt) zeroE)
      (tkh := Array.replicate (P.y.lPd - P.y.ls) zeroE)
      (tkh₀ := Array.replicate (P.y.lPd - P.y.ls) zeroE) rfl rfl P.V
      (t := Array.replicate P.y.T 0) (t₀ := Array.replicate P.y.T 0) rfl rfl
    revert r
    cases (blankClaims { P with sc := s } hp g).claimE _ _ _ _ <;>
      cases (blankClaims P hp g).claimE _ _ _ _ <;> intro r
    · rfl
    · exact r.elim
    · exact r.elim
    · exact claimTests_alike _ _ (hc.append (.cons r .nil))
  · simp only [if_neg hg]
    exact claimTests_alike _ _ (hc.append .nil)

theorem joinB_turn (iU3 : Nat) (tab : List TableAt) :
    joinB (pT P e1 e2 eF s) hp g iU3 tab = joinB P hp g iU3 tab := by
  have e : joinB (pT P e1 e2 eF s) hp g iU3 tab = joinB { P with sc := s } hp g iU3 tab := rfl
  rw [e]
  unfold joinB
  refine List.all_congr rfl fun q => ?_
  have S : EnvTurn (envBlank { P with sc := s } hp g iU3 tab) (envBlank P hp g iU3 tab) :=
    ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  exact isSome_rel (joinPart_rel S _ _ _ _ q _ #[] #[])

theorem hearB_turn : hearB (pT P e1 e2 eF s) hp g = hearB P hp g := by
  have e : hearB (pT P e1 e2 eF s) hp g = (hp.tl.funOpen &&
      (hp.tl.ix.U.getD 2 none).any fun iU3 => (RtPub.tablesAt P g).any fun r =>
        (r.2.2 == hp.nU.getD 2 0 &&
          pansB P (blankEnv { P with sc := s } hp g iU3 r.1) hp.lamS (nclpOf hp g) &&
          claimsB (pT P e1 e2 eF s) hp g)) := rfl
  have e2 : hearB P hp g = (hp.tl.funOpen &&
      (hp.tl.ix.U.getD 2 none).any fun iU3 => (RtPub.tablesAt P g).any fun r =>
        (r.2.2 == hp.nU.getD 2 0 && pansB P (blankEnv P hp g iU3 r.1) hp.lamS (nclpOf hp g) &&
          claimsB P hp g)) := rfl
  rw [e, e2, claimsB_turn]
  simp only [show ∀ (iU3 : Nat) (tab : List TableAt),
    pansB P (blankEnv { P with sc := s } hp g iU3 tab) hp.lamS (nclpOf hp g) =
      pansB P (blankEnv P hp g iU3 tab) hp.lamS (nclpOf hp g) from
    fun iU3 tab => pansB_skel (P := P) (v := blankEnv { P with sc := s } hp g iU3 tab)
      (v₀ := blankEnv P hp g iU3 tab) ⟨rfl, rfl, rfl⟩ hp.lamS (nclpOf hp g)]

theorem k4PlanB_turn (p : Par) :
    k4PlanB { p with P := pT p.P e1 e2 eF s } = k4PlanB p := by
  have e : k4PlanB { p with P := pT p.P e1 e2 eF s } =
      (covers p.P && planNumsB p.P p.hp p.g &&
        (hearB (pT p.P e1 e2 eF s) p.hp p.g &&
          (RtPub.tablesAt p.P p.g).any fun r => pointsB p.P p.g r.2.1) &&
        (p.hp.tl.ix.U.getD 2 none).any fun iU3 =>
          (RtPub.tablesAt p.P p.g).any fun r => joinB (pT p.P e1 e2 eF s) p.hp p.g iU3 r.1) := rfl
  rw [e, hearB_turn]
  simp only [joinB_turn]
  rfl

/-! ## 2 The hearing at blanks returns -/

theorem tapeOf_blank : ∀ ds : List Rd, TapeOf ds (blankTape ds)
  | [] => trivial
  | d :: ds => ⟨⟨rfl, rfl, rfl, List.length_replicate, List.length_replicate⟩, tapeOf_blank ds⟩

theorem blank_drawn {ds : List Rd} {t₁ t₂ : Tape} {r : FlatRound}
    (h : blankTape ds = t₁ ++ r :: t₂) {x : E} (hx : x ∈ r.drawn) : x = oneE := by
  have hm : r ∈ blankTape ds := by
    rw [h]
    simp
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hm
  exact List.eq_of_mem_replicate hx

theorem lastOf_blank {n k : Nat} {a : Array E}
    (h : (lastOf (Array.replicate n zeroE) k).toOption = some a) :
    a = Array.replicate k zeroE := by
  have hs := lastOf_size h
  unfold lastOf cutLast at h
  by_cases hk : k > (Array.replicate n zeroE).size
  · rw [if_pos hk] at h
    cases h
  · rw [if_neg hk] at h
    have e : (Array.replicate n zeroE).extract ((Array.replicate n zeroE).size - k)
        (Array.replicate n zeroE).size = a := Option.some.inj h
    subst e
    apply Array.ext
    · rw [hs, Array.size_replicate]
    · intro i h1 h2
      simp [Array.getElem_extract]

theorem ends_blank (la : Nat) : ∀ (l : List Nat) (r : List (Array E)),
    (l.map fun n => Array.replicate n zeroE).mapM (fun zk => (lastOf zk la).toOption) = some r →
    ∀ e ∈ r, e = Array.replicate la zeroE
  | [], r, h, e, he => by
    simp at h
    subst h
    cases he
  | n :: l, r, h, e, he => by
    simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rcases List.mem_cons.1 he with rfl | he
    · exact lastOf_blank ha
    · exact ends_blank la l b hb e he

theorem tokens_blank {p : Par} (h : hearPB p.P p.hp p.g = true) :
    tokensFit { p.P with tokv := Array.replicate p.P.y.T 0 } p.g = true := by
  unfold hearPB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, hc⟩ := hearB_parts h.1
  unfold tokensFit
  by_cases hg : (p.g == 0) = true
  · unfold claimsB at hc
    obtain ⟨TS, -, hc⟩ := any_some hc
    obtain ⟨cP, -, hc⟩ := any_some hc
    rw [if_pos hg] at hc
    obtain ⟨cE, he, -⟩ := any_some hc
    obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.1 he
    have k : ((Array.replicate p.P.y.T 0).size != p.P.y.T ||
        (Array.replicate p.P.y.T 0).any (· ≥ p.P.V)) = false := claimE_tok hx
    rw [Bool.or_eq_false_iff] at k
    have k2 := Array.any_eq_false.1 k.2
    have e1 : (p.g != 0) = false := by
      rw [bne, hg]
      rfl
    have hall : ((Array.replicate p.P.y.T 0).all fun t => decide (t < p.P.V)) = true := by
      rw [Array.all_eq_true]
      intro i hi
      have t := k2 i hi
      simp at t ⊢
      omega
    show (p.g != 0 || ((Array.replicate p.P.y.T 0).size == p.P.y.T &&
      (Array.replicate p.P.y.T 0).all fun t => decide (t < p.P.V))) = true
    rw [e1, hall, Array.size_replicate]
    simp
  · have e1 : (p.g != 0) = true := by
      simpa [bne] using hg
    simp [e1]

/-- **Under the test on the plan, the host's count, the ledger's room and the guard on the lookup's
record, K4's hearing at blanks returns.** -/
theorem own_returns (p : Par) (hP : k4PlanB p = true)
    (hL : VerifiableInference.Desc.First.Look.laidLayers p.P = some p.P.y.fo.pub) {h : HeardAll}
    {L : LedSh} (hR : roomB L (k4Takes p.P p.hp p.g + 0) = true)
    (hK : lookB p.P h L = true) :
    ∃ o G, hearFl { p.P with tokv := Array.replicate p.P.y.T 0 } p.hp p.g h.blank (ledBlank L)
      (blankTape (rounds p.P p.hp p.g)) = some (o, G, []) := by
  have hR' : Room (ledBlank L) (k4Takes p.P p.hp p.g + 0) :=
    room_of_B (by rw [ledSh_blank]; exact hR)
  have hK' : LookFacts p.P h.blank (ledBlank L) :=
    look_of_B (by rw [heardAll_blank, ledSh_blank]; exact hK)
  obtain ⟨Z, ztF, ends, hH⟩ := hK'.hands
  unfold k4PlanB at hP
  simp only [Bool.and_eq_true] at hP
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hP
  obtain ⟨iU3, tab, laid, n, hu, ht, hret⟩ :=
    hear_returns_of_PB (P := { p.P with tokv := Array.replicate p.P.y.T 0 }) (hp := p.hp)
      (g := p.g) p3 (tokens_blank p3)
  have ht' : RtPub.tablesAt p.P p.g = some (tab, laid, n) := ht
  rw [hu, ht'] at p4
  have hJ : joinB p.P p.hp p.g iU3 tab = true := p4
  have hN := planNums_of_B p2
  have hZ : Z = Array.replicate p.P.y.h.la zeroE := lastOf_blank hH.z
  have hE : ends.all (· == Z) = true := by
    have e0 := hH.ends
    rw [Array.mapM_eq_mapM_toList] at e0
    cases hm : (h.blank.zk.toList.mapM fun zk => (lastOf zk p.P.y.h.la).toOption) with
    | none =>
      rw [hm] at e0
      cases e0
    | some r =>
      rw [hm] at e0
      have e1 : r.toArray = ends := Option.some.inj e0
      subst e1
      have hall := ends_blank p.P.y.h.la h.zk r (by simpa [HeardAll.blank] using hm)
      rw [List.all_toArray, List.all_eq_true]
      intro e he
      rw [hall e he, hZ]
      simp
  obtain ⟨o, G, e, -⟩ := hret h.blank (F := ledBlank L) (k := 0)
    (t := blankTape (rounds p.P p.hp p.g)) (Z := Z) (ztF := ztF) (ends := ends) p1 hK'.fits hR'
    (tapeOf_blank _)
    ⟨hN.ns, hN.np, hN.no, hN.muV, hN.endT, hN.muH9, hN.muH29, hN.muH, hN.muH2, hN.ncl⟩
    ⟨hH.depth, hH.z, hH.ends, hH.zt, hH.ztSize, hH.cEnd⟩ hK'.zk hK'.planes
    (join_pay (P := { p.P with tokv := Array.replicate p.P.y.T 0 }) hL hJ hK'.calls hK'.e
      hK'.noPub hK'.pub) hE
    (fun t₁ s0 eps t₂ _ ht => by
      rw [blank_drawn ht (List.mem_singleton.2 rfl)]
      rfl)
  exact ⟨o, G, e⟩

/-! ## 3 The hearing on shapes and the step -/

theorem k4FrontB_turn (p : Par) (k : Nat) (a : ChainSh) :
    k4FrontB { p with P := pT p.P e1 e2 eF s } k a = k4FrontB p k a := rfl

theorem ownOf_turn {p : Par} (hP : k4PlanB p = true)
    (hL : VerifiableInference.Desc.First.Look.laidLayers p.P = some p.P.y.fo.pub) {h : HeardAll}
    {L : LedSh} (hR : roomB L (k4Takes p.P p.hp p.g + 0) = true)
    (hK : lookB p.P h L = true) :
    ownOf { p with P := pT p.P e1 e2 eF s } h L = ownOf p h L := by
  obtain ⟨o, G, e⟩ := own_returns p hP hL hR hK
  obtain ⟨o₁, G₁, e₁⟩ := own_returns { p with P := pT p.P e1 e2 eF s }
    (by rw [k4PlanB_turn]; exact hP) hL hR hK
  obtain ⟨r1, r2, -⟩ := hear_turn p.P e1 e2 eF s (Array.replicate p.P.y.T 0)
    (Array.replicate p.P.y.T 0) p.hp p.g (fo := h.blank) (fo' := h.blank) rfl (ledBlank L)
    (ledBlank L) (blankTape (rounds p.P p.hp p.g)) (blankTape (rounds p.P p.hp p.g)) _ _ _ _ _ _
    rfl rfl e₁ e
  unfold ownOf
  rw [e₁, e]
  simp only [Option.map_some]
  rw [r1.1, show o₁.funs.toList.map funSh = o.funs.toList.map funSh from r1.2, r2]

theorem k4Step_turn (p : Par) : k4Step { p with P := pT p.P e1 e2 eF s } = k4Step p := by
  funext a
  unfold k4Step
  have hL : (VerifiableInference.Desc.First.Look.laidLayers (pT p.P e1 e2 eF s) ==
      some (pT p.P e1 e2 eF s).y.fo.pub) =
      (VerifiableInference.Desc.First.Look.laidLayers p.P == some p.P.y.fo.pub) := rfl
  show (if (k4PlanB { p with P := pT p.P e1 e2 eF s } &&
      (VerifiableInference.Desc.First.Look.laidLayers (pT p.P e1 e2 eF s) ==
      some (pT p.P e1 e2 eF s).y.fo.pub) && k4FrontB { p with P := pT p.P e1 e2 eF s } 0 a) = true
    then k4G { p with P := pT p.P e1 e2 eF s } a else none) = _
  rw [k4PlanB_turn, hL, k4FrontB_turn]
  by_cases hb : (k4PlanB p &&
      (VerifiableInference.Desc.First.Look.laidLayers p.P == some p.P.y.fo.pub) &&
      k4FrontB p 0 a) = true
  · rw [if_pos hb, if_pos hb]
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨⟨hP, hL'⟩, hF⟩ := hb
    unfold k4FrontB at hF
    rw [Bool.and_eq_true, beq_iff_eq] at hF
    unfold k4G
    obtain ⟨h1, hF⟩ := hF
    rw [if_neg (by simp [h1]), if_neg (by simp [h1])]
    cases hl : a.look with
    | none =>
      rw [hl] at hF
    | some h =>
      cases hd : a.led with
      | none => rfl
      | some L =>
        rw [hl, hd] at hF
        have hF' : (roomB L (k4Takes p.P p.hp p.g + 0) && lookB p.P h L) = true := hF
        rw [Bool.and_eq_true] at hF'
        show Option.map _ (ownOf { p with P := pT p.P e1 e2 eF s } h L) = Option.map _ (ownOf p h L)
        rw [ownOf_turn e1 e2 eF s hP hL' hF'.1 hF'.2]
  · rw [if_neg hb, if_neg hb]

/-- **K4's HEARING MEMBER's STEP ON SHAPES IS ONE FUNCTION AT THE TWO RECORDS.** -/
theorem k4StepW_turn (p : Par) : k4StepW { p with P := pT p.P e1 e2 eF s } = k4StepW p := by
  funext a
  unfold k4StepW k4StepS
  rw [k4Step_turn]

end OnBytes.Desc.First.K4.Rt.Two

#print axioms OnBytes.Desc.First.K4.Rt.Two.claimsB_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.joinB_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.hearB_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.k4PlanB_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.own_returns
#print axioms OnBytes.Desc.First.K4.Rt.Two.ownOf_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.k4Step_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.k4StepW_turn
