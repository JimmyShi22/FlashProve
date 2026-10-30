-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamFacts.lean: **THE SEAM's CORE AT THE SHARED CHAIN's TWO SEATS (TupleNine | TupleTen, SeamCore.lean) FROM tuple_core (SeamTuple.lean) AND ONE NAMED BUNDLE OF PLAIN FACTS.** Definitions, statements and proofs. What for: THAT tuple_core's
CONCLUSION IS THE CORE's BODY is hereby held by Lean, and what is left of the seam is written out as ONE Prop with no chance, no transcript's count and no "there are words" in it.
  CoreFacts    at a record t of the kind, strings y, a record a0 and plain strings Y of the row words_are_committed's side: AT WHATEVER THE RECORD FIXES (a · rest · G0 · Ly · D): the data's codes are the plan's cs, and there are radii e0s and a laying memJ of the data's
               members onto members of the list with tuple_core's premises, written at cs.
  core_at      CoreFacts · InOrder · QN π (NTuple …) (t, y) ⟹ at the group under test: ∃ m : Tup cs, all taken rows hold of wordsT cs mem rd m ∧ CandAt at every member that CoreFacts' "sits" names.
  **tupleNine_of | tupleTen_of**   TupleNine | TupleTen from: CoreFacts at the record behind the seat's door in (at a yes, inside the promise) · InOrder inside the promise.
Limits. CoreFacts IS A PREMISE; no member of it is shown. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamTuple
import Johnson.Desc.Sound.SeamCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok made_of oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

/-- **What is left of the seam, as plain facts.** sits: which members of the list the tuple is to be a candidate at. -/
def CoreFacts (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12) (no : ℕ → ℕ)
    (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop) (t : T12) (y : Fr.E.Str) (a0 : A) (Y : Strs) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    D.st.codes = cs ∧
    (sgOf a).StageJ (rad (sgOf a)) ∧
    combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true ∧
    Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h ∧
    (∀ j : Fin D.mems.length, ok (siteL cs a (D.mems.get j)) = true) ∧
    (∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      ok (sampleL cs (D.mems.get j) x) = true) ∧
    (∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val) ∧
    (∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o) ∧
    ∃ (e0s : Fin D.mems.length → ℕ) (memJ : Fin D.mems.length → Mem),
      (∀ j : Fin D.mems.length,
        rad (sgOf a) < (e0s j + 1) * 2 ^ ((sgOf a).C.a - aOf cs (D.mems.get j).sh)) ∧
      Function.Injective memJ ∧ (∀ x, sits x → ∃ j, memJ j = x) ∧
      (∀ j, (memJ j).1.l.get (memJ j).2 = ((D.mems.get j).sh, e0s j)) ∧
      (∀ j, mem (D.mems.get j).id = some (memJ j)) ∧
      (∀ j : Fin D.mems.length, ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row)
        (tt : E) (β : GEˣ), D.st.oracles[(D.mems.get j).id]? = some x ∧
        Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
        x.sampleRows.toList = [{ row0 with target := tt }] ∧
        bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
        ∃ (z σ' : ((sigOf cs (memJ j).1.l).om (memJ j).2).Smp),
          smp a0 (memJ j).1 (memJ j).2 = some z ∧
          HEq (((readP (bitsZ cs (D.mems.get j).sh) seed.z, β), fun _ => readE tt) :
            (portOmZ cs (D.mems.get j).sh (e0s j)).Smp) σ' ∧ z.2 = σ'.2 ∧
          ((sigOf cs (memJ j).1.l).om (memJ j).2).Z.val z.1 =
            ((sigOf cs (memJ j).1.l).om (memJ j).2).Z.val σ'.1) ∧
      ∀ j : Fin D.mems.length,
        HEq (strOf cs (D.mems.get j).sh (e0s j) (layOf (D.mems.get j))
            (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
          (VerifiableInference.Desc.Sound.wordsOf G cs (memJ j).1.l (memJ j).1.seat Y (memJ j).2)

/-- **The core's body, at the kind's record, from the facts.** -/
theorem core_at (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (t : T12) (y : Fr.E.Str) (a0 : A) (Y : Strs)
    (facts : CoreFacts cs G Fr π no rad smp mem sits t y a0 Y) (hI : InOrder t.st)
    (hq : QN π (NTuple Fr π no rad rdN) (t, y)) (G0 : Group) (hG : t.st.groups[t.g]? = some G0) :
    ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
      AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
        (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
      ∀ x, sits x → CandAt cs G smp x a0 Y (m x) := by
  obtain ⟨a, rest, G0', Ly, D, hf, hN⟩ := hq
  obtain rfl : G0' = G0 := Option.some.inj (hf.2.1.symm.trans hG)
  obtain ⟨hcs, hJ, ht, hk, hh, hS, hQ, hfind, hmembers, e0s, memJ, hfit, hinj, hsits, he, hmem, seeds,
    s1⟩ := facts a rest G0' Ly D hf
  subst hcs
  obtain ⟨m, hall, hc⟩ := tuple_core G Fr π no rad rdN t y a rest G0' Ly D smp a0 Y mem
    (List.ofFn memJ) rd hrd hf hN hJ ht hk hh e0s hS hQ hfit hI memJ hinj
    (fun x hx => by
      obtain ⟨j, hj⟩ := (List.mem_ofFn' _ _).1 hx
      exact ⟨j, hj⟩) he hmem hfind hmembers seeds s1
  refine ⟨m, hall, fun x hx => hc x ?_⟩
  obtain ⟨j, rfl⟩ := hsits x hx
  exact (List.mem_ofFn' _ _).2 ⟨j, rfl⟩

section
variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (ms : List Mem) (N : NumbersS)
  (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ) (P : P14)
  (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (π : P12) (t₁ t₂ c : ℕ) (rad : Sg → ℕ) (rdN : ℕ → ℕ)
  (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))

/-- **THE CORE AT THE TEST ON G_u, FROM THE FACTS.** -/
theorem tupleNine_of (hrd : ∀ z m part i, rd z m part i = tabP cs (z.1.l.get z.2).1 m part i)
    (facts : ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b → inGu a.1.2 = .ok t →
      CoreFacts cs G Fr π (noAt t₁ t₂ c) rad (smpSt cs oNo stSh) mem
        (fun z => z ∈ ms ∧ (SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 ∨
          SitsAt z (N.tenant .oSp).1 (N.tenant .oSp).2))
        t a.2 ((actQ N f l 9).2 a).1 (strsOfAct Fr ((actQ N f l 9).2 a)))
    (hI : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      InOrder a.1.2.st) :
    TupleNine cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c rad rdN x := by
  intro a τ b t ha hout ht hq G0 hG0
  have hF := facts a τ b t ha hout ht
  cases ht
  obtain ⟨m, hall, hc⟩ := core_at cs G Fr π (noAt t₁ t₂ c) rad rdN (smpSt cs oNo stSh) mem _ rd hrd _
    a.2 _ _ hF (hI a ha) hq G0 hG0
  refine ⟨m, hall, fun μ hμ z hz hs => hc z ⟨hz, ?_⟩⟩
  rcases hμ with rfl | hμ
  · exact .inl hs
  · obtain rfl : μ = .oSp := by simpa using hμ
    exact .inr hs

/-- **THE CORE AT THE TEST ON G_omega, FROM THE FACTS.** -/
theorem tupleTen_of (hrd : ∀ z m part i, rd z m part i = tabP cs (z.1.l.get z.2).1 m part i)
    (facts : ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      x.ior.red.out a τ = some b → inGomega a.1.2 = .ok t →
      CoreFacts cs G Fr π (noAt t₁ t₂ c) rad (smpSt cs oNo stSh) mem
        (fun z => z ∈ ms ∧ (SitsAt z (N.tenant .oSp).1 (N.tenant .oSp).2 ∨
          SitsAt z (N.tenant .oOmega).1 (N.tenant .oOmega).2))
        t a.2 ((actQ N f l 10).2 a).1 (strsOfAct Fr ((actQ N f l 10).2 a)))
    (hI : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      InOrder a.1.2.st) :
    TupleTen cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c rad rdN x := by
  intro a τ b t ha hout ht hq G0 hG0
  have hF := facts a τ b t ha hout ht
  cases ht
  obtain ⟨m, hall, hc⟩ := core_at cs G Fr π (noAt t₁ t₂ c) rad rdN (smpSt cs oNo stSh) mem _ rd hrd _
    a.2 _ _ hF (hI a ha) hq G0 hG0
  refine ⟨m, hall, fun μ hμ z hz hs => hc z ⟨hz, ?_⟩⟩
  rcases hμ with rfl | hμ
  · exact .inl hs
  · obtain rfl : μ = .oOmega := by simpa using hμ
    exact .inr hs

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.tupleNine_of
#print axioms Desc.K14.Law.Fence.tupleTen_of
#print axioms Desc.K14.Law.Fence.core_at
