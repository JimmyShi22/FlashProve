-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamFactsQ.lean: **tupleNine_of | tupleTen_of (SeamFacts.lean) WITH A WEAKER PREMISE: THE FACTS MAY SPEND THE GAME's OWN CONCLUSION (QN π (NTuple …) at the record behind the door in).** Two statements and one lemma; the proofs are SeamFacts.lean's with one argument more.
What for. site_nine | site_ten (Johnson/Desc/K12/Coin/SiteAtSeats.lean; MemberFacts' first clause) spend "the yes of gpL", which NTuple holds as its own "there is": CoreFacts was asked without it. TupleNine | TupleTen have QN among their own premises: so it is at hand.
  fixes_unique      what a record fixes, it fixes once.
  **tupleNine_ofQ | tupleTen_ofQ**   as tupleNine_of | tupleTen_of; facts : … → QN π (NTuple Fr π (noAt t₁ t₂ c) rad rdN) (t, a.2) → CoreFacts ….
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamFacts

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

/-- What a record fixes, it fixes once. -/
theorem fixes_unique {π : P12} {t : T12} {a a' : Fmt.M1.Stage} {rest rest' : List Fmt.M1.Stage}
    {G0 G0' : Group} {Ly Ly' : GroupLayout} {D D' : Plain} (h : Fixes π t a rest G0 Ly D)
    (h' : Fixes π t a' rest' G0' Ly' D') : a = a' ∧ rest = rest' ∧ G0 = G0' ∧ Ly = Ly' ∧ D = D' := by
  obtain ⟨rfl, rfl⟩ := List.cons.inj (h.1.symm.trans h'.1)
  obtain rfl := Option.some.inj (h.2.1.symm.trans h'.2.1)
  obtain rfl := Option.some.inj (h.2.2.1.symm.trans h'.2.2.1)
  exact ⟨rfl, rfl, rfl, rfl, Option.some.inj ((h.2.2.2 default).symm.trans (h'.2.2.2 default))⟩

section
variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (ms : List Mem) (N : NumbersS)
  (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ) (P : P14)
  (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (π : P12) (t₁ t₂ c : ℕ) (rad : Sg → ℕ) (rdN : ℕ → ℕ)
  (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))

/-- **THE CORE AT THE TEST ON G_u, FROM THE FACTS, WHICH MAY SPEND THE GAME's CONCLUSION.** -/
theorem tupleNine_ofQ (hrd : ∀ z m part i, rd z m part i = tabP cs (z.1.l.get z.2).1 m part i)
    (facts : ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b → inGu a.1.2 = .ok t →
      QN π (NTuple Fr π (noAt t₁ t₂ c) rad rdN) (t, a.2) →
      CoreFacts cs G Fr π (noAt t₁ t₂ c) rad (smpSt cs oNo stSh) mem
        (fun z => z ∈ ms ∧ (SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 ∨
          SitsAt z (N.tenant .oSp).1 (N.tenant .oSp).2))
        t a.2 ((actQ N f l 9).2 a).1 (strsOfAct Fr ((actQ N f l 9).2 a)))
    (hI : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      InOrder a.1.2.st) :
    TupleNine cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c rad rdN x := by
  intro a τ b t ha hout ht hq G0 hG0
  have hF := facts a τ b t ha hout ht hq
  cases ht
  obtain ⟨m, hall, hc⟩ := core_at cs G Fr π (noAt t₁ t₂ c) rad rdN (smpSt cs oNo stSh) mem _ rd hrd _
    a.2 _ _ hF (hI a ha) hq G0 hG0
  refine ⟨m, hall, fun μ hμ z hz hs => hc z ⟨hz, ?_⟩⟩
  rcases hμ with rfl | hμ
  · exact .inl hs
  · obtain rfl : μ = .oSp := by simpa using hμ
    exact .inr hs

/-- **THE CORE AT THE TEST ON G_omega, FROM THE FACTS, WHICH MAY SPEND THE GAME's CONCLUSION.** -/
theorem tupleTen_ofQ (hrd : ∀ z m part i, rd z m part i = tabP cs (z.1.l.get z.2).1 m part i)
    (facts : ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      x.ior.red.out a τ = some b → inGomega a.1.2 = .ok t →
      QN π (NTuple Fr π (noAt t₁ t₂ c) rad rdN) (t, a.2) →
      CoreFacts cs G Fr π (noAt t₁ t₂ c) rad (smpSt cs oNo stSh) mem
        (fun z => z ∈ ms ∧ (SitsAt z (N.tenant .oSp).1 (N.tenant .oSp).2 ∨
          SitsAt z (N.tenant .oOmega).1 (N.tenant .oOmega).2))
        t a.2 ((actQ N f l 10).2 a).1 (strsOfAct Fr ((actQ N f l 10).2 a)))
    (hI : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      InOrder a.1.2.st) :
    TupleTen cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c rad rdN x := by
  intro a τ b t ha hout ht hq G0 hG0
  have hF := facts a τ b t ha hout ht hq
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

#print axioms Desc.K14.Law.Fence.fixes_unique
#print axioms Desc.K14.Law.Fence.tupleNine_ofQ
#print axioms Desc.K14.Law.Fence.tupleTen_ofQ
