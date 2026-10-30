-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P4SR/K6BackAtSeat.lean (a law about the seat's form and the lot's block, no part of
either): THE NAMED PREMISE K6Back (Johnson/Desc/Kinds/Law/K6SilentRides.lean: THE WAY BACK: where
the kind's own run answers and leaves the heard reply, the run that stands at the link's hearing
block under that name gives that answer) AT THE SEATED BLOCK IN THE SEAT's DRESS, and at the
description's own first chain. Theorems.

Why. P4SR/K6StatesAtSeat.lean gives the way there (a run in the dress answers only as the kind's own
does). The equation of the silent reader with the run wants the way back too. The dress is the guard
on the heard reply (IMR/SeatForm.lean: guardRun): its yes is the run's yes TOGETHER WITH "the heard
reply is as it was" (claim_yes: both ways). So under that clause the way back holds.

What is said.
  lookup_of_find    the first pair with a name, as the list's lookup under it.
  kind_no_join      the bare kind states no run under "join".
  same_of_eq        the guard's test says yes where the heard reply is as it was.
  **k6Back_of_laid**   for all W, l, ms, b', b, name, a, Lk, i with Head.seatedClaims W l ms = some
                  b', LaidAlone ProofFile.sameReply b b' name a and Lk.hear[i]? = some b: there is iU3
                  with W.H.tl.ix.U.getD 2 none = some iU3 and K6Back W.hS iU3 (parOf W.hS (workAtW
                  W)) l 4 (K9.statesOfLink Lk) i.
  **k6Back_at_seat**   in the goals' scope, at an opening of the description's value at the second
                  hash function: the same at link 24, hearing block number 3; WITH K6States at the
                  same Lk and iU3.

The letters. Lk and iU3 stand under "there is", each tied by the equation that makes it; ONE Lk AND
ONE iU3 SERVE BOTH K6States AND K6Back.
What it does not give. That an opening is there. At the second hash function alone; the full size
alone; in scope: as k6_of is. Nothing on soundness.

-/
import Johnson.IMR.K6Seat
import Johnson.P4SR.K6StatesAtSeat
import Johnson.Desc.Kinds.Law.K6SilentRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4
open Inst.Model (ScalesAndPolicy)
open VerifiableInference.Desc (Block Claim Chain Link Place FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW seated_claims seated_run seated_join K6States
  K6Back)
open ProofFile (Cl)

/-- The first pair with a name, as the list's lookup under it. -/
theorem lookup_of_find {β : Type} : ∀ (l : List (String × β)) (n : String) (r : β),
    l.find? (fun x => x.1 == n) = some (n, r) → l.lookup n = some r
  | [], _, _, h => by cases h
  | (a, q) :: tl, n, r, h => by
    by_cases e : a = n
    · subst e
      rw [List.find?_cons_of_pos (by simp)] at h
      obtain rfl : q = r := congrArg Prod.snd (Option.some.inj h)
      exact List.lookup_cons_self
    · have e' : (n == a) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun k => e k.symm
      rw [List.find?_cons_of_neg (by simpa using e)] at h
      rw [List.lookup_cons, e']
      exact lookup_of_find tl n r h

/-- The bare kind states no run under "join". -/
theorem kind_no_join (L : Seat S) (l piece : Nat) (p : Par) :
    (kind asClaim L l piece p).claims.lookup "join" = none := rfl

/-- The guard's test says yes where the heard reply is as it was. -/
theorem same_of_eq {s t : S} (h : t.out.reply = s.out.reply) : ProofFile.sameReply s t = true := by
  unfold ProofFile.sameReply
  exact beq_iff_eq.2 h.symm

/-- **K6Back at our seated block in the seat's dress.** -/
theorem k6Back_of_laid {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b' b : Block S Claim} {name : String} {a : Place} {Lk : Link S Claim} {i : Nat}
    (hs : seatedClaims W l ms = some b') (hla : IM.LaidAlone ProofFile.sameReply b b' name a)
    (hb : Lk.hear[i]? = some b) {iU3 : Nat} (hU : W.H.tl.ix.U.getD 2 none = some iU3) :
    K6Back W.hS iU3 (parOf W.hS (workAtW W)) l 4 (VerifiableInference.Desc.K9.statesOfLink Lk)
      i := by
  have hst : VerifiableInference.Desc.K9.statesOfLink Lk i = b.claims := by
    unfold VerifiableInference.Desc.K9.statesOfLink
    rw [hb]
    rfl
  refine ⟨fun n run run' hf hk k t y hy hr => ?_, fun run hf k t y hy hr => ?_⟩
  · rw [hst] at hf
    obtain ⟨r', h', -, hyes⟩ := IM.claim_yes hla (lookup_of_find _ _ _ hf)
    have hne : n ≠ "join" := by
      rintro rfl
      rw [kind_no_join] at hk
      cases hk
    obtain ⟨j, hU', hk'⟩ := seated_run hs h' hne
    obtain rfl : j = iU3 := Option.some.inj (hU'.symm.trans hU)
    obtain rfl : r' = run' := Option.some.inj (hk'.symm.trans hk)
    exact (hyes k t y).2 ⟨hy, same_of_eq hr⟩
  · rw [hst] at hf
    obtain ⟨r', h', -, hyes⟩ := IM.claim_yes hla (lookup_of_find _ _ _ hf)
    obtain ⟨j, hU', e⟩ := seated_join hs h'
    obtain rfl : j = iU3 := Option.some.inj (hU'.symm.trans hU)
    exact (hyes k t y).2 ⟨by rw [e]; exact hy, same_of_eq hr⟩

/-- **K6States and K6Back at link 24's fourth hearing block of the description's first chain.** -/
theorem k6Back_at_seat {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (iU3 : Nat), c.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      K6States Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
      K6Back Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 := by
  obtain ⟨Lk, b, b', ms, e1, e2, _, hs, hla, _, _, _⟩ := IM.k6_of hS hR O
  obtain ⟨iU3, hU, K⟩ := k6States_of_laid hs hla e2
  exact ⟨Lk, iU3, e1, hU, K, k6Back_of_laid hs hla e2 hU⟩

end P4

#print axioms P4.k6Back_of_laid
#print axioms P4.k6Back_at_seat
