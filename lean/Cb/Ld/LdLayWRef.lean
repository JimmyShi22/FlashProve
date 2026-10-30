-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayWRef.lean: the reference request, link by link: where its range checks' draws occur;
when its honest prover gives up.

Statements (in `Cb.Spec`) and proofs: unfoldings, on Cb/Ld/LdLayWGive.lean (`Link.GivesAt`,
`Link.RoomAt`, `Chain.Each`). For all data: no toy occurs here.
`H.withheld w x` is the union of two sets of verifier randomness that the honest side names:
`H.Bad`, which takes no argument, and `H.Hid w x`, which takes the witness and the explicit
statement. `A.core` is a map from the witnesses at a joint to a type K; the clause `keeps` of `Good`
asks that, for every w, x, coins c and ρ, `B.core` of the witness with which the honest prover ends
equals `A.core w`. In `Spec.ldLayW_draw` both names stand in the conclusion; the clause `keeps` is
no part of it.

Main names:
  `Spec.ldLayW_draw`: the link in which the verifier draws the ternary matrix (`LdRrD.draw`)
    withholds, at a witness w, exactly the window event (`rngEv`, Cb/Ld/LdRng.lean) of the integer
    matrix that is read off the core of w: nothing in public, nothing that reads a message, a mask,
    a pad or a coin, in this sense:
    `D.draw.H.withheld w x = rngEv D.p (D.c.yz (D.s2.J.rels.core w))` (`core` is by type any map of
    the witness; that `D.c.yz (D.A₀.core (m, wp))` reads no message m, for `D := A.Xa.Q.D` of a body
    `A`: `Spec.ldSegRefAll_noLook`, Cb/Req1/LdSegRefAll.lean, under its hypotheses).
  `Spec.ldLayW_draw_gives`: so it gives up, at the core k, with the probability of the window event
    of k's matrix; `Spec.ldLayW_draw_room`: and it has room at k if some ternary matrix is outside
    that event.
  `Spec.ldLayW_rr_at`, `Spec.ldLayW_body_at`, `Spec.ldLayW_tail_at`, `Spec.ldLayW_ref_at`: a
    property Q of every link of the five moves "read, then the range check" / of a body / of the
    last segment / of the whole chain of the reference request with one first sending
    (`ldReqRef1`) holds of the (last segment's) draw.
  `Spec.ldLayW_ref_gives`: the reference request r with one first sending (`ldReqRef1`), as one
    link, with `r.Hyp`: at every witness with the core k its honest prover gives up with at least
    the probability of the window event of the last segment's range check at k's matrix.

Limits: the other segments' range checks add to the set; that is not counted. This file says nothing
on a bound from above. `Spec.ldLayW_draw` is an equality, for the draw's link alone; the event's
probability: `Spec.ldRng_pWin`, Cb/Ld/LdRng.lean, under `p.OK`. This file does not say that the
event has members: a matter of the numbers (of `rngEv` alone, at a toy's numbers:
`Spec.ldRng_toyNoEv`,
Cb/Req1/LdSegRefToyNoEv.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayWGive
import Cb.Req1.LdReqRefStd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

namespace Spec

/-- What the draw's link withholds. -/
def ldLayW_draw : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (D : LdRrD E Kc E₀ Wp)
      (w : D.s2.J.W) (x : D.s2.J.X),
    D.draw.H.withheld w x = rngEv D.p (D.c.yz (D.s2.J.rels.core w))

def ldLayW_draw_gives : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (D : LdRrD E Kc E₀ Wp) (k : Kc),
    D.draw.GivesAt k (prRho (rngEv D.p (D.c.yz k)))

def ldLayW_draw_room : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (D : LdRrD E Kc E₀ Wp) (k : Kc),
    (∃ ρ, ρ ∉ rngEv D.p (D.c.yz k)) → D.draw.RoomAt k

def ldLayW_rr_at : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E]
      (Q : ∀ A B : Joint Kc, Link Kc A B → Prop) (D : LdRrD E Kc E₀ Wp),
    D.prog.Each Q → Q _ _ D.draw

def ldLayW_body_at : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E]
      (Q : ∀ A B : Joint Kc, Link Kc A B → Prop) (Y : LdBodyD E Kc E₀ Wp)
      (z : LdStage E Kc) (tensor : LdProg Y.tgt z),
    (Y.body z tensor).Each Q → Q _ _ Y.G.Q.D.draw

def ldLayW_tail_at : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (Q : ∀ A B : Joint Kc, Link Kc A B → Prop) (R : LdORE F E Kc)
      (b : LdStage E Kc) (T : LdRefT R b),
    T.tail.Each Q → Q _ _ T.A.Xa.Q.D.draw

def ldLayW_ref_at : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (Q : ∀ A B : Joint Kc, Link Kc A B → Prop) (R : LdORE F E Kc) (a : LdStage E Kc)
      (first : LdSendD a) (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b),
    (ldReqRef1 R first b L T).chain.Each Q → Q _ _ T.A.Xa.Q.D.draw

/-- Under the one hypothesis below: the honest prover of the reference request with one first
sending gives up (with which probability at least: the head's row). -/
def ldLayW_ref_gives : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b)
      (T : LdRefT R b) (d : a.J.W) (k : Kc),
    (ldReqRef1 R first b L T).Hyp →
    ((ldReqRef1 R first b L T).chain.link d).GivesAt
      k (prRho (rngEv T.A.Xa.Q.D.p (T.A.Xa.Q.D.c.yz k)))

end Spec

theorem ldLayW_draw : Spec.ldLayW_draw := by
  intro E Kc E₀ Wp _ _ D w x
  exact Set.empty_union _

theorem ldLayW_draw_gives : Spec.ldLayW_draw_gives := by
  intro E Kc E₀ Wp _ _ D k
  refine ⟨rngEv D.p (D.c.yz k), le_refl _, fun w x hk => ?_⟩
  rw [ldLayW_draw, hk]

theorem ldLayW_draw_room : Spec.ldLayW_draw_room := by
  intro E Kc E₀ Wp _ _ D k h
  obtain ⟨ρ, hρ⟩ := h
  refine ⟨ρ, fun w x hk => ?_⟩
  rw [ldLayW_draw, hk]
  exact hρ

theorem ldLayW_rr_at : Spec.ldLayW_rr_at := by
  intro E Kc E₀ Wp _ _ Q D h
  unfold LdRrD.prog at h
  rw [LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc] at h
  have c3 : (LdMv.sub D.s2 D.s3 (.one D.draw)).chain = .one D.draw := by rw [LdMv.chain]
  have h3 := h.1.1.2
  rw [c3, each_one] at h3
  exact h3

theorem ldLayW_body_at : Spec.ldLayW_body_at := by
  intro E Kc E₀ Wp _ _ Q Y z tensor h
  unfold LdBodyD.body at h
  rw [ldLayW_app, LdProg.each_snoc, ldLayW_app, ldLayW_app] at h
  exact ldLayW_rr_at E Kc E₀ Wp Q Y.G.Q.D h.1.1.1.2

theorem ldLayW_tail_at : Spec.ldLayW_tail_at := by
  intro F E Kc _ _ _ _ _ Q R b T h
  unfold LdRefT.tail at h
  rw [LdProg.each_snoc, ldLayW_app] at h
  exact ldLayW_body_at E Kc _ _ Q T.A.Y _ _ h.1.2

theorem LdProg.each_asSub {E Kc : Type} [Field E] [Fintype E]
    (Q : ∀ A B : Joint Kc, Link Kc A B → Prop) {a b : LdStage E Kc} (p : LdProg a b) :
    p.asSub.Each Q ↔ p.Each Q := by
  induction p with
  | nil => rw [LdProg.asSub_nil]
  | snoc p m ih => rw [LdProg.asSub_snoc, LdProg.each_snoc, LdProg.each_snoc, ih, LdMv.asSub_chain]

theorem ldLayW_ref_at : Spec.ldLayW_ref_at := by
  intro F E Kc _ _ _ _ _ Q R a first b L T h
  have h1 := ((ldLayW_req E Kc Q _ _ _).1 h).last
  have h2 : (T.tail.app R.lastP).asSub.Each Q := h1
  rw [LdProg.each_asSub, ldLayW_app] at h2
  exact ldLayW_tail_at F E Kc Q R b T h2.1

/-- all of the bundle but zero knowledge, in every link of a request -/
theorem LdReq.chain_allB {E Kc : Type} [Field E] [Fintype E] {a z : LdStage E Kc}
    (r : LdReq a z) (h : r.Hyp) : r.chain.AllB :=
  r.last.onto_allB _
    (r.segs.onto_allB _
      (r.more.onto_allB _ ((allB_one _).2 (goodB_of_goodT' (r.first.goodT h.first))) h.more) h.segs)
    h.last

theorem ldLayW_ref_gives : Spec.ldLayW_ref_gives := by
  intro F E Kc _ _ _ _ _ R a first b L T d k hH
  refine ldLayW_gives Kc _ _ _ d k _ (LdReq.chain_allB _ hH) fun h => ?_
  exact ldLayW_ref_at F E Kc _ R a first b L T h (ldLayW_draw_gives E Kc _ _ T.A.Xa.Q.D k)

end Cb
