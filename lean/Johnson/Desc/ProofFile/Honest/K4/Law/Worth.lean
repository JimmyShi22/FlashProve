-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/Worth.lean: CONDITIONAL: the hypothesis on values `K4Values`
(Law/Table.lean) brought down to the worths of K4's forms, group by group. One definition of a
hypothesis, and statements with their proofs.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: `K4Worths` is a hypothesis. That the hypotheses can
hold together: no example is known. Nothing on soundness, on completeness or on any other property.

  `K4Worths T At b M own rdOf tl p`   at every state s' behind the member's step, every continuation
      of the challenges and the open segment's part A: with what K4 has heard (o), the ledger that
      the run "front" leaves (F₁) and the one that "back", run from F₁, leaves (F₂): `FrontWorth` in
      F₁'s world and `BackWorth` in F₂'s (Johnson/Road/K4/WorthGroups.lean): one field a group of
      the format's claims. The two worlds: under a slot what the ledger shows less its factor times
      the mask row's entry, the mask row read off the witness's tables; an entry of the reads is the
      true entry at what was heard (`entryTrue`), of the matrices M.
  `values_of_worths`: K4Sits, K4Front and K4Worths give K4Values. That the runs return and that each
      form names only what is there is drawn from four of K4Front's eight clauses (asks · names ·
      reads · runs) by `kept_formsT` (Johnson/Road/K4/KeptWorth.lean): THE DEBT IS MOVED TO THESE
      FOUR, NOT PAID.
  `k4_own_share_of_worths`: SO K4's SHARE OF Exchange AT ITS OWN ITEM, under K4Table, K4Sits,
      K4Front and K4Worths, at every At.

Who is meant to prove K4Worths. Field by field: the own claims of six sumchecks (norms' and gated's
first members, rowV, stack, merge): from the general statement on the masked sumcheck · batch, rows,
norms, terms, gated, hot, emb, sideA, sideB: K4's writers · rowL, planes: the lookup's writers.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Kept
import Johnson.Road.K4.KeptWorth
import Johnson.Road.K4.WorthGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS formsBack planesParts)
open OnBytes.Road.K4 (semQ entryTrue kept_atS kept_formsT FrontWorth BackWorth front_worth
  back_worth)
open VerifiableInference.Desc (Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ)
open VerifiableInference.Desc.Plain.K04 (frontRun)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **THE WORTHS, GROUP BY GROUP**, at every state behind the member's step, at every continuation.
A hypothesis's form. Nothing is claimed by the definition. -/
def K4Worths (T : Thread Bk First.S Claim V W X Pb)
    (At : Coins Bk → First.S → Mid W X → Env → Prop) (b : Nat)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    (∀ sh pp,
      ((Array.range (4 * p.P.y.NI)).mapM fun i => (seatS.fork s').shown (o.H.tV.sEnd + i)) =
        some sh →
      planesParts o.v o.H.fo = some pp →
      FrontWorth Reading.gl
        (F₁.worldOf Reading.gl
          (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
          (entryTrue tl o (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))))
        p.P p.g o sh pp) ∧
    ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
      BackWorth Reading.gl
        (F₂.worldOf Reading.gl
          (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
          (entryTrue tl o (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))))
        o

section
variable {T : Thread Bk First.S Claim V W X Pb} {b : Nat}
  {At : Coins Bk → First.S → Mid W X → Env → Prop} {M : First.S → Bound GQ → Road.Mats GQ}
  {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated} {own : List (Nat × Nat)}
  {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par}

/-- **The values, from the worths.** CONDITIONAL: on the seat, four of the eight clauses (asks ·
names · reads · runs) and the worths. -/
theorem values_of_worths (hSit : K4Sits T b p) (hF : K4Front T At b M Hh l St own rdOf tl p)
    (hW : K4Worths T At b M own rdOf tl p) : K4Values T At b M own rdOf tl p := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' A hseg
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  have F := hF blk hblk k s m E ds y cols s' hA hd hS ds'
  obtain ⟨_, _, Ak⟩ := F.asks
  refine kept_formsT _ _ (kept_atS hdec) Ak F.names F.reads F.runs ?_ ?_
  · intro o fs₁ F₁ ho hf
    exact front_worth Reading.gl _ hf
      (hW blk hblk k s m E ds y cols s' hA hd hS ds' A hseg o fs₁ F₁ ho hf).1
  · intro o fs₁ F₁ fs₂ F₂ ho hf hb
    exact back_worth Reading.gl _ hb
      ((hW blk hblk k s m E ds y cols s' hA hd hS ds' A hseg o fs₁ F₁ ho hf).2 fs₂ F₂ hb)

/-- **K4's SHARE OF `Exchange` AT ITS OWN ITEM, FROM THE WORTHS.** CONDITIONAL: on the table's
parameters, the seat, the eight clauses and the worths. -/
theorem k4_own_share_of_worths {iOwn iPl iJo : T.ι} {rest : List T.ι}
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf) (hSit : K4Sits T b p)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (hW : K4Worths T At b M own rdOf tl p) :
    ShareAt T At b [iOwn] :=
  k4_own_share Tb hSit hF (values_of_worths hSit hF hW)

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.values_of_worths
#print axioms ProofFile.Honest.K4.k4_own_share_of_worths
