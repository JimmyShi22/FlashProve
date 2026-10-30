-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/FullErrSubs.lean: the four parameter lists of the holographic IOP at full error lists: the
items on knowledge soundness hold there of every four sub-protocols with a round each; all other
items, and all numbers that the compiler is handed (at the same b, εs), are the same.

In standard terms: the parameter lists (`S.Hyp P`) of the
sub-protocols of the holographic IOP have two parts: round-by-round knowledge soundness, and the
other items. At the trivial soundness errors (probability 1 in every round) the first part holds of
every sub-protocol that has a round.

Definitions, statements (in `Cb.Spec`) and proofs. Framework only: no protocol occurs. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
The sub-protocols are S : `SubsR C` (Hiop/RecSubs.lean): four reductions and a batch protocol: the
test (IOPP) for the constraint relation (`Left.Rlin`, Hiop/RecConf.lean) stands at one instance
(`linOff`) and at up to N (`linOn`). The four sub-protocols are the two preambles (`wf`, `req`), the
IOPP and the link; since the IOPP stands twice, S has five protocols and five shapes, and the lists
are five. The lists are `S.Hyp P` (P : `S.Nums`), their items on knowledge soundness `S.HypK P`
(round-by-round knowledge soundness of the five, each on the statements that `HypK` names, at the
errors in P), the other items `S.HypH P` (Hiop/RecBuild.lean).
The full list of a shape is `Err.full` (Cb/Gen/FullErr.lean): each entry is the number of all values
of that round's verifier message.

Why: S.Hyp P = (S.HypH P, S.HypK P) is one hypothesis. At the full lists HypK says nothing: so
S.HypH P alone gives S.Hyp, at other numbers. That is so if `S.Rounds`: see Limits.






Main names:
  `P.full`: pBad, pHid, q, qpar, qch, bud are P's own.
  `Spec.know_full`: every reduction with a round has round-by-round knowledge soundness at the full
    list: all statements, all relations, every extractor.
  `Spec.jWithin_full`: at the full list all families of bad sets are within the errors, jointly.
  `Spec.sndBP_full`: every batch protocol with a round: "for every statement the prover has lost at
    the start towards (V rejects or ok)" at the full list, at `early` = id, `late` = none (`SndBP`,
    Ior/KnowWide.lean), for every goal ok.
  `Spec.hypK_full`: S.Rounds → S.HypK P.full.
  `Spec.hypH_full`: S.HypH P ↔ S.HypH P.full, proved field by field: each of the 55 items of the
    five lists and the two budgets at `P.full` is, by unfolding, the item at P; no item reads an
    error list.
  `Spec.hyp_full`: S.Rounds → S.HypH P → S.Hyp P.full.
  `Spec.full_lh`: P.full.lh b εs = P.lh b εs: the numbers that the compiler is handed
    (Hiop/RecBuild.lean).
  `Spec.full_alpha`, `Spec.full_zeta`, `Spec.full_fit`: `alphaT`, `zetaT`, `TargetFit`
    (Cond/ObjBounds.lean) at `P.full` are those at P: by unfolding. (`failO`, `WorkFit` take no
    P.)

Notation: `Know` (Ior/Know.lean): round-by-round knowledge soundness, working form; `Doomed s ε bad`
(Iop/Rbr.lean): the prover has lost towards the goal `bad`; `JWithin` (Blocks/Batch/Kit.lean): the
bad sets are within the errors, jointly; `b` : ℕ, `εs` : ℝ≥0∞: in `P.lh b εs` (Hiop/RecBuild.lean),
the fields b, εs of `LH.Nums` (Iop/InteractiveOracleProof.lean); `TargetFit` (Cond/ObjBounds.lean): the conditions on
sizes.

Limits: S.Hyp P.full says of S what S.HypH P says, and nothing on the chance of a cheating prover:
whatever is drawn from it on index binding says nothing on the sub-protocols: at the full lists
every round error, as a probability, is 1. That is so if `S.Rounds`: see below.
Here, where all parameters are variables, "void" would be too much to say of what is drawn on index
binding: with proof of work counted, a bound drawn at the full lists can lie below 1 where every
round carries work; that bound is the work's own: it says that nobody finds the nonces.


And: the proofs that the items on knowledge soundness are free read the first entry of a list alone;
the later entries could be anything. That is so of the four reductions (`doomed_fullOf`); the proof
for the batch protocol (`jWithin_full`) reads every entry.
S.Rounds is a condition: without a round "knowledge soundness" is a plain implication between the
relations, at every list, and is not free. This file does not say that S.HypH P holds of anything.
It says nothing on numerals.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.FullErr
import Hiop.RecBuild
import Ior.KnowWide
import Cond.ObjBounds

set_option autoImplicit false

namespace Iop

/-- every value of every verifier message is bad -/
def BadFam.all : (s : Shape) → BadFam s
  | [] => ()
  | _ :: s => (fun _ => Set.univ, fun _ _ => BadFam.all s)

end Iop

namespace Hiop.SubsR
open Iop
variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C}

/-- the numbers of the five lists with the full lists for their errors; all other numbers are P's
own -/
def Nums.full (P : S.Nums) : S.Nums where
  wf     := { P.wf with err := Err.full S.wf.shape }
  linOff := { P.linOff with err := Err.full S.linOff.shape }
  link   := { P.link with err := Err.full S.link.shape }
  req    := { P.req with err := Err.full S.req.shape }
  linOn  := { P.linOn with err := Err.full S.linOn.ior.shape }

variable (S)

/-- each of the five shapes has a round -/
structure Rounds : Prop where
  wf     : S.wf.shape ≠ []
  linOff : S.linOff.shape ≠ []
  link   : S.link.shape ≠ []
  req    : S.req.shape ≠ []
  linOn  : S.linOn.ior.shape ≠ []

end Hiop.SubsR

namespace Cb
open Iop Prob Hiop TopC Compile Compile.Batch
open scoped ENNReal

namespace Spec

def know_full : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop)
      (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA),
    K.shape ≠ [] → K.Know on RA RB ext (Err.full K.shape)

def jWithin_full : Prop :=
  ∀ (N : ℕ) (s : Shape) (A : RoundSplits s) (G : Fin N → Option (Bool × BadFam s)),
    JWithin N s A (Err.full s) G

def sndBP_full : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (ok : X → E.Str → Tr Q.loc.shape → Prop),
    Q.loc.shape ≠ [] → Q.SndBP N id none ok (Err.full Q.loc.shape)

/-- States that the items on knowledge soundness hold at the full lists, of every four sub-protocols
with a round each (`S.Rounds`). -/
def hypK_full : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), S.Rounds → S.HypK P.full

/-- no other item reads an error list -/
def hypH_full : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), S.HypH P ↔ S.HypH P.full

/-- States: if `S.Rounds` holds, the lists without their items on knowledge soundness (`S.HypH P`)
give the lists, whole, at the full error lists (`S.Hyp P.full`). -/
def hyp_full : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), S.Rounds → S.HypH P → S.Hyp P.full

def full_lh : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b : ℕ) (εs : ℝ≥0∞), P.full.lh b εs = P.lh b εs

def full_alpha : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (N : ℕ) (κ : ℝ≥0∞), P.full.alphaT N κ = P.alphaT N κ

def full_zeta : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (r : C.Rec) (lam : ℕ)
      (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)),
    zetaT P.full r D κ₀ n o = zetaT P r D κ₀ n o

def full_fit : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b : ℕ) (r : C.Rec) (lam : ℕ)
      (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ),
    TargetFit P b r D κ₀ n ↔ TargetFit P.full b r D κ₀ n

end Spec

theorem doomed_fullOf : ∀ (s : Shape), s ≠ [] → ∀ bad : Tr s → Prop, Doomed s (Err.full s) bad
  | [], h, _ => absurd rfl h
  | _ :: _, _, _ => fun _ => cnt_le_card _

theorem know_full : Spec.know_full := fun _ _ _ _ _ _ _ _ _ hne _ _ => doomed_fullOf _ hne _

theorem jWithin_full : Spec.jWithin_full := by
  intro N s
  induction s with
  | nil => intro _ _; trivial
  | cons r s ih =>
    rintro ⟨a, A⟩ G m0 m
    refine ⟨?_, fun v => ih A _⟩
    split
    · intro _ _ _ _; exact cnt_le_card _
    · exact cnt_le_card _

theorem badAll_clean : ∀ (s : Shape), s ≠ [] → ∀ τ : Tr s, ¬ (BadFam.all s).Clean τ
  | [], h, _ => absurd rfl h
  | _ :: _, _, (_, _, _) => fun hc => hc.1 (Set.mem_univ _)

theorem sndBP_full : Spec.sndBP_full := fun X E Q N ok hne =>
  (sndBP_iff_badFam X E Q N ok _).2 ⟨fun _ _ => BadFam.all _,
    fun _ _ τ hc => absurd hc (badAll_clean _ hne τ),
    fun _ _ => jWithin_full N _ _ _⟩

theorem hypK_full : Spec.hypK_full := fun _ S _ h =>
  { wf := know_full _ _ _ _ _ _ _ _ _ h.wf
    linOff := know_full _ _ _ _ _ _ _ _ _ h.linOff
    link := know_full _ _ _ _ _ _ _ _ _ h.link
    req := know_full _ _ _ _ _ _ _ _ _ h.req
    linOn := fun _ => sndBP_full _ _ _ S.N _ h.linOn }

theorem hypH_full : Spec.hypH_full := fun _ _ _ =>
  ⟨fun h =>
    { wf := ⟨h.wf.point, h.wf.isLocal, h.wf.acc, h.wf.prBad, h.wf.prHid, h.wf.exact, h.wf.noReads,
        h.wf.noTie, h.wf.passes, h.wf.hands, h.wf.copy, h.wf.srcIdx, h.wf.srcAux⟩
      linOff := ⟨h.linOff.point, h.linOff.isLocal, h.linOff.acc, h.linOff.noHid, h.linOff.prBad,
        h.linOff.exact, h.linOff.bud0, h.linOff.tied, h.linOff.idxReads⟩
      link := ⟨h.link.point, h.link.isLocal, h.link.acc, h.link.noHid, h.link.prBad, h.link.exact,
        h.link.bud0, h.link.tied, h.link.cntPar, h.link.cntCh⟩
      req := ⟨h.req.point, h.req.isLocal, h.req.acc, h.req.prBad, h.req.prHid,
        h.req.exact, h.req.noReads, h.req.noTie, h.req.passes, h.req.hands, h.req.copy,
        h.req.srcIdx, h.req.srcAux⟩
      linOn := ⟨h.linOn.point, h.linOn.isLocal, h.linOn.coherent, h.linOn.acc, h.linOn.prBad,
        h.linOn.exact, h.linOn.bud0, h.linOn.tied, h.linOn.idxShared, h.linOn.idxReads⟩
      fitOff := h.fitOff
      fitOn := h.fitOn },
   fun h =>
    { wf := ⟨h.wf.point, h.wf.isLocal, h.wf.acc, h.wf.prBad, h.wf.prHid, h.wf.exact, h.wf.noReads,
        h.wf.noTie, h.wf.passes, h.wf.hands, h.wf.copy, h.wf.srcIdx, h.wf.srcAux⟩
      linOff := ⟨h.linOff.point, h.linOff.isLocal, h.linOff.acc, h.linOff.noHid, h.linOff.prBad,
        h.linOff.exact, h.linOff.bud0, h.linOff.tied, h.linOff.idxReads⟩
      link := ⟨h.link.point, h.link.isLocal, h.link.acc, h.link.noHid, h.link.prBad, h.link.exact,
        h.link.bud0, h.link.tied, h.link.cntPar, h.link.cntCh⟩
      req := ⟨h.req.point, h.req.isLocal, h.req.acc, h.req.prBad, h.req.prHid,
        h.req.exact, h.req.noReads, h.req.noTie, h.req.passes, h.req.hands, h.req.copy,
        h.req.srcIdx, h.req.srcAux⟩
      linOn := ⟨h.linOn.point, h.linOn.isLocal, h.linOn.coherent, h.linOn.acc, h.linOn.prBad,
        h.linOn.exact, h.linOn.bud0, h.linOn.tied, h.linOn.idxShared, h.linOn.idxReads⟩
      fitOff := h.fitOff
      fitOn := h.fitOn }⟩

theorem hyp_full : Spec.hyp_full := fun C S P hr h => ⟨(hypH_full C S P).1 h, hypK_full C S P hr⟩

theorem full_lh : Spec.full_lh := fun _ _ _ _ _ => rfl

theorem full_alpha : Spec.full_alpha := fun _ _ _ _ _ => rfl

theorem full_zeta : Spec.full_zeta := fun _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem full_fit : Spec.full_fit := fun _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨h.bias, h.samplers, h.blocks, h.opens, h.slots, h.fmt, h.budget0, h.budgetJ⟩,
    fun h => ⟨h.bias, h.samplers, h.blocks, h.opens, h.slots, h.fmt, h.budget0, h.budgetJ⟩⟩

end Cb
