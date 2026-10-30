-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FineAtRecWrap.lean: the committer that asks for its seed: what makes the goal for
tables with a record speak of EVERY committer. Definitions, the claim as a statement, and its part
without probability.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

OF THE GOAL: THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN.

WHY. `FineAtRec` (OnBytes/Slice/FineAtRec.lean) reads the seed of a record off the committer's own
log, and says nothing of a committer that has hashed its ID and not asked for its seed. Of the ID as
it is here (the head's second paragraph): such a committer exists and can be accepted: the table of
zeros has the answers 0 at every seed. The seed is a function of the oracle at strings made of the
table's name. So the committer is followed by an algorithm that asks there: its output is the
committer's, the prover and the verifier see no difference, and its log shows the seed.

Main definitions.
 `AskRead D`            a `LogRead` with what to ask: `ask`, `qS`, and three laws.
 `RawBlind R`           a property, not a field: the raw string does not see what is asked.
 `AskRead.more`, `wrap R dig C`   the log of what is asked for the first key of an ID in a log; the
                        committer that asks.
 `FineO`                WHAT IS FINE, READ WITH THE ORACLE: under the ID there lies a matrix in
                        range, in the committer's log with what is asked under g put behind it, and
                        the claim holds of it. No condition on the committer.
 `WrapClaim`            the claim, as a statement.
 `askReadOf`, `askRead`   the programs' record as a term of `AskRead`: `askSeed` at the
                        table's name; qS = 2 * `seedCalls` + 1.

Main theorems.
 `wrap_bound`           the committer that asks asks at most qS questions more.
 `seedNotMissing_more`, `fineAtRec_moreAt`   in a log of g's own answers: behind what is asked the
                        seed is not missing; so `FineAtRec` of the outcome with the lengthened log
                        IS `FineO`.
 `fineO_iff_own`        under `RawBlind`: `FineO` reads key, answers and raw string off the
                        committer's own log, the seed alone off the lengthened one.
 `seedAt_ask`           the law `seed_ask` for the programs' record.

What is not claimed. `RawBlind` is not shown here.
That the seed read off the oracle is near uniform is
not said here (OnBytes/Slice/SeedOracle.lean, for one table and one key fixed beforehand). Nothing
on any hash function.

-/
import OnBytes.Slice.SeedAsked
import Rom.StateFirstCB

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (IdKey idCode firstId)

variable {β δ Xi : Type} {D : DecR}

/-! ## What to ask -/

/-- **A reading of logs and keys, with what to ask so that a log shows a key's seed.** `ask k`: an
algorithm without coins that asks at most qS questions. `seed_ask`: behind any log of g's own
answers, the log of `ask k` under g shows the seed of k. -/
structure AskRead (D : DecR) extends LogRead D where
  /-- what to ask for the seed of a key's table -/
  ask : IdKey → OComp (rom 256) Unit
  /-- the number of its questions -/
  qS : ℕ
  /-- it asks at most qS questions -/
  ask_bound : ∀ k, (ask k).QueryBound qS
  /-- it tosses no coin -/
  ask_noCoin : ∀ k, (ask k).NoCoin
  /-- behind a log of g's own answers its log shows the seed -/
  seed_ask : ∀ (g : Fam (rom 256)) (σ : Trace (rom 256)) (k : IdKey), Answers g σ →
    ∃ ρ, seed k (σ ++ ((ask k).withTrace.det g).2) = some ρ

/-- **The raw string does not see what is asked.** A property, not a field: no theorem on `wrap`
uses it. With it `FineO` reads the raw string off the committer's own log (`fineO_iff_own`). It is
asked for every g and every log, also for logs in which two strings have one answer.
-/
def RawBlind (R : AskRead D) : Prop :=
  ∀ (g : Fam (rom 256)) (c : ByteArray) (σ : Trace (rom 256)) (k : IdKey) (cm : Dig 256),
    R.raw c (σ ++ ((R.ask k).withTrace.det g).2) cm = R.raw c σ cm

/-- The log of what is asked, under g, for the first key that σ holds for the ID d; empty if σ holds
none. -/
def AskRead.more (R : AskRead D) (g : Fam (rom 256)) (d : ZKCP.Digest 256)
    (σ : Trace (rom 256)) : Trace (rom 256) :=
  match firstId d σ with
  | some k => ((R.ask k).withTrace.det g).2
  | none => []

/-- **The committer that asks**: C, and then, for the first key that its own log holds for the ID
that it puts out, what `R.ask` asks. Its output is C's. -/
def wrap (R : AskRead D) (dig : β → ZKCP.Digest 256) (C : OComp (rom 256) β) :
    OComp (rom 256) β :=
  C.withTrace.bind fun x =>
    match firstId (dig x.1) x.2 with
    | some k => (R.ask k).bind fun _ => .pure x.1
    | none => .pure x.1

/-- It asks at most qS questions more than C. -/
theorem wrap_bound (R : AskRead D) (dig : β → ZKCP.Digest 256) (C : OComp (rom 256) β) (tC : ℕ)
    (hC : C.QueryBound tC) : (wrap R dig C).QueryBound (tC + R.qS) :=
  OComp.QueryBound.bind (Rom.queryBound_withTrace C tC hC) fun x => by
    cases firstId (dig x.1) x.2 with
    | none => trivial
    | some k => exact OComp.QueryBound.bind (t := 0) (R.ask_bound k) fun _ => trivial

/-! ## Behind what is asked the seed is not missing -/

/-- The first key that a log holds for a digest stays the first when entries are put behind. -/
theorem firstId_append (d : ZKCP.Digest 256) (σ τ : Trace (rom 256)) (k : IdKey)
    (h : firstId d σ = some k) : firstId d (σ ++ τ) = some k := by
  unfold firstId at h ⊢
  rw [List.findSome?_append, h]
  rfl

section
variable (A : D.Claims Xi) (R : AskRead D) (shape₀ : Params.IndexShape)

/-- **Behind what is asked the seed is not missing**, in a log of g's own answers. -/
theorem seedNotMissing_more (g : Fam (rom 256)) (d : ZKCP.Digest 256) (σ : Trace (rom 256))
    (hσ : Answers g σ) : SeedNotMissing R.toLogRead d (σ ++ R.more g d σ) := by
  intro k hk
  cases hf : firstId d σ with
  | none =>
    have hm : R.more g d σ = [] := by
      unfold AskRead.more
      rw [hf]
    rw [hm, List.append_nil, hf] at hk
    cases hk
  | some k' =>
    have hm : R.more g d σ = ((R.ask k').withTrace.det g).2 := by
      unfold AskRead.more
      rw [hf]
    rw [hm] at hk ⊢
    rw [firstId_append d σ _ k' hf] at hk
    obtain rfl : k' = k := Option.some.inj hk
    exact R.seed_ask g σ k' hσ

/-- **What is fine, read with the oracle**: under the ID that the committer put out there lies, in
its own log WITH WHAT `R.ask` ASKS UNDER g PUT BEHIND IT, a matrix in range, and the claim of what
`xReq` reads off the prover's output holds of it. NO CONDITION ON THE COMMITTER: it need not have
asked for its seed. -/
def FineO (dig : β → ZKCP.Digest 256) (xReq : δ → Xi) (g : Fam (rom 256))
    (w : ((β × Trace (rom 256)) × δ) × Trace (rom 256)) : Prop :=
  ∃ M, MatUnderRec A R.toLogRead shape₀ (dig w.1.1.1)
    (w.1.1.2 ++ R.more g (dig w.1.1.1) w.1.1.2) M ∧ A.Rel M (xReq w.1.2)

/-- **If the raw string does not see what is asked, `FineO` reads key, answers and raw string off
the committer's OWN log, and the seed alone off the lengthened one.** -/
theorem fineO_iff_own (hR : RawBlind R) (dig : β → ZKCP.Digest 256) (xReq : δ → Xi)
    (g : Fam (rom 256)) (w : ((β × Trace (rom 256)) × δ) × Trace (rom 256)) :
    FineO A R shape₀ dig xReq g w ↔
      ∃ M k rec u, firstId (dig w.1.1.1) w.1.1.2 = some k ∧ k.1 = shape₀ ∧
        R.recAt k (w.1.1.2 ++ ((R.ask k).withTrace.det g).2) = some rec ∧
        D.dcdRaw (R.raw k.2.1 w.1.1.2 (bytesToDig k.2.2.root)) rec = some u ∧ M = A.mat u ∧
        A.inRange M ∧ A.Rel M (xReq w.1.2) := by
  unfold FineO MatUnderRec
  cases hf : firstId (dig w.1.1.1) w.1.1.2 with
  | none =>
    have hm : R.more g (dig w.1.1.1) w.1.1.2 = [] := by
      unfold AskRead.more
      rw [hf]
    rw [hm, List.append_nil, hf]
    constructor
    · rintro ⟨M, ⟨k, rec, u, h, -⟩, -⟩
      cases h
    · rintro ⟨M, k, rec, u, h, -⟩
      cases h
  | some k' =>
    have hm : R.more g (dig w.1.1.1) w.1.1.2 = ((R.ask k').withTrace.det g).2 := by
      unfold AskRead.more
      rw [hf]
    rw [hm, firstId_append _ _ _ k' hf]
    constructor
    · rintro ⟨M, ⟨k, rec, u, h, hs, hr, hd, hM, hi⟩, hrel⟩
      obtain rfl : k' = k := Option.some.inj h
      rw [hR] at hd
      exact ⟨M, k', rec, u, rfl, hs, hr, hd, hM, hi, hrel⟩
    · rintro ⟨M, k, rec, u, h, hs, hr, hd, hM, hi, hrel⟩
      obtain rfl : k' = k := Option.some.inj h
      exact ⟨M, ⟨k', rec, u, rfl, hs, hr, by rw [hR]; exact hd, hM, hi⟩, hrel⟩

/-- An outcome with what is asked put behind the committer's log. -/
def moreAt (dig : β → ZKCP.Digest 256) (g : Fam (rom 256))
    (w : ((β × Trace (rom 256)) × δ) × Trace (rom 256)) :
    ((β × Trace (rom 256)) × δ) × Trace (rom 256) :=
  (((w.1.1.1, w.1.1.2 ++ R.more g (dig w.1.1.1) w.1.1.2), w.1.2), w.2)

/-- **`FineAtRec` of the outcome with what is asked put behind the committer's log IS `FineO`**, if
that log holds g's own answers. -/
theorem fineAtRec_moreAt (dig : β → ZKCP.Digest 256) (xReq : δ → Xi) (g : Fam (rom 256))
    (w : ((β × Trace (rom 256)) × δ) × Trace (rom 256)) (hσ : Answers g w.1.1.2) :
    FineAtRec A R.toLogRead shape₀ dig xReq (moreAt R dig g w) ↔
      FineO A R shape₀ dig xReq g w :=
  ⟨fun h => h (seedNotMissing_more R g _ _ hσ), fun h _ => h⟩

/-- **THE CLAIM: for every committer C, the probability of "the verifier says yes and it is not
fine, read with the oracle" is at most the probability of "yes and not `FineAtRec`" for the
committer that asks.** The latter is what `join_fine_rec_run` bounds, at tC + qS questions
(`wrap_bound`). A statement here; shown in OnBytes/Slice/WrapLaw.lean (`wrapClaim`). -/
def WrapClaim (dig : β → ZKCP.Digest 256) (xReq : δ → Xi) : Prop :=
  ∀ (C : OComp (rom 256) β) (P : β → OComp (rom 256) δ) (V : β × δ → OComp (rom 256) Bool),
    Rom.Pr (twoExp (twoExp C P) fun x => V (x.1.1, x.2))
        (fun g => {z | z.2 = true ∧ ¬ FineO A R shape₀ dig xReq g z.1}) ≤
      Rom.Pr (twoExp (twoExp (wrap R dig C) P) fun x => V (x.1.1, x.2))
        (fun _ => {z | z.2 = true ∧ ¬ FineAtRec A R.toLogRead shape₀ dig xReq z.1})

end

/-! ## The programs' record -/

/-- Behind a log of g's own answers, the log of `askSeed` under g shows the seed. -/
theorem seedAt_ask (lg s : ℕ) (g : Fam (rom 256)) (σ : Trace (rom 256)) (k : IdKey)
    (hσ : Answers g σ) :
    ∃ ρ, seedAt lg s k
      (σ ++ ((askSeed lg s (Key.nameOf k.1 k.2.1 k.2.2)).withTrace.det g).2) = some ρ := by
  have ha := askSeed_asked g lg s (Key.nameOf k.1 k.2.1 k.2.2)
  have up : ∀ x, Asked ((askSeed lg s (Key.nameOf k.1 k.2.1 k.2.2)).withTrace.det g).2 x →
      Asked (σ ++ ((askSeed lg s (Key.nameOf k.1 k.2.1 k.2.2)).withTrace.det g).2) x :=
    fun x ⟨e, he, hq⟩ => ⟨e, List.mem_append_right _ he, hq⟩
  exact seedAt_of_asked g _ (fun e he => (List.mem_append.1 he).elim (hσ e)
    (det_withTrace_ans g _ e)) k lg s (up _ ha.1) fun x hx => up x (ha.2 x hx)

/-- A reading with `askSeed` as what to ask, from the law on its log. -/
def askReadOf (R : LogRead D) (lg s : ℕ)
    (seed_ask : ∀ (g : Fam (rom 256)) (σ : Trace (rom 256)) (k : IdKey), Answers g σ →
      ∃ ρ, R.seed k
        (σ ++ ((askSeed lg s (Key.nameOf k.1 k.2.1 k.2.2)).withTrace.det g).2) = some ρ) :
    AskRead D where
  toLogRead := R
  ask := fun k => askSeed lg s (Key.nameOf k.1 k.2.1 k.2.2)
  qS := 2 * seedCalls lg s + 1
  ask_bound := fun _ => askSeed_bound lg s _
  ask_noCoin := fun _ => askSeed_noCoin lg s _
  seed_ask := seed_ask

/-- **What to ask, for the programs' record**: `askSeed` at the table's name, at `logRead`. The raw
string and its law are parameters. -/
noncomputable def askRead (T : Fmt.M1.Code) (v eM lg s : ℕ)
    (raw : ByteArray → Trace (rom 256) → Dig 256 → Raw SgX)
    (raw_off : ∀ (S : Finset (List Bool)), (∀ x ∈ S, IsCall169 x) → ∀ c σ cm,
      raw c (offSet S σ) cm = raw c σ cm) : AskRead (decRec T v eM lg s) :=
  askReadOf (logRead T v eM lg s raw raw_off) lg s (seedAt_ask lg s)

end OnBytes.Slice
