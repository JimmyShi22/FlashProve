-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FineAtRec.lean: the goal's statement for stored tables with a record.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN. Definitions, six small laws, and an implication:
no part that meets its hypotheses with a bound below 1 is written.

Why. This file writes what it is for the outcome of "a committer, then a prover" to be fine, for
tables with a record, so that the statement which would be aimed at, at a setting with a record,
can be read.


Main definitions.
 `LogRead D` how a log and a key are read: the raw string under a root; a key's seed as the log
     shows it; the answers in the key. DATA with two laws; no field is defined.
 `MatUnderRec A R shape₀ d σ M` M is the matrix under the ID d in σ: the first key that σ holds for
     d has the shape shape₀; σ shows that key's record; with it the raw string at that key's digest
     and root decodes; M is its matrix, and is in range.
 `SeedNotMissing`, `FineAtRec` if the seed is not missing (the committer's own log, where it holds a
     key for the ID that it put out, shows the seed of the first such key), then under that ID there
     lies, in that log, a matrix of which the claim read off the prover's output holds. A log that
     holds no key for the ID is not fine.
Main theorems: `MatUnderRec.unique`; `matUnderRec_offSet`, `fineAtRec_offBoth`; `join_fine_rec_run`.

Where the record comes from. The ANSWERS stand in the key, which the ID binds: they are read from
the first key that the committer's log holds for the ID. The SEED follows from the table's name (its
root, the configuration's digest and six numbers of the shape; NOT the answers) by hash calls in two
steps: one call on the name, then a few calls at strings that hold the first's answer (by a reading
of the program's text; not written here). What is fine must stay a function of the ID and the
committer's log, or read the oracle. OF THE ID AS IT IS HERE (the head's second paragraph): A
COMMITTER NEED NOT ASK FOR ITS SEED: the table of zeros has the answers 0 at every seed, so a
committer can write them, publish the ID and never ask; its proofs pass. So "no seed in the log: no
matrix: not fine" would be FALSE as a claim. Of an ID whose string holds the seed
(`Fmt.publishedBytes`, Fmt/Rules4.lean) nothing is said here. THREE CANDIDATES. TAKEN HERE: what is
fine is CONDITIONAL: it lets go only the outcomes in which the committer's own log holds a key for
the ID and does not show that key's seed (`SeedNotMissing` fails). The statement for every committer
then comes by a wrapping (OnBytes/Slice/FineAtRecWrap.lean, WrapLaw.lean: `wrapClaim`,
`join_fine_rec_all`): let the committer, at its end, ask for the seed of the first key in its own
log: the law of what follows does not turn, its count of queries grows by the seed's few calls, and
the seed is never missing in its log. SO FOR EVERY COMMITTER WHAT IS FINE READS THE ORACLE AT THE
SEED's STRINGS: table, key and answers come off the committer's own log; THE SEED DOES NOT. The
first candidate, wrapped, and the third say the same. For the wrapping `LogRead` lacks a field, what
to ask: `AskRead` of FineAtRecWrap.lean has it. The second: that wrapping's property as a hypothesis
on the committer. The third: what is fine reads the oracle at the seed's strings; then the joins
must take a `Fine` that sees the oracle.

What is not claimed. IT IS THE STATEMENT "WITH A RECORD", NOT "A RECORD WITH WORK". Of proof of work
nothing is said: it would stand in the checkers and in the parts' bounds, which are variables. By a
reading of the program's text the chain on which a record's seeds are drawn has none, whatever the
parameter file says (the call is written with work 0): whoever tries many roots for a seed at which
a record does not single one table out pays one try a root, without a factor for work. No condition
on the radius is written. ALL THREE PARTS, the verifier, the sample map, the way out, both readings
of a log, the shape, the matrix and the claims are variables; nothing is joined, and no part for a
table with a record exists. A member of `LogRead` is written from the program's text in
OnBytes/Slice/RecordRead.lean; it is put into no statement here. That a matrix lies under any ID in
any log: not shown. The public strings' sets are variables with their conditions. All limits in the
heads of JoinDecRec.lean and DecoderRec.lean hold here too. That shape₀ is the shape at whose sizes
the string is read and decoded: not asked.
-/
import OnBytes.Slice.JoinDecRec
import OnBytes.Slice.FineAt

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (IdKey idCode firstId)

variable {β δ Xi : Type} {D : DecR}

/-! ## Two readings of a log, as data -/

/-- **How a log and a key are read**, for tables with a record. Data with two laws; no field is
defined here. `raw c σ cm`: the raw string under the root cm in the log σ, at the configuration
digest c.

`seed k σ`: the seed of the key
k's table AS THE LOG σ SHOWS IT: what follows from the oracle's answers, in σ, at the strings made
of the table's name; nothing, if σ does not hold these entries. `ans k`: the answers that stand in
the key; nothing, if they have not the right number. Neither `raw` nor `seed` sees the entries of a
log at strings of calls with the number 169. -/
structure LogRead (D : DecR) where
  /-- the raw string under a root in a log, at a configuration digest -/
  raw : ByteArray → Trace (rom 256) → Dig 256 → Raw SgX
  /-- the seed of a key's table, as a log shows it -/
  seed : IdKey → Trace (rom 256) → Option D.Z.D
  /-- the answers that stand in a key -/
  ans : IdKey → Option (D.ix.Row × D.Z.S → GE)
  /-- `raw` does not see the entries at strings of calls with the number 169 -/
  raw_off : ∀ (S : Finset (List Bool)), (∀ s ∈ S, IsCall169 s) → ∀ c σ cm,
    raw c (offSet S σ) cm = raw c σ cm
  /-- nor does `seed` -/
  seed_off : ∀ (S : Finset (List Bool)), (∀ s ∈ S, IsCall169 s) → ∀ k σ,
    seed k (offSet S σ) = seed k σ

/-- The record of the key k as the log σ shows it: the seed off the log, the answers off the key. -/
def LogRead.recAt (R : LogRead D) (k : IdKey) (σ : Trace (rom 256)) : Option D.Rec :=
  (R.seed k σ).bind fun ρ => (R.ans k).map fun a => (ρ, a)

/-- It does not see the entries at strings of calls with the number 169. -/
theorem LogRead.recAt_off (R : LogRead D) (S : Finset (List Bool)) (hS : ∀ s ∈ S, IsCall169 s)
    (k : IdKey) (σ : Trace (rom 256)) : R.recAt k (offSet S σ) = R.recAt k σ := by
  unfold LogRead.recAt
  rw [R.seed_off S hS]

/-! ## What lies under an ID in a committer's log -/

section
variable (A : D.Claims Xi) (R : LogRead D) (shape₀ : Params.IndexShape)

/-- **The matrix under the ID d in the log σ is M**: the first key that σ holds for d has the shape
`shape₀`; σ shows that key's record; with that record the raw string that is read off σ, at the
digest in that key, under the root in that key, decodes; M is the matrix of what it decodes to; and
M is in range. Of an outcome it reads d and σ alone: no oracle, no table of values, nothing of a
prover. At a seed at which the record does not single one table out, M is the decoder's choice; that
such seeds are rare is in the parts' bounds, not here. -/
def MatUnderRec (d : ZKCP.Digest 256) (σ : Trace (rom 256)) (M : A.Mat) : Prop :=
  ∃ k rec u, firstId d σ = some k ∧ k.1 = shape₀ ∧ R.recAt k σ = some rec ∧
    D.dcdRaw (R.raw k.2.1 σ (bytesToDig k.2.2.root)) rec = some u ∧ M = A.mat u ∧ A.inRange M

/-- At most one matrix lies under an ID in a log. -/
theorem MatUnderRec.unique {d : ZKCP.Digest 256} {σ : Trace (rom 256)} {M M' : A.Mat}
    (h : MatUnderRec A R shape₀ d σ M) (h' : MatUnderRec A R shape₀ d σ M') : M = M' := by
  obtain ⟨k, rec, u, hk, -, hr, hu, rfl, -⟩ := h
  obtain ⟨k', rec', u', hk', -, hr', hu', rfl, -⟩ := h'
  cases hk.symm.trans hk'
  cases hr.symm.trans hr'
  cases hu.symm.trans hu'
  rfl

/-- It does not see the entries at strings of calls with the number 169. -/
theorem matUnderRec_offSet (S : Finset (List Bool)) (hS : ∀ s ∈ S, IsCall169 s)
    (d : ZKCP.Digest 256) (σ : Trace (rom 256)) (M : A.Mat) :
    MatUnderRec A R shape₀ d (offSet S σ) M ↔ MatUnderRec A R shape₀ d σ M := by
  unfold MatUnderRec
  simp only [firstId_offSet S hS, R.raw_off S hS, R.recAt_off S hS]

/-- **The seed is not missing**: if the log σ holds a key for the ID d, it shows the seed of the
first such key. TRUE IF IT HOLDS NONE: so an ID that the committer never hashed stays "not fine". -/
def SeedNotMissing (d : ZKCP.Digest 256) (σ : Trace (rom 256)) : Prop :=
  ∀ k, firstId d σ = some k → ∃ ρ, R.seed k σ = some ρ

/-- It does not see the entries at strings of calls with the number 169. -/
theorem seedNotMissing_offSet (S : Finset (List Bool)) (hS : ∀ s ∈ S, IsCall169 s)
    (d : ZKCP.Digest 256) (σ : Trace (rom 256)) :
    SeedNotMissing R d (offSet S σ) ↔ SeedNotMissing R d σ := by
  unfold SeedNotMissing
  simp only [firstId_offSet S hS, R.seed_off S hS]

/-- **What is fine**, of an outcome of "a committer, then a prover", for tables with a record: IF
THE SEED IS NOT MISSING (the committer's own log, where it holds a key for the ID that it put out,
shows the seed of the first such key), then under that ID there lies, in that log, a matrix in
range, and the claim of what `xReq` reads off the prover's output holds of it. OF A COMMITTER THAT
HAS HASHED ITS ID AND NOT ASKED FOR ITS SEED IT SAYS NOTHING: see the head. -/
def FineAtRec (dig : β → ZKCP.Digest 256) (xReq : δ → Xi)
    (w : ((β × Trace (rom 256)) × δ) × Trace (rom 256)) : Prop :=
  SeedNotMissing R (dig w.1.1.1) w.1.1.2 →
    ∃ M, MatUnderRec A R shape₀ (dig w.1.1.1) w.1.1.2 M ∧ A.Rel M (xReq w.1.2)

/-- It does not see the entries at strings of calls with the number 169, in either log. -/
theorem fineAtRec_offBoth (dig : β → ZKCP.Digest 256) (xReq : δ → Xi) (S : Finset (List Bool))
    (hS : ∀ s ∈ S, IsCall169 s) (w : ((β × Trace (rom 256)) × δ) × Trace (rom 256)) :
    FineAtRec A R shape₀ dig xReq (offBoth S w) ↔ FineAtRec A R shape₀ dig xReq w := by
  unfold FineAtRec
  show (SeedNotMissing R (dig w.1.1.1) (offSet S w.1.1.2) →
    ∃ M, MatUnderRec A R shape₀ (dig w.1.1.1) (offSet S w.1.1.2) M ∧ A.Rel M (xReq w.1.2)) ↔ _
  simp only [matUnderRec_offSet A R shape₀ S hS, seedNotMissing_offSet R S hS]

end

/-! ## The join with what is fine written out -/

/-- **THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN. The goal's statement for stored tables with a
record.** `join_id_decR_run` with `FineAtRec` for what is fine. The public strings' sets S₀, S₁ hold
strings of calls with the number 169 alone. C puts out something of which `dig` reads the ID; P, on
C's output, something of which `table` reads the stored table's ROOT AND ANSWERS and `xReq` what is
claimed; V, an algorithm without coins, runs on the two outputs. With probability at most B: V says
yes, THE SEED IS NOT MISSING in C's own log (`SeedNotMissing`), and it is not so that under the ID,
in that log, with the record that it shows, there lies a matrix in range of which the claim holds.
IN `hYes`, among its clauses: the two ties of records; where C's log shows the
key's seed, the record that the key's checker speaks of IS what that log and the key show
(`R.recAt`): THIS CLAUSE TIES C's LOG TO g: X' must hold the outcomes whose log does not hold g's
answers (they have probability 0; no lemma here says so); the key's part reads `R.raw` off C's log;
the third checker's instance is the one read off P's output. ALL THREE PARTS, the verifier, the
decoder's sample map, the two readings of a log, the shape, the matrix and the claims are variables.
-/
theorem join_fine_rec_run (w : DecR.Way D) (sc : List Bool) (S₀ : Finset (List Bool))
    (S₁ : Tab → Finset (List Bool))
    (h169₀ : ∀ s ∈ S₀, IsCall169 s) (h169₁ : ∀ T₀, ∀ s ∈ S₁ T₀, IsCall169 s)
    (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256) (P : β → OComp (rom 256) δ)
    (shape₀ : Params.IndexShape) (table : δ → Params.TableName) (tC tP : ℕ)
    (hC : C.QueryBound tC) (hP : ∀ b, (P b).QueryBound tP)
    (K E F : Tab → Tab → PartO 256 ((β × Trace (rom 256)) × δ) SgX)
    (hK : ∀ T₀ T₁, (K T₀ T₁).OK) (hE : ∀ T₀ T₁, (E T₀ T₁).OK) (hF : ∀ T₀ T₁, (F T₀ T₁).OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : ∀ T₀ T₁, (K T₀ T₁).Stable bS)
    (hKE : ∀ T₀ T₁, SameRaw (K T₀ T₁) (E T₀ T₁)) (hEF : ∀ T₀ T₁, SameRaw (E T₀ T₁) (F T₀ T₁))
    (A : D.Claims Xi) (R : LogRead D) (xReq : δ → Xi) (xOf : ∀ T₀ T₁, (F T₀ T₁).Out → Xi)
    (recK : ∀ T₀ T₁, (K T₀ T₁).Out → D.Rec) (recE₀ recE₁ : ∀ T₀ T₁, (E T₀ T₁).Out → D.Rec)
    (recF : ∀ T₀ T₁, (F T₀ T₁).Out → D.Rec)
    (hLK : ∀ T₀ T₁ oK Y, (K T₀ T₁).Lang oK [Y] → DecR.LangK A w (recK T₀ T₁ oK) Y)
    (hLE : ∀ T₀ T₁ oE Y₀ Y₁, (E T₀ T₁).Lang oE [Y₀, Y₁] →
      DecR.LangE w (recE₀ T₀ T₁ oE) (recE₁ T₀ T₁ oE) Y₀ Y₁)
    (hLF : ∀ T₀ T₁ oF Y, (F T₀ T₁).Lang oF [Y] →
      DecR.LangP A w (xOf T₀ T₁ oF) (recF T₀ T₁ oF) Y)
    (X' : Tab → Tab → Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (bX' : ℝ≥0∞)
    (hX' : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C))
      fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))).withTrace (X' T₀ T₁) ≤ bX')
    (hid : ∀ k s, idCode k = some s → s ∉ S₀ ∧ ∀ T₀, s ∉ S₁ T₀)
    (V : β × δ → OComp (rom 256) Bool) (hV : ∀ x, (V x).NoCoin)
    (hYes : ∀ T₀ T₁ g z,
      (V (z.1.1.1, z.1.2)).det (over S₀ T₀ (over (S₁ T₀) T₁ g)) = true → z ∉ X' T₀ T₁ g →
      (∃ s, idCode (keyAt shape₀ sc table T₀ z.1.2) = some s ∧
        over S₀ T₀ (over (S₁ T₀) T₁ g) () s = dig z.1.1.1) ∧ ∃ oK oE oF cm',
        ((K T₀ T₁).chk z.1).det g = some oK ∧ ((E T₀ T₁).chk z.1).det g = some oE ∧
        ((F T₀ T₁).chk z.1).det g = some oF ∧
        (K T₀ T₁).roots oK = [bytesToDig (table z.1.2).root] ∧
        (E T₀ T₁).roots oE = [bytesToDig (table z.1.2).root, cm'] ∧
        (F T₀ T₁).roots oF = [cm'] ∧
        recE₀ T₀ T₁ oE = recK T₀ T₁ oK ∧ recF T₀ T₁ oF = recE₁ T₀ T₁ oE ∧
        (∀ ρ, R.seed (keyAt shape₀ sc table T₀ z.1.2) z.1.1.2 = some ρ →
          R.recAt (keyAt shape₀ sc table T₀ z.1.2) z.1.1.2 = some (recK T₀ T₁ oK)) ∧
        (NoClash z.1.1.2 → (K T₀ T₁).raw z.1.1.2 (bytesToDig (table z.1.2).root) =
          R.raw (cOf sc T₀) z.1.1.2 (bytesToDig (table z.1.2).root)) ∧
        xOf T₀ T₁ oF = xReq z.1.2)
    (B : ℝ≥0∞)
    (hB : ∀ T₀ T₁, (K T₀ T₁).bound (tC + tP) + ((E T₀ T₁).bound (tC + tP) +
      ((F T₀ T₁).bound (tC + tP) +
        (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) ≤ B) :
    Rom.Pr (twoExp (twoExp C P) fun x => V (x.1.1, x.2))
      (fun _ => {z | z.2 = true ∧ ¬ FineAtRec A R shape₀ dig xReq z.1}) ≤ B :=
  join_id_decR_run w S₀ S₁ C dig P (fun T₀ _ d => keyAt shape₀ sc table T₀ d) tC tP hC hP K E F
    hK hE hF bS hS hKE hEF (fun _ _ => A) xOf recK recE₀ recE₁ recF hLK hLE hLF X' bX' hX' hid V hV
    (FineAtRec A R shape₀ dig xReq) (fun _ _ => FineAtRec A R shape₀ dig xReq) (fun _ _ _ h => h)
    (fun z h h' => h ((fineAtRec_offBoth A R shape₀ dig xReq S₀ h169₀ z).1 h'))
    (fun T₀ z h h' => h ((fineAtRec_offBoth A R shape₀ dig xReq (S₁ T₀) (h169₁ T₀) z).1 h'))
    (fun T₀ T₁ g z hy hx => by
      obtain ⟨hI, oK, oE, oF, cm', cK, cE, cF, rK, rE, rF, t0, t1, hrec, hraw, hxq⟩ :=
        hYes T₀ T₁ g z hy hx
      refine ⟨hI, oK, oE, oF, cm', cK, cE, cF, rK, rE, rF, t0, t1, ?_⟩
      rintro hfirst hclash ⟨τ, hτ⟩ ⟨u, hu, hr, hrel⟩ hs
      obtain ⟨ρ, hρ⟩ := hs _ hfirst
      have hσ : NoClash z.1.1.2 :=
        hclash.of_subset fun e he => by rw [hτ]; exact List.mem_append_left _ he
      have hu' : D.dcdRaw (R.raw (cOf sc T₀) z.1.1.2 (bytesToDig (table z.1.2).root))
          (recK T₀ T₁ oK) = some u := by
        rw [← hraw hσ]
        exact hu
      exact ⟨A.mat u, ⟨_, _, u, hfirst, rfl, hrec ρ hρ, hu', rfl, hr⟩, hxq ▸ hrel⟩)
    B hB

end OnBytes.Slice
