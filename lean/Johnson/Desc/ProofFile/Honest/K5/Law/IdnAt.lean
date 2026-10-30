-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/IdnAt.lean: the premise "the witness's cells meet the library's
three families of identities on an attention segment" (`AtIdn`,
Johnson/Desc/K5/Honest/Law/Idn.lean), which the laws on the values of the kind "an attention
segment's own rounds" (K5) take at the input of the prover's run, AS ONE SENTENCE ON THE LETTER
`valid` of the chain's invariant; and how the invariant hands it out.

Why. The invariant (`Thr`, Honest/Thread/Thr.lean) holds `valid` of the run's input as its last
clause, and `valid` is a free letter: "the input is one of which something is to be said"
(Honest/Thread/File.lean, its head). That the cells are those of an honest computation is such a
sentence: it speaks of the input alone, of no coin and no challenge.

  `IdnOwed`          a premise's form: every valid input's cells, read at the segment, meet the
                     identities
  `atIdn_of_thr`     GENERAL in `Thread`, CONDITIONAL: from `IdnOwed` at the letter `valid` of T and
                     `Thr` at any border: `AtIdn` at the run's input, in the letters in which the
                     laws on values take it
  `atIdn_at`         CONDITIONAL: the same at the first chain's `Thread` at the library's own
                     letters, where `valid` is the free letter itself
  `idnOwed_of_int`   CONDITIONAL: `IdnOwed` from integers: each valid input's cells, read in the
                     field, are the casts of integer cells that meet the identities over the
                     integers (`atIdn_of_int`)

Who is meant to show `IdnOwed`: whoever lays the letter `valid`, with whoever holds that a valid
input's trace is one of the model's relation: in `idnOwed_of_int`'s letters: integer cells tz with
`idnVal D tz j = 0` at every valid index j of the three families at1, at2, at3. The integers may be
negative: the cast into the field takes them as they are.
`IdnOwed` speaks at one segment's public data Z: a caller who wants all twelve groups asks twelve
sentences of the one letter `valid`.

Limits. `IdnOwed` is a definition: nothing is claimed of it, and it is shown of no `valid` here. At
a `valid` that no input meets it is true and says nothing, and `Thr` then holds nowhere. A narrower
`valid` narrows the inputs of which the chain's invariant speaks.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Ready
import Johnson.Desc.K5.Honest.Law.Idn
import Johnson.Desc.K5.Honest.Law.Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.Slice (GE)
open Inst.Model.AttSeg (Raw Idn idnVal castT)
open VerifiableInference.Desc (Strs Chain)
open H2K5.Honest (AtIdn tOf atIdn_of_int)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-- **Every valid input's cells, read at the segment, meet the library's three families of
identities.** It is a definition: a premise's form on the letter `valid`. Nothing is claimed of it.
-/
def IdnOwed {W₀ Rc Xi Tr : Type} (valid : Local W₀ Rc Xi Tr → Prop) (cells : Tr → Cells)
    (Z : Seat5) : Prop :=
  ∀ w, valid w → AtIdn Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells w.trace)))

/-- **The invariant hands the identities out at the run's input.** General in `Thread`.
CONDITIONAL: `IdnOwed` at T's letter `valid`; `Thr` at a border. -/
theorem atIdn_of_thr {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}
    (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) {cells : Tr → Cells}
    {Z : Seat5} (hI : IdnOwed T.valid cells Z) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T b k s m E) :
    AtIdn Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace))) :=
  hI _ hT.2.2.2.2.2.2

/-- **`IdnOwed` from integers.** CONDITIONAL: each valid input's cells, read in the field, are the
casts of integer cells that meet the identities over the integers at every valid index. -/
theorem idnOwed_of_int {W₀ Rc Xi Tr : Type} {valid : Local W₀ Rc Xi Tr → Prop}
    {cells : Tr → Cells} {Z : Seat5}
    (hz : ∀ w, valid w → ∃ tz : Raw → ℤ,
      tOf Reading.gl (inOf Z.P.S Z.link (cells w.trace)) = (castT tz : Raw → GE) ∧
        ∀ j : Idn, j.Valid Z.P.D → idnVal Z.P.D tz j = 0) :
    IdnOwed valid cells Z := by
  intro w hw
  obtain ⟨tz, e, hj⟩ := hz w hw
  rw [e]
  exact atIdn_of_int hj

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **The same at the first chain's `Thread` at the library's own letters**, where `valid` is the
free letter itself. CONDITIONAL: `IdnOwed` at the letter; `Thr` at a border. The hypothesis h stands
in the `Thread`'s other letters alone. -/
theorem atIdn_at {cells : Tr → Cells} {Z5 : Seat5} (hI : IdnOwed valid cells Z5) {b : Nat}
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) b k s m E) :
    AtIdn Z5.P.D (tOf Reading.gl (inOf Z5.P.S Z5.link (cells m.st.input.trace))) :=
  atIdn_of_thr _ hI hT

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atIdn_of_thr
#print axioms ProofFile.Honest.K5.idnOwed_of_int
#print axioms ProofFile.Honest.K5.atIdn_at
