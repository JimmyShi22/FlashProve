-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/SeedAtRch.lean: THE SENDINGS' INVARIANT `K1.SeedIs` AT EVERY
STATE THAT IS REACHED, BY THE SUB-PROTOCOLS EACH UNDER THE TEST ON THE WORDS (`below`), AT A NUMBER
IN FRONT OF THE LAST CODE SWITCH OF THE PROOF FILE's FIRST CHAIN: so in front of every link's
closing (kind K10). A JOIN OF LAWS THAT LIE: no walk is typed here. Theorems. A law file; no running
text imports it.
  `seedIs_at_rch`     an opened seat · onlineDescription returns F · F.planOk = true · k ≤ (frontOf
                    c).length · Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s) · the codes · the
                    message x at number o, of the shape sh, MARKED AS SAMPLED · K1.Tie cs sh ⊢ ∃ ρ
                    y, K1.SeedIs cs sh s.st o ρ y. CALLED: P1K2.both_at_open
                    (Johnson/P1K2R/FoldSide.lean: both invariants on the stored sample rows at the
                    opening's own chain) · seedIs_of_rows (Link/Law/SeedOfRows.lean).
  `sampled_of_held`   THE MARK OUT OF THE PROMISE's OWN TEST: smpHeld st book j t = true
                    (Johnson/Desc/SmpRows.lean; the composed meaning's "held" is that test) ⊢ there
                    are a number o and a message x: the book lays o at tenant t of tree j, x stands
                    at o, and x is marked as sampled.
  `seedIs_of_held`    the same end with the mark paid so: the book lays o at (j, t) · no two
numbers of the book lie at (j, t) · smpHeld s.st s.book j t = true · the message at o has the shape
sh. WHY "below". At the wider family (Reach over c.blocksInOrder itself) the end is false in kind:
raw_zero_reads_zero (SeedOfRows.lean).

Limits. At OnBytes.secondHashFunction (both_at_open's letter). The codes, the shape, the book's place and "no
two numbers" are premises (the fold's facts codes, msgShapes, seatsCarried are their natural payers:
not joined here). K1.Tie is a premise (four tests on public data). No member. Nothing on soundness
or on hiding.
-/
import Johnson.Desc.First.Link.Law.SeedOfRows
import Johnson.P1K2R.FoldSide
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription smpHeld smpSeed smpRows oracleNo)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2 (frontOf)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The sendings' invariant at a reached state.** -/
theorem seedIs_at_rch (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true) {k : ℕ}
    (hk : k ≤ (frontOf c).length) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) {cs : Codes} {sh : OracleShape}
    {o : ℕ} {x : OnBytes.Oracle} (hc : s.st.codes = cs) (hx : s.st.oracles[o]? = some x)
    (hs : x.shape = sh) (hm : x.sampled = true) (hT : K1.Tie cs sh) :
    ∃ ρ y, K1.SeedIs cs sh s.st o ρ y :=
  seedIs_of_rows hc hx hs hm hT (P1K2.both_at_open O hF hpl hk hr).1
    (P1K2.both_at_open O hF hpl hk hr).2

end

/-- **The mark, out of the promise's own test.** -/
theorem sampled_of_held {st : Statement} {book : TreeBook} {j t : ℕ}
    (h : smpHeld st book j t = true) :
    ∃ (o : ℕ) (x : OnBytes.Oracle), book.place[o]? = some (j, t) ∧ st.oracles[o]? = some x ∧
      x.sampled = true := by
  unfold smpHeld at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  unfold smpSeed at hv
  obtain ⟨o, ho, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨rows, hrows, _⟩ := Option.bind_eq_some_iff.1 hv
  unfold smpRows at hrows
  rw [ho, Option.bind_some, hx, Option.bind_some] at hrows
  refine ⟨o, x, ?_, hx, ?_⟩
  · unfold oracleNo at ho
    have := List.find?_some ho
    simpa using this
  · split at hrows
    · rename_i hcnd
      simp only [Bool.and_eq_true] at hcnd
      exact hcnd.1.1
    · cases hrows

section
variable {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The same, the mark paid by the promise's test.** -/
theorem seedIs_of_held (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true) {k : ℕ}
    (hk : k ≤ (frontOf c).length) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) {cs : Codes} {sh : OracleShape}
    {o j t : ℕ} (hc : s.st.codes = cs) (hb : s.book.place[o]? = some (j, t))
    (hone : ∀ o', s.book.place[o']? = some (j, t) → o' = o)
    (hh : smpHeld s.st s.book j t = true)
    (hs : ∀ x, s.st.oracles[o]? = some x → x.shape = sh) (hT : K1.Tie cs sh) :
    ∃ ρ y, K1.SeedIs cs sh s.st o ρ y := by
  obtain ⟨o', x, h1, hx, hm⟩ := sampled_of_held hh
  obtain rfl := hone o' h1
  exact seedIs_at_rch O hF hpl hk hr hc hx (hs x hx) hm hT

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seedIs_at_rch
#print axioms VerifiableInference.Desc.LinkJoin.sampled_of_held
#print axioms VerifiableInference.Desc.LinkJoin.seedIs_of_held
