-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReadyOfLots.lean: conditional: at a filling that lays no side in the shared and the
second chain: where the maker "onlineProverFromPublicFiles" returns A, and A's description passes its own test on its plan, "ready"
(Honest/Frame.lean) returns at A's description, book and prover, IF EACH LOT OF THE FILLING PAYS FOR ITSELF AND NO TWO
LOTS SHARE A PLACE. What a lot pays is stated so that it names no other lot: each group of authors can pay at its own
members, and the payments join. One definition; two theorems; nothing is evaluated.

  LotPays F B Z G L   no two sides of the lot stand at one place; and at every side g of the lot and every member b of the
                      first chain's list at g's place: wherever a list of sides has g as its first at that place,
                      "chainSteps" returns at [b], at the book B, at every input and every run's coins
  ready_of_lots_desc  **the statement, general in the description**: at A's own description, where its test on its plan
                      accepts; no head
  ready_of_lots       the same under the library's head, in the head's letters

The premises. h: the library's head (in the second alone). hA: the maker returns A. hpl: the description's test on its
plan. hpay: each lot pays. hap: the lots are pairwise apart. hS, h2: no side in the other two chains. hi: the index is in
the filling's range. ht: the request has a trace.

By. ready_of_parts, chainSteps_of_members, chainSteps_bare (ReadyOfParts.lean); twice_firstOf (LotClean.lean);
atPure_ok, atPure_tests (Honest/AtPureLaw.lean); planOk_all (Honest/Thread/File.lean); shaped_parts
(Honest/Law/Data.lean). The proof is that of ready_at_k5Lot (ReadyAtK5Lot.lean) with the three places that name the kind
K5 replaced by hpay and hap: the side that is found lies in some lot, and that lot pays.

Limits. An implication: that any lot pays is not shown in this file. At a side whose place is no member's LotPays asks
nothing: such a side is a stray, and the maker refuses a filling that lays one (atPure_tests). A filling with few lots is
NOT THE HONEST PROVER: the kinds without a lot send nothing. Never under a law over coins, never as "the prover", never as
a ground that anything is simulated. "ready returns" says nothing on whether a part plays, a round is reached or a
verifier accepts. Sides in the shared and the second chain are not treated.
The second theorem: the full size and the format's second hash function alone.
No property of the protocol is claimed: nothing on soundness, completeness or what anything reveals.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReadyOfParts
import Johnson.Desc.ProofFile.Honest.K5.Law.LotClean
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.Thread.File
import Johnson.Desc.ProofFile.Honest.Law.Data
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block FileDescription Place Chain)
open P5J (AtMgA TS)

/-- **What one lot pays**, at a description, a book, a public part and a ground: it names no other lot. -/
def LotPays {Xi V W X : Type} (F : FileDescription Xi) (B : ProverCoinCounts) (Z : Pub) (G : Ground) (L : HLot V W X) :
    Prop :=
  ((L.halves Z G).map (·.place)).Nodup ∧
    ∀ g ∈ L.halves Z G, ∀ b ∈ F.first.blocksInOrder, b.place = g.place →
      ∀ hs : List (Placed V W X), (hs.find? fun q => q.place == b.place) = some g →
        ∀ (w : V) (k : Coins B),
          ∃ l, chainSteps B (B.rowsOf 0) (k.look 0) (some w) [b] hs = .ok l

/-- **Where each lot pays and the lots are apart, "ready" returns: general in the description.** A filling with few lots
is not the honest prover. Conditional: hA; hpl: the description's own test on its plan accepts; hpay; hap; hS, h2; hi; ht.
It says nothing on whether a part plays. -/
theorem ready_of_lots_desc {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (hpl : A.F.planOk = true) (hpay : ∀ L ∈ P.lots, LotPays A.F A.B A.Z A.G L)
    (hap : P.lots.Pairwise fun L M =>
      ∀ x ∈ L.halves A.Z A.G, ∀ y ∈ M.halves A.Z A.G, x.place ≠ y.place)
    (hS : ∀ Z' G', P.shared Z' G' = []) (h2 : ∀ Z' G', P.second Z' G' = []) {w₀ : W₀}
    {x : ProofFile.Inst} {tr : Tr} (hi : P.inRange w₀ = true) (ht : P.trace A.Z w₀ x = some tr) (rc : Rc)
    (k : Coins A.B) : ∃ R, ready A.F A.B A.H w₀ rc x k = .ok R := by
  obtain ⟨-, -, -, eT, -, eI, -, eH1, eSh, eSe, -, -⟩ := atPure_ok hA
  obtain ⟨hw, s1, s2, s3, hd⟩ := atPure_tests hA
  have hp : A.F.placesOk = true := Johnson.RunOne.Sound.placesOk_of_planOk _ hpl
  obtain ⟨sh1, sh2, sh3⟩ := planOk_all hpl
  have eH2 : A.H.shared = [] := eSh.trans (hS _ _)
  have eH3 : A.H.second = [] := eSe.trans (h2 _ _)
  have t1 : twice A.H.first = [] := by
    rw [eH1]
    exact twice_firstOf A.Z A.G P.lots (fun L hL => (hpay L hL).1) hap
  have hT : readyTests A.F A.B A.H w₀ = .ok () := by
    have i1 : A.H.inRange w₀ = true := by
      rw [eI]
      exact hi
    unfold readyTests
    rw [List.isEmpty_iff.1 s1, List.isEmpty_iff.1 s2, List.isEmpty_iff.1 s3, t1, eH2, eH3, hp,
      hd, i1, hw]
    rfl
  refine ready_of_parts hT (tr := tr) (by rw [eT]; exact ht) ?_ ?_ ?_
  · refine chainSteps_of_members _ _ _ _ _ _ fun b hb => ?_
    cases hf : A.H.first.find? fun q => q.place == b.place with
    | none => exact chainSteps_bare _ _ _ _ _ (shaped_parts (sh1 b hb).2).1 hf
    | some q =>
      have hq0 : q ∈ A.H.first := List.mem_of_find?_eq_some hf
      rw [eH1] at hq0
      have hq : q ∈ P.lots.flatMap fun L => L.halves A.Z A.G := hq0
      have hqp : q.place = b.place := by simpa using List.find?_some hf
      obtain ⟨L, hL, hqL⟩ := List.mem_flatMap.1 hq
      exact (hpay L hL).2 q hqL b hb hqp.symm A.H.first hf ⟨w₀, rc, x, tr⟩ k
  · refine chainSteps_of_members _ _ _ _ _ _ fun b hb => ?_
    refine chainSteps_bare _ _ _ _ _ (shaped_parts (sh2 b hb).2).1 ?_
    rw [eH2]
    rfl
  · refine chainSteps_of_members _ _ _ _ _ _ fun b hb => ?_
    refine chainSteps_bare _ _ _ _ _ (shaped_parts (sh3 b hb).2).1 ?_
    rw [eH3]
    rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The same under the library's head, in the head's letters.** A filling with few lots is not the honest prover.
Conditional: h; hA; hpay; hap; hS, h2; hi; ht. -/
theorem ready_of_lots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hpay : ∀ L ∈ P.lots, LotPays (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B Zp A.G L)
    (hap : P.lots.Pairwise fun L M =>
      ∀ x ∈ L.halves Zp A.G, ∀ y ∈ M.halves Zp A.G, x.place ≠ y.place)
    (hS : ∀ Z' G', P.shared Z' G' = []) (h2 : ∀ Z' G', P.second Z' G' = []) {w₀ : W₀}
    {x : ProofFile.Inst} {tr : Tr} (hi : P.inRange w₀ = true) (ht : P.trace Zp w₀ x = some tr) (rc : Rc)
    (k : Coins A.B) :
    ∃ R, ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B A.H w₀ rc x k = .ok R := by
  obtain ⟨e1, -, e3, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  have hpl : A.F.planOk = true := by
    rw [eF]
    exact h.laid.planOk
  have hpay' : ∀ L ∈ P.lots, LotPays A.F A.B A.Z A.G L := by
    rw [eF, eZ]
    exact hpay
  have hap' : P.lots.Pairwise fun L M =>
      ∀ x ∈ L.halves A.Z A.G, ∀ y ∈ M.halves A.Z A.G, x.place ≠ y.place := by
    rw [eZ]
    exact hap
  have ht' : P.trace A.Z w₀ x = some tr := by
    rw [eZ]
    exact ht
  have res := ready_of_lots_desc hA hpl hpay' hap' hS h2 hi ht' rc k
  rw [eF] at res
  exact res

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.LotPays
#print axioms ProofFile.Honest.K5.ready_of_lots_desc
#print axioms ProofFile.Honest.K5.ready_of_lots
