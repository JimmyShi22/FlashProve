-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberAtHead.lean (nothing imports it): THE MEMBERS OF "REACHED" ON EACH OF THE THREE
CHAINS AT THE HEAD's OWN LETTERS: that the description at which the members stand (IM.fileOf at an
opening's letters) and the main road's seated term P5J.F0T secondHashFunction Zp Np cF under P5J.LaidAt are ONE.




  member_at_head   the goals' scope test at the public files · the proof file's decision behind its
                   gate accepts at z, v₁, v₂, v₃ · L : P5J.LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np
                   cF: there are st, st₂, st₃: the run of Johnson/IMR/MemberRun.lean AT Zp AND cF
                     (so: no st
                   k bears a mark), and RchPub, RchPub₂, RchPub₃ AT P5J.F0T secondHashFunction Zp Np cF, at
                   every border of each chain, at the rider "the public part is a typed
                   instance's".
  head_of_verify   from verify()'s accept alone: in scope · the live test passes · there are Zp, Np,
                   cF at which the verifier's own value is laid (at its own data and run) · and z,
                   v₁, st, st₂, st₃ with member_at_head's four clauses at these letters.

HOW. L.opened is an IM.Open at the head's letters; IM.member_pub gives an IM.Open at its own;
IM.Open.unique makes the seven letters one. IM.fileOf Zp (seatZ Zp Np) (secondAt Zp Np) cF and
P5J.F0T secondHashFunction Zp Np cF are one term by unfolding (as in P5J.laid_opens' own line "have e : F = F0T
o Z N c := O.desc"). head_of_verify: FlashProve.scope_and_live_of_accept · gates_of_accept ·
P5J.laid_at_name · P5J.laid_opens.
THE WORDING THAT TRAVELS WITH EVERY USE OF head_of_verify: what is met
through it is "met at an accepting run at these public files", NOT "at the honest run": z and the
views are had by contradiction: tied neither to the prompt, the reply, the commitment ID or the
form, nor to the hash function.
NOT A MEMBER OF P5J.AtMg.rch BY THAT NAME, FOR TWO REASONS. (i) AtMg asks At.PlanOk, the named
tests on the plan, which no accept gives: so this file stands at LaidAt and RchPub, which need no
test. (ii) Johnson/P5J/FourAtMg.lean has rch := RchAt ∧ h.typed, and h.typed is this file's rider up
to the bound name: there "RchPub (F0T …) ‹typed› k a is h.rch k a" is one unfolding for whoever
holds a head. THAT COROLLARY IS NOT HERE: this file does not import FourAtMg.lean.


WHAT IS NOT SAID. That the two tests, or verify(), say yes anywhere. "No mark", or anything else, of
the shared or the second chain's states. At the second hash function alone. All that
Johnson/IMR/MemberPub.lean does not say. No soundness.
-/
import Johnson.IMR.MemberPubOfVerify
import Johnson.P5J.AtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (RchPub RchPub₂ RchPub₃)
open VerifierAndGoals FlashProve

/-- **The members of "reached" on each chain, at the head's own letters.** -/
theorem member_at_head {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles Z) z v₁ v₂ v₃ = true)
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain P5J.TS ProofFile.Cl}
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ (st : ℕ → S) (st₂ : ℕ → (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂)
      (st₃ : ℕ → (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃),
      RunAt Zp cF (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st ∧
      (∀ k ≤ 358, ∀ (Str : Type) (y : Str),
        RchPub (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          (((LPFD.Full.instanceAsPlainRecord z).pub, st k), y)) ∧
      (∀ k ≤ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          ((((LPFD.Full.instanceAsPlainRecord z).pub, st 358), st₂ k), y)) ∧
      ∀ k ≤ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          ((((LPFD.Full.instanceAsPlainRecord z).pub, st 358,
            st₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length), st₃ k), y) := by
  obtain ⟨Bs, base, O⟩ := L.opened
  obtain ⟨pp, Z', Bs', base', c', A', B', st, st₂, st₃, -, O', Rn, h₁, h₂, h₃⟩ := member_pub hS hg
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := O.unique O'
  exact ⟨st, st₂, st₃, Rn, h₁, h₂, h₃⟩

/-- **From verify()'s accept alone: the verifier's own value is laid, and "reached" has members at
the letters at which it is laid**, at some instance and views. -/
theorem head_of_verify (Z : VerifierAndGoals.PublicFiles) {Form : Type}
    (parse : Parser (atSecondHashFunction theDescription) Z Form) (hash : VerifiableInference.Hash)
    (commitment : VerifiableInference.Commitment)
    (prompt output : List VerifiableInference.Token) (form : Form)
    (h : (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z parse commitment prompt output form).evaluate
      hash = true) :
    VerifierAndGoals.InScope Z = true ∧ FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true ∧
    ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl),
      P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z))
        (theProofRun (asDescriptionFiles Z)) Zp Np cF ∧
      ∃ (z : LPFD.Full.XF × OnBytes.Flat.RecFull) (v₁ : Fmt.View) (st : ℕ → S)
        (st₂ : ℕ → (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂)
        (st₃ : ℕ → (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃),
        RunAt Zp cF (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st ∧
        (∀ k ≤ 358, ∀ (Str : Type) (y : Str),
          RchPub (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
            (((LPFD.Full.instanceAsPlainRecord z).pub, st k), y)) ∧
        (∀ k ≤ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length, ∀ (Str : Type) (y : Str),
          RchPub₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
            ((((LPFD.Full.instanceAsPlainRecord z).pub, st 358), st₂ k), y)) ∧
        ∀ k ≤ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.length, ∀ (Str : Type) (y : Str),
          RchPub₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
            ((((LPFD.Full.instanceAsPlainRecord z).pub, st 358,
              st₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length), st₃ k), y) := by
  obtain ⟨hS, hl⟩ := scope_and_live_of_accept Z parse hash commitment prompt output form h
  obtain ⟨z, v₁, v₂, v₃, hg⟩ := (gates_of_accept Z parse hash commitment prompt output form h).2.2
  obtain ⟨Zp, Np, cF, L⟩ := P5J.laid_opens (P5J.laid_at_name hl)
  exact ⟨hS, hl, Zp, Np, cF, L, z, v₁, member_at_head hS hg L⟩

#print axioms member_at_head
#print axioms head_of_verify

end IM
