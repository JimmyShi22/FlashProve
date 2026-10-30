-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/AcceptedPair.lean: kind K13, the members' batching: THE MEMBER IS
ACCEPTED, WITH BOTH PREMISES ON THE SENTENCE IN FRONT ASKED FROM THE PAIR "the thread and what is
said" (`AcceptedS`, `ThrS`, Honest/Thread/PaysS.lean); the thread T and the sentence Said are
variables. One statement with its proof. It imports AtThread.lean of this folder and PaysS.lean
alone: it does not stand over the library's hypothesis at the first chain's own list.
Main name:
  `k13_thread_acceptedS`: **`AcceptedS` at the kind's member**, at every `fall`.

What is not claimed. That the pair gives the guards at any thread: at the frame's own laying of the
first chain's thread that is GuardsAtHead.lean of this folder, under premises named there. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.AtThread
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (Where atM3)

variable {Bk : ProverCoinCounts} {Cl Cl' W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {weights : W₀ → Weights} {pile : PileOf Xi} {P : Where}

/-- **It is accepted, from the pair**, at every `fall` and every Said; T a variable: both premises
on the sentence in front are asked FROM THE PAIR: it gives the guards; and the member accepts
wherever `atM3 P` does. `k13_thread_accepted` (AtThread.lean) with weaker premises and a weaker end.
-/
theorem k13_thread_acceptedS (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (h : AtK13 T b weights pile P)
    (hdec : ∀ blk, T.bs[b]? = some blk → ∀ k s m En, ThrS T Said b k s m En → ∀ rs gs t',
      (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → blk.decide s rs gs = .ok t')
    (hG : ∀ k s m En, ThrS T Said b k s m En → K13Guards P s)
    (fall : Nat → S → List Fmt.Drawn → Option String) : AcceptedS T Said fall b := by
  intro blk hb k s m En ds y cols hT hd _ _ hM
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  obtain ⟨s', hst⟩ := k13_accepted weights pile P blk (h.rounds blk hb) (h.oracles blk hb)
    (h.half blk hb) hl (hdec blk hb k s m En hT) m ds hd (hG k s m En hT) _ _ _ _ hy hc
  exact ⟨s', ⟨⟨l, hl, hy⟩, hc⟩, hst⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_thread_acceptedS
