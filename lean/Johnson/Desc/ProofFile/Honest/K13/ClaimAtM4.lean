-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ClaimAtM4.lean: WHAT THE VERIFIER's STATE HOLDS AT THE BORDER
RIGHT BEHIND THE MEMBERS' BATCHING, FROM THE THREAD AT THAT BORDER: it stands at the chain's end
with a claim made of a row: the first of the seven sentences of `PublicAtM4` (ExchangeM4.lean of
this folder). Statements with their proofs.

How. The sub-protocol at the place "M:4" stands right behind the batching's. The thread at a border
holds the verifier's own fold over the sub-protocols in front; the frame's `thr_back_decide`
(Honest/Thread/ReachBack.lean) goes one step back along it: there is a state in front of the
batching's sub-protocol, reached too, from which that sub-protocol's own decision accepts with the
state at the border. `MemberIs` (ShapeAtM3.lean) takes that decision to the kind's own;
`atM3_return_row` (Johnson/Desc/K13/Honest/ShapeSim.lean) says what it returns. So no sentence need
be carried from the batching's border to the next.
Main names:
  `back_at_m4`: **from the thread at the border b + 1, where number b is the batching's
    sub-protocol: the state is `withClaim` at a state s₀ that is reached at b, at what the taking of
    mask entries returns there, W's message, and the row `Batt.rowOf` of s₀'s pile at what the
    sumcheck's run returns.**
  `claim_at_m4`: so it stands at the chain's end, with a claim made of a row and nothing else laid
    beside it.

What is not claimed. s₀ stands under "there is": it is not said to be the state at which the thread
stood at b; of the rounds of that accepting decision nothing is said. The other six sentences of
`PublicAtM4`. That the thread holds at any run. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeM4
import Johnson.Desc.ProofFile.Honest.K13.ShapeAtM3
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where St)
open VerifiableInference.Desc.K13.Law (dOf)
open VerifiableInference.Desc.K13.Honest (withClaim atM3_return_row)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl Cl' W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M)

/-- **One step back from the border behind the batching's sub-protocol.** -/
theorem back_at_m4 {b : Nat} {P : Where} (hM : MemberIs L.bs b P Cl') (hb : b + 1 ≤ L.bs.length)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env}
    (hT : Thr L.thread (b + 1) k s m En) :
    ∃ (s₀ : S) (t : List ℕ × St) (msg : Array OracleNotice) (x : E) (hd : Psc.Heard)
      (o : Psc.Out), Reach 0 L.bs L.first b (L.pubOf m.st.input.x, s₀) ∧
      takeMasksP (dOf s₀) s₀.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linMessageW P.lin = some msg ∧ Batt.fits P.lin.kCol s₀.out.pending = true ∧
      Psc.run (Batt.claimOf s₀.out.pending x) (Batt.summandOf s₀.out.pending x)
        (t.1.map fun i => ⟨s₀.out.indexMasks, i⟩) hd = some o ∧
      s = withClaim s₀ t.2.st msg (Batt.rowOf s₀.out.pending o) := by
  obtain ⟨s₀, blk, rs, gs, hblk, hR, hd⟩ :=
    thr_back_decide L.thread L.first (L.pubOf m.st.input.x) hb (fun _ h0 => h0) hT
  obtain ⟨t, msg, x, hd', o, h1, h2, h3, h4, h5⟩ :=
    atM3_return_row (hM.back blk hblk s₀ rs gs s hd)
  exact ⟨s₀, t, msg, x, hd', o, hR, h1, h2, h3, h4, h5⟩

/-- **The first sentence of `PublicAtM4`, from the thread.** It forgets what `back_at_m4` knows:
that no number is handed on yet, and that the message is the plan's. -/
theorem claim_at_m4 {b : Nat} {P : Where} (hM : MemberIs L.bs b P Cl') (hb : b + 1 ≤ L.bs.length)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env}
    (hT : Thr L.thread (b + 1) k s m En) :
    ∃ (msg : Array OracleNotice) (ids : Array ℕ) (row : TensorRow),
      s.here = .mem ⟨msg, ids, some { claim := memberClaim row }⟩ := by
  obtain ⟨s₀, t, msg, x, hd, o, _, _, _, _, _, rfl⟩ := back_at_m4 L hM hb hT
  exact ⟨msg, #[], _, rfl⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.back_at_m4
#print axioms ProofFile.Honest.K13.claim_at_m4
