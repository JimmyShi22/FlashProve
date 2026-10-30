--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ShapeQuiet.lean: THE RULE "STRUCTURE | VALUES" (`accepted_of_shape`,
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) AT A SUB-PROTOCOL WITHOUT A ROUND. Of the rule's
premises two are paid there. General in the thread's and the shape's letters: no kind is named.

  **`fitsAt_quiet`**: at a sub-protocol without a round nothing is played and no column is read: so
    what was played and read passes the step's own tests on rounds and columns (`FitsAt`).
  `values_true`: where the sub-protocol's named tests on values are constantly true, `Values` holds.
  **`accepted_quiet_shape`**: so the rule there: from the named premise (`Shape.yes`), the first
    shape, (B1) `Carries` at every sub-protocol of the chain and (B2) `Returns` at this one:
    `Accepted`.

Limits.
- The four premises that are left are the rule's own. (B1) IS ASKED AT EVERY SUB-PROTOCOL OF THE
  CHAIN, those with rounds among them. `Shape.yes` is a debt with a name: an evaluation.
- Nothing shows that they can be met at a description of the protocol.

-/
import Johnson.Desc.ProofFile.Honest.Thread.Shape

set_option autoImplicit false

namespace AtPublicFiles.KeyLink
open ProofFile.Honest
open VerifiableInference.Desc (Block)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **At a sub-protocol without a round the step's own tests on rounds and columns pass.** -/
theorem fitsAt_quiet {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    (hr : blk.rounds = []) : FitsAt T b := by
  intro blk' hb' k m E ds y cols hd hM
  rw [hblk] at hb'
  obtain rfl := Option.some.inj hb'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  have hl0 : l = [] := by
    have e := steps_decl hl
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hr] at e
    exact List.map_eq_nil_iff.1 e
  have hd0 : ds = [] := by
    have e := drawsFit_length _ _ hd
    rw [hr] at e
    exact List.eq_nil_of_length_eq_zero e
  subst hl0
  subst hd0
  obtain rfl : (([], m) : List Played × Mid W X) = y := Except.ok.inj hy
  rw [hr] at hc
  obtain rfl : ([] : List VerifiableInference.Desc.OpenedColumn) = cols := Except.ok.inj hc
  unfold Block.Fits Block.want
  rw [hr]
  exact ⟨rfl, rfl⟩

/-- Where the named tests on values are constantly true. -/
theorem values_true (Z : Shape S) {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat}
    (hv : ∀ s rs gs, Z.vals b s rs gs = true) : Values T Z fall b :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => hv _ _ _

/-- **The rule at a sub-protocol without a round.** -/
theorem accepted_quiet_shape (Z : Shape S) {a₀ : Z.Sh} {n b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hn : n ≤ T.bs.length) (hb : b < n)
    (hyes : Z.yes a₀ n = true) (hfirst : ∀ k w h s₀, T.valid w → T.begun k w h s₀ → Z.sh s₀ = a₀)
    (hC : ∀ j, Carries T.bs T.ft Z j) (hR : Returns T.bs T.ft Z b) (hblk : T.bs[b]? = some blk)
    (hr : blk.rounds = []) (hv : ∀ s rs gs, Z.vals b s rs gs = true) : Accepted T fall b :=
  accepted_of_shape T Z hn hb hyes hfirst hC hR (fitsAt_quiet T hblk hr) (values_true T Z hv)

end AtPublicFiles.KeyLink

#print axioms AtPublicFiles.KeyLink.fitsAt_quiet
#print axioms AtPublicFiles.KeyLink.values_true
#print axioms AtPublicFiles.KeyLink.accepted_quiet_shape
