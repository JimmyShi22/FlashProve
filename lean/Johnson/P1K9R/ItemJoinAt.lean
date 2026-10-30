-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/ItemJoinAt.lean: the batching kind's law (K9), AT THE CLOSED CONSTANT:
WHAT IS LEFT OF hitems (the structure HitemsLeft, Johnson/LPFE1R/HitemsAtConst.lean), ITS FIELD
k3i AT AN ATTENTION LINK's ENTRY (2, "join").
  join_in_attention · join_not_in_layers  the entry is of attention's order, and not of the layers':
                   by decide +kernel
  k3i_join_att_at  THE CLAUSE, at the field's own letters, general in rd, c, tm4, bv, pv, AT kv :=
                   kvAtt A (the choice of Johnson/P1K9R/CallerAtLetters.lean)
PREMISES BESIDE THE HEAD AND THE FIELD's OWN (hm · hs · hlk · hL · hK · ok): hAt: the lookup's bare
run at attention's keys stands at the entry (at_join_is and K05_join_of_open pay
it from an opening) · hQ: K5's files' promise K5OkAt at the snapshot, a clause of the named Ok.
HOW. ItemJoin.lean's item_join. Its hkv: att_read_keys (Johnson/P1K9R/CallerReads.lean): at a state
that goes on from q the key forms are read off q: spent at the state itself and q := what is fixed
there; then kvAtt's own text. NO «pinned» IS WANTED: that sentence of the caller's speaks of the
world of the sum at full later states; the item's clause speaks of the table's world at the state in
front.
LIMITS. An implication. No state is shown to meet on0At. The full size alone. From the head (with
the fourteen entry tests): a verifier whose entry tests lack the two pins' rows gives no such head.
No example of the head by Lean's kernel. No soundness is claimed.
-/
import Johnson.P1K9R.ItemJoin
import Johnson.P1K9R.CallerAtLetters
import Johnson.LPFE1R.HitemsAtConst
import Johnson.Desc.First.Link.Law.SortLook
import Johnson.Desc.First.Link.Law.SortK3Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart orderOf)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.OnPublicFiles (jnVals k03_atS2_calls fits_at heard_at keysOf kvAtt refValQ
        att_read_keys)
open K5Law
open IM (subAt)

/-- "join" is of attention's order. -/
theorem join_in_attention : ((2 : ℕ), "join") ∈ orderOf ModelPart.attention := by decide +kernel

/-- A negative test: it is not of the layers' order. -/
theorem join_not_in_layers : ¬ ((2 : ℕ), "join") ∈ orderOf ModelPart.layers := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
variable {W : Type} {L : Link S Claim} {u : HTailF2} {Ok : Q BetaAll → Prop} {lmC jC lmD jD : ℕ}
  {tm4 : ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8)}
  {bv : Q BetaAll → Bound GE8 → ℕ → ℕ → GE8} {pv : Q BetaAll → Bound GE8 → ℕ → GE8}

/-- **AT AN ATTENTION LINK: THE FIELD k3i's CLAUSE AT (2, "join").** -/
theorem k3i_join_att_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (hs : subAt m = .attention) (hlk : h.𝔇.lk m = some L)
    (hL : SegAt m .attention L) (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q) (A : Attention.Plan)
    (hAt : At L (2, "join") (K3.joinRun (K3.seatCalls K3Lot.ofForm) (P.keysOfO A)))
    (hQ : ∀ q u g h, Ok q → q.2 = some u → rdAll q.1 = some (g, h) →
      K5OkAt (P.parCOf A) g.zk h u.F)
    (rd : Phi BetaAll → Option (Forest.Heard × First.Att.P.Heard)) (c : First.Att.P.ParC)
    (rdW : W → ℕ × ℕ → MsgQ) (ok : ∀ a, on0At h z m a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z m a →
      ItemIn L (phiAll u psiAll) (tmA rd c entUnit tm4 (t3All lmC jC lmD jD bv pv (kvAtt A)))
        (lenA rd c (l3All lmC jC lmD jD)) (h.𝔇.Rd m) (h.𝔇.N.group m) rdW a w (2, "join") := by
  have hne : m ≠ 24 := by
    rintro rfl
    exact absurd hs (by decide)
  have h24 : (m == 24) = false := by simpa using hne
  intro a w ha
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (part_at h z hm a ha)
  have he : ((2 : ℕ), "join") ∈ orderOf (subAt m) := by
    rw [hs]
    exact join_in_attention
  have hin := hin_at h hm z _ a ha he rfl
  rw [readers_at24 h m, K9.readersAt_some _ _ _ _ L hlk] at hin ⊢
  have hq2 : (fixed9 (phiAll u psiAll) a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  refine item_join _ L (phiAll u psiAll) hdCalls lmC jC (K3.seatCalls K3Lot.ofForm)
    k03_atS2_calls (fits_at false) (heard_at u false) (P.keysOfO A) (kvAtt A) _ _ _ rdW
    (2, "join") (by rw [hL.order]; exact join_in_attention) rfl hAt
    (by simp [tmA, t3All, v3All]) a w b hb ((hK _ (ok a ha)).1) ?_ hin ?_
  · show (if m == 24 then _ else fun _ _ _ => none : ℕ → String → S → Option K9.Read) _ _ _ = none
    rw [h24]
    rfl
  · intro k
    have hf : Fx9 (phiAll u psiAll) Ok (fixed9 (phiAll u psiAll) a.1) a.1 :=
      ⟨ok a ha, rfl, pubOf b, b, hq2, hb, goesOn_refl b⟩
    rw [att_read_keys (phiAll u psiAll) Ok rdAll A (hrd_all u) hQ k _ a.1 hf]
    unfold kvAtt refValQ
    rw [hq2]
    rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.join_in_attention
#print axioms VerifiableInference.Desc.LinkJoin.join_not_in_layers
#print axioms VerifiableInference.Desc.LinkJoin.k3i_join_att_at
