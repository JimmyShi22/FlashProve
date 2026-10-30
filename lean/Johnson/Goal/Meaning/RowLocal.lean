-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RowLocal.lean: what each of the 25 shares of Means
(Johnson/Goal/Meaning/Row.lean) reads, and the meaning's conjunct of a boundary's relation under the
decoder's binder. Tools for whoever shows the first chain knowledge sound from firstMeans, link by
link.

WHY. firstMeans is asked at the public part of the request WITH THE WITNESS'S TOKEN PUT IN, and at a
whole Hid. A link's law speaks of the request without its reply and of that link's own arrays. So:
  share_layers, share_attention, share_head
                  sub-proof 2 g's share is MeansG at g, 2 g + 1's MeansA at g, 24's MeansH.
  share_put       the shares of the 24 sub-proofs of the layers do not read the reply: at
                  (putReq p t).val they say what they say at p.val. The head's share alone may read
                  it (that it does is not shown here).
  shareG_congr, shareA_congr, shareH_congr
                  the share of group g reads the group's list and, where 0 < g, number iXO of the
                  list of the group before; that of its attention reads its own list and number iQA
                  of the group's; the head's reads its stream and the stream that the last group's
                  list holds, inside the window and the width. "Reads" is "reads at most". No
                  premise names Hid.tok: no share reads it (share_tok).
  firstFrom k     the shares from sub-proof k on, at every index that the decoded matrix holds: the
                  meaning's conjunct of the relation at the boundary in front of sub-proof k, in
                  firstMeans' own form.
  firstFrom_zero, firstFrom_succ, firstFrom_end
                  firstFrom 0 is firstMeans; in front of sub-proof k: its own share and firstFrom
                  (k + 1); behind the last nothing is left.
  firstShare_put  for k < 24 the share in firstFrom_succ is asked at p.val: no token in it.

What is not claimed. THE SEAMS ARE NEITHER MOVED NOR PAID HERE: each stays in the share of the
sub-proof that READS the borrowed array (2 g: LaySeam; 2 g + 1: AttSeam; 24: HeadSeam), so a share
is not local to one sub-proof's arrays. (Lists can be made so that the seams hold by the make.)
As in Johnson/Goal/Meaning/Row.lean: firstFrom k is a conjunct of a boundary's relation and not
that relation: what is pending there is not stated here. Nothing on any description, link or
extractor.
-/
import Johnson.Goal.Meaning.Row

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Flat (putReq)
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.OnPublicFiles.Flat (Holds GE Req)

variable {X : Model.Verify.Public} {pp : ScalesAndPolicy} {i : Cm.Idx}

/-- A group of layers' share reads of the request its tokens alone. -/
theorem meansG_tokens {x x' : Instance ppref} (h : Cm.Seg.tokX x = Cm.Seg.tokX x')
    {MG : ℕ → Mats ℤ} {g : ℕ} (M : MeansG X i x MG g) : MeansG X i x' MG g := by
  refine ⟨M.small, ?_, ?_, ?_, M.key, M.seam⟩
  · have k := M.norm
    unfold NormField at k ⊢
    rw [← h]
    exact k
  · have k := M.hot
    unfold HotField at k ⊢
    rw [← h]
    exact k
  · have k := M.emb
    unfold EmbField at k ⊢
    rw [← h]
    exact k

/-- putReq turns the reply alone: the tokens stay. -/
theorem tokX_putReq (p : Req) (t : Fin ppref.V) :
    Cm.Seg.tokX (putReq p t).val = Cm.Seg.tokX p.val := by
  unfold putReq
  split <;> rfl

/-- Sub-proof 2 g's share is the share of group g of layers. -/
theorem share_layers (x : Instance ppref) (w : Hid) {g : ℕ} (hg : g < 12) :
    Share X pp i x w (2 * g) ↔ MeansG X i x w.MG g := by
  unfold Share
  rw [if_neg (show ¬ 2 * g = 24 by omega), if_pos (show 2 * g % 2 = 0 by omega),
    show 2 * g / 2 = g by omega]

/-- Sub-proof 2 g + 1's share is the share of group g's attention. -/
theorem share_attention (x : Instance ppref) (w : Hid) (g : ℕ) :
    Share X pp i x w (2 * g + 1) ↔ MeansA X.y (Hd.shapeA X g) (w.MG g) (w.MA g) := by
  unfold Share
  rw [if_neg (show ¬ 2 * g + 1 = 24 by omega), if_neg (show ¬ (2 * g + 1) % 2 = 0 by omega),
    show (2 * g + 1) / 2 = g by omega]

/-- Sub-proof 24's share is the head's. -/
theorem share_head (x : Instance ppref) (w : Hid) :
    Share X pp i x w 24 ↔ MeansH X pp i x w := by
  unfold Share
  rw [if_pos rfl]

/-- **The shares of the layers' 24 sub-proofs do not read the reply.** -/
theorem share_put (p : Req) (t : Fin ppref.V) (w : Hid) {k : ℕ} (hk : k < 24) :
    Share X pp i (putReq p t).val w k ↔ Share X pp i p.val w k := by
  unfold Share
  simp only [if_neg (show ¬ k = 24 by omega)]
  by_cases h2 : k % 2 = 0
  · simp only [if_pos h2]
    exact ⟨meansG_tokens (tokX_putReq p t), meansG_tokens (tokX_putReq p t).symm⟩
  · simp only [if_neg h2]

/-- The share of group g reads the group's own list and, where 0 < g, number iXO of the list of the
group before. -/
theorem shareG_congr {x : Instance ppref} {w w' : Hid} {g : ℕ} (h : w.MG g = w'.MG g)
    (h' : 0 < g → ∀ r c,
      w.MG (g - 1) (matIx X.y).iXO r c = w'.MG (g - 1) (matIx X.y).iXO r c) (hg : g < 12) :
    Share X pp i x w (2 * g) ↔ Share X pp i x w' (2 * g) := by
  have one : ∀ {v v' : Hid}, v.MG g = v'.MG g →
      (0 < g → ∀ r c, v.MG (g - 1) (matIx X.y).iXO r c = v'.MG (g - 1) (matIx X.y).iXO r c) →
      MeansG X i x v.MG g → MeansG X i x v'.MG g := fun e e' M =>
    ⟨e ▸ M.small, e ▸ M.norm, e ▸ M.hot, e ▸ M.emb, e ▸ M.key,
      fun h0 r c => by rw [← e]; exact (M.seam h0 r c).trans (e' h0 r c)⟩
  rw [share_layers x w hg, share_layers x w' hg]
  exact ⟨one h h', one h.symm fun h0 r c => (h' h0 r c).symm⟩

/-- The share of group g's attention reads its own list and number iQA of the group's. -/
theorem shareA_congr {x : Instance ppref} {w w' : Hid} {g : ℕ}
    (h : ∀ r c, w.MG g (matIx X.y).iQA r c = w'.MG g (matIx X.y).iQA r c)
    (h' : w.MA g = w'.MA g) :
    Share X pp i x w (2 * g + 1) ↔ Share X pp i x w' (2 * g + 1) := by
  rw [share_attention x w g, share_attention x w' g, ← h']
  exact ⟨fun M => ⟨M.small, M.key, M.own1, M.own2, M.ridden,
      fun r c => (M.seam r c).trans (h r c)⟩,
    fun M => ⟨M.small, M.key, M.own1, M.own2, M.ridden,
      fun r c => (M.seam r c).trans (h r c).symm⟩⟩

/-- The head's share reads the head's stream, and the stream that the last group's list holds, at
the window's positions and the stream's coordinates alone. -/
theorem shareH_congr {x : Instance ppref} {w w' : Hid}
    (h : Agree ppref (lastOf X.y (w.MG 11)) (lastOf X.y (w'.MG 11)))
    (h' : Agree ppref w.Xl w'.Xl) : Share X pp i x w 24 ↔ Share X pp i x w' 24 := by
  have one : ∀ {v v' : Hid}, Agree ppref (lastOf X.y (v.MG 11)) (lastOf X.y (v'.MG 11)) →
      Agree ppref v.Xl v'.Xl → MeansH X pp i x v → MeansH X pp i x v' := fun a b M =>
    ⟨fun pos hp j hj =>
        ((b pos hp j hj).symm.trans (M.seam pos hp j hj)).trans (a pos hp j hj),
      SaysHead.congr b (fun _ _ _ => rfl) M.plain⟩
  rw [share_head x w, share_head x w']
  exact ⟨one h h', one (fun pos hp j hj => (h pos hp j hj).symm)
    fun pos hp j hj => (h' pos hp j hj).symm⟩

/-- No share reads the witness's token. (firstMeans reads it: it puts it into the request.) -/
theorem share_tok {x : Instance ppref} (w : Hid) (t : Fin ppref.V) (k : ℕ) :
    Share X pp i x { w with tok := t } k ↔ Share X pp i x w k := by
  by_cases h : k = 24
  · subst h
    rw [share_head, share_head]
    exact ⟨fun M => ⟨M.seam, M.plain⟩, fun M => ⟨M.seam, M.plain⟩⟩
  · unfold Share
    rw [if_neg h, if_neg h]

/-- **The meaning's conjunct of the relation at the boundary in front of sub-proof k**, in
firstMeans' own form. -/
def firstFrom {rows cols : ℕ} (X : Model.Verify.Public) (pp : ScalesAndPolicy)
    (put : Req → Fin ppref.V → Req) (dec : Option (Fin rows → Fin cols → GE)) (p : Req) (w : Hid)
    (k : ℕ) : Prop :=
  ∀ M (i : Cm.Idx), dec = some M → Holds M i → MeansFrom X pp i (put p w.tok).val w k

/-- One sub-proof's share in that form. -/
def firstShare {rows cols : ℕ} (X : Model.Verify.Public) (pp : ScalesAndPolicy)
    (put : Req → Fin ppref.V → Req) (dec : Option (Fin rows → Fin cols → GE)) (p : Req) (w : Hid)
    (k : ℕ) : Prop :=
  ∀ M (i : Cm.Idx), dec = some M → Holds M i → Share X pp i (put p w.tok).val w k

section
variable {rows cols : ℕ} {put : Req → Fin ppref.V → Req}
  {dec : Option (Fin rows → Fin cols → GE)} {p : Req} {w : Hid}

theorem firstFrom_zero : firstFrom X pp put dec p w 0 ↔ firstMeans X pp put dec p w :=
  ⟨fun H M i hM hi => means_iff_from.2 (H M i hM hi),
    fun H M i hM hi => means_iff_from.1 (H M i hM hi)⟩

theorem firstFrom_succ (k : ℕ) (hk : k < 25) :
    firstFrom X pp put dec p w k ↔
      firstShare X pp put dec p w k ∧ firstFrom X pp put dec p w (k + 1) :=
  ⟨fun H => ⟨fun M i hM hi => ((meansFrom_succ k hk).1 (H M i hM hi)).1,
      fun M i hM hi => ((meansFrom_succ k hk).1 (H M i hM hi)).2⟩,
    fun H M i hM hi => (meansFrom_succ k hk).2 ⟨H.1 M i hM hi, H.2 M i hM hi⟩⟩

theorem firstFrom_end : firstFrom X pp put dec p w 25 := fun _ _ _ _ => meansFrom_end

/-- **For the layers' 24 sub-proofs the share is asked at the public part itself.** -/
theorem firstShare_put {k : ℕ} (hk : k < 24) :
    firstShare X pp putReq dec p w k ↔
      ∀ M (i : Cm.Idx), dec = some M → Holds M i → Share X pp i p.val w k :=
  ⟨fun H M i hM hi => (share_put p w.tok w hk).1 (H M i hM hi),
    fun H M i hM hi => (share_put p w.tok w hk).2 (H M i hM hi)⟩

end

end Meaning

#print axioms Meaning.meansG_tokens
#print axioms Meaning.tokX_putReq
#print axioms Meaning.share_layers
#print axioms Meaning.share_attention
#print axioms Meaning.share_head
#print axioms Meaning.share_put
#print axioms Meaning.shareG_congr
#print axioms Meaning.shareA_congr
#print axioms Meaning.shareH_congr
#print axioms Meaning.share_tok
#print axioms Meaning.firstFrom_zero
#print axioms Meaning.firstFrom_succ
#print axioms Meaning.firstFrom_end
#print axioms Meaning.firstShare_put
