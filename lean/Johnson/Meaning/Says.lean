-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/Says.lean: what the hidden values of a proof must say for a request to be true, as
plain statements on integers, one for each block of the integer model (the embedding; each layer's
attention block and feed-forward block; the head); and that together they say exactly "the request
is true under its policy".

The record Says speaks of one family of integers, the residual stream S: S l pos j is coordinate j
of the stream at position pos, before layer L (l = 2 L), between its attention block and its
feed-forward block (l = 2 L + 1), and behind the last layer (l = 2 * layers). Each clause is a
definition of the integer program (Inst/Model/Program.lean, Inst/Model/ProgramR.lean), applied to S:
  emb      the stream begins as the embedding of the request's tokens;
  attOK    no range condition of the attention block of layer L fails on S (2 L);
  att      S (2 L + 1) is that block's output on S (2 L);
  ffOK     no range condition of the feed-forward block of layer L fails on S (2 L + 1);
  ff       S (2 L + 2) is that block's output on S (2 L + 1);
  normOK   no range condition of the final normalisation fails;
  form     the request has its form: r < e ≤ T, and y = 0 if e < T;
  policy   the acceptance policy's three clauses hold of the logits, which are the products of the
           normalised last stream with the output matrix.
Beside docs/model.md. NORM is its section 5, Att its section 6, FF its section 7; emb, logitOf and
the gap in the policy's clauses its section 8. What happens inside a block (the rotary turn, the
softmax, the router, the experts) is in Att.x' and FF.x''. The range conditions of its section 9:
conditions 1 and 2 are NORM.OK; 3 and 4, with the first norm's 1 and 2, are Att.OK; 5, 6 and 7, with
the second norm's 1 and 2, are FF.OK; condition 8 follows from 1 (Meaning.last_bound,
Johnson/Meaning/Halves.lean). The intervals are those of its column "defined".

Equalities are asked at the positions below T and the coordinates below d alone (Agree,
Inst/Model/All/Congr.lean): nothing is asked where the model has no value.

Main definitions: logitOf, Says.
Main theorems:
  says_stream: under Says, S is the integer program's stream, at all indices.
  true_of_says: Says gives the relation RinfPP (Inst/Model/Scales.lean).
  says_of_true: under RinfPP the program's own stream meets Says.
  says_iff, isTrueUnder_iff_says: some stream meets Says exactly if the request is true under its
  policy (Policy.IsTrueUnder, Policy/Rel/True.lean). So nothing is lost and nothing is added.

What is not claimed. That the hidden values of a proof which a verifier accepts meet Says. Nothing
on a protocol, on probabilities or on hiding. The sizes are the reference model's (ppref), the five
lookup tables the library's (tbRef).
-/
import Policy.Rel.True
import Inst.Model.All.NoWrapK

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All

/-- The logits that a last stream X gives: the normalised stream times the output matrix. -/
def logitOf (nf : NormPar) (w : Weights) (X : ℕ → Vec) (pos ι : ℕ) : ℤ :=
  dot ppref.d (NORM.out nf ppref.d (X pos)) fun j => w.H j ι

/-- **What the stream S says**, at the settings pp, the weights w and the request x. -/
structure Says (pp : ScalesAndPolicy) (w : Weights) (x : Instance ppref) (S : ℕ → ℕ → Vec) : Prop where
  emb : ∀ pos (h : pos < ppref.T), ∀ j < ppref.d, S 0 pos j = w.Emb (x.prompt ⟨pos, h⟩) j
  attOK : ∀ L < ppref.layers, Att.OK (ppref.at (pp.kap L)) tbRef (w.layer L) L (S (2 * L))
  att : ∀ L < ppref.layers,
    Agree ppref (S (2 * L + 1)) (Att.x' (ppref.at (pp.kap L)) tbRef (w.layer L) L (S (2 * L)))
  ffOK : ∀ L < ppref.layers, FF.OK (ppref.at (pp.kap L)) tbRef (w.layer L) L (S (2 * L + 1))
  ff : ∀ L < ppref.layers,
    Agree ppref (S (2 * L + 2)) (FF.x'' (ppref.at (pp.kap L)) tbRef (w.layer L) L (S (2 * L + 1)))
  normOK : ∀ pos < ppref.T, NORM.OK pp.nf ppref.d (S (2 * ppref.layers) pos)
  form : Head3 x
  policy : PolOK (logitOf pp.nf w (S (2 * ppref.layers))) pp.pol x

variable {pp : ScalesAndPolicy} {w : Weights} {x : Instance ppref} {S : ℕ → ℕ → Vec}

/-- The integer program's stream at the settings pp. -/
abbrev streamOf (pp : ScalesAndPolicy) (w : Weights) (x : Instance ppref) : ℕ → ℕ → Vec :=
  XK ppref pp.kap (fun _ => tbRef) w x.prompt

theorem stream_att (pp : ScalesAndPolicy) (w : Weights) (x : Instance ppref) (L : ℕ) :
    streamOf pp w x (2 * L + 1) =
      Att.x' (ppref.at (pp.kap L)) tbRef (w.layer L) L (streamOf pp w x (2 * L)) := by
  have e := XK_even (κ := pp.kap) (fun _ => tbRef) w x.prompt (n := 2 * L) (by omega)
  rwa [show 2 * L / 2 = L by omega] at e

theorem stream_ff (pp : ScalesAndPolicy) (w : Weights) (x : Instance ppref) (L : ℕ) :
    streamOf pp w x (2 * L + 2) =
      FF.x'' (ppref.at (pp.kap L)) tbRef (w.layer L) L (streamOf pp w x (2 * L + 1)) := by
  have e := XK_odd (κ := pp.kap) (fun _ => tbRef) w x.prompt (n := 2 * L + 1) (by omega)
  rwa [show (2 * L + 1) / 2 = L by omega] at e

/-- **Under Says, S is the integer program's stream.** -/
theorem says_stream (H : Says pp w x S) :
    ∀ l ≤ 2 * ppref.layers, Agree ppref (S l) (streamOf pp w x l)
  | 0, _ => fun i hi j hj => by
    show S 0 i j = if h : i < ppref.T then w.Emb (x.prompt ⟨i, h⟩) j else 0
    rw [dif_pos hi]
    exact H.emb i hi j hj
  | l + 1, hl => by
    have ih := says_stream H l (Nat.le_of_succ_le hl)
    by_cases hev : l % 2 = 0
    · obtain ⟨L, rfl⟩ : ∃ L, l = 2 * L := ⟨l / 2, by omega⟩
      rw [stream_att]
      exact (H.att L (by omega)).trans (att_x'_congr (P := ppref.at (pp.kap L)) ih)
    · obtain ⟨L, rfl⟩ : ∃ L, l = 2 * L + 1 := ⟨l / 2, by omega⟩
      rw [show 2 * L + 1 + 1 = 2 * L + 2 from rfl, stream_ff]
      exact (H.ff L (by omega)).trans (ff_x''_congr (P := ppref.at (pp.kap L)) ih)

/-- Two last streams that agree give the same logits at every position below T. -/
theorem logitOf_congr (nf : NormPar) (w : Weights) {X X' : ℕ → Vec} (h : Agree ppref X X')
    {pos : ℕ} (hp : pos < ppref.T) : logitOf nf w X pos = logitOf nf w X' pos :=
  funext fun _ => dot_congr _ fun _ hj => norm_out nf (fun k hk => h pos hp k hk) hj

/-- The policy's clauses read the logits at the positions below T alone. -/
theorem polOK_congr {lg lg' : ℕ → ℕ → ℤ} (h : ∀ t < ppref.T, lg t = lg' t) {pol : AcceptancePolicy}
    (H : PolOK lg pol x) : PolOK lg' pol x := by
  have hc : ∀ t ∈ x.cnt, costOf lg x t = costOf lg' x t := fun t ht => by
    have ht' : t < ppref.T := by
      have h2 := (Finset.mem_Ico.1 ht).2
      have h3 : min x.e (ppref.T - 1) ≤ ppref.T - 1 := min_le_right _ _
      have h4 : 0 < ppref.T := by decide
      omega
    unfold costOf
    rw [h t ht']
  refine ⟨?_, ?_, fun h1 h2 => ?_⟩
  · have e : ∑ t ∈ x.cnt, min (costOf lg x t) (pol.C : ℤ) =
        ∑ t ∈ x.cnt, min (costOf lg' x t) (pol.C : ℤ) :=
      Finset.sum_congr rfl fun t ht => by rw [hc t ht]
    rw [← e]
    exact H.a
  · have e : (x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t) =
        x.cnt.filter fun t => (pol.C : ℤ) < costOf lg' x t :=
      Finset.filter_congr fun t ht => by rw [hc t ht]
    rw [← e]
    exact H.b
  · rw [← h (ppref.T - 1) (by decide)]
    exact H.c h1 h2

/-- **Says gives the relation**: the program runs on the request's tokens, the request has its form,
and the policy's clauses hold of the program's logits. -/
theorem true_of_says {i : Index ppref} (H : Says pp i.val x S) : RinfPP pp i x := by
  have hS := says_stream H
  refine ⟨⟨fun L hL => ⟨?_, ?_⟩, fun pos hp => ?_⟩, H.form, ?_⟩
  · exact (att_ok_congr (P := ppref.at (pp.kap L)) (hS (2 * L) (by omega))).1 (H.attOK L hL)
  · exact (ff_ok_congr (P := ppref.at (pp.kap L)) (hS (2 * L + 1) (by omega))).1 (H.ffOK L hL)
  · exact (norm_OK pp.nf fun k hk => hS _ le_rfl pos hp k hk).1 (H.normOK pos hp)
  · exact polOK_congr (fun t ht => logitOf_congr pp.nf i.val (hS _ le_rfl) ht) H.policy

/-- **Under the relation the program's own stream meets Says.** -/
theorem says_of_true {i : Index ppref} (H : RinfPP pp i x) :
    Says pp i.val x (streamOf pp i.val x) where
  emb pos h j _ := by
    show (if h : pos < ppref.T then i.val.Emb (x.prompt ⟨pos, h⟩) j else 0) = _
    rw [dif_pos h]
  attOK L hL := (H.1.1 L hL).1
  att L _ := fun _ _ _ _ => by rw [stream_att]
  ffOK L hL := (H.1.1 L hL).2
  ff L _ := fun _ _ _ _ => by rw [stream_ff]
  normOK := H.1.2
  form := H.2.1
  policy := H.2.2

/-- **Nothing is lost, nothing is added.** -/
theorem says_iff (pp : ScalesAndPolicy) (i : Index ppref) (x : Instance ppref) :
    (∃ S, Says pp i.val x S) ↔ RinfPP pp i x :=
  ⟨fun ⟨_, H⟩ => true_of_says H, fun H => ⟨_, says_of_true H⟩⟩

/-- **A request is true under its policy exactly if some stream meets Says** at the weights that
the index holds. -/
theorem isTrueUnder_iff_says (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) :
    Policy.IsTrueUnder s pol i x ↔ ∃ S, Says (Policy.ppOf s pol) i.index.val x S :=
  (says_iff _ _ _).symm

end Meaning

#print axioms Meaning.says_stream
#print axioms Meaning.true_of_says
#print axioms Meaning.says_of_true
#print axioms Meaning.isTrueUnder_iff_says
