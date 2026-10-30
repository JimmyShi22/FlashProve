-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SplitProofs.lean: properties of a protocol whose rounds are split.

For `InteractiveOracleProof.split` (Iop/Split.lean; words of this library: lean/GLOSSARY.md):
  `splitLength : Spec.splitLength`: one round more for each split (statement: Iop/Split.lean)
  `InteractiveOracleProof.Sound.split`: round-by-round soundness after a split, with the errors `Err.split`
      (statement and hypotheses: below): from `Q.Sound L ε`, for every plan P,
      `(Q.split P).Sound L (Err.split P ε)`; `P.OK` is not among its hypotheses
Some of the other properties are proved for plans with `SPlan.OK`.

As in Iop/PullProofs.lean: `Tr.merge` maps a transcript of the new protocol to one of the old.
Verifier randomness, plain parts, answers of oracles, runs of strategies and the disclosed view
(`DView`, Iop/InteractiveOracleProof.lean) commute with it (answers of oracles and the disclosed view: under
`P.OK`). So, under `P.OK`, the honest output at ρ is the image of the honest output at
`Rho.merge P ρ`, the simulator is the image of the old simulator, each abort set
(`Honest.withheld`) is the preimage of the old one, and each exceptional set of a simulator is
contained in the preimage of the old one. `Rho.merge` is a bijection (it drops empty challenges), so
a preimage has the same probability.
Soundness: after a first part the transcript is doomed (`Doomed`) if it is doomed whatever the
remainder is.
That the oracles of the parts are strings if the round's oracle is one (`RCut.pointFst`,
`RCut.pointSnd`) is shown for every split with `RCut.OK`. They transport a string along the
bijection of the positions (`Equiv.piCongrLeft`); an instantiation that needs plainer terms supplies
its own.

Notation: `Q.Sound L ε : Prop` (`InteractiveOracleProof.Sound`, Iop/InteractiveOracleProof.lean): round-by-round soundness for a
language of pairs (x, y), y a value of the external strings: for every pair outside it the empty
transcript is doomed to rejection, with the errors ε; `L : X → E.Str → Prop`: the language;
`Err s : Type` (Iop/Rbr.lean): one number for each round; in `Doomed s ε bad` (there), how many
values of the challenge may lead from a doomed transcript to one that is not doomed;
`Doomed s ε bad : Prop` (there): the empty transcript is doomed with respect to `bad` (a property
of full transcripts, bad for the prover); `Err.Below ε b : Prop` (Iop/InteractiveOracleProof.lean): every error of
the list, as a probability, is at most b, for a round r with the error e:
`(e : ℝ≥0∞) ≤ b * (Fintype.card r.Chal : ℝ≥0∞)`; `P.OK : Prop` (`SPlan.OK`, Iop/Split.lean): all
splits of the plan satisfy `RCut.OK`; `valid : Wt → X → Prop`, `z : ℝ≥0∞`: arguments of
`Honest.HVZK` (Iop/InteractiveOracleProof.lean).
-/
import Iop.Split
import Prob.Count
import Mathlib.Data.Finset.Sum

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. One split -/

section OneCut
variable {r : Round} (c : RCut r)

theorem RCut.join_left_right (m : r.Msg) : c.join (c.left m) (c.right m) = m :=
  Prod.ext (c.orc.symm_apply_apply m.1) (c.plain.symm_apply_apply m.2)

theorem RCut.left_join (a : c.fst.Msg) (b : c.snd.Msg) : c.left (c.join a b) = a := by
  refine Prod.ext ?_ ?_
  · show (c.orc (c.orc.symm (a.1, b.1))).1 = a.1
    rw [Equiv.apply_symm_apply]
  · show (c.plain (c.plain.symm (a.2, b.2))).1 = a.2
    rw [Equiv.apply_symm_apply]

theorem RCut.right_join (a : c.fst.Msg) (b : c.snd.Msg) : c.right (c.join a b) = b := by
  refine Prod.ext ?_ ?_
  · show (c.orc (c.orc.symm (a.1, b.1))).2 = b.1
    rw [Equiv.apply_symm_apply]
  · show (c.plain (c.plain.symm (a.2, b.2))).2 = b.2
    rw [Equiv.apply_symm_apply]

variable {c} {s : Shape}

theorem RCut.rho_glue (a : c.fst.Msg) (w : Tr (c.snd :: s)) : (c.glue a w).rho = w.rho := by
  obtain ⟨b, ch, t⟩ := w
  rfl

theorem RCut.plains_glue (a : c.fst.Msg) (w : Tr (c.snd :: s)) :
    (c.glue a w).plains = (c.plain.symm (a.2, w.plains.1), w.plains.2) := by
  obtain ⟨b, ch, t⟩ := w
  rfl

theorem RCut.read_glue_inl (hc : c.OK) (a : c.fst.Msg) (w : Tr (c.snd :: s)) (p : c.PosA) :
    (c.glue a w).read (c.posAssoc s (.inl p)) = c.rdA a.1 p := by
  show r.rd (c.orc.symm (a.1, w.1.1)) (c.pos (.inl p)) = c.rdA a.1 p
  rw [hc.rdA, Equiv.apply_symm_apply]

theorem RCut.read_glue_inr (hc : c.OK) (a : c.fst.Msg) (w : Tr (c.snd :: s)) :
    ∀ z : OPos (c.snd :: s), (c.glue a w).read (c.posAssoc s (.inr z)) = c.symUp z (w.read z)
  | .inl p => by
      obtain ⟨b, ch, t⟩ := w
      show r.rd (c.orc.symm (a.1, b.1)) (c.pos (.inr p)) = c.rdB b.1 p
      rw [hc.rdB, Equiv.apply_symm_apply]
  | .inr _ => by
      obtain ⟨b, ch, t⟩ := w
      rfl

theorem RCut.symDown_symUp :
    ∀ (z : OPos (c.snd :: s)) (a : OSym (c.snd :: s) z), c.symDown z (c.symUp z a) = a
  | .inl _, _ => rfl
  | .inr _, _ => rfl

end OneCut

/-! ## 2. The maps to the old rounds -/

theorem splitLength : Spec.splitLength := by
  intro s P
  induction P with
  | nil => rfl
  | keep r P ih =>
      show P.shape.length + 1 = _ + 1 + P.cuts
      omega
  | cut c P ih =>
      have ih' : P.shape.length = _ + 1 + P.cuts := ih
      show P.shape.length + 1 = _ + 1 + (P.cuts + 1)
      omega

theorem Tr.rho_merge {s : Shape} (P : SPlan s) :
    ∀ τ : Tr P.shape, (Tr.merge P τ).rho = Rho.merge P τ.rho := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨m, c, τ⟩
      show (c, (Tr.merge P τ).rho) = (c, Rho.merge P τ.rho)
      rw [ih]
  | cut c P ih =>
      rintro ⟨a, u, τ⟩
      exact (RCut.rho_glue a (Tr.merge P τ)).trans (ih τ)

theorem Tr.plains_merge {s : Shape} (P : SPlan s) :
    ∀ τ : Tr P.shape, (Tr.merge P τ).plains = Plains.merge P τ.plains := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨m, c, τ⟩
      show (m.2, (Tr.merge P τ).plains) = (m.2, Plains.merge P τ.plains)
      rw [ih]
  | cut c P ih =>
      rintro ⟨a, u, τ⟩
      refine (RCut.plains_glue a (Tr.merge P τ)).trans ?_
      rw [ih]
      rfl

theorem Plains.split_merge {s : Shape} (P : SPlan s) :
    ∀ pl : Plains P.shape, Plains.split P (Plains.merge P pl) = pl := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨a, pl⟩
      show (a, Plains.split P (Plains.merge P pl)) = (a, pl)
      rw [ih]
  | cut c P ih =>
      rintro ⟨a, pl⟩
      show ((c.plain (c.plain.symm (a, (Plains.merge P pl).1))).1,
          Plains.split P
            ((c.plain (c.plain.symm (a, (Plains.merge P pl).1))).2, (Plains.merge P pl).2)) =
        (a, pl)
      rw [Equiv.apply_symm_apply]
      exact congrArg (Prod.mk a) (ih pl)

theorem OSym.split_merge {s : Shape} (P : SPlan s) :
    ∀ (p : OPos P.shape) (a : OSym P.shape p), OSym.split P p (OSym.merge P p a) = a := by
  induction P with
  | nil => intro p; exact Empty.elim p
  | keep r P ih =>
      rintro (p | q) a
      · rfl
      · exact ih q a
  | cut c P ih =>
      rintro (p | q) a
      · rfl
      · show OSym.split P q (c.symDown _ (c.symUp _ (OSym.merge P q a))) = a
        rw [RCut.symDown_symUp, ih]

/-- Under `P.OK`, the answers of the prover's oracles do not change. -/
theorem Tr.read_merge {s : Shape} (P : SPlan s) (hP : P.OK) : ∀ (τ : Tr P.shape) (p : OPos P.shape),
    (Tr.merge P τ).read (OPos.mergeEquiv P p) = OSym.merge P p (τ.read p) := by
  induction P with
  | nil => intro _ p; exact Empty.elim p
  | keep r P ih =>
      rintro ⟨m, c, τ⟩ (p | q)
      · rfl
      · exact ih hP τ q
  | cut c P ih =>
      rintro ⟨a, u, τ⟩ (p | q)
      · exact RCut.read_glue_inl hP.1 a (Tr.merge P τ) p
      · refine (RCut.read_glue_inr hP.1 a (Tr.merge P τ) (OPos.mergeEquiv P q)).trans ?_
        rw [ih hP.2]
        rfl

/-- The transcript of a run of the strategy that sends in parts, mapped by `Tr.merge`, is that of
the run of the old strategy at `Rho.merge P ρ`. -/
theorem Strat.run_split {s : Shape} {β : Type} (P : SPlan s) : ∀ (S : Strat s β) (ρ : Rho P.shape),
    Tr.merge P ((Strat.split P S).run ρ).1 = (S.run (Rho.merge P ρ)).1 := by
  induction P with
  | nil => intro _ _; rfl
  | keep r P ih =>
      rintro ⟨m, k⟩ ⟨c, ρ⟩
      show (m, c, Tr.merge P ((Strat.split P (k c)).run ρ).1) =
        (m, c, ((k c).run (Rho.merge P ρ)).1)
      rw [ih]
  | @cut r s c P ih =>
      rintro ⟨m, k⟩ ⟨u, ρ⟩
      show c.glue (c.left m) (Tr.merge P ((Strat.split P (c.right m, k)).run ρ).1) =
        (Strat.run (s := r :: s) (m, k) (Rho.merge (s := c.snd :: s) P ρ)).1
      rw [ih]
      generalize Rho.merge P ρ = ρ'
      obtain ⟨ch, ρ''⟩ := ρ'
      show (c.join (c.left m) (c.right m), ch, ((k ch).run ρ'').1) = (m, ch, ((k ch).run ρ'').1)
      rw [RCut.join_left_right]

/-! ## 3. The verifier randomness: a bijection -/

theorem Rho.split_merge {s : Shape} (P : SPlan s) :
    ∀ ρ : Rho P.shape, Rho.split P (Rho.merge P ρ) = ρ := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨c, ρ⟩
      show (c, Rho.split P (Rho.merge P ρ)) = (c, ρ)
      rw [ih]
  | cut c P ih =>
      rintro ⟨u, ρ⟩
      show ((), Rho.split P (Rho.merge P ρ)) = (u, ρ)
      rw [ih]

theorem Rho.merge_split {s : Shape} (P : SPlan s) :
    ∀ ρ : Rho s, Rho.merge P (Rho.split P ρ) = ρ := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨c, ρ⟩
      show (c, Rho.merge P (Rho.split P ρ)) = (c, ρ)
      rw [ih]
  | cut c P ih => exact fun ρ => ih ρ

/-- The new verifier randomness is the old one, with empty challenges put in. -/
def Rho.mergeEquiv {s : Shape} (P : SPlan s) : Rho P.shape ≃ Rho s :=
  ⟨Rho.merge P, Rho.split P, Rho.split_merge P, Rho.merge_split P⟩

/-- The preimage of a set of values of the verifier randomness has the same probability. -/
theorem prRho_merge {s : Shape} (P : SPlan s) (S : Set (Rho s)) :
    prRho {ρ : Rho P.shape | Rho.merge P ρ ∈ S} = prRho S := by
  unfold prRho
  rw [← map_unif_equiv (Rho.mergeEquiv P), pr_map]
  rfl

/-! ## 4. Soundness -/

/-- `Doomed` is preserved; in a new round no value of the (empty) challenge leads to a transcript
that is not doomed. -/
theorem Doomed.splitS {s : Shape} (P : SPlan s) : ∀ (ε : Err s) (bad : Tr s → Prop),
    Doomed s ε bad → Doomed P.shape (Err.split P ε) (fun τ => bad (Tr.merge P τ)) := by
  induction P with
  | nil => intro _ _ h; exact h
  | keep r P ih =>
      rintro ⟨e, ε⟩ bad h
      exact fun m => le_trans (cnt_mono fun c hc hd => hc (ih ε (fun τ => bad (m, c, τ)) hd)) (h m)
  | cut c P ih =>
      intro ε bad h
      refine fun a => le_of_eq (cnt_false fun _ hn => hn (ih ε (fun z => bad (c.glue a z)) ?_))
      obtain ⟨e, ε⟩ := ε
      exact fun b => h (c.join a b)

theorem InteractiveOracleProof.Sound.split {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} (P : SPlan Q.shape)
    {L : X → E.Str → Prop} {ε : Err Q.shape} (h : Q.Sound L ε) :
    (Q.split P).Sound L (Err.split P ε) :=
  fun x y hL => Doomed.splitS P ε _ (h x y hL)

/-- A bound on all errors of the old list bounds all errors of the new one. -/
theorem Err.Below.split {s : Shape} (P : SPlan s) :
    ∀ {ε : Err s} {b : ℝ≥0∞}, Err.Below ε b → Err.Below (Err.split P ε) b := by
  induction P with
  | nil => intro _ _ _; trivial
  | keep r P ih =>
      rintro ⟨e, ε⟩ b h
      exact ⟨h.1, ih h.2⟩
  | cut c P ih =>
      intro ε b h
      exact ⟨by simp, ih h⟩

/-! ## 5. Locality, acceptance, abort sets -/

section OneProtocol

variable {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} {Wt : Type}

theorem InteractiveOracleProof.mem_reads_split
    (P : SPlan Q.shape) (x : X) (ρ : Rho P.shape) (pl : Plains P.shape) (p : OPos P.shape) :
    p ∈ (Q.split P).reads x ρ pl ↔
    OPos.mergeEquiv P p ∈ Q.reads x (Rho.merge P ρ) (Plains.merge P pl) := by
  show p ∈
      (Q.reads x (Rho.merge P ρ) (Plains.merge P pl)).map (OPos.mergeEquiv P).symm.toEmbedding ↔
    _
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

/-- The verifier reads as many positions as before. -/
theorem InteractiveOracleProof.card_reads_split (P : SPlan Q.shape) (x : X) (ρ : Rho P.shape) (pl : Plains P.shape) :
    ((Q.split P).reads x ρ pl).card = (Q.reads x (Rho.merge P ρ) (Plains.merge P pl)).card :=
  Finset.card_map _

theorem InteractiveOracleProof.IsLocal.split (h : Q.IsLocal) {P : SPlan Q.shape} (hP : P.OK) :
    (Q.split P).IsLocal := by
  intro x y y' τ τ' hρ hpl hext hrd
  refine h x y y' (Tr.merge P τ) (Tr.merge P τ') ?_ ?_ ?_ ?_
  · rw [Tr.rho_merge, Tr.rho_merge]
    exact congrArg (Rho.merge P) hρ
  · rw [Tr.plains_merge, Tr.plains_merge]
    exact congrArg (Plains.merge P) hpl
  · intro p hp
    rw [Tr.rho_merge] at hp
    exact hext p hp
  · intro p hp
    rw [Tr.rho_merge, Tr.plains_merge] at hp
    obtain ⟨p', rfl⟩ := (OPos.mergeEquiv P).surjective p
    rw [Tr.read_merge P hP, Tr.read_merge P hP]
    exact congrArg (OSym.merge P p') (hrd p' ((InteractiveOracleProof.mem_reads_split P x _ _ p').2 hp))

theorem Honest.mem_withheld_split
    (H : Honest Q Wt) (P : SPlan Q.shape) (w : Wt) (x : X) (ρ : Rho P.shape) :
    ρ ∈ (H.split P).withheld w x ↔ Rho.merge P ρ ∈ H.withheld w x := Iff.rfl

theorem Honest.Acc.split {H : Honest Q Wt} {valid : Wt → X → Prop}
    (h : H.Acc valid) (P : SPlan Q.shape) : (H.split P).Acc valid := by
  intro w x c ρ hv hρ
  show Q.accept x (H.ext w) (Tr.merge P ((Strat.split P (H.strat w x c)).run ρ).1) = true
  rw [Strat.run_split]
  exact h w x c (Rho.merge P ρ) hv hρ

theorem Honest.prRho_withheld_split (H : Honest Q Wt) (P : SPlan Q.shape) (w : Wt) (x : X) :
    prRho ((H.split P).withheld w x) = prRho (H.withheld w x) := prRho_merge P (H.withheld w x)

/-! ## 6. Honest-verifier zero knowledge -/

/-- A disclosed view (`DView`) of the protocol, read as a disclosed view of the protocol that sends
in parts. -/
def DView.split (P : SPlan Q.shape) (v : DView Q) : DView (Q.split P) where
  plains := Plains.split P v.plains
  ext := v.ext
  orc := fun p => (v.orc (OPos.mergeEquiv P p)).map (OSym.split P p)

theorem InteractiveOracleProof.extAns_split (P : SPlan Q.shape) (x : X) (ρ : Rho P.shape) (y : E.Str) :
    (Q.split P).extAns x ρ y = Q.extAns x (Rho.merge P ρ) y := rfl

/-- Under `P.OK`, the disclosed view of a transcript is the image of the disclosed view of the old
transcript. -/
theorem InteractiveOracleProof.dview_split {P : SPlan Q.shape} (hP : P.OK) (x : X) (y : E.Str) (τ : Tr P.shape) :
    (Q.split P).dview x y τ = DView.split P (Q.dview x y (Tr.merge P τ)) := by
  have h1 : τ.plains = Plains.split P (Tr.merge P τ).plains := by
    rw [Tr.plains_merge, Plains.split_merge]
  have h2 : (Q.split P).extAns x τ.rho y = Q.extAns x (Tr.merge P τ).rho y := by
    rw [Tr.rho_merge, InteractiveOracleProof.extAns_split]
  have h3 : ((Q.split P).dview x y τ).orc = (DView.split P (Q.dview x y (Tr.merge P τ))).orc := by
    funext p
    have hiff : (p ∈ (Q.split P).reads x τ.rho τ.plains ∨ (Q.split P).blinded p = false) ↔
        (OPos.mergeEquiv P p ∈ Q.reads x (Tr.merge P τ).rho (Tr.merge P τ).plains ∨
          Q.blinded (OPos.mergeEquiv P p) = false) := by
      refine or_congr ?_ Iff.rfl
      rw [Tr.rho_merge, Tr.plains_merge]
      exact InteractiveOracleProof.mem_reads_split P x τ.rho τ.plains p
    dsimp only [InteractiveOracleProof.dview, DView.split]
    split_ifs with ha hb hb
    · exact congrArg some
        ((OSym.split_merge P p (τ.read p)).symm.trans
          (congrArg (OSym.split P p) (Tr.read_merge P hP τ p).symm))
    · exact absurd (hiff.1 ha) hb
    · exact absurd (hiff.2 hb) ha
    · rfl
  show DView.mk τ.plains ((Q.split P).extAns x τ.rho y) ((Q.split P).dview x y τ).orc
    = DView.mk (Plains.split P (Tr.merge P τ).plains) (Q.extAns x (Tr.merge P τ).rho y)
        (DView.split P (Q.dview x y (Tr.merge P τ))).orc
  rw [← h1, ← h2, ← h3]

/-- Under `P.OK`, the honest output at ρ is the image of the honest output at `Rho.merge P ρ`. -/
theorem Honest.output_split (H : Honest Q Wt) {P : SPlan Q.shape} (hP : P.OK) (w : Wt)
    (x : X) (ρ : Rho P.shape) :
    (H.split P).output w x ρ = (H.output w x (Rho.merge P ρ)).map (Option.map (DView.split P)) := by
  by_cases h : Rho.merge P ρ ∈ H.withheld w x
  · have e1 : (H.split P).output w x ρ = PMF.pure none := if_pos h
    have e2 : H.output w x (Rho.merge P ρ) = PMF.pure none := if_pos h
    rw [e1, e2, PMF.pure_map]
    rfl
  · have e1 : (H.split P).output w x ρ
        = (unif H.Coin).map fun c =>
          some ((Q.split P).dview x (H.ext w) ((Strat.split P (H.strat w x c)).run ρ).1) := if_neg h
    have e2 : H.output w x (Rho.merge P ρ) =
        (unif H.Coin).map fun c =>
          some (Q.dview x (H.ext w) ((H.strat w x c).run (Rho.merge P ρ)).1) := if_neg h
    rw [e1, e2, PMF.map_comp]
    congr 1
    funext c
    show some ((Q.split P).dview x (H.ext w) ((Strat.split P (H.strat w x c)).run ρ).1)
      = some (DView.split P (Q.dview x (H.ext w) ((H.strat w x c).run (Rho.merge P ρ)).1))
    rw [InteractiveOracleProof.dview_split hP, Strat.run_split]

/-- Under `P.OK`, honest-verifier zero knowledge in the exact form is preserved, with the same
number: the simulator is the image of the old one, and the exceptional set is contained in the
preimage of the old one. -/
theorem Honest.HVZK.split {H : Honest Q Wt} {valid : Wt → X → Prop} {z : ℝ≥0∞} (h : H.HVZK valid z)
    {P : SPlan Q.shape} (hP : P.OK) : (H.split P).HVZK valid z := by
  obtain ⟨Sim, hS⟩ := h
  refine ⟨fun x ρ a => (Sim x (Rho.merge P ρ) a).map (Option.map (DView.split P)), fun w x hv => ?_⟩
  refine le_trans (pr_mono _ ?_) ((le_of_eq (prRho_merge P _)).trans (hS w x hv))
  intro ρ hρ heq
  apply hρ
  rw [Honest.output_split H hP, heq]
  rfl

end OneProtocol

/-! ## 7. String oracles -/

section Points
variable {r : Round} (c : RCut r)

/-- A string of r from the symbols of the two parts. -/
def RCut.spread (f : ∀ p : c.PosA, r.Sym (c.pos (.inl p)))
    (g : ∀ p : c.PosB, r.Sym (c.pos (.inr p))) : ∀ q : r.Pos, r.Sym q :=
  Equiv.piCongrLeft r.Sym c.pos fun z => match z with
    | .inl p => f p
    | .inr p => g p

theorem RCut.spread_inl (f : ∀ p : c.PosA, r.Sym (c.pos (.inl p)))
    (g : ∀ p : c.PosB, r.Sym (c.pos (.inr p))) (p : c.PosA) :
    c.spread f g (c.pos (.inl p)) = f p :=
  Equiv.piCongrLeft_apply_apply r.Sym c.pos _ (.inl p)

theorem RCut.spread_inr (f : ∀ p : c.PosA, r.Sym (c.pos (.inl p)))
    (g : ∀ p : c.PosB, r.Sym (c.pos (.inr p))) (p : c.PosB) :
    c.spread f g (c.pos (.inr p)) = g p :=
  Equiv.piCongrLeft_apply_apply r.Sym c.pos _ (.inr p)

variable {c}

/-- Under `c.OK`, for a string oracle, the string with given halves is the string of their symbols.
-/
theorem RCut.OK.ofSyms_spread (hc : c.OK) (h : r.IsPoint) (a : c.OrcA) (b : c.OrcB) :
    h.ofSyms (c.spread (c.rdA a) (c.rdB b)) = c.orc.symm (a, b) := by
  rw [← h.ofSyms_rd (c.orc.symm (a, b))]
  congr 1
  funext q
  obtain ⟨z, rfl⟩ := c.pos.surjective q
  cases z with
  | inl p => rw [RCut.spread_inl, hc.rdA, Equiv.apply_symm_apply]
  | inr p => rw [RCut.spread_inr, hc.rdB, Equiv.apply_symm_apply]

/-- Under `c.OK`: if r's oracle is a string, so is the first part's. -/
def RCut.pointFst (hc : c.OK) (h : r.IsPoint) : c.fst.IsPoint where
  finPos := letI := h.finPos; letI : Fintype (c.PosA ⊕ c.PosB) := Fintype.ofEquiv r.Pos c.pos.symm
    ⟨(Finset.univ : Finset (c.PosA ⊕ c.PosB)).toLeft, fun p => by simp⟩
  decPos := fun a b => letI := h.decPos
    decidable_of_iff (c.pos (.inl a) = c.pos (.inl b))
      ⟨fun e => Sum.inl.inj (c.pos.injective e), fun e => by rw [e]⟩
  ofSyms := fun f => (c.orc (h.ofSyms (c.spread f fun p => h.zero _))).1
  rd_ofSyms := fun f p => by
    show c.rdA (c.orc (h.ofSyms (c.spread f fun p => h.zero _))).1 p = f p
    rw [← hc.rdA, h.rd_ofSyms, RCut.spread_inl]
  ofSyms_rd := fun a => by
    show (c.orc (h.ofSyms (c.spread (c.rdA a) fun p => h.zero _))).1 = a
    have e : (fun p : c.PosB => h.zero (c.pos (.inr p))) =
        c.rdB (c.orc (h.ofSyms (c.spread (c.rdA a) fun p => h.zero _))).2 := by
      funext p
      rw [← hc.rdB, h.rd_ofSyms, RCut.spread_inr]
    generalize hb : (c.orc (h.ofSyms (c.spread (c.rdA a) fun p => h.zero _))).2 = b at e
    rw [e, hc.ofSyms_spread h, Equiv.apply_symm_apply]
  zero := fun p => h.zero _

/-- Under `c.OK`: if r's oracle is a string, so is the remainder's. -/
def RCut.pointSnd (hc : c.OK) (h : r.IsPoint) : c.snd.IsPoint where
  finPos := letI := h.finPos; letI : Fintype (c.PosA ⊕ c.PosB) := Fintype.ofEquiv r.Pos c.pos.symm
    ⟨(Finset.univ : Finset (c.PosA ⊕ c.PosB)).toRight, fun p => by simp⟩
  decPos := fun a b => letI := h.decPos
    decidable_of_iff (c.pos (.inr a) = c.pos (.inr b))
      ⟨fun e => Sum.inr.inj (c.pos.injective e), fun e => by rw [e]⟩
  ofSyms := fun g => (c.orc (h.ofSyms (c.spread (fun p => h.zero _) g))).2
  rd_ofSyms := fun g p => by
    show c.rdB (c.orc (h.ofSyms (c.spread (fun p => h.zero _) g))).2 p = g p
    rw [← hc.rdB, h.rd_ofSyms, RCut.spread_inr]
  ofSyms_rd := fun b => by
    show (c.orc (h.ofSyms (c.spread (fun p => h.zero _) (c.rdB b)))).2 = b
    have e : (fun p : c.PosA => h.zero (c.pos (.inl p))) =
        c.rdA (c.orc (h.ofSyms (c.spread (fun p => h.zero _) (c.rdB b)))).1 := by
      funext p
      rw [← hc.rdA, h.rd_ofSyms, RCut.spread_inl]
    generalize ha : (c.orc (h.ofSyms (c.spread (fun p => h.zero _) (c.rdB b)))).1 = a at e
    rw [e, hc.ofSyms_spread h, Equiv.apply_symm_apply]
  zero := fun p => h.zero _

end Points

/-- Under `P.OK`, the new rounds' oracles are strings if the old ones are. -/
def Shape.IsPoint.split : {s : Shape} → (P : SPlan s) → P.OK → s.IsPoint → P.shape.IsPoint
  | _, .nil => fun _ _ => ()
  | _, .keep _ P => fun hP h => (h.1, Shape.IsPoint.split P hP h.2)
  | _, .cut _ P =>
    fun hP h => (RCut.pointFst hP.1 h.1, Shape.IsPoint.split P hP.2 (RCut.pointSnd hP.1 h.1, h.2))

end Iop
