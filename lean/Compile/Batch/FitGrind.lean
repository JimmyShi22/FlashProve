-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/FitGrind.lean: the protocols with proof-of-work bits and their wire record meet three
hypotheses of the compiler theorem for such rounds, given soundness of these protocols. Statement
and proof.

Proof-of-work bits are written twice. In the record of protocols (`L.grind W gT gL gB`,
Iop/BatchGrind.lean): the nonce in the plain part, the bits in the verifier message, the verifier's
check. In the wire record (the records `gr0`, `grJ`, Iop/BatchWire.lean), which is all that the
honest prover's search reads. The compiler theorems for such rounds are generic: they take a record
of protocols with all properties but (Acc) (`BatchProtocol.PropsNoAcc`, Iop/BatchGrind.lean), a well-formed
wire record, and that the two fit (`GrFit`, `GrFitB`: Compile/Batch/SpecFit.lean). They do not name
`L.grind`. This file shows that `L.grind` and `Wr.grind D` (Iop/GrindWire.lean) meet these
hypotheses, for every inhabited type W of nonces, every L with `BatchProtocol.Props`, every well-formed wire
record Wr of L, all lists of numbers of proof-of-work bits up to some n ≤ λ, all data D of the
search that are well-formed up to n, and given soundness of `L.grind` at εs'.

  `strip_putB_grind`, `strip_putB_grindLocal`  To write numbers in as nonces changes nothing but
                                               nonces.
  `GrFit.of_strip`  The six clauses of `GrFit`, from: everything of the new honest side is the old
                    one at the stripped randomness; (Acc) and locality of the old protocol; the wire
                    record's checks are the protocol's; to write numbers in as nonces changes
                    nothing but nonces.
  `failBits D b`, `gFail D g`, `cFail_grind`, `cFail_grindLocal`  The term that stands for the
                                                                  probability that a search fails,
                                                                  (1 - 2^-b)^(mo b + 1); its sum
                                                                  over the rounds with such bits;
                                                                  that is the wire record's sum.
  `tVB_wireGrind`, `epsB_wireGrind`  The bound on the verifier's queries is as before, so ε is the
                                     old formula at the old wire record.
  `Spec.fitGrind`, `fitGrind`  The main statement.

Where (Acc) and locality of L are used: `GrFit.acc` is about any transcript that has the honest
prover's oracle answers and its plain parts with other nonces. Its stripped transcript agrees with
the old honest run in the verifier randomness, the plain parts and all answers; the old verifier,
being local, decides the same on both.

Notation: `D`: a `GrData W` (Iop/GrindWire.lean): what the wire record adds to the numbers of
proof-of-work bits; `D.mo`: in a round with b proof-of-work bits the honest prover tries the nonces
for 0, .., mo b; `gT`, `gL`, `gB`: `GBits` of the three shapes (Iop/GBits.lean): for each round a
number of proof-of-work bits; `M`: an `LH.Nums` (Iop/InteractiveOracleProof.lean): all numbers of the interface ("the
numbers of L"); `εs'`: an `ℝ≥0∞`, which takes the place of `M.εs` in `{ M with εs := εs' }`; α:
`alphaB` (Compile/Batch/Spec.lean), `alphaBG` (Compile/Batch/SpecGrind.lean); ε: `epsB`
(Compile/Batch/SpecBinding.lean); ζ: the third bound of the compiler's theorem (the arguments of
`IsZKCPArgWith`, ZKCP/Gen.lean).

Limits: soundness of `L.grind` at the number εs' is a hypothesis (`grindSoundB`,
Iop/BatchGrindProofs.lean, gives it from explicit lists of errors). Nothing at concrete parameters.
That `failBits` is the probability that a search fails is not part of this file. `fitGrind` does not
ask the format (`RoundSplits.Fmt`); without it α (`alphaBG`, Compile/Batch/SpecGrind.lean) counts searches
that are never run. ζ is at the new wire record: it counts all attempts.
-/
import Compile.Batch.SpecGrind
import Iop.GrindWire

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open scoped ENNReal

variable {W : Type} [Inhabited W] {lam K : ℕ}

/-! ## 1. To write numbers in as nonces changes nothing but nonces -/

/-- With the round's record q (`grJOf`): to write a number into the slot's component changes the
nonce only. -/
theorem old_putJ {r : Round} (a : RAnn r) (D : GrData W) :
    ∀ (b : ℕ) (q : GrW (GChal b r.Chal) (GPlain W (a.kind.bJ b) a.Pj)),
      grJOf D r.Chal a.Pj a.kind b = some q →
      ∀ (k : ℕ) (pl : GPlain W b r.Plain),
        GPlain.old ((a.grind W b).plain.symm
              (((a.grind W b).plain pl).1, q.put k ((a.grind W b).plain pl).2)) =
          GPlain.old pl := by
  obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pe, own⟩ := a
  intro b
  cases k <;> cases b
  · intro _ e; cases e
  · intro _ e; cases e
  · intro _ e; cases e
  · intro _ e
    cases e
    rintro _ ⟨p, _⟩
    exact pe.symm_apply_apply p

/-- With the round's record q (`gr0Of`): to write a number into the shared component changes the
nonce only. -/
theorem old_put0 {r : Round} (a : RAnn r) (D : GrData W) :
    ∀ (b : ℕ) (q : GrW (GChal b r.Chal) (GPlain W (a.kind.b0 b) a.P0)),
      gr0Of D r.Chal a.P0 a.kind b = some q →
      ∀ (k : ℕ) (pl : GPlain W b r.Plain),
        GPlain.old ((a.grind W b).plain.symm
              (q.put k ((a.grind W b).plain pl).1, ((a.grind W b).plain pl).2)) =
          GPlain.old pl := by
  obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pe, own⟩ := a
  intro b
  cases k <;> cases b
  · intro _ e; cases e
  · intro _ e
    cases e
    rintro _ ⟨p, _⟩
    exact pe.symm_apply_apply p
  · intro _ e; cases e
  · intro _ e; cases e

/-- To write numbers in as nonces changes nothing but nonces: Batch. -/
theorem strip_putB_grind (D : GrData W) :
    ∀ {s : Shape} {A : RoundSplits s} (ws : RoundsQueryLayout lam K s A) (g : GBits s) (ph : PhT)
        (nJ n0 : List ℕ) (pl : Plains (s.grind W g)),
      Plains.strip g (putB (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g) ph nJ n0 pl) =
        Plains.strip g pl
  | [], _, _, _, _, _, _, _ => rfl
  | r :: s, (a, A), (w, ws), (b, g), ph, nJ, n0, (pl, pls) => by
      have hJ := old_putJ a D b
      have h0 := old_put0 a D b
      have ih := fun ph nJ n0 => strip_putB_grind D ws g ph nJ n0 pls
      show Plains.strip (s := r :: s) (b, g)
          (putB (r.grind W b :: Shape.grind W s g) (a.grind W b, A.grind W g)
            (w.grind D b, RoundsQueryLayout.grind ws D g) ph nJ n0 (pl, pls)) =
        (GPlain.old pl, Plains.strip g pls)
      obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pe, own⟩ := a
      cases k <;> cases ph <;> cases b <;>
        first
          | exact Prod.ext rfl (ih _ _ _)
          | exact Prod.ext (hJ _ rfl _ pl) (ih _ _ _)
          | exact Prod.ext (h0 _ rfl _ pl) (ih _ _ _)

/-- The same for Test and Link. -/
theorem strip_putB_grindLocal (D : GrData W) :
    ∀ {s : Shape} (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)) (g : GBits s) (ph : PhT)
        (nJ n0 : List ℕ) (pl : Plains (s.grind W g)),
      Plains.strip g
          (putB (s.grind W g) (RoundSplits.allLocal (s.grind W g))
            (RoundsQueryLayout.grindLocal ws D g) ph nJ n0 pl) =
        Plains.strip g pl
  | [], _, _, _, _, _, _ => rfl
  | r :: s, (w, ws), (b, g), ph, nJ, n0, (pl, pls) => by
      have ih := fun ph nJ n0 => strip_putB_grindLocal D ws g ph nJ n0 pls
      show Plains.strip (s := r :: s) (b, g)
          (putB (r.grind W b :: Shape.grind W s g)
            (RAnn.allLocal (r.grind W b), RoundSplits.allLocal (Shape.grind W s g))
            (w.grindLocal D b, RoundsQueryLayout.grindLocal ws D g) ph nJ n0 (pl, pls)) =
        (GPlain.old pl, Plains.strip g pls)
      cases ph <;> cases b <;> exact Prod.ext rfl (ih _ _ _)

/-! ## 2. The six clauses -/

/-- An oracle answer of a new transcript is that of the stripped transcript. -/
theorem read_eq_fill {s : Shape} (g : GBits s) (τ : Tr (s.grind W g)) (p : OPos (s.grind W g)) :
    τ.read p = OSym.fill g p ((Tr.strip g τ).read (OPos.stripE g p)) := by
  rw [Tr.read_strip, OSym.fill_strip]

/-- An oracle answer of a run of an old strategy with a rule for the nonces is that of the old run
at the stripped randomness. -/
theorem read_run_grind {s : Shape} {β : Type} (g : GBits s) (σ : Strat s β) (n : NStrat W s g)
    (ρ : Rho (s.grind W g)) (p : OPos (s.grind W g)) :
    ((Strat.grind g σ n).run ρ).1.read p =
      OSym.fill g p ((σ.run (Rho.strip g ρ)).1.read (OPos.stripE g p)) := by
  rw [read_eq_fill, Strat.strip_run_grind]

/-- The records fit, if everything of the new honest side is the old one at the stripped randomness,
the wire record's checks are the protocol's, the old protocol has (Acc) and is local, and hput. -/
theorem GrFit.of_strip {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} (g : GBits Q.shape)
    {A' : RoundSplits (Q.shape.grind W g)} {Wt : Type}
    (H' : BatchHonestProver (⟨Q.grind W g, A'⟩ : BatchInteractiveOracleProof Y E) Wt)
    (wq : ProtocolQueryLayout lam K (⟨Q.grind W g, A'⟩ : BatchInteractiveOracleProof Y E)) (valid : Wt → Y → Prop)
    (H : Honest Q Wt) (ν : GNon W Q.shape)
    (hs : ∀ w x c, ∃ c0, H'.one.strat w x c = Strat.grind g (H.strat w x c0) (NStrat.const g ν))
    (hw : ∀ w x (ρ : Rho (Q.shape.grind W g)),
      ρ ∈ H'.one.withheld w x ↔ Rho.strip g ρ ∈ H.withheld w x)
    (he : ∀ w, H'.ext w = H.ext w)
    (hz : ∀ ρ, RoundsQueryLayout.zero (Q.shape.grind W g) A' wq.sh ρ = Rho.fill g (Rho.strip g ρ))
    (hp : ∀ ρ, RoundsQueryLayout.pass (Q.shape.grind W g) A' wq.sh ρ = Rho.pass g ρ)
    (hput : ∀ ph nJ n0 pl,
      Plains.strip g (putB (Q.shape.grind W g) A' wq.sh ph nJ n0 pl) = Plains.strip g pl)
    (hacc : H.Acc valid) (hloc : Q.IsLocal) : GrFit H' wq valid := by
  have sz : ∀ ρ, Rho.strip g (RoundsQueryLayout.zero (Q.shape.grind W g) A' wq.sh ρ) = Rho.strip g ρ :=
    fun ρ => by rw [hz, Rho.strip_fill]
  refine ⟨⟨fun w x ρ => ?_, fun w x c ρ => ?_, fun x ρ pl => ?_,
      fun x ρ => ?_, fun x ρ pl ph nJ n0 => ?_⟩,
    ?_⟩
  · have h2 := hw w x (RoundsQueryLayout.zero (Q.shape.grind W g) A' wq.sh ρ)
    rw [sz] at h2
    exact (hw w x ρ).trans h2.symm
  · obtain ⟨c0, e⟩ := hs w x c
    rw [e]
    exact ⟨(Strat.plains_run_grind g _ ν ρ).trans
        ((congrArg (fun r0 => Plains.fill g ((H.strat w x c0).run r0).1.plains ν) (sz ρ).symm).trans
          (Strat.plains_run_grind g _ ν _).symm),
      fun p =>
        (read_run_grind g _ _ ρ p).trans
          ((congrArg (fun r0 => OSym.fill g p (((H.strat w x c0).run r0).1.read (OPos.stripE g p)))
              (sz ρ).symm).trans
            (read_run_grind g _ _ _ p).symm)⟩
  · show (Q.reads x (Rho.strip g ρ) (Plains.strip g pl)).map _ =
      (Q.reads x (Rho.strip g (RoundsQueryLayout.zero (Q.shape.grind W g) A' wq.sh ρ))
        (Plains.strip g pl)).map _
    rw [sz]
  · show Q.extReads x (Rho.strip g ρ) =
      Q.extReads x (Rho.strip g (RoundsQueryLayout.zero (Q.shape.grind W g) A' wq.sh ρ))
    rw [sz]
  · show (Q.reads x (Rho.strip g ρ)
        (Plains.strip g (putB (Q.shape.grind W g) A' wq.sh ph nJ n0 pl))).map _ =
      (Q.reads x (Rho.strip g ρ) (Plains.strip g pl)).map _
    rw [hput]
  · intro w x c ρ hv hρ hpass nJ n0 τ hτρ hτpl hτrd
    obtain ⟨c0, e⟩ := hs w x c
    rw [e] at hτpl hτrd
    have h1 : Rho.pass g τ.rho = true := by
      have : τ.rho = ρ := hτρ
      rw [this, ← hp]
      exact hpass
    have h2 : Q.accept x (H.ext w) (Tr.strip g τ) =
        Q.accept x (H.ext w) ((H.strat w x c0).run (Rho.strip g ρ)).1 := by
      refine hloc x _ _ _ _ ?_ ?_ (fun _ _ => rfl) fun p _ => ?_
      · rw [Tr.rho_strip, Strat.rho_run]
        exact congrArg (Rho.strip g) hτρ
      · rw [Tr.plains_strip]
        exact (congrArg (Plains.strip g) hτpl).trans
          ((hput _ _ _ _).trans
            ((Tr.plains_strip g _).symm.trans (congrArg Tr.plains (Strat.strip_run_grind g _ _ ρ))))
      · obtain ⟨p', rfl⟩ := (OPos.stripE (W := W) g).surjective p
        rw [Tr.read_strip]
        exact (congrArg (OSym.strip g p') (hτrd p')).trans
          ((Tr.read_strip g _ p').symm.trans
            (congrArg (fun t => Tr.read t (OPos.stripE g p')) (Strat.strip_run_grind g _ _ ρ)))
    show (Rho.pass g τ.rho && Q.accept x (H'.ext w) (Tr.strip g τ)) = true
    rw [h1, he, h2, hacc w x c0 _ hv fun hm => hρ ((hw w x ρ).2 hm)]
    rfl

/-! ## 3. The term for a failed search -/

/-- the term that stands for the probability that no attempt of a search passes, in a round with b
proof-of-work bits: (1 - 2^-b)^(mo b + 1); 0 in a round without -/
def failBits {W : Type} (D : GrData W) : ℕ → ℝ≥0∞
  | 0 => 0
  | b + 1 => (1 - ((2 : ℝ≥0∞) ^ (b + 1))⁻¹) ^ (D.mo (b + 1) + 1)

/-- the sum over the rounds -/
def gFail {W : Type} (D : GrData W) : {s : Shape} → GBits s → ℝ≥0∞
  | [], _ => 0
  | _ :: _, (b, g) => failBits D b + gFail D g

/-- The wire record's sum over the rounds of one local transcript of Batch is the sum over the list,
whatever the kinds of the rounds. -/
theorem cFail_grind (D : GrData W) :
    ∀ {s : Shape} {A : RoundSplits s} (ws : RoundsQueryLayout lam K s A) (g : GBits s),
      cFail (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g) = gFail D g
  | [], _, _, _ => rfl
  | _ :: _, (a, _), (_, ws), (b, g) => by
      refine congrArg₂ (· + ·) ?_ (cFail_grind D ws g)
      obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pe, own⟩ := a
      cases k <;> cases b <;> rfl

/-- The same for Test and Link. -/
theorem cFail_grindLocal (D : GrData W) :
    ∀ {s : Shape} (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)) (g : GBits s),
      cFail (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g) = gFail D g
  | [], _, _ => rfl
  | _ :: _, (_, ws), (b, g) => by
      refine congrArg₂ (· + ·) ?_ (cFail_grindLocal D ws g)
      cases b <;> rfl

/-! ## 4. The main statement -/

/-- The bound on the compiled verifier's queries is as before: the rounds and the numbers of
openings are those of the old wire record. -/
theorem tVB_wireGrind {I X : Type} {L : BatchProtocol I X} (Wr : QueryLayout lam L) (D : GrData W)
    (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) :
    tVB (Wr.grind D gT gL gB) = tVB Wr := by
  show ((L.offline.shape.grind W gT).length + 1 + _) + ((L.link.shape.grind W gL).length + 1 + _) +
      ((L.onlineBatch.loc.shape.grind W gB).length + 1 + _) = _
  rw [Shape.grind_length, Shape.grind_length, Shape.grind_length]
  rfl

/-- ε is the old formula at the old wire record. -/
theorem epsB_wireGrind {I X : Type} {L : BatchProtocol I X} (Wr : QueryLayout lam L) (D : GrData W)
    (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (M : LH.Nums) :
    epsB (Wr.grind D gT gL gB) M = epsB Wr M := by
  unfold epsB
  rw [tVB_wireGrind]

/-- Let W be an inhabited type of nonces, L a record of protocols with all properties, Wr a
well-formed wire record of L, gT, gL, gB lists of numbers of proof-of-work bits up to n ≤ λ, and D
data of the search that are well-formed up to n; and let soundness of `L.grind` at εs' be supplied.
Then `L.grind` and its wire record meet, with the numbers of L and εs', the three hypotheses of the
compiler theorem for such rounds that are about the protocols and the verifier's wire record:
`PropsNoAcc`, `OKG`, `GrFitB`.
And α is that of L plus (1 - 2^-b)^(mo b + 1) for each
round with such bits: of Test once, of Link once, of Batch N times, a shared round too. -/
def Spec.fitGrind : Prop :=
  ∀ (W : Type) [Inhabited W] (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (Wr : QueryLayout lam L) (D : GrData W)
      (n : ℕ) (Ryes Rno : I → X → Prop) (M : LH.Nums) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (εs' : ℝ≥0∞),
    L.Props Ryes Rno M → Wr.OKG → D.OK n → n ≤ lam → gT.AllLe n → gL.AllLe n →
    gB.AllLe n → (L.grind W gT gL gB).Sound Rno εs' →
    (L.grind W gT gL gB).PropsNoAcc Ryes Rno { M with εs := εs' } ∧
    (Wr.grind D gT gL gB).OKG ∧
    GrFitB (Wr.grind D gT gL gB) Ryes ∧
    alphaBG (Wr.grind D gT gL gB) { M with εs := εs' } =
      alphaB L M + (gFail D gT + gFail D gL + L.maxBatchSize * gFail D gB)

theorem fitGrind : Spec.fitGrind := by
  intro W _ I X lam L Wr D n Ryes Rno M gT gL gB εs' h hW hD hn hT hL hB hS
  refine ⟨grindPropsB W I X L Ryes Rno M gT gL gB εs' h hS,
    hW.grind hD hn hT hL hB, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact GrFit.of_strip gT (BatchHonestProver.ofHonest (L.honestOfflineProver.grind gT (GNon.nil W _))) (Wr.T.grindLocal D gT)
      _ L.honestOfflineProver (GNon.nil W _) (fun w x c => ⟨c.2, BatchOne.ofHonest_strat _ w x c⟩)
      (fun w x ρ => by rw [BatchOne.ofHonest_withheld]; rfl) (fun _ => rfl)
      (RoundsQueryLayout.zero_grindLocal D _ gT) (RoundsQueryLayout.pass_grindLocal D _ gT) (strip_putB_grindLocal D _ gT)
      h.complete.accT h.localT
  · exact GrFit.of_strip gL (BatchHonestProver.ofHonest (L.honestLinkProver.grind gL (GNon.nil W _)))
      (Wr.Lk.grindLocal D gL) _ L.honestLinkProver (GNon.nil W _)
      (fun w x c => ⟨c.2, BatchOne.ofHonest_strat _ w x c⟩)
      (fun w x ρ => by rw [BatchOne.ofHonest_withheld]; rfl) (fun _ => rfl)
      (RoundsQueryLayout.zero_grindLocal D _ gL) (RoundsQueryLayout.pass_grindLocal D _ gL) (strip_putB_grindLocal D _ gL)
      h.complete.accL h.localL
  · exact GrFit.of_strip gB (L.honestOnlineBatchProver.grind gB (GNon.nil W _)) (Wr.B.grind D gB) _ L.honestOnlineBatchProver.one
      (GNon.nil W _) (fun w x c => ⟨c, BatchGrind.one_strat_grind L.honestOnlineBatchProver gB _ w x c⟩)
      (BatchGrind.mem_one_withheld_grind L.honestOnlineBatchProver gB _) (fun _ => rfl) (RoundsQueryLayout.zero_grind D _ gB)
      (RoundsQueryLayout.pass_grind D _ gB) (strip_putB_grind D _ gB) h.complete.accB h.localB
  · show alphaB L M +
        (cFail _ _ (RoundsQueryLayout.grindLocal Wr.T.sh D gT) + cFail _ _ (RoundsQueryLayout.grindLocal Wr.Lk.sh D gL) +
          L.maxBatchSize * cFail _ _ (RoundsQueryLayout.grind Wr.B.sh D gB)) = _
    rw [cFail_grindLocal, cFail_grindLocal, cFail_grind]

end Compile.Batch
