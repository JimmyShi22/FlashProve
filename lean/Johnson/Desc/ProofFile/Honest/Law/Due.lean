-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Due.lean: the challenges that the library's slot draws, read as
Honest/Frame.lean's lists (`drawsAt`, Honest/Law/StratWords.lean), are such as the description's
rounds can draw (`Draws.due`, Honest/Frame.lean). This is the lemma `due_typed`. It is general in
the description, the data and the challenge kit (`CK`: the library's choice of the types of
challenges and of how a view shows them).

  `KindFits`        a round's data have the declared round's entry, and the kind of that entry's
                    name
  `drawFit_typed`   one round
  `drawsFit_typed`  one chain (with `drawnT_len`)
  `due_typed`       the three chains, with the empty challenge after the first

Limits.
  * Six hypotheses, none proved here: the data's entries and kinds, for each of the three chains;
    three clauses on the challenge kit, as one hypothesis; that no declared entry asks for more
    non-zero elements than elements; that the first chain's last declared round can draw the empty
    challenge.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.K12.Law.FitWritten
import Johnson.Desc.ProofFile.Honest.Law.StratWords
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT chainsOf drawnT)
open _root_.Run.PQ (CK)

variable {Xi TF TJ T3 : Type}

/-- A round's data have the declared round's entry, and the kind of that entry's name. -/
def KindFits (d : RDT) (z : Fmt.DeclaredRound) : Prop :=
  d.entry = z.entry ∧ Fmt.kindOf z.entry.name = some d.kind

theorem drawFit_typed {z : Fmt.DeclaredRound} {k : Fmt.Kind} {R : Fmt.Drawn}
    (hk : Fmt.kindOf z.entry.name = some k) (hF : H2K.Fit.FitsDrawn z.entry k R)
    (hw : ∀ u ∈ R.elems, u.1 < fieldPrimeWord ∧ u.2.1 < fieldPrimeWord ∧ u.2.2 < fieldPrimeWord)
    (hd : R.digest = none ∨ k = .sealed) (hz : z.entry.drawNZ ≤ z.entry.drawE) :
    drawFit z R = true := by
  have a2 : (R.elems.length == z.entry.drawE) = true := by
    rw [hF.elems hz]
    exact beq_self_eq_true _
  have a3 : (R.poss.length == z.entry.poss) = true := by
    rw [hF.poss]
    exact beq_self_eq_true _
  have a4 : (R.trits.length == z.entry.trits) = true := by
    rw [hF.trits]
    exact beq_self_eq_true _
  have a5 : (R.poss.all (· < 2 ^ z.entry.logN)) = true := by
    rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (hF.below x hx)
  have a6 : (R.trits.all fun t => t == -1 || t == 0 || t == 1) = true := by
    rw [List.all_eq_true]
    intro t ht
    rcases hF.signs t ht with rfl | rfl | rfl <;> rfl
  have a7 : drawsMarkedNonzeroHaveNonzeroWords z ⟨[], R⟩ = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    rw [hk, Option.any_some]
    exact H2K.Fit.zip_all_of_forall₂ _ _ hF.nz
  have a8 : (R.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true := by
    rw [List.all_eq_true]
    intro u hu
    obtain ⟨h1, h2, h3⟩ := hw u hu
    simp [h1, h2, h3]
  have a9 : (R.digest.isNone || Fmt.kindOf z.entry.name == some .sealed) = true := by
    rcases hd with h | h
    · rw [h]
      rfl
    · rw [hk, h]
      simp
  unfold drawFit
  rw [a2, a3, a4, a5, a6, a7, a8, a9]
  rfl

theorem drawnT_len (C : CK) : ∀ (ds : List RDT) (ρ : Iop.Rho (uLT C ds)),
    (drawnT C ds ρ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, ρ) => congrArg (· + 1) (drawnT_len C ds ρ)

section
variable (C : CK)
  (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
    (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
    ((C.dr e k c).digest = none ∨ k = .sealed))
include hC

theorem drawsFit_typed : ∀ (ds : List RDT) (zs : List Fmt.DeclaredRound),
    List.Forall₂ KindFits ds zs → (∀ z ∈ zs, z.entry.drawNZ ≤ z.entry.drawE) →
    ∀ ρ : Iop.Rho (uLT C ds), drawsFit zs (drawnT C ds ρ) = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | d :: ds, z :: zs, h, hz, (c, ρ) => by
    obtain ⟨⟨e1, e2⟩, h2⟩ := List.forall₂_cons.1 h
    obtain ⟨c1, c2, c3⟩ := hC d.entry d.kind (Iop.GChal.old (b := d.entry.work) c)
    have ih := drawsFit_typed ds zs h2 (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz')) ρ
    show (drawFit z (C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c)) &&
      drawsFit zs (drawnT C ds ρ)) = true
    generalize C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c) = R at c1 c2 c3 ⊢
    rw [e1] at c1
    rw [ih, drawFit_typed e2 c1 c2 c3 (hz z List.mem_cons_self)]
    rfl

theorem due_typed (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi}
    (h₁ : List.Forall₂ KindFits D.ds₁ F.roundsDeclaredByBlocks.1.dropLast)
    (h₂ : List.Forall₂ KindFits D.ds₂ F.roundsDeclaredByBlocks.2.1) (h₃ : List.Forall₂ KindFits D.ds₃ F.roundsDeclaredByBlocks.2.2)
    (hz : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE)
    (hs : ∃ d, F.roundsDeclaredByBlocks.1.getLast? = some d ∧ drawFit d ⟨[], [], [], none⟩ = true)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) : (drawsAt C D tF tJ t3 ρ).due F = true := by
  obtain ⟨d, hd, hd'⟩ := hs
  obtain ⟨A, hA⟩ := List.getLast?_eq_some_iff.1 hd
  have hdl : F.roundsDeclaredByBlocks.1.dropLast = A := by rw [hA, List.dropLast_concat]
  rw [hdl] at h₁
  have z1 : ∀ z ∈ A, z.entry.drawNZ ≤ z.entry.drawE := fun z hz' =>
    hz z (List.mem_append_left _ (List.mem_append_left _ (by
      rw [hA]
      exact List.mem_append_left _ hz')))
  have f1 := drawsFit_typed C hC D.ds₁ A h₁ z1 ((chainsOf C D tF tJ t3).rho₁ ρ)
  have f2 := drawsFit_typed C hC D.ds₂ _ h₂
    (fun z hz' => hz z (List.mem_append_left _ (List.mem_append_right _ hz')))
    ((chainsOf C D tF tJ t3).rho₂ ρ)
  have f3 := drawsFit_typed C hC D.ds₃ _ h₃ (fun z hz' => hz z (List.mem_append_right _ hz'))
    ((chainsOf C D tF tJ t3).rho₃ ρ)
  have hlen : (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).length = A.length := by
    rw [drawnT_len C, h₁.length_eq]
  have g1 : drawsFit F.roundsDeclaredByBlocks.1
      (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++ [⟨[], [], [], none⟩]) = true := by
    rw [hA, drawsFit_append, ← hlen, List.take_left' rfl, List.drop_left' rfl, f1]
    show (true && (drawFit d ⟨[], [], [], none⟩ && true)) = true
    rw [hd']
    rfl
  unfold Draws.due
  show (drawsFit F.roundsDeclaredByBlocks.1
      (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++ [⟨[], [], [], none⟩]) &&
    drawsFit F.roundsDeclaredByBlocks.2.1 (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) &&
    drawsFit F.roundsDeclaredByBlocks.2.2 (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)) &&
    (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++
      ([⟨[], [], [], none⟩] : List Fmt.Drawn)).getLast? ==
      some (⟨[], [], [], none⟩ : Fmt.Drawn)) = true
  rw [g1, f2, f3]
  simp

end

end ProofFile.Honest

#print axioms ProofFile.Honest.drawFit_typed
#print axioms ProofFile.Honest.drawnT_len
#print axioms ProofFile.Honest.drawsFit_typed
#print axioms ProofFile.Honest.due_typed
