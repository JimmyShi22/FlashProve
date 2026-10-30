-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/LawY.lean: **THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM, BOTH ARMS, WITH
THE BATCHING's CONVERSE OWED ONLY AT CHALLENGES BEHIND WHICH THE PIECE SAYS YES.** Definitions,
statements and proofs.

The proof lays a challenge c of "BAT"'s round into the counted set only where some transcript
behind that very c is accepted. So the set may ask that: then every guard of the block is at the
hand of whoever pays the count, at that c (`yes_acc` | `yes_accO`, `yes_pass0`, `yes_labels`,
`yes_free`, `yes_fits`, `yes_kept`). The premise gets weaker, the law stronger; the laws of
LawN.lean and OwnArm.lean follow from these.

  `leads_of_yes`: for every reduction: a promise is owed only at statements from which the verifier
    ever puts out.
  `BatAtY`: `BatAtN` with "some transcript behind c is accepted" in the place of "the work passes".
  `batAtY_of_N`: `BatAtN` gives it.
  `K12LawY`, `k12_lawY`; `K12LawYO`, `k12_lawYO`: the two arms.
The two proofs' texts were made of `k12_lawN`'s and `k12_lawNO`'s own by a program that turns two
places each.
Limits: those of Sheet.lean, Law.lean, LawN.lean, OwnArm.lean. NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.K12.Coin.OwnArm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK
open H2K.Pub
open H2K.First (gpL Plain)

/-- A promise is owed only at statements from which the verifier ever puts out. -/
theorem leads_of_yes {A B : Type} {K : Reduction A B} {on : A → Prop} {Q : A → B → Prop}
    {ε : Err K.shape} (h : K.Leads on Q ε) :
    K.Leads (fun a => (∃ τ b, K.out a τ = some b) → on a) Q ε := by
  intro a ha
  by_cases hy : ∃ τ b, K.out a τ = some b
  · exact h a (ha hy)
  · exact Doomed.of_forall _ _ fun τ b hb => absurd ⟨τ, b, hb⟩ hy

/-- The batching's converse at one statement, towards N, counted at the challenges behind which the
piece says yes. -/
def BatAtY (F : Frame) (W : Type) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ)
    (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (N : ConclK F)
    (x : T12 × F.E.Str) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (row₀ : GroupRow) (hok : H2K.First.ok (gpL π a row₀ D) = true), Fixes π x.1 a rest G0 Ly D →
    ∀ m : (roundT (ckP .two) dB).up.Msg,
    cnt (fun c : (roundT (ckP .two) dB).up.Chal =>
      (∃ (τ : Iop.Tr (uLT (ckP .two) dt)) (b : T12 × F.E.Str),
        (pieceT F W π base dB dt e₀ εt).ior.red.out x (m, c, τ) = some b) ∧
      ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
        First.Close.bat x.1.st x.1.g dB.entry (noDigest (r0Of dB m c)) =
          .ok (row, Ly, begun x.1.st x.1.g G0) ∧
        (sgOf a).RIn (rad (sgOf a))
          (stmG (sgOf a) row, yOf π a row₀ D hok rd (W0 F no D.book x.2)) w ∧
        ¬ N x a rest G0 Ly D) ≤ e₀

theorem batAtY_of_N (F : Frame) (W : Type) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (N : ConclK F)
    (x : T12 × F.E.Str) (h : BatAtN F π no rad rd dB e₀ N x) :
    BatAtY F W π no rad rd base dB dt e₀ εt N x := by
  intro a rest G0 Ly D row₀ hok hf m
  refine le_trans (cnt_mono ?_) (h a rest G0 Ly D row₀ hok hf m)
  rintro c ⟨⟨τ, b, hb⟩, hc⟩
  exact ⟨yes_pass0 F π base dB dt e₀ εt x m c τ b hb, hc⟩

def K12LawY : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (N : ConclK F),
    AtPlace F π num L mC mS mW rad base dB dt εt →
    (pieceT F W π base dB dt e₀ εt).ior.red.Leads
      (fun x => FirstOpens π num no base x.1 ∧ BatAtY F W π no rad rd base dB dt e₀ εt N x)
      (fun x _ => QN π N x) (pieceT F W π base dB dt e₀ εt).err

def K12LawYO : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (N : ConclK F),
    AtPlaceOwn F π num L mC mS mW rad base dB dt εt →
    (pieceT F W π base dB dt e₀ εt).ior.red.Leads
      (fun x => FirstOpensOwn π num no base x.1 ∧ BatAtY F W π no rad rd base dB dt e₀ εt N x)
      (fun x _ => QN π N x) (pieceT F W π base dB dt e₀ εt).err

/-- **THE FIRST ARM.** -/
theorem k12_lawY : K12LawY := by
  intro F W π num no L mC mS mW rad rd base dB dt e₀ εt N hA x hx
  obtain ⟨hfo, hbat⟩ := hx
  obtain ⟨w0, l, hw, hlike⟩ := hA.like
  cases hlike with
  | cons hB hT =>
  obtain ⟨lo, rfl, hlo⟩ := like_lo dt l hT
  show ∀ m : (roundT (ckP .two) dB).up.Msg,
    cnt (fun c : (roundT (ckP .two) dB).up.Chal =>
      ¬ Doomed (uLT (ckP .two) (lo.map mk)) εt fun τ =>
        ∀ b, (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b →
          QN π N x) ≤ e₀
  intro m
  by_cases hany : ∃ c τ b,
      (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b
  · obtain ⟨c₀, τ₀, b₀, hb₀⟩ := hany
    obtain ⟨a, rest, ch, hR, G0, Ly, D, row₀, hok₀, e3, hfix, hpub, _, _, _⟩ :=
      yes_acc F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c₀ τ₀ b₀ hb₀
    refine le_trans (cnt_mono ?_) (hbat a rest G0 Ly D row₀ hok₀ hfix m)
    intro c hc
    by_contra hnot
    apply hc
    by_cases hyc : ∃ τ b,
        (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b
    · obtain ⟨τ₁, b₁, hb₁⟩ := hyc
      obtain ⟨a', rest', ch', hR', G0', Ly', D', row, hok, e3', hfix', _, hbt, _, _⟩ :=
        yes_acc F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c τ₁ b₁ hb₁
      obtain ⟨rfl, rfl⟩ := List.cons.inj (hfix'.1.symm.trans hfix.1)
      obtain rfl := Option.some.inj (e3'.symm.trans e3)
      obtain rfl := Option.some.inj (hfix'.2.1.symm.trans hfix.2.1)
      obtain rfl := Option.some.inj (hfix'.2.2.1.symm.trans hfix.2.2.1)
      obtain rfl := Option.some.inj ((hfix'.2.2.2 row).symm.trans (hfix.2.2.2 row))
      by_cases hN : N x a' rest' G0' Ly' D'
      · exact Doomed.of_forall _ _ fun τ b _ => ⟨a', rest', G0', Ly', D', hfix, hN⟩
      · have hno : ∀ w, ¬ (sgOf a').RIn (rad (sgOf a'))
            (stmG (sgOf a') row, yOf π a' row D' hok rd (W0 F no D'.book x.2)) w :=
          fun w hw' => hnot ⟨⟨τ₁, b₁, hb₁⟩, row, w, hbt, hw', hN⟩
        obtain ⟨hH, hrad⟩ := holds_at π L mC mS mW rad x.1.st.codes hpub hA.spend hA.codes a' rest'
          w0 l ch' hfix.1 hw e3
        classical
        have hd := chain_many_list ch' hH (stmG (sgOf a') row)
          (yOf π a' row D' hok rd (W0 F no D'.book x.2))
          (zOf π a' row D' hok rd (W0 F no D'.book x.2) (W0 F no D'.book x.2 D'.fresh.t))
          (fun _ _ => 0) (by rw [hrad]; exact hno)
          (fun τ' => decide (ch'.Acc (stmG (sgOf a') row)
              (yOf π a' row D' hok rd (W0 F no D'.book x.2))
              (zOf π a' row D' hok rd (W0 F no D'.book x.2) (W0 F no D'.book x.2 D'.fresh.t))
              (fun _ _ => 0) (blOf ch' τ') ∧
            PQ.passSL (ckP .two) ch'.rds (PQ.rhoSL (ckP .two) ch'.rds τ') = true))
          (fun b hb => by
            have h := of_decide_eq_true hb
            rw [blOf_trL] at h
            exact h)
        have hd2 := doomed_back (ckP .two) lo _ _ (doomed_castL hR _ _ hd)
        refine Doomed.mono _ _ ?_ (Doomed.mono_err _ (bears_le _ _ εt ?_) hd2)
        · intro τ hτ b hb
          exfalso
          obtain ⟨a₂, rest₂, ch₂, hR₂, G₂, Ly₂, D₂, row₂, hok₂, e3₂, hfix₂, _, hbt₂, hacc₂,
            hpass₂⟩ :=
            yes_acc F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c τ b hb
          obtain ⟨rfl, rfl⟩ := List.cons.inj (hfix₂.1.symm.trans hfix.1)
          obtain rfl := Option.some.inj (e3₂.symm.trans e3)
          obtain rfl := Option.some.inj (hfix₂.2.1.symm.trans hfix.2.1)
          obtain rfl := Option.some.inj (hfix₂.2.2.1.symm.trans hfix.2.2.1)
          obtain rfl := Option.some.inj ((hfix₂.2.2.2 row).symm.trans (hfix.2.2.2 row))
          obtain rfl : row₂ = row := congrArg Prod.fst (Except.ok.inj (hbt₂.symm.trans hbt))
          have ht : decide (ch₂.Acc (stmG (sgOf a₂) row₂)
              (yOf π a₂ row₂ D₂ hok rd (W0 F no D₂.book x.2))
              (zOf π a₂ row₂ D₂ hok rd (W0 F no D₂.book x.2) (W0 F no D₂.book x.2 D₂.fresh.t))
              (fun _ _ => 0) (blOf ch₂ (castT hR.symm (trW (ckP .two) lo τ))) ∧
            PQ.passSL (ckP .two) ch₂.rds
              (PQ.rhoSL (ckP .two) ch₂.rds (castT hR.symm (trW (ckP .two) lo τ))) = true) = true :=
            decide_eq_true ⟨hacc₂, hpass₂⟩
          exact Bool.noConfusion (ht.symm.trans hτ)
        · unfold Bears
          rw [errList_errW, errList_cast]
          exact hA.bears a' rest' w0 l ch' hfix.1 hw e3
    · exact Doomed.of_forall _ _ fun τ b hb => absurd ⟨τ, b, hb⟩ hyc
  · exact le_trans (le_of_eq (cnt_false fun c hc =>
      hc (Doomed.of_forall _ _ fun τ b hb => absurd ⟨c, τ, b, hb⟩ hany))) (Nat.zero_le _)

/-- **THE SECOND ARM: THE FIRST FOLD SENDS ITS OWN MASK.** -/
theorem k12_lawYO : K12LawYO := by
  intro F W π num no L mC mS mW rad rd base dB dt e₀ εt N hA x hx
  obtain ⟨hfo, hbat⟩ := hx
  obtain ⟨w0, l, hw, hlike⟩ := hA.like
  cases hlike with
  | cons hB hT =>
  obtain ⟨lo, rfl, hlo⟩ := like_lo dt l hT
  show ∀ m : (roundT (ckP .two) dB).up.Msg,
    cnt (fun c : (roundT (ckP .two) dB).up.Chal =>
      ¬ Doomed (uLT (ckP .two) (lo.map mk)) εt fun τ =>
        ∀ b, (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b →
          QN π N x) ≤ e₀
  intro m
  by_cases hany : ∃ c τ b,
      (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b
  · obtain ⟨c₀, τ₀, b₀, hb₀⟩ := hany
    obtain ⟨a, rest, ch, hR, G0, Ly, D, row₀, hok₀, e3, hfix, hpub, _, _, _⟩ :=
      yes_accO F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c₀ τ₀ b₀ hb₀
    refine le_trans (cnt_mono ?_) (hbat a rest G0 Ly D row₀ hok₀ hfix m)
    intro c hc
    by_contra hnot
    apply hc
    by_cases hyc : ∃ τ b,
        (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b
    · obtain ⟨τ₁, b₁, hb₁⟩ := hyc
      obtain ⟨a', rest', ch', hR', G0', Ly', D', row, hok, e3', hfix', _, hbt, _, _⟩ :=
        yes_accO F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c τ₁ b₁ hb₁
      obtain ⟨rfl, rfl⟩ := List.cons.inj (hfix'.1.symm.trans hfix.1)
      obtain rfl := Option.some.inj (e3'.symm.trans e3)
      obtain rfl := Option.some.inj (hfix'.2.1.symm.trans hfix.2.1)
      obtain rfl := Option.some.inj (hfix'.2.2.1.symm.trans hfix.2.2.1)
      obtain rfl := Option.some.inj ((hfix'.2.2.2 row).symm.trans (hfix.2.2.2 row))
      by_cases hN : N x a' rest' G0' Ly' D'
      · exact Doomed.of_forall _ _ fun τ b _ => ⟨a', rest', G0', Ly', D', hfix, hN⟩
      · have hno : ∀ w, ¬ (sgOf a').RIn (rad (sgOf a'))
            (stmG (sgOf a') row, yOf π a' row D' hok rd (W0 F no D'.book x.2)) w :=
          fun w hw' => hnot ⟨⟨τ₁, b₁, hb₁⟩, row, w, hbt, hw', hN⟩
        obtain ⟨hH, hrad⟩ := holds_at π L mC mS mW rad x.1.st.codes hpub hA.spend hA.codes a' rest'
          w0 l ch' hfix.1 hw e3
        classical
        have hd := chain_many_list_own ch' hH (stmG (sgOf a') row)
          (yOf π a' row D' hok rd (W0 F no D'.book x.2))
          (fun m₁ => zOf π a' row D' hok rd (W0 F no D'.book x.2) (fMown ch' D' m₁))
          (fun _ _ => 0) (by rw [hrad]; exact hno)
          (fun τ' => decide (ch'.Acc (stmG (sgOf a') row)
              (yOf π a' row D' hok rd (W0 F no D'.book x.2))
              (zOf π a' row D' hok rd (W0 F no D'.book x.2) (fMown ch' D' (msg1 ch' (blOf ch' τ'))))
              (fun _ _ => 0) (blOf ch' τ') ∧
            PQ.passSL (ckP .two) ch'.rds (PQ.rhoSL (ckP .two) ch'.rds τ') = true))
          (fun b hb => by
            have h := of_decide_eq_true hb
            rw [blOf_trL] at h
            exact h)
        have hd2 := doomed_back (ckP .two) lo _ _ (doomed_castL hR _ _ hd)
        refine Doomed.mono _ _ ?_ (Doomed.mono_err _ (bears_le _ _ εt ?_) hd2)
        · intro τ hτ b hb
          exfalso
          obtain ⟨a₂, rest₂, ch₂, hR₂, G₂, Ly₂, D₂, row₂, hok₂, e3₂, hfix₂, _, hbt₂, hacc₂,
            hpass₂⟩ :=
            yes_accO F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c τ b
              hb
          obtain ⟨rfl, rfl⟩ := List.cons.inj (hfix₂.1.symm.trans hfix.1)
          obtain rfl := Option.some.inj (e3₂.symm.trans e3)
          obtain rfl := Option.some.inj (hfix₂.2.1.symm.trans hfix.2.1)
          obtain rfl := Option.some.inj (hfix₂.2.2.1.symm.trans hfix.2.2.1)
          obtain rfl := Option.some.inj ((hfix₂.2.2.2 row).symm.trans (hfix.2.2.2 row))
          obtain rfl : row₂ = row := congrArg Prod.fst (Except.ok.inj (hbt₂.symm.trans hbt))
          have ht : decide (ch₂.Acc (stmG (sgOf a₂) row₂)
              (yOf π a₂ row₂ D₂ hok rd (W0 F no D₂.book x.2))
              (zOf π a₂ row₂ D₂ hok rd (W0 F no D₂.book x.2)
                (fMown ch₂ D₂ (msg1 ch₂ (blOf ch₂ (castT hR.symm (trW (ckP .two) lo τ))))))
              (fun _ _ => 0) (blOf ch₂ (castT hR.symm (trW (ckP .two) lo τ))) ∧
            PQ.passSL (ckP .two) ch₂.rds
              (PQ.rhoSL (ckP .two) ch₂.rds (castT hR.symm (trW (ckP .two) lo τ))) = true) = true :=
            decide_eq_true ⟨hacc₂, hpass₂⟩
          exact Bool.noConfusion (ht.symm.trans hτ)
        · unfold Bears
          rw [errList_errW, errList_cast]
          exact hA.bears a' rest' w0 l ch' hfix.1 hw e3
    · exact Doomed.of_forall _ _ fun τ b hb => absurd ⟨τ, b, hb⟩ hyc
  · exact le_trans (le_of_eq (cnt_false fun c hc =>
      hc (Doomed.of_forall _ _ fun τ b hb => absurd ⟨c, τ, b, hb⟩ hany))) (Nat.zero_le _)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.leads_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.batAtY_of_N
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawY
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawYO
