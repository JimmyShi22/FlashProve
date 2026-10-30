-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/LawN.lean: **THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM, WITH A LETTER
FOR WHAT IS CONCLUDED.** Definitions, one statement and its proof; and the sheet's law again, from
it.

The proof of `k12_lawT` (Law.lean) spends `NearAll` as an unopened proposition: in a split by cases,
as the conclusion, and under the "not" inside the count of `BatAt`. So any proposition N of the
statement and of what the record fixes may stand in its place: whoever has the batching's converse
in another tongue ("either all rows say so of these tables, or the drawn element is one of few")
sets N and pays that count. And "the first fold's mask has come" is not spent: it is no part of the
promise here.

  `BatAtN`: at all but e₀ values of "BAT"'s challenge: if the round's own test of work passes and
    the row batched at the stretch's own entry has a witness within the radius of the group's word,
    then N. (A yes of the piece has that test of work, `yes_pass0`; it lets the count go by typed
    values: Vals.lean.)
  `QN`: what the record fixes, and N of it. `K12LawN`, `k12_lawN`: the law.
  `k12_lawT'`: `K12LawT` again, as the case N := `NearAll …`.
The proof's text was made of `k12_lawT`'s own text by a program that turns four places.
Limits: those of Sheet.lean and Law.lean. NO SOUNDNESS IS CLAIMED. At N := "true" the law says only
what the record fixes; at N := "false" `BatAtN` asks that few challenges give a batched row with a
witness: what N is worth is the reader's to look at.

-/
import Johnson.Desc.K12.Coin.Law

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

/-- What is concluded, as a letter: of the statement and of what its record fixes. -/
abbrev ConclK (F : Frame) : Type :=
  T12 × F.E.Str → Fmt.M1.Stage → List Fmt.M1.Stage → Group → GroupLayout → Plain → Prop

/-- The batching's converse at one statement, towards N. -/
def BatAtN (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT) (e₀ : ℕ)
    (N : ConclK F) (x : T12 × F.E.Str) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (row₀ : GroupRow) (hok : H2K.First.ok (gpL π a row₀ D) = true), Fixes π x.1 a rest G0 Ly D →
    ∀ m : (roundT (ckP .two) dB).up.Msg,
    cnt (fun c : (roundT (ckP .two) dB).up.Chal =>
      GChal.pass (b := dB.entry.work) c = true ∧
      ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
        First.Close.bat x.1.st x.1.g dB.entry (noDigest (r0Of dB m c)) =
          .ok (row, Ly, begun x.1.st x.1.g G0) ∧
        (sgOf a).RIn (rad (sgOf a))
          (stmG (sgOf a) row, yOf π a row₀ D hok rd (W0 F no D.book x.2)) w ∧
        ¬ N x a rest G0 Ly D) ≤ e₀

/-- Where the piece says yes, "BAT"'s own test of work has passed. -/
theorem yes_pass0 {W : Type} (F : Frame) (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str) (m : (roundT (ckP .two) dB).up.Msg)
    (c : (roundT (ckP .two) dB).up.Chal) (τ : Iop.Tr (uLT (ckP .two) dt)) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB dt e₀ εt).ior.red.out x (m, c, τ) = some b) :
    GChal.pass (b := dB.entry.work) c = true := by
  obtain ⟨ht, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x (m, c, τ) b hb
  have h1 : (passT (ckP .two) (dB :: dt) (rhoT (ckP .two) (dB :: dt) (m, c, τ)) &&
      fullOf (dB :: dt) (drawnT (ckP .two) (dB :: dt) (rhoT (ckP .two) (dB :: dt) (m, c, τ))) &&
      sCarries ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2
        (sWants (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩
          (rhoT (ckP .two) (dB :: dt) (m, c, τ)))) = true := ht
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1
  have h2 : (GChal.pass (b := dB.entry.work) c &&
      passT (ckP .two) dt (rhoT (ckP .two) dt τ)) = true := h1.1.1
  rw [Bool.and_eq_true] at h2
  exact h2.1

/-- What the record fixes, and N of it. -/
def QN {F : Frame} (π : P12) (N : ConclK F) (x : T12 × F.E.Str) : Prop :=
  ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π x.1 a rest G0 Ly D ∧ N x a rest G0 Ly D

def K12LawN : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (N : ConclK F),
    AtPlace F π num L mC mS mW rad base dB dt εt →
    (pieceT F W π base dB dt e₀ εt).ior.red.Leads
      (fun x => FirstOpens π num no base x.1 ∧ BatAtN F π no rad rd dB e₀ N x)
      (fun x _ => QN π N x) (pieceT F W π base dB dt e₀ εt).err

/-- **THE LAW OF THE KIND K12, AT ITS OWN RECORD, WITH A LETTER FOR WHAT IS CONCLUDED.** -/
theorem k12_lawN : K12LawN := by
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
          fun w hw' => hnot ⟨yes_pass0 F π base dB (lo.map mk) e₀ εt x m c τ₁ b₁ hb₁, row, w, hbt,
            hw', hN⟩
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

/-- The sheet's law again, as a case. -/
theorem k12_lawT' : K12LawT := by
  intro F W π num no L mC mS mW rad rd base dB dt e₀ εt hA
  exact Reduction.Leads.conseq
    (k12_lawN F W π num no L mC mS mW rad rd base dB dt e₀ εt
      (fun x a _ G0 Ly D => NearAll π a D rd (W0 F no D.book x.2) (rad (sgOf a))
        (rowG (begun x.1.st x.1.g G0) Ly x.1.g) (runRows x.1.st G0).toList) hA)
    (fun _ hx => ⟨hx.2.1, fun a rest G0 Ly D row₀ hok hf m =>
      le_trans (cnt_mono fun _ hc => hc.2) (hx.2.2 a rest G0 Ly D row₀ hok hf m)⟩)
    (fun _ _ _ _ _ h => h)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_lawN
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawT'
