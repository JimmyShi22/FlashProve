-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Law.lean: **THE LAW OF THE PROXIMITY TEST (the kind K12) IN THE PLAIN FORM, AT
THE BLOCK's OWN RECORD: PROVED, UNDER THE SHEET's NAMED PREMISES.** Statements and proofs.

  `holds_at`: the library's `Chain.Holds` of the place's chain, and its first radius, from `pubOk`,
    `spendOk` and `CodesAt`: the proof of `K12Condition.gives`
    (Johnson/Desc/K12/Law/ChainHolds.lean) without its field on the errors' size.
  `k12_lawT`: `K12LawT` (Sheet.lean).
How it goes. "The prover has lost" at a first round says: whatever message, few challenges lead on.
A challenge c of "BAT"'s round leads on only if the batching returns a row that has a witness within
the radius while there is no one witness for all rows: these `BatAt` counts. At every other c:
either no transcript behind c is accepted; or there is one witness for all rows, which is the
conclusion; or the batched row has no witness within the radius: then the library's law on the chain
(`chain_many_list`, OnBytes/Slice/ManyCloses.lean) says that the prover has lost towards "the chain
does not say yes in the field, or a test of work fails"; that loss is carried to the stretch's own
rounds (`doomed_castL`, `doomed_back`), and where the piece says yes the chain does (`yes_acc`).
Limits: those of Sheet.lean: NO SOUNDNESS IS CLAIMED: `BatAt`, `CodesAt` and the bound on the errors
are premises; no member of `AtPlace` is known; that the piece ever says yes is not shown.

-/
import Johnson.Desc.K12.Coin.Acc

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

theorem holds_at (π : P12) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (K : Codes)
    (hpub : pubOk π K = true) (hspend : spendOk π = true)
    (hcodes : CodesAt L mC mS mW rad π.nums.stages) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (ch : OnBytes.Slice.Chain (sgOf a))
    (e1 : π.nums.stages = a :: rest) (e2 : writtenOf π.nums = some (w0 :: l))
    (e3 : chainFrom (.at L mC mS mW rad) rest a l = some ch) :
    ch.Holds ∧ ch.rad = rad (sgOf a) := by
  obtain ⟨a', rest', w0', l', c', f1, f2, f3, _, _, f6⟩ :=
    pub_of_ok (.at L mC mS mW rad) π K hpub
  obtain ⟨rfl, rfl⟩ := List.cons.inj (f1.symm.trans e1)
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (f2.symm.trans e2))
  obtain rfl := Option.some.inj (f3.symm.trans e3)
  obtain ⟨cu, restI, g1, g2⟩ : ∃ cu restI, stageAt π 0 a' = some cu ∧
      stagesAt π 1 rest' = some restI := by
    have hp := hpub
    unfold pubOk pubL at hp
    rw [e1, e2] at hp
    exact walk_forms π K rest' 0 a' l' hp
  exact ⟨holds_on L mC mS mW c' cu restI (f6 a' rest' cu restI e1 g1 g2)
    (spend_of_ok _ π hspend a' rest' w0' l' c' e1 e2 e3)
    (okOn_chainFrom L mC mS mW rad rest' a' l' c' e3 (e1 ▸ hcodes)),
    rad_chainFrom _ rest' a' l' c' e3⟩

/-- **THE LAW OF THE KIND K12, AT ITS OWN RECORD.** -/
theorem k12_lawT : K12LawT := by
  intro F W π num no L mC mS mW rad rd base dB dt e₀ εt hA x hx
  obtain ⟨_, hfo, hbat⟩ := hx
  obtain ⟨w0, l, hw, hlike⟩ := hA.like
  cases hlike with
  | cons hB hT =>
  obtain ⟨lo, rfl, hlo⟩ := like_lo dt l hT
  show ∀ m : (roundT (ckP .two) dB).up.Msg,
    cnt (fun c : (roundT (ckP .two) dB).up.Chal =>
      ¬ Doomed (uLT (ckP .two) (lo.map mk)) εt fun τ =>
        ∀ b, (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b →
          QK F π no rad rd x) ≤ e₀
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
      by_cases hN : NearAll π a' D' rd (W0 F no D'.book x.2) (rad (sgOf a'))
          (rowG (begun x.1.st x.1.g G0') Ly' x.1.g) (runRows x.1.st G0').toList
      · exact Doomed.of_forall _ _ fun τ b _ => ⟨a', rest', G0', Ly', D', hfix, hN⟩
      · have hno : ∀ w, ¬ (sgOf a').RIn (rad (sgOf a'))
            (stmG (sgOf a') row, yOf π a' row D' hok rd (W0 F no D'.book x.2)) w :=
          fun w hw' => hnot ⟨row, w, hbt, hw', hN⟩
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

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.holds_at
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawT
