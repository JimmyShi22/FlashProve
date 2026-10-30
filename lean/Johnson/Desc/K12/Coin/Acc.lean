-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Acc.lean: WHERE THE PIECE SAYS YES, THE LIBRARY's CHAIN SAYS YES IN THE FIELD,
AT THE SAME TRANSCRIPT. Statements and proofs.

  `step_k`: `Block.step` takes as many columns as it reads.
  `yes_acc`: **the one premise with content.** Under `AtPlace` and `FirstOpens`: where the piece of
    `proximityTestKind guardedProximityTestParts π` puts out at the transcript (m, c, τ): the place's chain ch over its written
    rounds; what the record fixes (`Fixes`); `pubOk`; the batching returned AT THE STRETCH's OWN
    ENTRY on "BAT"'s round as (m, c) shows it; `ch.Acc` of the batched row, at the group's word and
    the mask's word read off THE STATEMENT's OWN ORACLES (`W0`), at τ read as the chain's blocks'
    transcripts; and all tests of work behind "BAT" pass.
By `k12_step_accH` (Johnson/Desc/K12/Law/TopH.lean), whose two sentences on the view are paid here:
the rounds by `rvT_trW`, `rvSL_cast`, `trL_blOf`; the columns by `follows_of_yes`, `first_cols`,
`own_cols`.
-/
import Johnson.Desc.K12.Coin.First
import Johnson.Desc.K12.Coin.Entry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK
open H2K.Pub (pubOk sgOf writtenOf WR chainFrom)
open H2K.First (gpOf gpL Plain made_of keyAt_of)

theorem step_k {S Cl : Type} {ft : ℕ} {b : Block S Cl} {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {s' : S} {k : ℕ} (H : b.step ft s rs cols = .ok (s', k)) :
    k = ((groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id).length := by
  unfold Block.step at H
  obtain ⟨_, _, H⟩ := bindOk H
  obtain ⟨_, _, H⟩ := bindOk H
  obtain ⟨t, _, H⟩ := bindOk H
  exact (congrArg Prod.snd (Except.ok.inj H)).symm

theorem yes_acc {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (lo : List (PQ.RD × List ℕ)) (e₀ : ℕ) (εt : Err (uLT (ckP .two) (lo.map mk)))
    (hA : AtPlace F π num L mC mS mW rad base dB (lo.map mk) εt) (w0 : WR) (l : List WR)
    (hw : writtenOf π.nums = some (w0 :: l)) (hB : Like dB w0) (hlo : lo.map (·.1) = l.map WR.rd)
    (x : T12 × F.E.Str) (hfo : FirstOpens π num no base x.1)
    (m : (roundT (ckP .two) dB).up.Msg) (c : (roundT (ckP .two) dB).up.Chal)
    (τ : Iop.Tr (uLT (ckP .two) (lo.map mk))) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (ch : OnBytes.Slice.Chain (sgOf a))
      (hR : ch.rds = lo.map (·.1)) (G0 : Group) (Ly : GroupLayout) (D : Plain) (row : GroupRow)
      (hok : H2K.First.ok (gpL π a row D) = true),
      chainFrom (.at L mC mS mW rad) rest a l = some ch ∧ Fixes π x.1 a rest G0 Ly D ∧
      pubOk π x.1.st.codes = true ∧
      First.Close.bat x.1.st x.1.g dB.entry (noDigest (r0Of dB m c)) =
        .ok (row, Ly, begun x.1.st x.1.g G0) ∧
      ch.Acc (stmG (sgOf a) row) (yOf π a row D hok rd (W0 F no D.book x.2))
        (zOf π a row D hok rd (W0 F no D.book x.2) (W0 F no D.book x.2 D.fresh.t)) (fun _ _ => 0)
        (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) ∧
      PQ.passSL (ckP .two) ch.rds
        (PQ.rhoSL (ckP .two) ch.rds (castT hR.symm (trW (ckP .two) lo τ))) = true := by
  obtain ⟨ht, k, hst, hdrop⟩ :=
    yes_step (pieceT F W π base dB (lo.map mk) e₀ εt) rfl x (m, c, τ) b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: lo.map mk) (m, c, τ))
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ x.2 (m, c, τ)).opened =
      .ok (b.1, k) := hst
  have hdrop' : (sView (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ x.2
      (m, c, τ)).opened.drop k = [] := hdrop
  rw [step_k hst'] at hdrop'
  obtain ⟨hfit, hcols, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨a, rest, w0', l', ch, e1, e2, e3, e4, e5, e, r, row, Ly, S', G0, g1, g2, g3, g4, g5, D,
    hok, g6, g7⟩ := k12_step_accH (.at L mC mS mW rad) π hA.early hA.answers x.1 hA.planOk F.ft b.1
      _ _ k hst'
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (e2.symm.trans hw))
  have hR : ch.rds = lo.map (·.1) := e4.trans hlo.symm
  subst g5
  have hfix : Fixes π x.1 a rest G0 Ly D := ⟨e1, g3, g4, fun _ => g6⟩
  obtain ⟨f1, f2⟩ := hfo a rest G0 Ly D hfix
  obtain ⟨_, hpub, _⟩ := k12_guards π hA.early x.1 b.1 _ _ hA.planOk hdec
  obtain ⟨r', row', L', S'', q1, q2⟩ := k12_bat_entry π x.1 b.1 _ _ hA.planOk hdec w0' l' hw
  have hr : r' = r := by
    rw [g1] at q1
    exact (List.cons.inj q1).1.symm
  subst hr
  cases bat_unique _ _ _ _ _ _ _ g2 q2
  have hr0 : r' = noDigest (r0Of dB m c) := by
    have h1 : ((rvT (ckP .two) (dB :: lo.map mk) (m, c, τ)).map noDigest).take 1 =
        [noDigest (r0Of dB m c)] := rfl
    rw [g1] at h1
    exact (List.cons.inj h1).1
  rw [hr0, ← hB.1] at q2
  have hm := made_of π _ a Ly D g6
  refine ⟨a, rest, ch, hR, G0, Ly, D, row, hok, e3, hfix, hpub, q2, ?_, ?_⟩
  · have hacc := g7 rd (fun z => (W0 F no D.book x.2 z).1) (fun z => (W0 F no D.book x.2 z).2)
      (fun i => by
        show 2 ^ H2K.First.logAt D.book (D.mems.get i).t = _
        rw [(keyAt_of (F := 0) (hm.mem i).2).2])
      (by
        show 2 ^ H2K.First.logAt D.book D.fresh.t = _
        rw [(keyAt_of (F := 0) hm.fresh).2])
      (fun _ _ => 0) (blOf ch (castT hR.symm (trW (ckP .two) lo τ)))
      (by
        show (rvT (ckP .two) (lo.map mk) τ).map noDigest = _
        rw [← rvSL_trL ch, trL_blOf, rvSL_cast, rvT_trW])
      (follows_of_yes F π num base (dB :: lo.map mk) hA.planOk hA.deal a rest e1 ch e5 x.2 (m, c, τ)
        hA.wants hfit hcols hdrop' D.ts _
        (first_cols F π num no base (dB :: lo.map mk) x.2 (m, c, τ) _ a row Ly D g6 hok f1 f2) _
        (own_cols F π num base dB lo x.2 m c τ ch hR (hA.trees a rest w0' l' ch e1 hw e3) hA.own0
          hA.numOwn hA.batNone))
    unfold yOf zOf
    exact hacc
  · rw [pass_cast, pass_trW]
    have h1 : (passT (ckP .two) (dB :: lo.map mk) (rhoT (ckP .two) (dB :: lo.map mk) (m, c, τ)) &&
        fullOf (dB :: lo.map mk) (drawnT (ckP .two) (dB :: lo.map mk)
          (rhoT (ckP .two) (dB :: lo.map mk) (m, c, τ))) &&
        sCarries ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ x.2
          (sWants (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩
            (rhoT (ckP .two) (dB :: lo.map mk) (m, c, τ)))) = true := ht
    rw [Bool.and_eq_true, Bool.and_eq_true] at h1
    have h2 : (GChal.pass (b := dB.entry.work) c &&
        passT (ckP .two) (lo.map mk) (rhoT (ckP .two) (lo.map mk) τ)) = true := h1.1.1
    rw [Bool.and_eq_true] at h2
    exact h2.2

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yes_acc
